package command

import (
	"bytes"
	"database/sql"
	"encoding/json"
	"fmt"
	"io/ioutil"
	"log"
	"math"
	"net/http"
	"os"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"unicode/utf8"

	"github.com/missinglink/pbf/parser"
	"github.com/missinglink/pbf/sqlite"

	"github.com/missinglink/pbf/handler"
	"github.com/missinglink/pbf/lib"
	"github.com/missinglink/pbf/proxy"
	"github.com/missinglink/pbf/tags"

	geo "github.com/paulmach/go.geo"
	"github.com/urfave/cli"
)

type street struct {
	Path *geo.Path
	Name string
	Oneway string
	WayId int
}

type config struct {
	Format          string
	Delim           string
	ExtendedColumns bool
}

// A Response struct to map the Entire Response
type Response struct {
    Solutions []Solution `json:"solutions"`
}

// A Solution Struct to map every solution to.
type Solution struct {
    Score int            `json:"score"`
    Classifications []Classification `json:"classifications"`
}

// A struct to map our Classification which includes it's value
type Classification struct {
    Value string `json:"value"`
		Label string `json:"label"`
}

type Vector struct {
	dX float64
	dY float64
}

func (s *street) Print(conf *config) {

	// geojson
	// feature := s.Path.ToGeoJSON()
	// for _, way := range s.Ways {
	// 	for k, v := range way.Tags {
	// 		feature.SetProperty(k, v)
	// 	}
	// 	feature.SetProperty("id", way.ID)
	// }
	//
	// json, _ := feature.MarshalJSON()
	// fmt.Println(string(json))

	var cols []string

	switch conf.Format {
	case "geojson":
		bytes, err := s.Path.ToGeoJSON().MarshalJSON()
		if nil != err {
			log.Println("failed to marshal geojson")
			os.Exit(1)
		}
		cols = append(cols, string(bytes))
	case "wkt":
		cols = append(cols, s.Path.ToWKT())
	default:
		cols = append(cols, s.Path.Encode(1.0e6))
	}

	// extended columns
	if true == conf.ExtendedColumns {
		// mid-point centroid
		var centroid = s.Path.Interpolate(0.5)
		cols = append(cols, strconv.FormatFloat(centroid.Lng(), 'f', 7, 64))
		cols = append(cols, strconv.FormatFloat(centroid.Lat(), 'f', 7, 64))

		// geodesic distance in meters
		cols = append(cols, strconv.FormatFloat(s.Path.GeoDistance(), 'f', 0, 64))

		// bounds
		var bounds = s.Path.Bound()
		var sw = bounds.SouthWest()
		var ne = bounds.NorthEast()
		cols = append(cols, strconv.FormatFloat(sw.Lng(), 'f', 7, 64))
		cols = append(cols, strconv.FormatFloat(sw.Lat(), 'f', 7, 64))
		cols = append(cols, strconv.FormatFloat(ne.Lng(), 'f', 7, 64))
		cols = append(cols, strconv.FormatFloat(ne.Lat(), 'f', 7, 64))
	}

	cols = append(cols, s.Name)
	fmt.Println(strings.Join(cols, conf.Delim))
}

// StreetMerge cli command
func StreetMerge(c *cli.Context) error {
	// config
	var conf = &config{
		Format:          "polyline",
		Delim:           "\x00",
		ExtendedColumns: c.Bool("extended"),
	}
	switch strings.ToLower(c.String("format")) {
	case "geojson":
		conf.Format = "geojson"
	case "wkt":
		conf.Format = "wkt"
	}
	if "" != c.String("delim") {
		conf.Delim = c.String("delim")
	}

	// open sqlite database connection
	// note: sqlite is used to store nodes and ways
	filename := lib.TempFileName("pbf_", ".temp.db")
	defer os.Remove(filename)
	conn := &sqlite.Connection{}
	conn.Open(filename)
	defer conn.Close()

	// parse
	parsePBF(c, conn)
	var streets = generateStreetsFromWays(conn)
	var joined = joinStreets(streets)

	// print streets
	for _, street := range joined {
		// var normName = strings.ToLower(street.Name)
		// normName = removeAccent(normName)
		// normName = streetNameParser(normName)
		// street.Name = normName
		street.Print(conf)
	}

	// fmt.Println(len(ways))
	// fmt.Println(len(nodes))

	return nil
}

var debugMode = false

func joinStreets(streets []*street) []*street {

	var nameMap = make(map[string][]*street)
	var ret []*street
	// var merged = make(map[*street]bool)

	for _, st := range streets {
		var normName = strings.ToLower(st.Name)

		var normNameHasSign = normName

		// Convert to unasign vietnamese
		normName = removeAccent(normName)

		// Ignore "kiet", "hem", "cau", "vong xuyen"
		if strings.HasPrefix(normName, "kiet") ||
			strings.HasPrefix(normName, "hem") ||
			strings.HasPrefix(normName, "cau") ||
			strings.HasPrefix(normName, "vong xuyen") {
			continue
		}

		// TODO: Ignore "Ngõ Chu Huy Mân" to fix "Chu Huy Mân" street merge error
		if (normName == "ngo chu huy man") {
			continue
		}

		// Parse the street name
		// Add string "đường" to street name if it don't start with "đường"
		if !strings.HasPrefix(normNameHasSign, "đường") {
			normName = streetNameParser("duong " + normName)
		} else {
			normName = streetNameParser(normName)
		}

		if normName == "" {
			continue
		}
		// fmt.Println("debug::street::", normName)
		// log.Println("debug::street::", normName)
		st.Name = normName

		if _, ok := nameMap[normName]; !ok {
			nameMap[normName] = []*street{st}
		} else {
			nameMap[normName] = append(nameMap[normName], st)
		}
	}

	// var distanceGroup = 0.01 // roughly 1000 meters
	var distanceGroup = 0.003 // roughly 300 meters

	var groupDistanceNameMap = make(map[string][]*street)

	// Group the streets in distance not exceed 1 kilometers
	for _, strs := range nameMap {
		// Sort streets follow the descendant length
		strs = sortStreetsDescLength(strs)

		var normName = strings.ToLower(strs[0].Name)

		var baseStreet *street = nil
		var group = 1

		var streetGroup []*street = nil

		for i := 0; i < len(strs); i++ {
			if (i == 0) {
				baseStreet = strs[0]
				normName = strings.ToLower(baseStreet.Name)
				streetGroup = []*street{baseStreet}

				// Create a new group street
				normName += "__" + strconv.Itoa(group)
				group++
				groupDistanceNameMap[normName] = []*street{baseStreet}
				continue
			}

			var currentStreet = strs[i]

			// Check if distance from the street with street group < range then add street to group
			if (shortestDistanceToOtherStreets(currentStreet, streetGroup) < distanceGroup) {
				streetGroup = append(streetGroup, currentStreet)
				groupDistanceNameMap[normName] = append(groupDistanceNameMap[normName], currentStreet)
				strs = removeStreet(strs, i)
				// i--
				i = 0
				continue
			}

			// When to final element then remove first element from array, and loop array again
			if (i == (len(strs) - 1)) {
				strs = removeStreet(strs, 0)
				i = -1
			}
		}
	}

	var groupDirectionNameMap = make(map[string][]*street)

	// Group the street follow same direction together
	for groupStreetName, strs := range groupDistanceNameMap {
		// Sort streets follow the descendant length
		strs = sortStreetsDescLength(strs)

		var normName = groupStreetName

		var baseStreet *street = nil
		var baseVector *Vector = nil
		var group = 0

		for i := 0; i < len(strs); i++ {
			if (i == 0) {
				baseStreet = strs[0]
				baseVector = createPathVector(baseStreet.Path.First(), baseStreet.Path.Last())
			}

			// Only group streets when street is oneway
			if (strs[i].Oneway == "yes") {
				if debugMode {
					debugStreets(baseStreet, strs[i], normName, strs)
				}

				if (len(strs) <= 1) {
					// Create a new group street
					normName = groupStreetName + "--" + strconv.Itoa(group)
					group++

					if _, ok := groupDirectionNameMap[normName]; !ok {
						groupDirectionNameMap[normName] = []*street{baseStreet}
					} else {
						groupDirectionNameMap[normName] = append(groupDirectionNameMap[normName], baseStreet)
					}
					continue
				}

				if (i == 0) {
					// Create a new group street
					normName = groupStreetName + "--" + strconv.Itoa(group)
					group++

					if _, ok := groupDirectionNameMap[normName]; !ok {
						groupDirectionNameMap[normName] = []*street{baseStreet}
					} else {
						groupDirectionNameMap[normName] = append(groupDirectionNameMap[normName], baseStreet)
					}
					continue
				}

				var currentStreet = strs[i]

				var isTwoPathsSameDirection = isTwoPathsSameDirection(baseVector, createPathVector(currentStreet.Path.First(), currentStreet.Path.Last()))

				// Check distance between 2 street to divide group
				if (isTwoPathsSameDirection) {
					groupDirectionNameMap[normName] = append(groupDirectionNameMap[normName], currentStreet)
					strs = removeStreet(strs, i)
					i--
				}

				// When reach to the last item of list street, then remove the first item and loop again the list street
				if (i == (len(strs) - 1)) {
					strs = removeStreet(strs, 0)
					i = -1
				}

			} else {

				if _, ok := groupDirectionNameMap[groupStreetName]; !ok {
					groupDirectionNameMap[groupStreetName] = []*street{strs[i]}

				} else {
					groupDirectionNameMap[groupStreetName] = append(groupDirectionNameMap[groupStreetName], strs[i])

				}
				strs = removeStreet(strs, i)
				i--

				// When reach to the last item of list street, then remove the first item and loop again the list street
				if (i == (len(strs) - 1)) {
					strs = removeStreet(strs, 0)
					i = -1
				}
			}
		}
	}

	// DEBUG
	var mergedStreetSameDirection = mergeStreetSameDirection(groupDirectionNameMap, false)

	var mergeLaneSameDirection = mergeLaneSameDirection(mergedStreetSameDirection)

	// Merge one way and two way street together
	var mergedStreet = mergeStreet(mergeLaneSameDirection, false)

	// output lines in consistent order
	keys := make([]string, len(mergedStreet))
	for k := range mergedStreet {
		keys = append(keys, k)
	}
	sort.Strings(keys)

	for _, k := range keys {
		var strs = mergedStreet[k]

		if (strs == nil) {
			continue
		}

		for _, str := range strs {
			ret = append(ret, str)
		}
	}

	return ret
}

func loadStreetsFromDatabase(conn *sqlite.Connection, callback func(*sql.Rows)) {
	rows, err := conn.GetDB().Query(`
	SELECT
		ways.id,
		(
			SELECT GROUP_CONCAT(( nodes.lon || '#' || nodes.lat ))
			FROM way_nodes
			JOIN nodes ON way_nodes.node = nodes.id
			WHERE way = ways.id
			ORDER BY way_nodes.num ASC
		) AS nodeids,
		(
			SELECT value
			FROM way_tags
			WHERE ref = ways.id
			AND key = 'name'
			LIMIT 1
		) AS name,
		(
			SELECT value
			FROM way_tags
			WHERE ref = ways.id
			AND key = 'oneway'
			LIMIT 1
		) AS oneway
	FROM ways
	ORDER BY ways.id ASC;
	`)
	if err != nil {
		log.Fatal(err)
	}
	defer rows.Close()
	for rows.Next() {
		callback(rows)
	}
	err = rows.Err()
	if err != nil {
		log.Fatal(err)
	}
}

func generateStreetsFromWays(conn *sqlite.Connection) []*street {
	var streets []*street

	loadStreetsFromDatabase(conn, func(rows *sql.Rows) {

		var wayid int
		var nodeids, name string
		var maybeNodeIds, maybeOneway sql.NullString
		var oneway = ""

		err := rows.Scan(&wayid, &maybeNodeIds, &name, &maybeOneway)
		if err != nil {
			log.Fatal(err)
		}

		// handle the case where nodeids is NULL
		// note: this can occur when another tool has stripped the
		// nodes but left the ways which reference them in the file.
		if !maybeNodeIds.Valid {
			log.Println("invalid way, nodes not included in file", wayid)
			return
		}

		// convert sql.NullString to string
		if val, err := maybeNodeIds.Value(); err == nil {
			nodeids = val.(string)
		} else {
			log.Fatal("invalid nodeid value", wayid)
		}

		// convert sql.NullString to string
		if (maybeOneway.Valid) {
			if onewayStr, err := maybeOneway.Value(); err == nil {
				oneway = onewayStr.(string)
			}
		}

		var wayNodes = strings.Split(nodeids, ",")
		if len(wayNodes) <= 1 {
			log.Println("found 0 refs for way", wayid)
			return
		}

		var path = geo.NewPath()
		for i, node := range wayNodes {
			coords := strings.Split(node, "#")
			lon, lonErr := strconv.ParseFloat(coords[0], 64)
			lat, latErr := strconv.ParseFloat(coords[1], 64)
			if nil != lonErr || nil != latErr {
				log.Println("error parsing coordinate as float", coords)
				return
			}
			path.InsertAt(i, geo.NewPoint(lon, lat))
		}

		streets = append(streets, &street{Name: name, Path: path, Oneway: oneway, WayId: wayid})
	})

	return streets
}

func parsePBF(c *cli.Context, conn *sqlite.Connection) {

	// validate args
	var argv = c.Args()
	if len(argv) != 1 {
		log.Println("invalid arguments, expected: {pbf}")
		os.Exit(1)
	}

	// create parser handler
	DBHandler := &handler.Sqlite3{Conn: conn}

	// create parser
	parser := parser.NewParser(c.Args()[0])

	// streets handler
	streets := &handler.Streets{
		TagWhitelist: tags.Highway(),
		NodeMask:     lib.NewBitMask(),
		DBHandler:    DBHandler,
	}

	// parse file
	parser.Parse(streets)

	// reset file
	parser.Reset()

	// create a proxy to filter elements by mask
	filterNodes := &proxy.WhiteList{
		Handler:  DBHandler,
		NodeMask: streets.NodeMask,
	}

	// parse file again
	parser.Parse(filterNodes)
}

// Mang cac ky tu goc co dau
var SOURCE_CHARACTERS, LL_LENGTH = stringToRune(`ÀÁÂÃÈÉÊÌÍÒÓÔÕÙÚÝàáâãèéêìíòóôõùúýĂăĐđĨĩŨũƠơƯưẠạẢảẤấẦầẨẩẪẫẬậẮắẰằẲẳẴẵẶặẸẹẺẻẼẽẾếỀềỂểỄễỆệỈỉỊịỌọỎỏỐốỒồỔổỖỗỘộỚớỜờỞởỠỡỢợỤụỦủỨứỪừỬửỮữỰựỹỳỷỵỸỲỶỴ`)

// Mang cac ky tu thay the khong dau
var DESTINATION_CHARACTERS, _ = stringToRune(`AAAAEEEIIOOOOUUYaaaaeeeiioooouuyAaDdIiUuOoUuAaAaAaAaAaAaAaAaAaAaAaAaEeEeEeEeEeEeEeEeIiIiOoOoOoOoOoOoOoOoOoOoOoOoUuUuUuUuUuUuUuyyyyyyyy`)

func stringToRune(s string) ([]string, int) {

	ll := utf8.RuneCountInString(s)

	var texts = make([]string, ll+1)

	var index = 0

	for _, runeValue := range s {

		texts[index] = string(runeValue)

		index++

	}

	return texts, ll

}

func binarySearch(sortedArray []string, key string, low int, high int) int {

	var middle int = (low + high) / 2

	if high < low {
		return -1
	}

	if key == sortedArray[middle] {

		return middle

	} else if key < sortedArray[middle] {

		return binarySearch(sortedArray, key, low, middle-1)

	} else {

		return binarySearch(sortedArray, key, middle+1, high)

	}
}

/** * Bo dau 1 ky tu * * @param ch * @return */
func removeAccentChar(ch string) string {
	var index int = binarySearch(SOURCE_CHARACTERS, ch, 0, LL_LENGTH)

	if index >= 0 {
		ch = DESTINATION_CHARACTERS[index]
	}

	return ch
}

/** * Bo dau 1 chuoi * * @param s * @return */
func removeAccent(s string) string {
	var buffer bytes.Buffer

	// if (s == "quốc lộ 1a") {
	// 	fmt.Println("debug")
	// }

	// apiKey := "1a37dc708fbdeffe2001397e5b7052a3"
	// // Call API to replace specific characters to normal characters

	// text := strings.ReplaceAll(s, " ", "%20")
	// url := "https://api-private.map4d.vn/app/geojson/replace?str=" + text + "&Key=" + apiKey
	// //	https://api-private.map4d.vn/app/geojson/replace?str=Hoa%CC%80ng%20Qu%C3%B4%CC%81c%20Vi%C3%AA%CC%A3t&Key=1a37dc708fbdeffe2001397e5b7052a3
	// log.Println("replace url::", url)

	// req, _ := http.NewRequest("GET", url, nil)
	// q := req.URL.Query()
	// q.Add("str", text)
	// q.Add("Key", apiKey)
	// req.URL.RawQuery = q.Encode()
	// response, _ := client.Do(req)

	// response, err := http.Get(url)

	// if err != nil {
	// 	fmt.Print(err.Error())
	// 	os.Exit(1)
	// }

	// responseData, err := ioutil.ReadAll(response.Body)

	// var responseObject {t: string}
	// json.Unmarshal(responseData, &responseObject)

	// if err != nil {
	// 	log.Fatal(err)
	// }

	// fmt.Println("responseData::", response)

	// fmt.Println("responseData::", responseData)


	// TODO: Must use replace because not convert this characters
	if (strings.Contains(s, "ỷ")) {
		s = strings.ReplaceAll(s, "ỷ", "y")
	}
	if (strings.Contains(s, "ỳ")) {
		s = strings.ReplaceAll(s, "ỳ", "y")
	}
	if (strings.Contains(s, "ỵ")) {
		s = strings.ReplaceAll(s, "ỵ", "y")
	}
	if (strings.Contains(s, "ỳ")) {
		s = strings.ReplaceAll(s, "ỳ", "y")
	}
	if (strings.Contains(s, "ý")) {
		s = strings.ReplaceAll(s, "ý", "y")
	}
	if (strings.Contains(s, "ố")) {
		s = strings.ReplaceAll(s, "ố", "o")
	}
	if (strings.Contains(s, "ộ")) {
		s = strings.ReplaceAll(s, "ộ", "o")
	}
	if (strings.Contains(s, "ợ")) {
		s = strings.ReplaceAll(s, "ợ", "o")
	}
	if (strings.Contains(s, "ồ")) {
		s = strings.ReplaceAll(s, "ồ", "o")
	}
	if (strings.Contains(s, "ờ")) {
		s = strings.ReplaceAll(s, "ờ", "o")
	}
	if (strings.Contains(s, "ỗ")) {
		s = strings.ReplaceAll(s, "ỗ", "o")
	}
	if (strings.Contains(s, "ở")) {
		s = strings.ReplaceAll(s, "ở", "o")
	}
	if (strings.Contains(s, "ó")) {
		s = strings.ReplaceAll(s, "ó", "o")
	}
	if (strings.Contains(s, "ỏ")) {
		s = strings.ReplaceAll(s, "ỏ", "o")
	}
	if (strings.Contains(s, "õ")) {
		s = strings.ReplaceAll(s, "õ", "o")
	}
	if (strings.Contains(s, "ò")) {
		s = strings.ReplaceAll(s, "ò", "o")
	}
	if (strings.Contains(s, "ò")) {
		s = strings.ReplaceAll(s, "ò", "o")
	}
	if (strings.Contains(s, "ọ")) {
		s = strings.ReplaceAll(s, "ọ", "o")
	}
	if (strings.Contains(s, "ð")) {
		s = strings.ReplaceAll(s, "ð", "d")
	}
	if (strings.Contains(s, "ằ")) {
		s = strings.ReplaceAll(s, "ằ", "a")
	}
	if (strings.Contains(s, "ầ")) {
		s = strings.ReplaceAll(s, "ầ", "a")
	}
	if (strings.Contains(s, "ậ")) {
		s = strings.ReplaceAll(s, "ậ", "a")
	}
	if (strings.Contains(s, "ẩ")) {
		s = strings.ReplaceAll(s, "ẩ", "a")
	}
	if (strings.Contains(s, "ấ")) {
		s = strings.ReplaceAll(s, "ấ", "a")
	}
	if (strings.Contains(s, "ã")) {
		s = strings.ReplaceAll(s, "ã", "a")
	}
	if (strings.Contains(s, "ã")) {
		s = strings.ReplaceAll(s, "ã", "a")
	}
	if (strings.Contains(s, "à")) {
		s = strings.ReplaceAll(s, "à", "a")
	}
	if (strings.Contains(s, "ạ")) {
		s = strings.ReplaceAll(s, "ạ", "a")
	}
	if (strings.Contains(s, "á")) {
		s = strings.ReplaceAll(s, "á", "a")
	}
	if (strings.Contains(s, "ả")) {
		s = strings.ReplaceAll(s, "ả", "a")
	}
	if (strings.Contains(s, "ễ")) {
		s = strings.ReplaceAll(s, "ễ", "e")
	}
	if (strings.Contains(s, "ệ")) {
		s = strings.ReplaceAll(s, "ệ", "e")
	}
	if (strings.Contains(s, "ề")) {
		s = strings.ReplaceAll(s, "ề", "e")
	}
	if (strings.Contains(s, "ế")) {
		s = strings.ReplaceAll(s, "ế", "e")
	}
	if (strings.Contains(s, "ẹ")) {
		s = strings.ReplaceAll(s, "ẹ", "e")
	}
	if (strings.Contains(s, "è")) {
		s = strings.ReplaceAll(s, "è", "e")
	}
	if (strings.Contains(s, "é")) {
		s = strings.ReplaceAll(s, "é", "e")
	}
	if (strings.Contains(s, "ẽ")) {
		s = strings.ReplaceAll(s, "ẽ", "e")
	}
	if (strings.Contains(s, "ẻ")) {
		s = strings.ReplaceAll(s, "ẻ", "e")
	}
	if (strings.Contains(s, "ì")) {
		s = strings.ReplaceAll(s, "ì", "i")
	}
	if (strings.Contains(s, "ị")) {
		s = strings.ReplaceAll(s, "ị", "i")
	}
	if (strings.Contains(s, "į")) {
		s = strings.ReplaceAll(s, "į", "i")
	}
	if (strings.Contains(s, "í")) {
		s = strings.ReplaceAll(s, "í", "i")
	}
	if (strings.Contains(s, "ĩ")) {
		s = strings.ReplaceAll(s, "ĩ", "i")
	}
	if (strings.Contains(s, "ỉ")) {
		s = strings.ReplaceAll(s, "ỉ", "i")
	}
	if (strings.Contains(s, "ữ")) {
		s = strings.ReplaceAll(s, "ữ", "u")
	}
	if (strings.Contains(s, "ứ")) {
		s = strings.ReplaceAll(s, "ứ", "u")
	}
	if (strings.Contains(s, "ự")) {
		s = strings.ReplaceAll(s, "ự", "u")
	}
	if (strings.Contains(s, "ũ")) {
		s = strings.ReplaceAll(s, "ũ", "u")
	}
	if (strings.Contains(s, "ù")) {
		s = strings.ReplaceAll(s, "ù", "u")
	}
	if (strings.Contains(s, "ủ")) {
		s = strings.ReplaceAll(s, "ủ", "u")
	}
	if (strings.Contains(s, "ụ")) {
		s = strings.ReplaceAll(s, "ụ", "u")
	}
	if (strings.Contains(s, "ú")) {
		s = strings.ReplaceAll(s, "ú", "u")
	}

	for _, runeValue := range s {
		buffer.WriteString(removeAccentChar(string(runeValue)))
	}

	// Debug
	// fmt.Println("s::", s)
	// fmt.Println("buffer::", buffer.String())

	return buffer.String()
}

func streetNameParser(searchText string) string {
	var url string = ""
	// if (!strings.Contains(searchText, "duong")) {
	// 	url = "http://parser.map4d.vn/parser/parse?text=duong " + searchText
	// } else {
	// 	url = "http://parser.map4d.vn/parser/parse?text=" + searchText
	// }
	url = "http://parser.map4d.vn/parser/parse?text=" + searchText
	url = strings.ReplaceAll(url, " ", "%20")

	// TODO: Fix for street name same "Ten duong 1 (Ten duong 2)"
	removeString := regexp.MustCompile(`\(|\)|'|\*`)
	url = removeString.ReplaceAllString(url, "%20")

	// Debug
	// log.Println("url::", url)

	response, err := http.Get(url)

	if err != nil {
		fmt.Print(err.Error())
		os.Exit(1)
	}

	responseData, err := ioutil.ReadAll(response.Body)

	if err != nil {
		log.Fatal(err)
	}

	var responseObject Response
	json.Unmarshal(responseData, &responseObject)
	var streetName = ""
	if len(responseObject.Solutions) > 0 && len(responseObject.Solutions[0].Classifications) > 0 {
		var classifications = responseObject.Solutions[0].Classifications
		for _, classification := range classifications {
			if classification.Label == "housenumber" {
				return ""
			} else if classification.Label == "street" {
				streetName = classification.Value
			}
		}
		return streetName
	}

	return streetName
}

func getShortestDistance(Path1, Path2 *geo.Path) float64 {
	var shortestDistance = Path1.First().DistanceFrom(Path2.First())

	if shortestDistance > Path1.First().DistanceFrom(Path2.Last()) {
		shortestDistance = Path1.First().DistanceFrom(Path2.Last())
	}

	if shortestDistance > Path1.Last().DistanceFrom(Path2.First()) {
		shortestDistance = Path1.Last().DistanceFrom(Path2.First())
	}

	if shortestDistance > Path1.Last().DistanceFrom(Path2.Last())  {
		shortestDistance = Path1.Last().DistanceFrom(Path2.Last())
	}

	return shortestDistance
}

func shortestDistanceWhenSameDirection(Path1, Path2 *geo.Path) float64 {
	var shortestDistance = Path1.Last().DistanceFrom(Path2.First())

	if shortestDistance > Path1.First().DistanceFrom(Path2.Last()) {
		shortestDistance = Path1.First().DistanceFrom(Path2.Last())
	}

	return shortestDistance
}

func shortestDistanceToOtherSameDirectionStreets(current *street, streets []*street) float64 {
	if (len(streets) < 1) {
		return 0.0
	}

	shortestDistance := shortestDistanceWhenSameDirection(current.Path, streets[0].Path)
	for i := 1; i < len(streets); i++ {
		distance := shortestDistanceWhenSameDirection(current.Path, streets[i].Path)
		if (shortestDistance > distance) {
			shortestDistance = distance
		}
	}

	return shortestDistance
}

func shortestDistanceToOtherStreets(current *street, streets []*street) float64 {
	if (len(streets) < 1) {
		return 0.0
	}

	shortestDistance := getShortestDistance(current.Path, streets[0].Path)
	for i := 1; i < len(streets); i++ {
		distance := getShortestDistance(current.Path, streets[i].Path)
		if (shortestDistance > distance) {
			shortestDistance = distance
		}
	}
	return shortestDistance
}

func isIntersection(path1, path2 *geo.Path) bool {
	var firstLine = geo.NewLine(path1.First(), path1.Last())
	var secondLine = geo.NewLine(path2.First(), path2.Last())
	return firstLine.Intersects(secondLine)
}

// Calculate angle between two line
func calcangle(p00, p01, p10, p11 *geo.Point) float64 {
	var A1x = p00[0]
	var A1y = p00[1]
	var A2x = p01[0]
	var A2y = p01[1]
	var B1x = p10[0]
	var B1y = p10[1]
	var B2x = p11[0]
	var B2y = p11[1]

	var dAx = A2x - A1x;
	var dAy = A2y - A1y;
	var dBx = B2x - B1x;
	var dBy = B2y - B1y;

	var angle = math.Atan2(dAx * dBy - dAy * dBx, dAx * dBx + dAy * dBy);
	if(angle < 0) {angle = angle * -1;}
	var degree_angle = 180 - angle * (180 / 3.1415926); // PI = 3.1415926

	return degree_angle
}

func angleBetween2Lines(A1, A2, B1, B2 *geo.Point, distanceTolerance float64) float64 {
	var A1x = A1[0]
	var A1y = A1[1]
	var A2x = A2[0]
	var A2y = A2[1]
	var B1x = B1[0]
	var B1y = B1[1]
	var B2x = B2[0]
	var B2y = B2[1]

	var PI = 3.1415926

    var angle1 = math.Atan2(A2y - A1y, A2x - A1x) * 180 / PI
    var angle2 = math.Atan2(B2y - B1y, B2x - B1x) * 180 / PI

	var angle = 0.0
	if (angle1 * angle2 > 0) {
		if (A2.DistanceFrom(B1) < distanceTolerance) {
			angle = 180 - math.Abs(angle1 - angle2)
		} else {
			angle = math.Abs(angle1 - angle2)
		}
	} else if (angle1 < 0 && angle2 > 0) {
		angle = (math.Abs(angle1) + math.Abs(angle2))
	} else if (angle1 > 0 && angle2 < 0) {
		angle = (math.Abs(angle1) + math.Abs(angle2))
	}

	return angle
}

func pathProjection(path *geo.Path) *geo.Path {
	var pathProjection = path.Clone().Transform(geo.Mercator.Project)

	return pathProjection
}

func createPathVector(pos1, pos2 *geo.Point) *Vector {
	ydiff := pos2[1] - pos1[1]
	xdiff := pos2[0] - pos1[0]

	return &Vector{
	  dX:  xdiff,
	  dY:  ydiff,
	}
}

func cosBetween2Vectors(a, b *Vector) float64 {
	var dividend = a.dX * b.dX + a.dY * b.dY
	var divisor = math.Sqrt(a.dX * a.dX + a.dY * a.dY) * math.Sqrt(b.dX * b.dX + b.dY * b.dY)
	var cos = dividend / divisor

	return cos
}

func isTwoPathsSameDirection(a, b *Vector) bool {
	var cos = cosBetween2Vectors(a, b)
	return cos > 0 && cos <= 1
}

func getLongestStreet(streets []*street) *street {
	var distance float64 = 0;
	var index = 0;
	for i, street := range streets {
		if (distance < street.Path.Distance()) {
			distance = street.Path.Distance()
			index = i
		}
	}

	return streets[index]
}

func getLongestStreetIndex(streets []*street) int {
	var distance float64 = 0;
	var index = 0;
	for i, street := range streets {
		if (distance < street.Path.Distance()) {
			distance = street.Path.Distance()
			index = i
		}
	}

	return index
}

func sortStreetsDescLength(streets []*street) []*street {
	var sortedStreets = streets

	// for i := 0; i < len(sortedStreets); i++ {
	// 	fmt.Println("before::length", sortedStreets[i].Path.Distance())
	// }

	for i := 0; i < len(sortedStreets) - 1; i++ {
		for j := i; j < len(sortedStreets); j++ {
			if (sortedStreets[j].Path.Distance() > sortedStreets[i].Path.Distance()) {
				temp := sortedStreets[i]
				sortedStreets[i] = sortedStreets[j]
				sortedStreets[j] = temp
			}
		}
	}

	// for i := 0; i < len(sortedStreets); i++ {
	// 	fmt.Println("after::length", sortedStreets[i].Path.Distance())
	// }

	return sortedStreets
}

func directionInRange(angle1, angle2 float64) bool {
	angle1 = math.Abs(angle1)
	angle2 = math.Abs(angle2)
	return (angle1 < 5 && angle2 < 5) ||
		(angle1 > 175 && angle2 > 175) ||
		(angle1 < 5 && angle2 > 175) ||
		(angle1 > 175 && angle2 < 5)
}

func RemoveIndex(s []string, index int) []string {
	return append(s[:index], s[index+1:]...)
}

func removeStreet(s []*street, index int) []*street {
	var streets []*street
	for i:= 0; i < len(s); i++ {
		if (index == i) {
			continue
		}
		streets = append(streets, s[i])
	}
	return streets
}

func removeRoundabout(streets []*street) []*street {
	for i:= 0; i < len(streets); i++ {
		first := streets[i].Path.PointSet.First()
		last := streets[i].Path.PointSet.Last()
		if first.DistanceFrom(last) == 0 {
			streets = removeStreet(streets, i)
			i--
		}
	}
	return streets
}

func debugStreets(baseStreet *street, currentStreet *street, normName string, streets []*street) {
	var vector1 = createPathVector(baseStreet.Path.First(), baseStreet.Path.Last())
	var vector2 = createPathVector(currentStreet.Path.First(), currentStreet.Path.Last())
	var isTwoPathsSameDirection = isTwoPathsSameDirection(vector1, vector2)

	var shortestDistanceToOtherStreets = shortestDistanceToOtherStreets(baseStreet, streets)
	var shortestDistanceToOtherSameDirectionStreets = shortestDistanceToOtherSameDirectionStreets(baseStreet, streets)

	if (normName == "dang tu kinh" || normName == "dang tu kinh__1" ||
			normName == "dang tu kinh__1--0" || normName == "dang tu kinh__1--1") {
		fmt.Println("--Start debug log--")
		fmt.Println("normName::", normName)
		fmt.Println("shortestDistanceToOtherStreets::", shortestDistanceToOtherStreets)
		fmt.Println("shortestDistanceToOtherSameDirectionStreets::", shortestDistanceToOtherSameDirectionStreets)
		fmt.Println("DistanceFrom::", baseStreet.Path.Last().DistanceFrom(currentStreet.Path.First()))
		fmt.Println("DistanceFrom inverse::", baseStreet.Path.First().DistanceFrom(currentStreet.Path.Last()))
		fmt.Println("DistanceFrom Last::", baseStreet.Path.Last().DistanceFrom(currentStreet.Path.Last()))
		fmt.Println("DistanceFrom First::", baseStreet.Path.First().DistanceFrom(currentStreet.Path.First()))
		fmt.Println("isTwoPathsSameDirection::", isTwoPathsSameDirection)
		fmt.Println("IntersectsPath::", baseStreet.Path.IntersectsPath(currentStreet.Path))

		var base, _ = baseStreet.Path.PointSet.ToGeoJSON().MarshalJSON()
		fmt.Println(baseStreet.Name, " 1.Street 1: ", string(base))

		var current, _ = currentStreet.Path.PointSet.ToGeoJSON().MarshalJSON()
		fmt.Println(currentStreet.Name, " 1.Street 2: ", string(current))

		fmt.Println("--End debug log--")
	}
}

func mergeStreetSameDirection(nameMap map[string][]*street, isUseStreetName bool) map[string][]*street {
	var reversePath = func(path *geo.Path) {
		for i := path.PointSet.Length()/2 - 1; i >= 0; i-- {
			opp := path.PointSet.Length() - 1 - i
			path.PointSet[i], path.PointSet[opp] = path.PointSet[opp], path.PointSet[i]
		}
	}

	var mergedStreetMap = make(map[string][]*street)

	// points do not have to be exact matches
	// var distanceTolerance = 0.01 // 1000 meters
	var distanceTolerance = 0.003 // 300 meters
	var distanceRange = 0.00065 // 65 meters, distance range to merge 2 paths which intersect together
	var merged = make(map[*street]bool)

	for strName, strs := range nameMap {
		// Sort streets follow the descendant length
		strs = sortStreetsDescLength(strs)

		var normName = strName

		var str1 *street = nil

		for i := 0; i < len(strs); i++ {

			if (len(strs) == 1) {
				if _, ok := mergedStreetMap[normName]; !ok {
					mergedStreetMap[normName] = []*street{strs[0]}
				} else {
					mergedStreetMap[normName] = append(mergedStreetMap[normName], strs[0])
				}
				continue
			}

			if (i == 0) {
				str1 = strs[0]
				continue
			}

			var shortestDistanceToOtherStreets = shortestDistanceToOtherStreets(str1, removeStreet(strs, 0))
			var shortestDistanceToOtherSameDirectionStreets = shortestDistanceToOtherSameDirectionStreets(str1, removeStreet(strs, 0))
			var str2 = strs[i]

			var vector1 = createPathVector(str1.Path.First(), str1.Path.Last())
			var vector2 = createPathVector(str2.Path.First(), str2.Path.Last())
			var isTwoPathsSameDirection = isTwoPathsSameDirection(vector1, vector2)

			if (str2.Oneway == "yes") {

				if debugMode {
					debugStreets(str1, str2, normName, strs)
				}

				shortestDistanceWhenSameDirection := shortestDistanceWhenSameDirection(str1.Path, str2.Path)

				// Not merge streets same direction, intersect together but distance greater than distance range
				if (str1.Path.IntersectsPath(str2.Path) && shortestDistanceWhenSameDirection > distanceRange) {
					if (i == (len(strs) - 1)) {
						strs = removeStreet(strs, 0)
						i = -1

						normName = strName

						if _, ok := mergedStreetMap[normName]; !ok {
							mergedStreetMap[normName] = []*street{str1}
						} else {
							mergedStreetMap[normName] = append(mergedStreetMap[normName], str1)
						}
					}
					continue
				}

				if (isTwoPathsSameDirection &&
					str1.Path.Last().DistanceFrom(str2.Path.First()) == shortestDistanceToOtherSameDirectionStreets &&
					shortestDistanceToOtherSameDirectionStreets < distanceTolerance) {

					var match = str1.Path.Last()

					// merge str2 in to str1
					for _, point := range str2.Path.PointSet {
						if point.Equals(match) {
							continue
						}
						str1.Path.Push(&point)
					}

					strs = removeStreet(strs, i)

					merged[str2] = true
					i = 0
				} else if (isTwoPathsSameDirection &&
									 str1.Path.First().DistanceFrom(str2.Path.Last()) == shortestDistanceToOtherSameDirectionStreets &&
									 shortestDistanceToOtherSameDirectionStreets < distanceTolerance) {

					var match = str1.Path.First()

					// flip str1 & str2 points
					reversePath(str1.Path)
					reversePath(str2.Path)

					// merge str2 in to str1
					for _, point := range str2.Path.PointSet {
						if point.Equals(match) {
							continue
						}
						str1.Path.Push(&point)
					}

					strs = removeStreet(strs, i)

					// flip str1 points back
					reversePath(str1.Path)
					reversePath(str2.Path)

					merged[str2] = true
					i = 0
				} else {

					// If distance not shortest
					if debugMode {
						debugStreets(str1, str2, normName, strs)
					}

					if ((str1.Path.Last().DistanceFrom(str2.Path.First()) == shortestDistanceToOtherSameDirectionStreets ||
						str1.Path.First().DistanceFrom(str2.Path.Last()) == shortestDistanceToOtherSameDirectionStreets) &&
						shortestDistanceToOtherSameDirectionStreets >= distanceTolerance) {
						if _, ok := mergedStreetMap[normName]; !ok {
							mergedStreetMap[normName] = []*street{str2}
						} else {
							mergedStreetMap[normName] = append(mergedStreetMap[normName], str2)
						}
						strs = removeStreet(strs, i)
						i--
					} else if shortestDistanceToOtherSameDirectionStreets < distanceTolerance {
						// TODO
						// fmt.Println("< mergeStreetSameDirection::Street name was not merged::oneway::street name::", str2.Name, "::wayid::", str2.WayId)
					} else {
						// TODO
						// fmt.Println(">= mergeStreetSameDirection::Street name was not merged::oneway::street name::", str2.Name, "::wayid::", str2.WayId)
					}

				}

			} else {
				// If two way
				if debugMode {
					debugStreets(str1, str2, normName, strs)
				}

				shortestDistance := getShortestDistance(str1.Path, str2.Path)

				// Not merge streets same direction, intersect together but distance greater than distance range
				if (str1.Path.IntersectsPath(str2.Path) && shortestDistance > distanceRange) {
					if (i == (len(strs) - 1)) {
						strs = removeStreet(strs, 0)
						i = -1

						normName = strName

						if _, ok := mergedStreetMap[normName]; !ok {
							mergedStreetMap[normName] = []*street{str1}
						} else {
							mergedStreetMap[normName] = append(mergedStreetMap[normName], str1)
						}
					}
					continue
				}

				if str1.Path.Last().DistanceFrom(str2.Path.First()) == shortestDistanceToOtherStreets &&
					shortestDistanceToOtherStreets < distanceTolerance {

					var match = str1.Path.Last()

					// merge str2 in to str1
					for _, point := range str2.Path.PointSet {
						if point.Equals(match) {
							continue
						}
						str1.Path.Push(&point)
					}

					strs = removeStreet(strs, i)
					merged[str2] = true
					i = 0
				} else if str1.Path.First().DistanceFrom(str2.Path.Last()) == shortestDistanceToOtherStreets &&
					shortestDistanceToOtherStreets < distanceTolerance {

					var match = str1.Path.First()

					// flip str1 & str2 points
					reversePath(str1.Path)
					reversePath(str2.Path)

					// merge str2 in to str1
					for _, point := range str2.Path.PointSet {
						if point.Equals(match) {
							continue
						}
						str1.Path.Push(&point)
					}

					// flip str1 points back
					reversePath(str1.Path)
					reversePath(str2.Path)

					strs = removeStreet(strs, i)
					merged[str2] = true
					i = 0
				} else if str1.Path.Last().DistanceFrom(str2.Path.Last()) == shortestDistanceToOtherStreets &&
					shortestDistanceToOtherStreets < distanceTolerance {

					var match = str1.Path.Last()

					// flip str2 points
					reversePath(str2.Path)

					// merge str2 in to str1
					for _, point := range str2.Path.PointSet {
						if point.Equals(match) {
							continue
						}
						str1.Path.Push(&point)
					}

					// flip str2 points back
					reversePath(str2.Path)

					strs = removeStreet(strs, i)
					merged[str2] = true
					i = 0
				} else if str1.Path.First().DistanceFrom(str2.Path.First()) == shortestDistanceToOtherStreets &&
					shortestDistanceToOtherStreets < distanceTolerance {

					var match = str1.Path.First()

					// flip str1 points
					reversePath(str1.Path)

					// merge str2 in to str1
					for _, point := range str2.Path.PointSet {
						if point.Equals(match) {
							continue
						}
						str1.Path.Push(&point)
					}

					// flip str1 points back
					reversePath(str1.Path)

					strs = removeStreet(strs, i)
					merged[str2] = true
					i = 0
				} else {

					// If two way and distance not shortest
					if debugMode {
						debugStreets(str1, str2, normName, strs)
					}

					if (str1.Path.Last().DistanceFrom(str2.Path.First()) == shortestDistanceToOtherStreets ||
							str1.Path.First().DistanceFrom(str2.Path.Last()) == shortestDistanceToOtherStreets ||
							str1.Path.Last().DistanceFrom(str2.Path.Last()) == shortestDistanceToOtherStreets ||
							str1.Path.First().DistanceFrom(str2.Path.First()) == shortestDistanceToOtherStreets) {
						if _, ok := mergedStreetMap[normName]; !ok {
							mergedStreetMap[normName] = []*street{str2}
						} else {
							mergedStreetMap[normName] = append(mergedStreetMap[normName], str2)
						}

						strs = removeStreet(strs, i)
						i--
					} else if shortestDistanceToOtherStreets < distanceTolerance {
						// TODO
						// fmt.Println("< mergeStreetSameDirection::Street name was not merged::street name::", str2.Name, "::wayid::", str2.WayId)
					} else {
						// TODO
						// fmt.Println(">= mergeStreetSameDirection::Street name was not merged::street name::", str2.Name, "::wayid::", str2.WayId)
					}
				}
			}

			// When reach to the last item of list street, then remove the first item and loop again the list street
			if (i == (len(strs) - 1) || len(strs) < 1) {
				strs = removeStreet(strs, 0)
				i = -1
				normName = strName

				if _, ok := mergedStreetMap[normName]; !ok {
					mergedStreetMap[normName] = []*street{str1}
				} else {
					mergedStreetMap[normName] = append(mergedStreetMap[normName], str1)
				}
			}
		}
	}

	return mergedStreetMap
}



func mergeLaneSameDirection(nameMap map[string][]*street) map[string][]*street {
	var reversePath = func(path *geo.Path) {
		for i := path.PointSet.Length()/2 - 1; i >= 0; i-- {
			opp := path.PointSet.Length() - 1 - i
			path.PointSet[i], path.PointSet[opp] = path.PointSet[opp], path.PointSet[i]
		}
	}

	var mergedStreetMap = make(map[string][]*street)

	// points do not have to be exact matches
	// var distanceTolerance = 0.01 // 1000 meters
	// var distanceTolerance = 0.0075 // 750 meters
	var distanceTolerance = 0.003 // 300 meters
	var distanceRange = 0.0005 // 55 meters, distance range to merge 2 paths which intersect together

	for strName, strs := range nameMap {
		// Sort streets follow the descendant length
		strs = sortStreetsDescLength(strs)

		// Debug
		var normName = strings.Split(strName, "--")[0]
		// var normName = strName

		if (len(strs) < 1) {
			continue
		} else if (len(strs) == 1) {
			if _, ok := mergedStreetMap[normName]; !ok {
				mergedStreetMap[normName] = []*street{strs[0]}
			} else {
				mergedStreetMap[normName] = append(mergedStreetMap[normName], strs[0])
			}
			continue
		}

		var index = getLongestStreetIndex(strs)
		var baseStreet = strs[index]
		strs = removeStreet(strs, index)

		for i := 0; i < len(strs); i++ {
			var shortestDistanceToOtherStreets = shortestDistanceToOtherStreets(baseStreet, strs)
			var shortestDistanceToOtherSameDirectionStreets = shortestDistanceToOtherSameDirectionStreets(baseStreet, strs)
			var currentStreet = strs[i]

			var vector1 = createPathVector(baseStreet.Path.First(), baseStreet.Path.Last())
			var vector2 = createPathVector(currentStreet.Path.First(), currentStreet.Path.Last())
			var isTwoPathsSameDirection = isTwoPathsSameDirection(vector1, vector2)

			if (currentStreet.Oneway == "yes") {

				if debugMode {
					debugStreets(baseStreet, currentStreet, normName, strs)
				}

				shortestDistanceWhenSameDirection := shortestDistanceWhenSameDirection(baseStreet.Path, currentStreet.Path)

				// Not merge streets same direction, intersect together but distance greater than distance range
				if (baseStreet.Path.IntersectsPath(currentStreet.Path) && shortestDistanceWhenSameDirection > distanceRange) ||
					shortestDistanceWhenSameDirection > distanceTolerance {
					strs = removeStreet(strs, i)
					i--

					if (i == (len(strs) - 1) || len(strs) < 1) {
						if _, ok := mergedStreetMap[normName]; !ok {
							mergedStreetMap[normName] = []*street{baseStreet}
						} else {
							mergedStreetMap[normName] = append(mergedStreetMap[normName], baseStreet)
						}
					}

					continue
				}

				if (isTwoPathsSameDirection &&
					baseStreet.Path.Last().DistanceFrom(currentStreet.Path.First()) == shortestDistanceToOtherSameDirectionStreets &&
					shortestDistanceToOtherSameDirectionStreets < distanceTolerance) {

					var match = baseStreet.Path.Last()

					// merge currentStreet in to baseStreet
					for _, point := range currentStreet.Path.PointSet {
						if point.Equals(match) {
							continue
						}
						baseStreet.Path.Push(&point)
					}

					// Debug
					// var merged, _ = baseStreet.Path.PointSet.ToGeoJSON().MarshalJSON()
					// fmt.Println(baseStreet.Name, " Merged Street :: ", string(merged))

					strs = removeStreet(strs, i)
					i = -1
				} else if (isTwoPathsSameDirection &&
									 baseStreet.Path.First().DistanceFrom(currentStreet.Path.Last()) == shortestDistanceToOtherSameDirectionStreets &&
									 shortestDistanceToOtherSameDirectionStreets < distanceTolerance) {

					var match = baseStreet.Path.First()

					// flip baseStreet & currentStreet points
					reversePath(baseStreet.Path)
					reversePath(currentStreet.Path)

					// merge currentStreet in to baseStreet
					for _, point := range currentStreet.Path.PointSet {
						if point.Equals(match) {
							continue
						}
						baseStreet.Path.Push(&point)
					}

					// Debug
					// var merged, _ = baseStreet.Path.PointSet.ToGeoJSON().MarshalJSON()
					// fmt.Println(baseStreet.Name, " Merged Street :: ", string(merged))

					strs = removeStreet(strs, i)
					i = -1

					// flip baseStreet points back
					reversePath(baseStreet.Path)
					reversePath(currentStreet.Path)
				} else {

					// If distance not shortest
					if debugMode {
						debugStreets(baseStreet, currentStreet, normName, strs)
					}

					if ((baseStreet.Path.Last().DistanceFrom(currentStreet.Path.First()) == shortestDistanceToOtherSameDirectionStreets ||
						baseStreet.Path.First().DistanceFrom(currentStreet.Path.Last()) == shortestDistanceToOtherSameDirectionStreets) &&
						shortestDistanceToOtherSameDirectionStreets >= distanceTolerance) {
						if _, ok := mergedStreetMap[normName]; !ok {
							mergedStreetMap[normName] = []*street{currentStreet}
						} else {
							mergedStreetMap[normName] = append(mergedStreetMap[normName], currentStreet)
						}
						strs = removeStreet(strs, i)
						i--
					}

				}

			} else {
				// If two way
				if debugMode {
					debugStreets(baseStreet, currentStreet, normName, strs)
				}

				shortestDistance := getShortestDistance(baseStreet.Path, currentStreet.Path)

				// Not merge streets same direction, intersect together but distance greater than distance range
				if (baseStreet.Path.IntersectsPath(currentStreet.Path) && shortestDistance > distanceRange) {
					strs = removeStreet(strs, i)
					i--

					if (i == (len(strs) - 1) || len(strs) < 1) {
						if _, ok := mergedStreetMap[normName]; !ok {
							mergedStreetMap[normName] = []*street{baseStreet}
						} else {
							mergedStreetMap[normName] = append(mergedStreetMap[normName], baseStreet)
						}
					}

					continue
				}

				if baseStreet.Path.Last().DistanceFrom(currentStreet.Path.First()) == shortestDistanceToOtherStreets &&
					shortestDistanceToOtherStreets < distanceTolerance {

					var match = baseStreet.Path.Last()

					// merge currentStreet in to baseStreet
					for _, point := range currentStreet.Path.PointSet {
						if point.Equals(match) {
							continue
						}
						baseStreet.Path.Push(&point)
					}

					strs = removeStreet(strs, i)
					i = -1

				} else if baseStreet.Path.First().DistanceFrom(currentStreet.Path.Last()) == shortestDistanceToOtherStreets &&
					shortestDistanceToOtherStreets < distanceTolerance {

					var match = baseStreet.Path.First()

					// flip baseStreet & currentStreet points
					reversePath(baseStreet.Path)
					reversePath(currentStreet.Path)

					// merge currentStreet in to baseStreet
					for _, point := range currentStreet.Path.PointSet {
						if point.Equals(match) {
							continue
						}
						baseStreet.Path.Push(&point)
					}

					// flip baseStreet points back
					reversePath(baseStreet.Path)
					reversePath(currentStreet.Path)

					strs = removeStreet(strs, i)
					i = -1

				} else if baseStreet.Path.Last().DistanceFrom(currentStreet.Path.Last()) == shortestDistanceToOtherStreets &&
					shortestDistanceToOtherStreets < distanceTolerance {

					var match = baseStreet.Path.Last()

					// flip currentStreet points
					reversePath(currentStreet.Path)

					// merge currentStreet in to baseStreet
					for _, point := range currentStreet.Path.PointSet {
						if point.Equals(match) {
							continue
						}
						baseStreet.Path.Push(&point)
					}

					// flip currentStreet points back
					reversePath(currentStreet.Path)

					strs = removeStreet(strs, i)
					i = -1

				} else if baseStreet.Path.First().DistanceFrom(currentStreet.Path.First()) == shortestDistanceToOtherStreets &&
					shortestDistanceToOtherStreets < distanceTolerance {

					var match = baseStreet.Path.First()

					// flip baseStreet points
					reversePath(baseStreet.Path)

					// merge currentStreet in to baseStreet
					for _, point := range currentStreet.Path.PointSet {
						if point.Equals(match) {
							continue
						}
						baseStreet.Path.Push(&point)
					}

					// flip baseStreet points back
					reversePath(baseStreet.Path)

					strs = removeStreet(strs, i)
					i = -1

				} else {

					// If two way and distance not shortest
					if debugMode {
						debugStreets(baseStreet, currentStreet, normName, strs)
					}

					if (baseStreet.Path.Last().DistanceFrom(currentStreet.Path.First()) == shortestDistanceToOtherStreets ||
							baseStreet.Path.First().DistanceFrom(currentStreet.Path.Last()) == shortestDistanceToOtherStreets ||
							baseStreet.Path.Last().DistanceFrom(currentStreet.Path.Last()) == shortestDistanceToOtherStreets ||
							baseStreet.Path.First().DistanceFrom(currentStreet.Path.First()) == shortestDistanceToOtherStreets) {
						if _, ok := mergedStreetMap[normName]; !ok {
							mergedStreetMap[normName] = []*street{currentStreet}
						} else {
							mergedStreetMap[normName] = append(mergedStreetMap[normName], currentStreet)
						}

						strs = removeStreet(strs, i)
						i--
					}
				}
			}

			// When reach to the last item of list street, then remove the first item and loop again the list street
			if (i == (len(strs) - 1) || len(strs) < 1) {
				strs = removeStreet(strs, i)
				i = -1

				if _, ok := mergedStreetMap[normName]; !ok {
					mergedStreetMap[normName] = []*street{baseStreet}
				} else {
					mergedStreetMap[normName] = append(mergedStreetMap[normName], baseStreet)
				}

			}
			continue
		}
	}

	return mergedStreetMap
}


func mergeStreet(nameMap map[string][]*street, isUseStreetName bool) map[string][]*street {
	var reversePath = func(path *geo.Path) {
		for i := path.PointSet.Length()/2 - 1; i >= 0; i-- {
			opp := path.PointSet.Length() - 1 - i
			path.PointSet[i], path.PointSet[opp] = path.PointSet[opp], path.PointSet[i]
		}
	}

	var mergedStreetMap = make(map[string][]*street)

	// points do not have to be exact matches
	// var distanceTolerance = 0.01 // 1000 meters
	var distanceTolerance = 0.003 // 300 meters
	var distanceRange = 0.0003 // roughly 30 meters

	for strName, strs := range nameMap {
		// Sort streets follow the descendant length
		strs = sortStreetsDescLength(strs)
		strs = removeRoundabout(strs)

		var normName = strings.Split(strName, "__")[0]

		if (len(strs) < 1) {
			continue
		} else if (len(strs) == 1) {
			if _, ok := mergedStreetMap[normName]; !ok {
				mergedStreetMap[normName] = []*street{strs[0]}
			} else {
				mergedStreetMap[normName] = append(mergedStreetMap[normName], strs[0])
			}
			continue
		}

		var index = getLongestStreetIndex(strs)
		var baseStreet = strs[index]
		strs = removeStreet(strs, index)

		for i := 0; i < len(strs); i++ {

			var shortestDistanceToOtherStreets = shortestDistanceToOtherStreets(baseStreet, strs)
			var shortestDistanceToOtherSameDirectionStreets = shortestDistanceToOtherSameDirectionStreets(baseStreet, strs)
			var currentStreet = strs[i]

			if debugMode {
				debugStreets(baseStreet, currentStreet, normName, strs)
			}

			// In the case the street is duplicated, then ignore the one
			if (baseStreet.Path == currentStreet.Path) {
				strs = removeStreet(strs, i)
				i--

				if (i == (len(strs) - 1) || len(strs) < 1) {
					if _, ok := mergedStreetMap[normName]; !ok {
						mergedStreetMap[normName] = []*street{baseStreet}
					} else {
						mergedStreetMap[normName] = append(mergedStreetMap[normName], baseStreet)
					}
				}

				continue
			}

			var vector1 = createPathVector(baseStreet.Path.First(), baseStreet.Path.Last())
			var vector2 = createPathVector(currentStreet.Path.First(), currentStreet.Path.Last())
			var isTwoStreetsSameDirection = isTwoPathsSameDirection(vector1, vector2)

			// In the case shortest distance to other same direction streets = 0,
			// or = shortest distance to other streets
			// but 2 streets don't intersect, then add street to last of list streets and continue loop
			// if ((shortestDistanceToOtherSameDirectionStreets == 0 ||
			if ((shortestDistanceToOtherSameDirectionStreets == 0 &&
				shortestDistanceToOtherSameDirectionStreets == shortestDistanceToOtherStreets) &&
				!isTwoStreetsSameDirection &&
				i < (len(strs) - 1)) {
					// strs = append(strs, strs[i])
					continue
			}

			shortestDistance := getShortestDistance(baseStreet.Path, currentStreet.Path)

			// Not merge streets same direction, intersect together but distance greater than distance range
			if (baseStreet.Path.IntersectsPath(currentStreet.Path) && shortestDistance > distanceRange) {
				strs = removeStreet(strs, i)
				i--

				if (i == (len(strs) - 1) || len(strs) < 1) {
					if _, ok := mergedStreetMap[normName]; !ok {
						mergedStreetMap[normName] = []*street{baseStreet}
					} else {
						mergedStreetMap[normName] = append(mergedStreetMap[normName], baseStreet)
					}
				}

				continue
			}

			if baseStreet.Path.Last().DistanceFrom(currentStreet.Path.First()) == shortestDistanceToOtherStreets &&
				shortestDistanceToOtherStreets < distanceTolerance {

				var match = baseStreet.Path.Last()

				// merge currentStreet in to baseStreet
				for _, point := range currentStreet.Path.PointSet {
					if point.Equals(match) {
						continue
					}
					baseStreet.Path.Push(&point)
				}

				strs = removeStreet(strs, i)
				i = -1
			} else if baseStreet.Path.First().DistanceFrom(currentStreet.Path.Last()) == shortestDistanceToOtherStreets &&
				shortestDistanceToOtherStreets < distanceTolerance {

				var match = baseStreet.Path.First()

				// flip baseStreet & currentStreet points
				reversePath(baseStreet.Path)
				reversePath(currentStreet.Path)

				// merge currentStreet in to baseStreet
				for _, point := range currentStreet.Path.PointSet {
					if point.Equals(match) {
						continue
					}
					baseStreet.Path.Push(&point)
				}

				// flip baseStreet points back
				reversePath(baseStreet.Path)
				reversePath(currentStreet.Path)

				strs = removeStreet(strs, i)
				i = -1
			} else if baseStreet.Path.Last().DistanceFrom(currentStreet.Path.Last()) == shortestDistanceToOtherStreets &&
				shortestDistanceToOtherStreets < distanceTolerance {

				var match = baseStreet.Path.Last()

				// flip currentStreet points
				reversePath(currentStreet.Path)

				// merge currentStreet in to baseStreet
				for _, point := range currentStreet.Path.PointSet {
					if point.Equals(match) {
						continue
					}
					baseStreet.Path.Push(&point)
				}

				// flip currentStreet points back
				reversePath(currentStreet.Path)

				strs = removeStreet(strs, i)
				i = -1
			} else if baseStreet.Path.First().DistanceFrom(currentStreet.Path.First()) == shortestDistanceToOtherStreets &&
				shortestDistanceToOtherStreets < distanceTolerance {

				var match = baseStreet.Path.First()

				// flip baseStreet points
				reversePath(baseStreet.Path)

				// merge currentStreet in to baseStreet
				for _, point := range currentStreet.Path.PointSet {
					if point.Equals(match) {
						continue
					}
					baseStreet.Path.Push(&point)
				}

				// flip baseStreet points back
				reversePath(baseStreet.Path)

				strs = removeStreet(strs, i)
				i = -1
			} else {

				if (baseStreet.Path.Last().DistanceFrom(currentStreet.Path.First()) == shortestDistanceToOtherStreets ||
						baseStreet.Path.First().DistanceFrom(currentStreet.Path.Last()) == shortestDistanceToOtherStreets ||
						baseStreet.Path.Last().DistanceFrom(currentStreet.Path.Last()) == shortestDistanceToOtherStreets ||
						baseStreet.Path.First().DistanceFrom(currentStreet.Path.First()) == shortestDistanceToOtherStreets) {
					if _, ok := mergedStreetMap[normName]; !ok {
						mergedStreetMap[normName] = []*street{currentStreet}
					} else {
						mergedStreetMap[normName] = append(mergedStreetMap[normName], currentStreet)
					}
				}
			}

			// When reach to the last item of list street, then remove the first item and loop again the list street
			if (i == (len(strs) - 1) || len(strs) < 1) {
				strs = removeStreet(strs, i)
				i = -1

				if _, ok := mergedStreetMap[normName]; !ok {
					mergedStreetMap[normName] = []*street{baseStreet}
				} else {
					mergedStreetMap[normName] = append(mergedStreetMap[normName], baseStreet)
				}
			}
		}
	}

	return mergedStreetMap
}
