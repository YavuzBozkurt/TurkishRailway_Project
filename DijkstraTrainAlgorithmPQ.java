
import javafx.util.Pair;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.*;
import java.util.Arrays;

public class DijkstraTrainAlgorithmPQ {
    private static final int NO_PARENT = -1;
    private static String PATH_STRING = "";
    private static String TIMES_STRING = "";
    private static final int TRAIN_VELOCITY = 2;
    private static final int SWITCH_WEIGHT = 5;
    private static final int SWITCH_DISTANCE = 10;
    private static final int TRACK_WEIGHT = 0;
    private static final int TRACK_DISTANCE = 5;

    static class Edge {
        public int source;
        public int destination;
        public int weight;
        public int distance;
        /*
        defines an edge
        @param source int, source vertex of the directed edge
        @param destination int, destination vertex the edge is pointing to
        @param weight int, weight / cost of the edge
        @param distance int, distance the edge entails
        @return None
        @throws IllegalArgumentException if {@code source == null || destination == null
                weight == null || distance == null}
        @pre {@code source != null && destination != null && weight != null && distance != null}
        @post {@code new edge(source, destination, weight, distance)}
         */
        public Edge(int source, int destination, int weight, int distance) throws IllegalArgumentException{
            this.source = source;
            this.destination = destination;
            this.weight = weight;
            this.distance = distance;
        }
    }

    static class Graph {
        int totalVertices;
        LinkedList<Edge>[] adjacencyList;
        int[] parents;
        public List<String> paths_to_print = new ArrayList<>();
        public List<String> times_to_print = new ArrayList<>();
        public List<String> checkpoint_arrival_times_from_source = new ArrayList<>();
        /*
        defines a graph G = (V,E) with |V(G)| = totalVertices number of isolated vertices
        @param totalVertices, |V(G)|
        @return None
        @throws IllegalArgumentException if {@code totalVertices == null}
        @pre {@code totalVertices != null}
        @modifies {@code adjacencyList}
        @modifies {@code parents}
        @post {@code adjacencyList.size() == totalVertices && \forall int i ; adjacencyList.has(i);
                    adjacencyList[i] = new LinkedList<>()}
        @post {@code parents.length == totalVertices && \forall int i ; parents.has(i); parents[i] == -2}
         */
        public Graph(int totalVertices) throws IllegalArgumentException{
            this.totalVertices = totalVertices;
            adjacencyList = new LinkedList[totalVertices];
            for (int i = 0; i < totalVertices; i++) {
                adjacencyList[i] = new LinkedList<>();
            }
            parents = new int[totalVertices];
            for (int i = 0; i < totalVertices; i++) {
                parents[i] = -2;
            }
        }
        /*
        creates an edge object
        @param source int, source vertex of the edge
        @param destination int, destination vertex the edge is pointing to
        @param weight int, weight / cost of the edge
        @param distance int, distance the edge entails
        @return None
        @throws IllegalArgumentException if {@code source = null ||
            destination == null || weight == null || distance == null}
        @pre {@code source != null && destination != null &&
                weight != null && distance != null}
        @modifies {@code adjacencyList}
        @post {@code \forall int i; adjacencyList.has(i) ; 
                adjacencyList[i] == new edge(source, destination, weight, distance)}
         */
        public void createEdge(int source, int destination, int weight, int distance) throws IllegalArgumentException{
            Edge edge = new Edge(source, destination, weight, distance);
            adjacencyList[source].add(edge);
        }
        /*
        uses adjacency lists (linked list), priority queues and Dijkstra's algorithm to find shortest paths
        @param source_checkpoint int, source vertex of the dijkstra run
        @param destination_checkpoint int, destination vertex of the dijkstra run
        @param train_arrival_checkpoint int, destination vertex at which the train stops
        @param train_departure_checkpoint int, the source vertex at which the train departs
        @param source_departure_time String, the time at which the train departs
        @param vertex_labels List<String>, the list in which all checkpoint names of all stations (KAS,CUM,ARI,DEM,KAR) are present
        @return None
        @throws IllegalArgumentException if {@code source_checkpoint == null || destination_checkpoint == null ||
                    train_arrival_checkpoint == null || train_departure_checkpoint == null || source_departure_time == null}
        @pre {@code source_checkpoint != null && destination_checkpoint =! null && train_arrival_checkpoint != null &&
                    train_departure_checkpoint != null && source_departure_time != null}
        @modifies {@code parents}
        @modifies {@code shortest_paths}
        @modifies {@code total_weights_from_source}
        @modifies {@code total_distances_from_source}
        @modifies {@code checkpoint_arrival_times_from_source}
        @modifies {@code priorityQueue}
        @post {@code \forall int i; shortest_paths.has(i) && vertex_labels.get(i).reachable_from_source == true
                      && total_weights_from_source[i] != Integer.MAX_VALUE; shortest_paths[i] == true}
        @post {@code  (\forall int i; total_weights_from_source.has(i) && vertex_labels.get(i).reachable_from_source == true;
                        total_weights_from_source[i] == total_weights_from_source[extracted_vertex] + adjacent_vertex.weight) &&
                            total_weights_from_source[source_checkpoint] == 0}
        @post {@code  (\forall int i; total_distances_from_source.has(i) && vertex_labels.get(i).reachable_from_source == true;
                         total_distances_from_source[i] == total_distances_from_source[extracted_vertex] + adjacent_vertex.distance) &&
                            total_distances_from_source[source_checkpoint] == 0;}
        @post {@code parents[source_checkpoint] == -1 && \forall int i; parents.has(i) &&
                         vertex_labels.get(i).reachable_from_source; parents[i] == vertex_labels.get(i).immediate_predecessor()}
        @post {@code checkpoint_arrival_times_from_source[source_checkpoint] == source_departure_time &&
                    \forall int i; checkpoint_arrival_times_from_source.has(i) && vertex_labels.get(i).reachable_from_source == true;
                        checkpoint_arrival_times_from_source[i] == clock(source_departure_time, total_distances_from_source[i]) }
        @post {@code priorityQueue.isEmpty() == true}
         */
        public void dijkstra_minDistFinder(int source_checkpoint, int destination_checkpoint, int train_arrival_checkpoint, int train_departure_checkpoint,
                                           String source_departure_time, List<String> vertex_labels) throws IllegalArgumentException{
            parents[source_checkpoint] = -1;
            boolean[] shortest_paths = new boolean[totalVertices];
            int[] total_weights_from_source = new int[totalVertices];
            int[] total_distances_from_source = new int[totalVertices];
            checkpoint_arrival_times_from_source.clear();
            for (int i = 0; i < totalVertices; i++) {
                checkpoint_arrival_times_from_source.add("xx:xx");
            }
            Arrays.fill(total_weights_from_source,Integer.MAX_VALUE);
            Arrays.fill(total_distances_from_source,Integer.MAX_VALUE);
            PriorityQueue<Pair<Integer, Integer>> priorityQueue = new PriorityQueue<>(totalVertices, Comparator.comparingInt(Pair::getKey));
            total_weights_from_source[source_checkpoint] = 0;
            total_distances_from_source[source_checkpoint] = 0;
            checkpoint_arrival_times_from_source.set(source_checkpoint,source_departure_time);
            priorityQueue.offer(new Pair<>(total_weights_from_source[source_checkpoint], source_checkpoint));
            while (!priorityQueue.isEmpty()) {
                Pair<Integer, Integer> pair_to_extract = priorityQueue.poll();
                int extracted_vertex = pair_to_extract.getValue();
                if (!shortest_paths[extracted_vertex]) {
                    shortest_paths[extracted_vertex] = true;
                }
                LinkedList<Edge> adjacent_vertices = adjacencyList[extracted_vertex];
                for (Edge adjacentVertex : adjacent_vertices) {
                    int adjacent_vertex = adjacentVertex.destination;
                    if (!shortest_paths[adjacent_vertex]) {
                        if (total_weights_from_source[extracted_vertex] + adjacentVertex.weight < total_weights_from_source[adjacent_vertex]) {
                            total_weights_from_source[adjacent_vertex] = total_weights_from_source[extracted_vertex] + adjacentVertex.weight;
                            total_distances_from_source[adjacent_vertex] = total_distances_from_source[extracted_vertex] + adjacentVertex.distance;
                            parents[adjacentVertex.destination] = extracted_vertex;
                            int time_spent_until_vertex = checkpoint_time_finder(TRAIN_VELOCITY,
                                    total_distances_from_source[extracted_vertex] + adjacentVertex.distance);
                            String checkpoint_arrival_time = clock(source_departure_time, time_spent_until_vertex);
                            checkpoint_arrival_times_from_source.set(adjacentVertex.destination, checkpoint_arrival_time);
                            priorityQueue.offer(new Pair<>(total_weights_from_source[adjacent_vertex], adjacent_vertex));
                        }
                    }
                }
            }
            printDijkstraResult(total_weights_from_source,
                    checkpoint_arrival_times_from_source,
                    source_checkpoint,
                    destination_checkpoint,
                    parents,
                    train_arrival_checkpoint,
                    train_departure_checkpoint,
                    vertex_labels);
        }
        /*
        prints the shortest path for a destination checkpoint and the visiting clock time for each of the checkpoints in that path
        @param total_weights_from_source int[], total weights from the source vertex
        @param checkpoint_arrival_times_from_source List<String>, clock times for arrival from the source vertex to all other vertices
        @param source_checkpoint int, source vertex of the dijkstra run
        @param destination_checkpoint int, destination vertex of the dijkstra run
        @param parents int[], immediate predecessor of every vertex in their shortest path from source
        @param train_arrival_checkpoint int, destination vertex at which the train stops
        @param train_departure_checkpoint int, the source vertex at which the train departs
        @param vertex_labels List<String>, the list in which all checkpoint names of all stations (KAS,CUM,ARI,DEM,KAR) are present
        @return None
        @throws IllegalArgumentException if {@code total_weights_from_source == null || checkpoint_arrival_times_from_source == null
                    || source_checkpoint == null || destination_checkpoint == null || train_arrival_checkpoint == null || train_departure_checkpoint == null || vertex_labels == null}
        @throws ArrayIndexOutOfBoundsException if {@code  vertex_index < 0 && vertex_index >= total_weights_from_source.length}
        @throws IndexOutOfBoundsException if {@code i >= paths_to_print.size() && i < 0}
        @throws IndexOutOfBoundsException if {@code i >= times_to_print.size() && i < 0}
        @pre {@code total_weights_from_source != null && checkpoint_arrival_times_from_source != null && source_checkpoint != null &&
                    destination_checkpoint != null && train_arrival_checkpoint != null && train_departure_checkpoint != null && vertex_labels != null}
        @modifies {@code paths_to_print}
        @modifies {@code times_to_print}
        @post {@code paths_to_print.size == 1 + (numberOfCheckpointsEntered + 1)}
        @post {@code times_to_print.size == 1 + (numberOfCheckpointsEntered + 1)}
         */
        public void printDijkstraResult(int[] total_weights_from_source, List<String> checkpoint_arrival_times_from_source,
                                        int source_checkpoint, int destination_checkpoint, int[] parents, int train_arrival_checkpoint, int train_departure_checkpoint, List<String> vertex_labels)
                throws IllegalArgumentException, IndexOutOfBoundsException {
            for (int vertex_index = 0; vertex_index < total_weights_from_source.length; vertex_index++) {
                if (vertex_index == destination_checkpoint ) {
                    if (total_weights_from_source[vertex_index] != Integer.MAX_VALUE) {
                        System.out.print("total weight from source vertex " + vertex_labels.get(source_checkpoint) + " to destination vertex " + vertex_labels.get(destination_checkpoint)
                                + " is: " + total_weights_from_source[vertex_index] + " and the path would be: ");
                    }
                    try {
                        path_printer(vertex_index, destination_checkpoint, parents, checkpoint_arrival_times_from_source, vertex_labels);
                    }
                    catch (ArrayIndexOutOfBoundsException throwables) {
                        System.out.println("Such shortest path does not exist!");
                        throwables.printStackTrace();
                    }
                    paths_to_print.add(PATH_STRING);
                    times_to_print.add(TIMES_STRING);
                    System.out.print(paths_to_print.get(paths_to_print.size() - 1));
                    System.out.print("\t" + times_to_print.get(times_to_print.size() - 1));
                    PATH_STRING = "";
                    TIMES_STRING = "";
                    System.out.println();
                    if (source_checkpoint != train_departure_checkpoint && destination_checkpoint == train_arrival_checkpoint) {
                        System.out.print(paths_to_print.get(1) + "");
                        for (int i = 2; i < paths_to_print.size(); i++) {
                            System.out.print(paths_to_print.get(i).substring(1));
                        }
                        System.out.print("\t" );
                        System.out.print(times_to_print.get(1) + "");
                        for (int i = 2; i < times_to_print.size(); i++) {
                            System.out.print(times_to_print.get(i).substring(5));
                        }
                    }
                }
            }
        }
        /*
        prepares the string paths to be printed
        @param vertex int, destination vertex and its direct or indirect predecessors
        @param destination_checkpoint int, destination vertex of the dijkstra run
        @param parents int[], array in which every vertex's immediate predecessor is stored
        @param checkpoint_arrival_times_from_source List<String>, arrival time to every vertex from the train_departure_checkpoint
        @param vertex_labels List<String>, the list in which all checkpoint names of all stations (KAS,CUM,ARI,DEM,KAR) are present
        @return None
        @throws IllegalArgumentException if {@code vertex == null || destination_checkpoint == null || parents == null
                    || checkpoint_arrival_times_from_source == null || vertex_labels == null}
        @throws ArrayIndexOutOfBoundsException if {@code vertex >= parents.length || vertex < 0}
        @throws IndexOutOfBoundsException if {@code vertex >= checkpoint_arrival_times_from_source.size()
                    || vertex < 0}
        @pre {@code vertex != null && destination_checkpoint != null && parents != null &&
                    checkpoint_arrival_times_from_source != null && vertex_labels != null}
        @pre {@code vertex < parents.length && vertex >= 0}
        @pre {@code vertex < checkpoint_arrival_times_from_source.size() && vertex >= 0}
        @modifies {@code PATH_STRING}
        @modifies {@code TIMES_STRING}
        @post path PATH_STRING from source_checkpoint to destination_checkpoint of the dijkstra run
        @post path TIMES_STRING from source_checkpoint to destination_checkpoint of the dijkstra run
         */
        public static void path_printer(int vertex, int destination_checkpoint, int[] parents, List<String> checkpoint_arrival_times_from_source, List<String> vertex_labels)
        throws IllegalArgumentException, IndexOutOfBoundsException{
            if (vertex == NO_PARENT) {
                return;
            }
            path_printer(parents[vertex],
                    destination_checkpoint,
                    parents,
                    checkpoint_arrival_times_from_source,
                    vertex_labels);
            PATH_STRING = PATH_STRING + vertex_labels.get(vertex);
            TIMES_STRING = TIMES_STRING + checkpoint_arrival_times_from_source.get(vertex);
            if (vertex != destination_checkpoint) {
                PATH_STRING = PATH_STRING + " -> ";
                TIMES_STRING = TIMES_STRING + " -> ";
            }
        }
        /*
        calculates time passed between two checkpoints
        @param velocity int, velocity of the train
        @param distance int, distance that the train is covering
        @return {@code Math.floor(distance / velocity) }
        @throws IllegalArgumentException if {@code velocity == null || distance == null}
        @pre {code velocity != null && distance != null}
         */
        public static int checkpoint_time_finder(int velocity, int distance) throws IllegalArgumentException {
            return distance / velocity;
        }
        /*
        defines the clock time
        @param source_departure_time String
        @param time_spent_until_destination int
        @return clock for the arrival time to destination_checkpoint
        @throws IllegalArgumentException if {@code current_time == null || time_spent_until_destination == null}
        @throws StringIndexOutOfBoundsException if {@code \forall int k; clock.substring(i, j) &&  k > j && k < i}
        @pre {@code current_time != null && time_spent_until_destination != null}
        @pre {@code \forall int k; clock.substring(i, j) &&  i <= k <= j; clock.charAt(k) != null}
        @post {@code clock} the clock time at which destination_checkpoint is visited
         */
        public static String clock(String source_departure_time, int time_spent_until_destination) throws IllegalArgumentException, StringIndexOutOfBoundsException {
            int clock_hour = Integer.parseInt(source_departure_time.substring(0, 2));
            String clock = source_departure_time.substring(0, 2) + ":" + source_departure_time.substring(3, 5);
            int updated_minutes = Integer.parseInt(source_departure_time.substring(3, 5)) + time_spent_until_destination;
            int hours_quotient = updated_minutes / 60;
            int clock_minutes = updated_minutes % 60;
            if (hours_quotient >= 1) {
                clock_hour = clock_hour + hours_quotient;
                clock = clock_hour + ":" + clock_minutes;
                if (clock_hour / 24 >= 1) {
                    clock_hour = clock_hour - 24;
                    if(clock_hour >= 0 && clock_hour < 10)
                        clock = "0" + clock_hour + ":" + clock_minutes;
                }
            }
            if(clock_minutes >= 0 && clock_minutes < 10) return clock.substring(0,3) + "0" + clock_minutes;
            return clock.substring(0,3) + clock_minutes;
        }

        public static void main(String[] args) throws SQLException {
            List<String> vertex_labels = new ArrayList<>();
            Graph graph = null;
            ResultSet rs_1 = null;
            ResultSet rs_2 = null;
            ResultSet rs_3 = null;
            Connection connection = null;
            try {
                 connection = DatabaseManager.getInstance().getConnection(); //connect to the ROUTE database in DBeaver
                 rs_1 = connection.createStatement().executeQuery("SELECT DISTINCT source AS column " +
                        "FROM  \"route\" UNION SELECT DISTINCT destination FROM \"route\" ");
            }
            catch (SQLException throwables) {
                throwables.printStackTrace();
            }
            while (Objects.requireNonNull(rs_1).next()) {
                vertex_labels.add(rs_1.getString("column"));
            }
            Graph graphForRightwardsTrains = new Graph(vertex_labels.size());
            Graph graphForLeftwardsTrains = new Graph(vertex_labels.size());
            try {
                 rs_2 = connection.createStatement().executeQuery("SELECT source, destination " +
                        "FROM \"route\" ");
            }
            catch (SQLException throwables) {
                throwables.printStackTrace();
            }
            while (Objects.requireNonNull(rs_2).next()) {
                if (rs_2.getString("destination").startsWith("M")) {
                    graphForRightwardsTrains.createEdge(vertex_labels.indexOf(rs_2.getString("source")),
                            vertex_labels.indexOf(rs_2.getString("destination")),
                            SWITCH_WEIGHT,
                            SWITCH_DISTANCE);
                }
                if (rs_2.getString("destination").startsWith("TC") )
                    graphForRightwardsTrains.createEdge(vertex_labels.indexOf(rs_2.getString("source")),
                            vertex_labels.indexOf(rs_2.getString("destination")),
                            TRACK_WEIGHT,
                            TRACK_DISTANCE);
            }
            try {
                rs_3 = connection.createStatement().executeQuery("SELECT source, destination " + //connect to the ROUTE database in DBeaver
                        "FROM \"route\" ");
            }
            catch (SQLException throwables) {
                throwables.printStackTrace();
            }
            while (Objects.requireNonNull(rs_3).next()) {
                if (rs_3.getString("source").startsWith("M")) {
                    graphForLeftwardsTrains.createEdge(vertex_labels.indexOf(rs_3.getString("destination")),
                            vertex_labels.indexOf(rs_3.getString("source")),
                            SWITCH_WEIGHT,
                            SWITCH_DISTANCE);
                }
                if (rs_3.getString("source").startsWith("TC")) {
                    graphForLeftwardsTrains.createEdge(vertex_labels.indexOf(rs_3.getString("destination")),
                            vertex_labels.indexOf(rs_3.getString("source")),
                            TRACK_WEIGHT,
                            TRACK_DISTANCE);
                }
            }
            int totalVertices = vertex_labels.size();
            Scanner scanner = new Scanner(System.in);
            System.out.print("Please select the direction of the train right/left: ");
            String train_direction = scanner.nextLine();
            if (train_direction.equals("right")) {
                graph = graphForRightwardsTrains;
            }
            if (train_direction.equals("left")) {
                graph = graphForLeftwardsTrains;
            }
            else {
                System.exit(0);
            }
            System.out.print("Please enter source and destination vertices in source-destination format: ");
            String input_source_destination = scanner.nextLine();
            System.out.print("Please enter the departure time of the train in xx:xx format: ");
            String source_departure_time = scanner.nextLine();
            if (source_departure_time.charAt(2) != ':') {
                System.exit(0);
            }
            int train_departure_checkpoint = vertex_labels.indexOf(input_source_destination.substring(0, input_source_destination.indexOf("-")));
            int train_arrival_checkpoint = vertex_labels.indexOf(input_source_destination.substring(input_source_destination.indexOf("-")+1));
                if (vertex_labels.indexOf(input_source_destination.substring(0, input_source_destination.indexOf("-"))) >= 0 &&
                        vertex_labels.indexOf(input_source_destination.substring(input_source_destination.indexOf("-")+1)) <= totalVertices
                                && vertex_labels.indexOf(input_source_destination.substring(input_source_destination.indexOf("-")+1)) >= 0 &&
                                vertex_labels.indexOf(input_source_destination.substring(input_source_destination.indexOf("-")+1)) <= totalVertices
                                && input_source_destination.charAt(input_source_destination.substring(0, input_source_destination.indexOf("-")).length())== '-') {
                    graph.dijkstra_minDistFinder(vertex_labels.indexOf(input_source_destination.substring(0, input_source_destination.indexOf("-"))),
                            vertex_labels.indexOf(input_source_destination.substring(input_source_destination.indexOf("-")+1)), train_arrival_checkpoint,
                            train_departure_checkpoint, source_departure_time, vertex_labels);
                }
                    else {
                    System.out.println(" There is no such destination or source, or you entered in incorrect format, please re-run the program again");
                    System.exit(0);
                }
            int source_checkpoint = vertex_labels.indexOf(input_source_destination.substring(0, input_source_destination.indexOf("-")));
            int destination_checkpoint = vertex_labels.indexOf(input_source_destination.substring(input_source_destination.indexOf("-")+1));
            System.out.println("Would you like to modulate the train route ? yes/no");
            String modulation_answer = scanner.nextLine();
            while (modulation_answer.equals("yes")) {
                System.out.print("Pick a checkpoint that the train should visit: ");
                String input_toVisit_checkpoint = scanner.nextLine();
                graph.dijkstra_minDistFinder(source_checkpoint, vertex_labels.indexOf(input_toVisit_checkpoint),
                        train_arrival_checkpoint, train_departure_checkpoint, source_departure_time, vertex_labels);
                source_checkpoint = vertex_labels.indexOf(input_toVisit_checkpoint);
                System.out.println("Would you like to modulate the train route ? yes/no");
                modulation_answer = scanner.nextLine();
                source_departure_time = graph.checkpoint_arrival_times_from_source.get(source_checkpoint);
            }
            graph.dijkstra_minDistFinder(source_checkpoint, destination_checkpoint, train_arrival_checkpoint, train_departure_checkpoint, source_departure_time, vertex_labels);
        }
    }
}
