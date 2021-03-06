import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Random;
import java.util.Set;

// Statistics
import org.apache.commons.math3.stat.descriptive.DescriptiveStatistics;

// Graph Implementation
import org.jgrapht.Graph;
import org.jgrapht.Graphs;
import org.jgrapht.alg.connectivity.ConnectivityInspector;
import org.jgrapht.alg.interfaces.MatchingAlgorithm;
import org.jgrapht.alg.matching.HopcroftKarpMaximumCardinalityBipartiteMatching;
import org.jgrapht.alg.shortestpath.GraphMeasurer;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.DefaultWeightedEdge;
import org.jgrapht.graph.DirectedAcyclicGraph;
import org.jgrapht.graph.SimpleGraph;
import org.jgrapht.graph.SimpleWeightedGraph;
import org.jgrapht.traverse.BreadthFirstIterator;
import org.jgrapht.traverse.DepthFirstIterator;
import org.jgrapht.traverse.RandomWalkVertexIterator;

public class SubgraphIsomorphism {
    // the statistics
    private static int numBackTracking = -1; // keep track of backtracking calls
    private static int numLocalPruning = -1; // keep track of how much pruned locally
    private static int numGlobalPruned = -1; // keep track of how much pruned globally
    private static double totalCostGraphQL = -1; // keep track of the total cost when computing the order for GraphQL
    private static double falseMatchingParents = -1; // keep track of the vertices removed from parent in SEQq
    private static double falseMatchingExtraEdge = -1; // keep track of the vertices removed from extra edge in SEQq
    private static Map<Graph<Vertex, DefaultEdge>, Integer> numIsomorphic = null; // the number of graphs that are isomorphic and removed
    // when finding hard-to-find graphs
    private static String algorithmNameC = ""; // algorithm in use for candidates
    private static String algorithmNamePO = ""; // algorithm in use for processing order
    private static String algorithmNameB = ""; // algorithm in use for backtracking
    // failing sets
    private static int fullSolutions = 0, partialSolutions = 0, emptyCandidates = 0, conflicts = 0;
    // veqs
    private static int numSymmetric = -1;
    // outlier value
    static double outlierValue = 1.5;

    // wander joins, separate file
    public static WanderJoins wj = new WanderJoins();
    // star graphs, and frequent dataset mining, seperate file
    public static HardToFindStarGraphs sg;


    // algorithms
    // isomorphisms
    private static final String GROUNDTRUTH = "groundTruth";
    private static final String GRAPHQL = "graphQL";
    private static final String QUICKSI = "quickSI";
    private static final String DYNAMIC_ORDER = "dynamic order";
    private static final String DAF = "DAF";
    private static final String VEQS = "VEQs";
    // creating random subgraphs
    private static final String RANDOM_WALK = "random walk";
    private static final String RANDOM_NODE_NEIGHBOR = "random node neighbor";
    // the format of the graph were reading
    private static final String PROTEINS = "proteins graph format";
    private static final String IGRAPH = "iGraph format";
    private static String formatTarget;
    private static String formatQuery;
    // if we are considering subsets or whole label
    private static final String SUBSETS = "subsets";
    private static final String COMPLETE = "complete";
    private static String labelCheck;

    // error messages
    // error message if didn't find isomorphism algorithm
    public static final String noAlgorithmFound = "Algorithm specified is not valid.\n" +
            "Specify one of the following algorithms: \n" +
            "\t "+GROUNDTRUTH+": finds the ground truth isomorphism.  Only uses LDA in pruning and BFS for ordering.\n" +
            "\t "+GRAPHQL+": uses the GraphQL algorithm.\n" +
            "\t "+QUICKSI+": uses the QuickSI algorithm. (Note: cannot be used for processing candidates)\n"+
            "\t "+DYNAMIC_ORDER+": uses the dynamic ordering for process order. (Note: cannot only be used for ordering\n" +
            "\t\tand cannot use QUICKSI isomorphism)\n"+
            "\t "+DAF+": uses the DAF algorithm. (Note: equivalent to "+GROUNDTRUTH+" for processing candidates " +
            "\t\tand cannot use " +DYNAMIC_ORDER+")\n"+
            "\t "+VEQS+": uses the VEQs algorithm (Note: only can be used for backtracking and cannot use dynamic ordering)";
    // error message if didn't find random subgraph algorithm
    private static final String noRandomSubgraphMethodFound = "Random subgraph creation method is not valid.\n " +
            "Specify one of the following connections methods: \n" +
            "\t "+RANDOM_WALK+": constructs non-induced subgraph using random walk algorithm.\n" +
            "\t "+RANDOM_NODE_NEIGHBOR+": constructs induced subgraph using random node neighbor algorithm.\n";
    // the format for the graphProteins files
    public static final String graphProteinsFileFormat = "Graph: <graphLocation> " +
            "\n Number of Nodes: <numberNodesInGraph> " +
            "\n Minsup (integer): <integerMinsup> " +
            "\n Minsup (percentage): <percentMinsup> " +
            "\n Attribute Label " +
            "\n <largeProfile> appears in <numAppearances> vertex profiles: " +
            "\n <listVerticesIds>";
    private static final String graphIGraphFileFormat = "v {id} {labels separated by space}\n" +
            "     *                  e {incoming vertex} {outgoing vertex} {label}";
    // no correct format was listed
    public static final String noGraphFormat ="Format of graph files specified is not valid.\n " +
            "Specify one of the following connections methods: \n" +
            "\t "+ PROTEINS +": uses the proteins format.\n" +
            "\t\t" + graphProteinsFileFormat +
            "\t "+IGRAPH+": uses the iGraph format.\n " +
            "\t\t" +graphIGraphFileFormat;

    // keep track of axillary structures
    private static QISequence SEQq; //QI-Sequence
    private static DirectedAcyclicGraph<Vertex, DefaultEdge> queryDAG; // directed acyclic graph
    private static List<Vertex> dynamicOrder = new ArrayList<>(); // keep track of elements added with dynamic programing
    private static CS cs;

    /**
     * Saves a graph in a file
     *                  Formatted :
     *                  {Number of Vertex}
     *                  {id} {label}
     *                  {Number of edges for Vertex}
     *                  {id outgoing vertex} {id incoming vertex}
     *                  # - comments to skip
     * @param graph graph to save
     * @param outputFolderName location where saving graph
     * @param graphName the name of the graph we are saving
     * @return the location of the file
     * @throws IOException check if file exists
     */
    public static String writeGraph(Graph<Vertex, DefaultEdge> graph, String outputFolderName,
                                    String graphName) throws IOException {
        // write to output file
        BufferedWriter writer = new BufferedWriter(new FileWriter(
                outputFolderName+graphName));
        writer.write("");

        // write the vertex information
        writer.append("# vertex information \n");
        int numVertices = graph.vertexSet().size();
        // iterate through vertices
        writer.append(String.valueOf(numVertices)).append("\n");
        for (Vertex v: graph.vertexSet()) {
            // get the next vertex and its label
            writer.append(String.valueOf(v.getId())).append(" ").append(v.getLabel()).append("\n");
        }

        // write the edge information
        writer.append("# edge information \n");
        for (Vertex v: graph.vertexSet()) {
            // get the next vertex and its edge
            writer.append(String.valueOf(graph.degreeOf(v))).append("\n");
            for(Vertex neighbor: Graphs.neighborListOf(graph, v)){
                writer.append(String.valueOf(v.getId())).append(" ").append(String.valueOf(neighbor.getId())).append("\n");
            }
        }
        writer.close();

        return outputFolderName+graphName;
    }

    /**
     * Create the graph for the proteins Dataset
     * @param graphFile the file which contains the vertex and edge information
     *                  Formatted :
     *                  {Number of Vertex}
     *                  {id} {label}
     *                  {Number of edges for Vertex}
     *                  {id outgoing vertex} {id incoming vertex}
     *                  # - comments to skip
     * @return associated graph
     * @throws IOException for file reader
     */
    private static Graph<Vertex, DefaultEdge> readProteinsGraph(File graphFile) throws IOException {
        // keep track of the vertices for easy access
        Map<Integer, Vertex> idToVertex = new LinkedHashMap<>();

        // create a new graph
        Graph<Vertex, DefaultEdge> g = new SimpleGraph<>(DefaultEdge.class);
        BufferedReader br = new BufferedReader(new FileReader(graphFile));
        String line = br.readLine().strip();

        // skip lines starting with "#"
        while (line.length()>0 && line.charAt(0) == '#') {
            line = br.readLine().strip();
        }

        // get the number of vertices first
        int numberVertices = Integer.parseInt(line);
        line = br.readLine();

        // iterate through the vertices
        for(int i = 0; i < numberVertices; i++) {
            line = line.strip();
            // skip lines starting with "#"
            if (line.length()>0 && line.charAt(0) == '#') {
                i--;
                continue;
            }

            // get the id and chemical from the line
            String[] vertexInfo = line.split(" ");
            // store the key
            int vID = Integer.parseInt(vertexInfo[0]);
            // store the attributes
            String vChemical = vertexInfo[1];

            // create/add new vertex
            Vertex v = new Vertex(vID, vChemical);
            idToVertex.put(vID, v);
            addVertex(g, v);

            line = br.readLine();
        }

        //iterate through the edges of each vertex
        while(line != null) {
            //skip lines starting with "#"
            if (line.length()>0 && line.charAt(0) == '#') {
                line = br.readLine();
                continue;
            }

            //find the number of edges and iterate through them
            int numEdges = Integer.parseInt(line);

            for(int i = 0; i < numEdges; i++) {
                //get the information from the line
                line = br.readLine();
                String[] edge = line.split(" ");
                int vID1 = Integer.parseInt(edge[0]);
                int vID2 = Integer.parseInt(edge[1]);

                // undirected edge so only add once
                if(vID1 < vID2){
                    Vertex v1 = idToVertex.get(vID1);
                    Vertex v2 = idToVertex.get(vID2);
                    addEdge(g, v1, v2);
                }

            }
            line = br.readLine();
        }
        br.close();

        return g;
    }

    /**
     * Reads the graphs from a iGraph format
     * @param inputFile the file which contains the vertex and edge information
     *                  Formatted :
     *                  v {id} {labels separated by space}
     *                  e {incoming vertex} {outgoing vertex} {label}
     * @return associated graph
     * @throws IOException for file reader
     */
    public static Graph<Vertex, DefaultEdge> readIGraph(File inputFile) throws IOException {
        // keep track of the vertices for easy access
        Map<Integer, Vertex> idToVertex = new LinkedHashMap<>();
        // create a new graph
        Graph<Vertex, DefaultEdge> g = new SimpleGraph<>(DefaultEdge.class);


        // read through input file
        BufferedReader br = new BufferedReader(new FileReader(inputFile));
        String line = br.readLine().strip();
        line = br.readLine().strip();
        // first read in the vertices
        while(line!=null){
            String[] info = line.split(" ");
            if(info[0].equals("v")){
                int id = Integer.parseInt(info[1]);
                // add the id
                StringBuilder labels = new StringBuilder();
                for(int i = 2; i<info.length; i++){
                    String label = info[i];
                    labels.append(label);
                    if(i<info.length-1){
                        labels.append(",");
                    }
                }
                // add the vertex
                String stringLabels = new String(labels);
                Vertex v = new Vertex(id, stringLabels);
                addVertex(g,v);

                // keep track of vertex and id
                idToVertex.put(id, v);
            }
            else{
                break;
            }

            line = br.readLine().strip();
        }

        // add the edges
        while(line!=null){
            line = line.strip();
            String[] info = line.split(" ");
            if(info[0].equals("e")){
                int vID1 = Integer.parseInt(info[1]);
                int vID2 = Integer.parseInt(info[2]);

                // undirected edge so only add once
                if(vID1 < vID2){
                    Vertex v1 = idToVertex.get(vID1);
                    Vertex v2 = idToVertex.get(vID2);
                    addEdge(g, v1, v2);
                }
            }
            line = br.readLine();
        }
        br.close();

        return g;
    }

    /**
     * Reads the graph depending on the format given
     * @param inputFile the input file containing the graph
     * @param method the method we will be using
     * @return the corresponding graph
     * @throws IOException for reading the file
     */
    public static Graph<Vertex, DefaultEdge> readGraph(File inputFile, String method) throws IOException {
        // create the graphs
        Graph<Vertex, DefaultEdge> g;
        // get extension
        String extension = inputFile.toString().substring(inputFile.toString().lastIndexOf('.')+1);

        if(method.equals(PROTEINS)) {
            if(!extension.equals("grf") && !extension.equals("txt")){
                System.out.println("NOTE: Are you sure it is "+method+" and not "+IGRAPH);
            }
            g = readProteinsGraph(inputFile);
        }
        else if(method.equals(IGRAPH)){
            if(!extension.equals("igraph")){
                System.out.println("NOTE: Are you sure it is "+method+" and not "+PROTEINS);
            }
            g = readIGraph(inputFile);
        }
        else{
            return null;
        }
        return g;
    }

    /**
     * Add a vertex to the graph.  Must update it's profile as well
     * @param graph the graph
     * @param u the vertex
     */
    public static void addVertex(Graph<Vertex, DefaultEdge> graph, Vertex u){
        // add the vertex to the graph
        graph.addVertex(u);

        // build the profile to include own label
        u.addToProfile(u);
    }

    /**
     * Add an edge to the graph between the two vertices.  Must update both of the vertices profiles
     * @param graph the graph
     * @param u the source vertex of edge within the graph
     * @param v the target vertex of edge within the graph
     */
    public static void addEdge(Graph<Vertex, DefaultEdge> graph, Vertex u, Vertex v){
        graph.addEdge(u, v);

        u.addToProfile(v);
        v.addToProfile(u);
    }

    /**
     * Remove an edge to the graph between the two vertices.  Must update both of the vertices profiles
     * @param graph the graph
     * @param u the source vertex of edge within the graph
     * @param v the target vertex of edge within the graph
     */
    public static void removeEdge(Graph<Vertex, DefaultEdge> graph, Vertex u, Vertex v){
        graph.removeEdge(u, v);

        u.removeFromProfile(v);
        v.removeFromProfile(u);
    }

    /**
     * A function that will copy a vertex and create a new one
     * @param vertex the vertex we are copying
     * @param newId the id of the new vertex
     * @return the copied vertex
     */
    public static Vertex copyVertex(Vertex vertex, int newId){
        // copy the attributes
        return new Vertex(newId, vertex.getLabel());
    }
    /**
     * Calculates the statistics for a given graph.
     * The number of subsets for a profile for each vertex.
     * NOTE: Only use for small graphs
     * @param graph the graph to calculate the statistics
     */
    private static void calculateStatistics(Graph<Vertex, DefaultEdge> graph){
        // keep track of a the possible labels within the graph
        Set<String> possibleValues = new HashSet<>();
        // keep track of the possible subsets
        Set<ArrayList<String>> possibleSubsets = new HashSet<>();

        // keep track of the maximum degree of the graph
        int maxDegree = 0;

        // iterate through the vertices and calculate the possible combinations for the profiles
        for(Vertex v: graph.vertexSet()){
            // find the maximum degree
            int degree = graph.degreeOf(v);
            if(degree>maxDegree){
                maxDegree = degree;
            }

            // calculate the statistics for the vertex
            ArrayList<ArrayList<String>> subsetValues = v.calculateNumberProfileSubsets();
            possibleSubsets.addAll(subsetValues);

            // find the label of the vertex
            possibleValues.add(v.getLabel());
        }
    }

    /**
     * Uses Label and Degree Filtering Technique (LDF): v is a candidate of u if they are the same labels and the degree
     * of v is larger or equal to the degree of u
     * @param query the query graph
     * @param target the target graph
     * @param u a vertex from the query graph
     * @param v a vertex from the target graph
     * @return true if v is a candidate of u
     */
    private static boolean labelDegreeFiltering(Graph<Vertex, DefaultEdge> query, Graph<Vertex, DefaultEdge> target,
                                                Vertex u, Vertex v){
        int vDegree = target.degreeOf(v);
        int uDegree = query.degreeOf(u);
        if(labelCheck.equals(SUBSETS)){
            return vDegree >= uDegree && u.subLabel(v);
        }
        return vDegree >= uDegree && u.sameLabel(v);
    }

    /**
     * Local Pruning: v is a candidate of u if u's profile is a subset of v's profile.  A profile is a lexicographically
     * sorted set of labels of the vertex
     * @param u a vertex from the query graph
     * @param v a vertex from the target graph
     * @return true if v is a candidate of u
     */
    private static boolean localPruning(Vertex u, Vertex v){
        if(labelCheck.equals(SUBSETS)){
            return u.profileSubsetLabelSubset(v);
        }
        return u.profileSubset(v);
    }

    /**
     * Perform global pruning on the candidates of the query vertices. Checks if the substructure of the neighbors can
     * be mapped to the substructure of the target vertex neighbors
     * @param query the query graph
     * @param target the target graph
     * @param candidates the candidates
     */
    private static void pruneGlobally(Graph<Vertex, DefaultEdge> query, Graph<Vertex, DefaultEdge> target,
                                     Map<Vertex, Set<Vertex>> candidates){
        // keep track of the previous candidates by their query/target vertex pair
        Set<List<Vertex>> T = new HashSet<>();

        // iterate through the query vertices
        for(Vertex u: query.vertexSet()){
            // iterate through the candidates of that graph
            for(Vertex v : candidates.get(u)){
                List<Vertex> element = new ArrayList<>();
                element.add(u);
                element.add(v);

                // union T an <u, v>
                T.add(element);
            }
        }

        while(true){
            // crate a new set T'
            Set<List<Vertex>> TPrime = new HashSet<>();

            // iterate through the T values
            for(List<Vertex> pair: T) {
                // get the u and v values from the pairs
                Vertex u = pair.get(0);
                Vertex v = pair.get(1);

                // create a bipartite graph
                // neighbors u - neighbors v
                // edges are from candidate set

                // create a new graph, which will be the bipartite graph
                Graph<Vertex, DefaultEdge> B = new SimpleGraph<>(DefaultEdge.class);
                // keep track of where the copy came from
                Map<Vertex, Vertex> copyToOriginal = new HashMap<>();
                int id = 0; // keep track of the current id being added
                // keep track of u neighbors added
                Set<Vertex> uPVertices = new HashSet<>();
                // add copy of the neighbors of u
                for(Vertex uP : Graphs.neighborListOf(query, u)){
                    Vertex uPCopy = copyVertex(uP, id); id++;
                    copyToOriginal.put(uPCopy, uP);
                    B.addVertex(uPCopy);
                    uPVertices.add(uPCopy);
                }
                // keep track of the v neighbors added
                Set<Vertex> vPVertices = new HashSet<>();
                // add the neighbors of v
                for(Vertex vP : Graphs.neighborListOf(target, v)){
                    Vertex vPCopy = copyVertex(vP, id); id++; // create copy so target vertices with same id can be added
                    copyToOriginal.put(vPCopy, vP);
                    B.addVertex(vPCopy);
                    vPVertices.add(vPCopy);
                }

                // crate a new set T''
                Set<List<Vertex>> TPrimePrime = new HashSet<>();

                // iterate through each combination in the bipartite graph
                // iterate through the u values
                for(Vertex uP: uPVertices) {
                    for(Vertex vP: vPVertices) {
                        // check if vP is a candidate of uP
                        if(candidates.get(copyToOriginal.get(uP)).contains(copyToOriginal.get(vP))){
                            // add edge between two values
                            B.addEdge(uP, vP);

                            // add to T''
                            List<Vertex> elementPrime = new ArrayList<>();
                            elementPrime.add(copyToOriginal.get(uP));
                            elementPrime.add(copyToOriginal.get(vP));
                            TPrimePrime.add(elementPrime);
                        }
                    }
                }
                // find the maximum matching of B
                HopcroftKarpMaximumCardinalityBipartiteMatching<Vertex, DefaultEdge> matchingAlgorithm =
                        new HopcroftKarpMaximumCardinalityBipartiteMatching<>(B, uPVertices, vPVertices);
                MatchingAlgorithm.Matching<Vertex, DefaultEdge> bipartiteMatching = matchingAlgorithm.getMatching();

                // matching does not contain all query vertices
                if(bipartiteMatching.getEdges().size() != uPVertices.size()){
                    candidates.get(u).remove(v);

                    // build T'
                    // add to T' if not already there
                    TPrime.addAll(TPrimePrime);
                }
            }
            if(TPrime.size() == 0){
                break;
            }
            else{
                T = TPrime;
            }
        }

    }

    /**
     * Computes the candidates, which are the possible target vertices for each of the vertices within the query graph
     * @param query the query graph
     * @param target the target graph
     * @return a candidates for each vertex within the query graph
     */
    private static Map<Vertex, Set<Vertex>> groundTruthComputeCandidates(Graph<Vertex, DefaultEdge> query,
                                                                     Graph<Vertex, DefaultEdge> target){
        numLocalPruning = 0;
        // keep track of the candidates for a given vertex
        Map<Vertex, Set<Vertex>> candidates = new HashMap<>();

        // find the possible candidates given vertex label and degree
        // iterate through the query vertices
        for(Vertex u: query.vertexSet()){
            // create a new set
            Set<Vertex> uCandidates = new HashSet<>();

            // iterate through the target vertices
            for(Vertex v: target.vertexSet()){

                // Label and Degree Filtering (LDF)
                // check that the target vertex has appropriate attributes and degree
                if(labelDegreeFiltering(query, target, u, v)){
                    uCandidates.add(v);
                }
                // if a pair has been pruned
                else{
                    numLocalPruning++;
                }
            }
            // store u candidates
            candidates.put(u, uCandidates);
        }

        return candidates;
    }

    /**
     * Computes the candidates, which are the possible target vertices for each of the vertices within the query graph
     * @param query the query graph
     * @param target the target graph
     * @return a candidates for each vertex within the query graph
     */
    private static Map<Vertex, Set<Vertex>> graphQLComputeCandidates(Graph<Vertex, DefaultEdge> query,
                                                             Graph<Vertex, DefaultEdge> target){
        numLocalPruning = 0; numGlobalPruned = 0;
        // keep track of the candidates for a given vertex
        Map<Vertex, Set<Vertex>> candidates = new HashMap<>();
        // keep track of the number of pairs before global pruning
        int numBefore = 0;

        // find the possible candidates given vertex label and degree
        // iterate through the query vertices
        for(Vertex u: query.vertexSet()){
            // create a new set
            Set<Vertex> uCandidates = new HashSet<>();

            // iterate through the target vertices
            for(Vertex v: target.vertexSet()){
                // Label and Degree Filtering (LDF)
                // check that the target vertex has appropriate attributes and degree
                if(labelDegreeFiltering(query, target, u, v) && localPruning(u, v)){
                    uCandidates.add(v);
                    numBefore++; // found a new pair
                }
                // pruned some value
                else{
                    numLocalPruning++;
                }
            }
            // store u candidates
            candidates.put(u, uCandidates);
        }
        pruneGlobally(query, target, candidates);

        // calculate the number of pairs after global pruning
        int numberAfter = 0;
        for(Vertex c: candidates.keySet()){
            numberAfter+=candidates.get(c).size();
        }
        // the number of pairs globally pruned is the difference between the number of pairs before and after
        numGlobalPruned = numBefore-numberAfter;

        return candidates;
    }

    /**
     * Compute the processing order of how the query vertices will be checked.  Now it picks the vertex with the
     * smallest candidate set and then adds them in BFS order
     * @param query the query graph
     * @param candidates sets of candidates for each query vertex
     * @return a list of the vertices in the order they should be checked
     */
    private static ArrayList<Vertex> groundTruthComputeProcessingOrder(Graph<Vertex, DefaultEdge> query,
                                                           Map<Vertex, Set<Vertex>> candidates){
        ArrayList<Vertex> order = new ArrayList<>();
        // if we're looking for the ground truth then order is by BFS
        while (order.size() < candidates.size()) {
            Iterator<Vertex> nodeIterator = candidates.keySet().iterator();
            // find the node with the fewest amount of candidates
            Vertex startingNode = nodeIterator.next();
            // find the next vertex that is not in the order
            while (order.contains(startingNode)) {
                startingNode = nodeIterator.next();
            }

            for (Vertex currentNode : candidates.keySet()) {
                // update it when find a node with smaller candidate size and not yet in order
                if (candidates.get(startingNode).size() > candidates.get(currentNode).size()
                        && !order.contains(currentNode)) {
                    startingNode = currentNode;
                }
            }

            // do breadth first search with starting node
            Iterator<Vertex> qIter = new BreadthFirstIterator<>(query, startingNode);
            while (qIter.hasNext()) {
                Vertex vertex = qIter.next();
                order.add(vertex);
            }
        }

        return order;
    }

    /**
     * Calculate the size of the joins between current order and u. Calculation from GraphQL.
     * @param query the query graph
     * @param leftSize the previous order size of joins
     * @param candidates the possible target vertices for the query vertices
     * @param order the order we are checking the query vertices
     * @param u the possible query vertex we are adding
     * @param gamma the gamma value
     * @return the size of joining u to the current order
     */
    private static double calculateSize(Graph<Vertex, DefaultEdge> query, double leftSize,
                                        Map<Vertex, Set<Vertex>> candidates, ArrayList<Vertex> order, Vertex u,
                                        double gamma){
        // size(i) = size(i.left)*size(i.right)*gamma^connection(order, u)
        double size = leftSize*candidates.get(u).size();
        int power = 0;
        // get the number of nodes it is currently connected to already within the order
        for(Vertex v: order){
            if(query.containsEdge(u, v)){
                power++;
            }
        }

        // multiply by gamma^power
        for(int i = 0; i<power; i++){
            size = size*gamma;
        }
        return size;
    }

    /**
     * Compute the processing order of how the query vertices will be checked.  Now it picks the vertex with the
     * smallest candidate set and then adds them in BFS order
     * @param query the query graph
     * @param candidates sets of candidates for each query vertex
     * @param gamma the gamma value
     * @return a list of the vertices in the order they should be checked
     */
    private static ArrayList<Vertex> graphQLComputeProcessingOrder(Graph<Vertex, DefaultEdge> query,
                                                                   Map<Vertex, Set<Vertex>> candidates, double gamma){
        ArrayList<Vertex> order = new ArrayList<>();
        Iterator<Vertex> iter = new DepthFirstIterator<>(query);
        // we do not know the next element or minimum candidate size so take first one we see
        Vertex uNext = iter.next();
        double min = candidates.get(uNext).size();

        // keep track of the vertices we need to check, originally all the vertices in query graph
        ArrayList<Vertex> toCheck = new ArrayList<>();
        toCheck.add(uNext);

        while(iter.hasNext()) {
            // get the graph vertex and compare number of candidates
            Vertex u = iter.next(); toCheck.add(u);
            if(candidates.get(u).size() < min){
                uNext = u;
                min = candidates.get(u).size();
            }
        }

        // add the vertex with the smallest candidate set
        order.add(uNext);
        toCheck.remove(uNext);
        // keep track of cost and total
        double cost = min;
        totalCostGraphQL = cost;

        // while there are still nodes to add
        while(toCheck.size()>0){
            Iterator<Vertex> toCheckIter = toCheck.iterator();
            uNext = toCheckIter.next();
            // don't know minimum
            min = calculateSize(query, cost, candidates, order, uNext, gamma);

            while(toCheckIter.hasNext()){
                Vertex u = toCheckIter.next();
                double currentSize = calculateSize(query, cost, candidates, order, u, gamma);
                // choose the minimum size
                if(currentSize<min){
                    uNext = u;
                    min = currentSize;
                }
            }

            // next smallest size, add the corresponding vertex
            order.add(uNext);
            toCheck.remove(uNext);
            cost = min;
            totalCostGraphQL += cost;
        }

        return order;
    }

    /**
     * Finds the weight for a given vertex
     * @param u vertex in question
     * @param candidates candidate set
     * @return weight for the given vertex
     */
    public static int vertexWeight(Vertex u, Map<Vertex, Set<Vertex>> candidates){
        return candidates.get(u).size();
    }

    /**
     * Finds the weight for a given edge
     * @param e edge in question
     * @param target target graph
     * @param query query graph
     * @param candidates candidate set
     * @return weight for the given vertex
     */
    public static int edgeWeight(DefaultEdge e, Graph<Vertex, DefaultEdge> target, Graph<Vertex, DefaultEdge> query,
                                 Map<Vertex, Set<Vertex>> candidates){
        Vertex u = query.getEdgeSource(e);
        Vertex v = query.getEdgeTarget(e);

        int weight = 0;
        for(Vertex uP : candidates.get(u)){
            for(Vertex vP: candidates.get(v)){
                if(target.containsEdge(uP, vP)){
                    weight++;
                }
            }
        }
        return weight;
    }

    /**
     * Choose a random edge from the set
     * @param edges the set of edges
     * @return a random edge from the set
     */
    public static DefaultWeightedEdge randomEdge(Set<DefaultWeightedEdge> edges){
        // get a random edge from the chosen
        Random random = new Random();
        // random index
        int index = random.nextInt(edges.size());
        // get corresponding edge
        Iterator<DefaultWeightedEdge> edgeIter = edges.iterator();
        DefaultWeightedEdge randomEdge = edgeIter.next();
        for(int i = 0; i< index; i++){
            randomEdge = edgeIter.next();
        }
        return randomEdge;
    }

    /**
     * Selects the first edge for the tree
     * @param weightedQuery the query with weighted vertices and edges
     * @return the next edge in the minimum spanning tree
     */
    public static  DefaultWeightedEdge selectFirstEdge(Graph<Vertex, DefaultWeightedEdge> weightedQuery){
        Set<DefaultWeightedEdge> possibleEdges = weightedQuery.edgeSet();
        // find minimum weight
        double minimumWeight = weightedQuery.getEdgeWeight(possibleEdges.iterator().next());
        for(DefaultWeightedEdge e: possibleEdges){
            if(weightedQuery.getEdgeWeight(e)<minimumWeight){
                minimumWeight = weightedQuery.getEdgeWeight(e);
            }
        }

        Set<DefaultWeightedEdge> edgesMinWeight = new HashSet<>();
        // get the edges of minimum weights
        for(DefaultWeightedEdge e: possibleEdges){
            if(weightedQuery.getEdgeWeight(e)==minimumWeight){
                edgesMinWeight.add(e);
            }
        }

        // get the edge with minim weights
        DefaultWeightedEdge maxEdge = edgesMinWeight.iterator().next();
        double maxDegree = weightedQuery.degreeOf(weightedQuery.getEdgeSource(maxEdge)) +
                weightedQuery.degreeOf(weightedQuery.getEdgeTarget(maxEdge));
        // find minimum weight
        for(DefaultWeightedEdge e: edgesMinWeight){
            double currentDegree =  weightedQuery.degreeOf(weightedQuery.getEdgeSource(e)) +
                    weightedQuery.degreeOf(weightedQuery.getEdgeTarget(e));
            if(currentDegree>maxDegree){
                maxDegree = currentDegree;
            }
        }

        Set<DefaultWeightedEdge> edgesMinWeightMaxDegree = new HashSet<>();
        // get the edges of minimum degree
        for(DefaultWeightedEdge e: edgesMinWeight){
            double currentDegree =  weightedQuery.degreeOf(weightedQuery.getEdgeSource(e)) +
                    weightedQuery.degreeOf(weightedQuery.getEdgeTarget(e));
            if(currentDegree==maxDegree){
                edgesMinWeightMaxDegree.add(e);
            }
        }

        return randomEdge(edgesMinWeightMaxDegree);
    }

    /**
     * Find which vertex will be added to the tree first for a given edge
     * @param e the edge
     * @param weightedGraph the weighted graph
     * @return the order of the vertices
     */
    public static List<Vertex> selectVertexOrder(DefaultWeightedEdge e,
                                                 Graph<Vertex, DefaultWeightedEdge> weightedGraph){
        Vertex u = weightedGraph.getEdgeSource(e);
        Vertex v = weightedGraph.getEdgeTarget(e);

        // the order of the vertices
        List<Vertex> orderVertices = new ArrayList<>();
        // if the first vertex has a smaller weight
        if(u.getWeight()<v.getWeight()){
            orderVertices.add(u); orderVertices.add(v);
        }
        // if the second vertex has a smaller weight
        else if(u.getWeight()>v.getWeight()){
            orderVertices.add(v); orderVertices.add(u);
        }
        // they have the same weight

        // if the first vertex has larger degree
        else if(weightedGraph.degreeOf(u)>weightedGraph.degreeOf(v)){
            orderVertices.add(u); orderVertices.add(v);
        }
        // if the second vertex has larger degree
        else if(weightedGraph.degreeOf(u)<weightedGraph.degreeOf(v)){
            orderVertices.add(v); orderVertices.add(u);
        }
        // they have the same weight and degrees

        // choose a random vertex to start
        else{
            Random random = new Random();
            int index = random.nextInt();
            if(index%2 == 0){
                orderVertices.add(u); orderVertices.add(v);
            }
            else{
                orderVertices.add(v); orderVertices.add(u);
            }
        }

        return orderVertices;
    }

    /**
     * Finds the next edge within the spanning tree
     * @param weightedQuery a weighted graph of the query
     * @param SEQq the QI-Sequence
     * @return the next edge to add to spanning tree
     */
    public static DefaultWeightedEdge selectSpanningEdge(Graph<Vertex, DefaultWeightedEdge> weightedQuery, QISequence SEQq){
        Set<DefaultWeightedEdge> possibleEdges = weightedQuery.edgeSet();

        // only add edge if only one vertex is within the current tree
        Set<DefaultWeightedEdge> connectedEdges = new HashSet<>();
        for(DefaultWeightedEdge e: possibleEdges){
            Vertex u = weightedQuery.getEdgeSource(e);
            Vertex v = weightedQuery.getEdgeTarget(e);

            if((SEQq.containsVertex(u) && !SEQq.containsVertex(v)) ||
                    (SEQq.containsVertex(v) && !SEQq.containsVertex(u))){
                connectedEdges.add(e);
            }
        }

        // get the minimum weighted edge
        Iterator<DefaultWeightedEdge> edgeIter = connectedEdges.iterator();
        double minimum = weightedQuery.getEdgeWeight(edgeIter.next());
        // iterate through edges
        while(edgeIter.hasNext()){
            double current = weightedQuery.getEdgeWeight(edgeIter.next());
            // update minimum
            if(current<minimum){
                minimum = current;
            }
        }

        // reduce the possible edges to only be the minimum
        Set<DefaultWeightedEdge> minimumEdges = new HashSet<>();
        for(DefaultWeightedEdge e: connectedEdges){
            if(weightedQuery.getEdgeWeight(e)==minimum){
                minimumEdges.add(e);
            }
        }

        if(minimumEdges.size()>1) {
            // keep track of edges with each size
            Map<Integer, Set<DefaultWeightedEdge>> edgesWithConnections = new HashMap<>();

            // if there are multiple possibilities then check the how connected it is to the tree
            int maximumConnection = -1;
            for (DefaultWeightedEdge e : minimumEdges) {
                // find the connection within the QI-Sequence
                Set<Vertex> currentVertices = SEQq.currentVertices();

                int currentConnection = 0;
                // get the vertex that is not already in the tree
                Vertex u = weightedQuery.getEdgeSource(e);
                if(currentVertices.contains(u)){
                    u = weightedQuery.getEdgeTarget(e);
                }
                // check if the neighbors of u are in QI-Sequence
                for (Vertex uP : Graphs.neighborListOf(weightedQuery, u)) {
                    if (currentVertices.contains(uP)) {
                        currentConnection++;
                    }
                }

                if(!edgesWithConnections.containsKey(currentConnection)){
                    edgesWithConnections.put(currentConnection, new HashSet<>());
                }
                edgesWithConnections.get(currentConnection).add(e);

                // update the maximum
                if (currentConnection > maximumConnection) {
                    maximumConnection = currentConnection;
                }
            }

            // choose the edges with maximum connection
            minimumEdges = edgesWithConnections.get(maximumConnection);
        }
        // get the vertex with largest degree
        if(minimumEdges.size()>1){
            // keep track of edges with each size
            Map<Integer, Set<DefaultWeightedEdge>> edgesWithDegree = new HashMap<>();

            // if there are multiple possibilities then check the how connected it is to the tree
            int maximumDegree = -1;
            for (DefaultWeightedEdge e : minimumEdges) {
                // find the connection within the QI-Sequence
                Set<Vertex> currentVertices = SEQq.currentVertices();

                // get the vertex that is not already in the tree
                Vertex u = weightedQuery.getEdgeSource(e);
                if (currentVertices.contains(u)) {
                    u = weightedQuery.getEdgeTarget(e);
                }

                // vertex is not in tree so only will contain edges in weighted query, also extra edges will not contain
                // this vertex because both vertices must be within the tree for this, but kept for sanity
                int currentDegree = weightedQuery.degreeOf(u)
                        + SEQq.getExtraEdges(u).size();

                if (!edgesWithDegree.containsKey(currentDegree)) {
                    edgesWithDegree.put(currentDegree, new HashSet<>());
                }
                edgesWithDegree.get(currentDegree).add(e);

                // update the maximum
                if (currentDegree > maximumDegree) {
                    maximumDegree = currentDegree;
                }
            }
            minimumEdges = edgesWithDegree.get(maximumDegree);
        }


        // randomly choose from the possible edges
        return randomEdge(minimumEdges);
    }


    /**
     * Build the QI-Sequence (spanning tree) with a given order
     * @param query the query graph
     * @param order the processing order
     * @return the QI-Sequence
     */
    public static QISequence buildSpanningTreeWithOrder(Graph<Vertex, DefaultEdge> query, ArrayList<Vertex> order){
        QISequence SEQq = new QISequence();
        // make sure for each vertex (beside root), there is a prev vertex connected to it
        convertOrderBFS(query, order);

        // add the first vertex to the tree
        Vertex u0 = order.get(0);
        SEQq.addVertex(u0, -1);
        if(query.degreeOf(u0)>=3){
            SEQq.extraDeg(u0, query.degreeOf(u0));
        }

        // iterate through remaining vertices
        for(int i = 1; i < order.size(); i++){
            Vertex ui = order.get(i);
            // keep track if we already assigned the parent
            boolean foundParent = false;

            // iterate through previous vertices
            for(int j = i-1; j >= 0; j--){
                Vertex uj = order.get(j);
                // check if they are adjacent
                if(query.containsEdge(ui, uj)){
                    // if we haven't found a parent yet then set
                    if(!foundParent){
                        SEQq.addVertex(ui, j);
                        foundParent = true;
                    }
                    // we want ui to contain uj because j<i
                    else{
                        SEQq.extraEdge(ui, uj);
                    }
                }
                // if there does not exists an edge then add to no extra edge information
                else{
                    SEQq.noExtraEdge(ui, uj);
                }
            }
            if(query.degreeOf(ui)>=3){
                SEQq.extraDeg(ui, query.degreeOf(ui));
            }
        }

        return SEQq;
    }

    /**
     * Build the spanning tree based on the weighted query
     * @param weightedQuery the query graph with weights for edges and nodes
     * @return the spanning tree and extra topology for the query graph
     */
    public static QISequence buildSpanningTree(Graph<Vertex, DefaultWeightedEdge> weightedQuery){
        QISequence SEQq = new QISequence();
        // keep track of the order we add the vertices in
        Map<Vertex, Integer> vertexToTree = new HashMap<>();

        // find the first edge in the sequence
        DefaultWeightedEdge firstEdge = selectFirstEdge(weightedQuery);

        // find the first vertex
        List<Vertex> vertexOrder = selectVertexOrder(firstEdge, weightedQuery);
        Vertex v1 = copyVertex(vertexOrder.get(0), vertexOrder.get(0).getId()); vertexToTree.put(vertexOrder.get(0), 0);
        Vertex v2 = copyVertex(vertexOrder.get(1), vertexOrder.get(1).getId()); vertexToTree.put(vertexOrder.get(1), 1);

        // add the first vertex to the tree
        SEQq.addVertex(v1, -1);
        int lastVertexAdded = SEQq.addVertex(v2, 0);

        // remove the edge from the graph
        weightedQuery.removeEdge(v1, v2);

        // keep adding vertices until seen all vertices
        while(lastVertexAdded != weightedQuery.vertexSet().size()-1){
            DefaultWeightedEdge nextEdge = selectSpanningEdge(weightedQuery, SEQq);

            // get the vertex that is not contained within the spanning tree
            Vertex u = weightedQuery.getEdgeTarget(nextEdge);
            Vertex uP = weightedQuery.getEdgeSource(nextEdge);
            // if the source is the parent vertex
            if(SEQq.containsVertex(u)){
                Vertex save = uP;
                uP = u;
                u = save;
            }
            lastVertexAdded = SEQq.addVertex(u, vertexToTree.get(uP));
            vertexToTree.put(u, lastVertexAdded);

            // remove the edge
            weightedQuery.removeEdge(u, uP);

            // get the extra edges within the query graph
            for(DefaultWeightedEdge extraEdges: new HashSet<>(weightedQuery.edgeSet())){
                Vertex uExtra = weightedQuery.getEdgeSource(extraEdges);
                Vertex vExtra = weightedQuery.getEdgeTarget(extraEdges);

                // if this is an extra edge
                if(SEQq.containsVertex(uExtra) && SEQq.containsVertex(vExtra)){
                    // update the extra degree information, remember edges that might have been deleted before
                    int uExtraDegree = weightedQuery.degreeOf(uExtra)
                            +SEQq.getT().degreeOf(uExtra)
                            +SEQq.getExtraEdges(uExtra).size();
                    if(uExtraDegree>2){
                        SEQq.extraDeg(uExtra, uExtraDegree);
                    }
                    int vExtraDegree = weightedQuery.degreeOf(vExtra)
                            +SEQq.getT().degreeOf(vExtra)
                            +SEQq.getExtraEdges(vExtra).size();
                    if(vExtraDegree>2){
                        SEQq.extraDeg(vExtra, vExtraDegree);
                    }

                    // update the extra edge information
                    if(vertexToTree.get(uExtra)>vertexToTree.get(vExtra)){
                        SEQq.extraEdge(uExtra, vExtra);
                    }
                    else{
                        SEQq.extraEdge(vExtra, uExtra);
                    }

                    // remove extra edge
                    weightedQuery.removeEdge(uExtra, vExtra);
                }
            }
        }

        List<Vertex> vertices = new ArrayList<>(weightedQuery.vertexSet());
        // add the no edge extra information
        for(int i = 0; i<vertices.size(); i++){
            for(int j = i+1; j<vertices.size(); j++){
                Vertex u = vertices.get(i);
                Vertex v = vertices.get(j);
                // we do not want to create an edge with itself
                if(v.equals(u)){
                    continue;
                }
                // add if u appears after v in order
                if(vertexToTree.get(u)>vertexToTree.get(v)) {
                    SEQq.noExtraEdge(u, v);
                }
                else{
                    SEQq.noExtraEdge(v, u);
                }
            }
        }

        return SEQq;
    }

    /**
     * Constructs the DAG and order for a query graph
     * @param query the query graph
     * @param candidates the candidates
     * @param order the processing order, should be empty
     * @return the DAG of the query graph
     */
    public static DirectedAcyclicGraph<Vertex, DefaultEdge> constructDAG(Graph<Vertex, DefaultEdge> query,
                                                                  Map<Vertex, Set<Vertex>> candidates, List<Vertex> order){
        DirectedAcyclicGraph<Vertex, DefaultEdge> qD = new DirectedAcyclicGraph<>(DefaultEdge.class);
        Iterator<Vertex> vertexIterator = query.vertexSet().iterator();

        Map<Double, Set<Vertex>> vertexWeights = new HashMap<>();

        Vertex u = vertexIterator.next();
        double candidateSize =  candidates.get(u).size();
        double degreeSize = query.degreeOf(u);
        double size = candidateSize/degreeSize;

        vertexWeights.put(size, new HashSet<>());
        vertexWeights.get(size).add(u);
        double minimum = size;

        // find the minimum size which is the root
        while(vertexIterator.hasNext()){
            u = vertexIterator.next();

            candidateSize =  candidates.get(u).size();
            degreeSize = query.degreeOf(u);
            size = candidateSize/degreeSize;

            if(!vertexWeights.containsKey(size)){
                vertexWeights.put(size, new HashSet<>());
            }
            vertexWeights.get(size).add(u);

            if(size<minimum){
                minimum = size;
            }
        }

        // root is randomly chosen from smallest sizes
        Vertex root = randomVertex(vertexWeights.get(minimum));
        qD.addVertex(root);

        // keep track of the vertices to add
        List<Vertex> layerLast = new ArrayList<>(); layerLast.add(root);

        while(layerLast.size()!=0){
            List<Vertex> layerNext = new ArrayList<>();
            // sort last layer by degree descending
            layerLast.sort(
                    (Vertex v1, Vertex v2) -> Integer.compare(query.degreeOf(v2), query.degreeOf(v1))
            );
            // sort last layer by candidate set ascending
            layerLast.sort(
                    (Vertex v1, Vertex v2) -> Integer.compare(candidates.get(v1).size(), candidates.get(v2).size())
            );

            // iterate through the vertices
            for(Vertex v: layerLast){
                // add to be next to be checked
                layerNext.addAll(Graphs.neighborListOf(query, v));
                layerNext.removeAll(order);

                for(Vertex vP: Graphs.neighborListOf(query, v)){
                    if(!qD.containsVertex(vP)){
                        qD.addVertex(vP);
                    }
                    if(!qD.containsEdge(vP, v)){
                        qD.addEdge(v, vP);
                    }
                }
            }
            layerLast.removeAll(order);
            order.addAll(layerLast);
            layerLast=layerNext;
        }

        return qD;
    }

    /**
     * Converts the order to BFS, so that trees and DAGs only have one root
     * @param query the query graph
     * @param order the original order
     */
    public static void convertOrderBFS(Graph<Vertex, DefaultEdge> query,
                                       List<Vertex> order){
        // make sure order is in BFS
        List<Vertex> pastOrder = new ArrayList<>(order);
        List<Vertex> newOrder = new ArrayList<>();
        List<Vertex> lastLayer = new ArrayList<>(); lastLayer.add(order.get(0));

        while(!lastLayer.isEmpty()){
            Set<Vertex> nextLayer = new HashSet<>();
            // sort by time appear in processing order
            lastLayer.sort((Vertex v1, Vertex v2) -> Integer.compare(pastOrder.indexOf(v1),
                    pastOrder.indexOf(v2)));

            for(Vertex v: lastLayer){
                newOrder.add(v);
                // get the neighbors of the nodes
                List<Vertex> nv = Graphs.neighborListOf(query, v);

                // iterate through neighbors in that order
                nextLayer.addAll(nv);
            }
            nextLayer.removeAll(newOrder);
            lastLayer = new ArrayList<>(nextLayer);
        }
        order.removeAll(order);
        order.addAll(newOrder);
    }

    /**
     * Create a DAG of the query graph given a processing order
     * @param query the query graph
     * @param order the processing order
     * @return a DAG of the query graph
     */
    public static DirectedAcyclicGraph<Vertex, DefaultEdge> constructDAGWithOrder(Graph<Vertex, DefaultEdge> query,
                                                                                  List<Vertex> order){
        convertOrderBFS(query, order);

        DirectedAcyclicGraph<Vertex, DefaultEdge> qD = new DirectedAcyclicGraph<>(DefaultEdge.class);
        // store the vertices we have seen
        Set<Vertex> seen = new HashSet<>();

        // iterate through the processing order
        for(Vertex u: order){
            if(!qD.containsVertex(u)){
                qD.addVertex(u);
            }
            seen.add(u);

            // get the neighbors of the nodes
            List<Vertex> nu = Graphs.neighborListOf(query, u);

            // sort by time appear in processing order
            nu.sort((Vertex v1, Vertex v2) -> Integer.compare(order.indexOf(v1), order.indexOf(v2)));

            // iterate through neighbors in that order
            for (Vertex uP : nu) {
                if (!seen.contains(uP)) {
                    if (!qD.containsVertex(uP)) {
                        qD.addVertex(uP);
                    }
                    if (!qD.containsEdge(uP, u)) {
                        qD.addEdge(u, uP);
                    }
                }
            }
        }

        return qD;
    }

    /**
     * Finds the processing order with QuickSI.  First build the QI-sequence then return the corresponding vertices
     * to the vertices within the tree.
     * @param target the target graph
     * @param query the query graph
     * @param candidates the candidates of the query vertices
     * @return the order of the query vertices
     */
    public static ArrayList<Vertex> quickSIComputeProcessingOrder(Graph<Vertex, DefaultEdge> target,
                                                                  Graph<Vertex, DefaultEdge> query,
                                                                  Map<Vertex, Set<Vertex>> candidates){
        Graph<Vertex, DefaultWeightedEdge> weightedQuery = new SimpleWeightedGraph<>(DefaultWeightedEdge.class);
        // keep track of the mappings from query vertex to weighted graph
        Map<Vertex, Vertex> oldToNew = new HashMap<>();

        ArrayList<Vertex> order = new ArrayList<>();
        // iterate through the vertices of query graph
        for(Vertex u: query.vertexSet()){
            // calculate the weight
            int uWeight = vertexWeight(u, candidates);

            // add the weighted vertex to the graph
            Vertex newVertex = copyVertex(u, u.getId());
            weightedQuery.addVertex(newVertex);
            newVertex.setWeight(uWeight);

            // keep track of old and new vertex
            oldToNew.put(u, newVertex);
        }
        // iterate through the edges of query graph
        for(DefaultEdge e: query.edgeSet()){
            int eWeight = edgeWeight(e, target, query, candidates);

            // get the vertex information
            Vertex u = query.getEdgeSource(e); Vertex uNew = oldToNew.get(u);
            Vertex v = query.getEdgeTarget(e); Vertex vNew = oldToNew.get(v);

            // add the weighted edge to graph
            DefaultWeightedEdge eNew = weightedQuery.addEdge(uNew, vNew);
            weightedQuery.setEdgeWeight(eNew, eWeight);
        }

        // create a new QI-Sequence
        SEQq = buildSpanningTree(weightedQuery);

        Map<Integer, Vertex> treeOrder = SEQq.getOrder();
        // add to the order
        for(int i: treeOrder.keySet()){
            order.add(treeOrder.get(i));
        }

        return order;
    }

    /**
     * Finds the neighbors of a given vertex, if using QuickSI only will check the neighbors of the extra edges
     * @param query the query graph
     * @param u the current query vertex
     * @return the neighbors of u within the query graph that will be checked
     */
    public static List<Vertex> getNeighborsU(Graph<Vertex, DefaultEdge> query, Vertex u){
        // iterate through neighbors of u
        List<Vertex> neighborsU = Graphs.neighborListOf(query, u);
        // if quickSI only look at extra edges
        if(algorithmNameB.equals(QUICKSI)){
            int sizeNeighbors = neighborsU.size();
            neighborsU = SEQq.getExtraEdges(u);
            falseMatchingExtraEdge+= (sizeNeighbors-neighborsU.size());
        }
        return neighborsU;
    }

    /**
     * Finds the vertices that within the current function, if using QuickSI check vertices that are not neighbors of u
     * @param currentFunction the current matching between previous query vertices
     * @param u vertex from the query graph
     * @return the vertices within currentFunction to be checked
     */
    public static Set<Vertex> getPreviousVerticesToCheck(Map<Vertex, Vertex> currentFunction, Vertex u){
        Set<Vertex> toCheck = currentFunction.keySet();
        // if quickSI already have information
        if(algorithmNameB.equals(QUICKSI)){
            toCheck = new HashSet<>(SEQq.getNoExtraEdges(u));
        }

        return toCheck;
    }

    /**
     * Checks to see if there exists a valid matching between u and v
     * @param query the query graph
     * @param target the target graph
     * @param currentFunction the current matching between previous query vertices
     * @param u vertex from the query graph
     * @param v vertex from the target graph
     * @param isInduced whether matching is induced
     * @return true if u can be matched to v
     */
    private static boolean isValid(Graph<Vertex, DefaultEdge> query, Graph<Vertex, DefaultEdge> target,
                                  Map<Vertex, Vertex> currentFunction, Vertex u, Vertex v, boolean isInduced){
        // iterate through neighbors of u
        List<Vertex> neighborsU = getNeighborsU(query, u);

        for(Vertex uPrime: neighborsU){
            // if u' is in the domain of current function
            if(currentFunction.containsKey(uPrime)){
                // see if there exists an edge with v and v'
                Vertex vPrime = currentFunction.get(uPrime);

                // if there isn't an edge then not a possible matching
                if(!target.containsEdge(v, vPrime)){
                    return false;
                }
            }
        }

        if(isInduced){
            Set<Vertex> toCheck = getPreviousVerticesToCheck(currentFunction, u);

            for(Vertex uPrime: toCheck){
                // if u and u' are not neighbors
                if(!query.containsEdge(u, uPrime)){
                    // see if there is an edge between v and v'
                    Vertex vPrime = currentFunction.get(uPrime);

                    // if there is an edge then not a possible matching
                    if(target.containsEdge(v, vPrime)){
                        return false;
                    }
                }
            }
        }

        // we didn't find any problems, so valid mapping
        return true;
    }

    /**
     * Finds the next vertex to check dynamically.  Given a local candidate set, it will be the one with a minimum
     * number of candidates
     * @param target the target graph
     * @param query the query graph
     * @param currentFunction the current isomorphism
     * @param order the vertices to be checked
     * @param candidates the current set of candidates
     * @return the next vertex in the order
     */
    public static Vertex dynamicProcessingOrder(Graph<Vertex, DefaultEdge> target, Graph<Vertex, DefaultEdge> query,
                                                Map<Vertex, Vertex> currentFunction, ArrayList<Vertex> order,
                                                Map<Vertex, Set<Vertex>> candidates){
        // keep track of the minimum number of candidates and max degree
        int minimumCandidateSize = candidates.get(order.get(0)).size();
        int maxDegree =query.degreeOf(order.get(0));

        // keep track of the vertices of the minimum size
        Set<Vertex> verticesOfMinSize = new HashSet<>();
        verticesOfMinSize.add(order.get(0));
        // iterate through the query vertices that have not been mapped yet
        for(Vertex u: order){
            //  look the last vertices that is in the function and neighbors of the current vertex
            if(dynamicOrder.size()!=0) {
                Vertex uP = dynamicOrder.get(dynamicOrder.size()-1);

                if(query.containsEdge(uP, u)) {
                    int numBefore = candidates.get(u).size();
                    candidates.get(u).retainAll(Graphs.neighborListOf(target, currentFunction.get(uP)));
                    // account backtracking calls
                    numBackTracking += numBefore - candidates.get(u).size();

                    // there are no possible vertices to check
                    if (candidates.get(u).size() == 0) {
                        return u;
                    }
                }
            }

            // find the minimum local candidate size
            if(candidates.get(u).size()<minimumCandidateSize){
                minimumCandidateSize=candidates.get(u).size();

                verticesOfMinSize = new HashSet<>();
                verticesOfMinSize.add(u);

                // find the next max degree
                maxDegree = query.degreeOf(u);
            }

            else if(candidates.get(u).size()==minimumCandidateSize){
                verticesOfMinSize.add(u);

                // update the maximum degree with the vertices of a given candidate size
                if(query.degreeOf(u)>maxDegree){
                    maxDegree = query.degreeOf(u);
                }
            }
        }

        // only take into account vertices of minimum size and maximum degree within those vertices
        Set<Vertex> verticesMinSizeMaxDegree = new HashSet<>();
        for(Vertex vMin: verticesOfMinSize){
            if(query.degreeOf(vMin)==maxDegree){
                verticesMinSizeMaxDegree.add(vMin);
            }
        }

        // return a random vertex with the minimum number of candidates
        return randomVertex(verticesMinSizeMaxDegree);
    }

    /**
     * Gets the next vertex within the processing order
     * @param query the query graph
     * @param target the target graph
     * @param order the processing order of the vertices
     * @param i the current vertex within the order
     * @param currentFunction the current matching between the query and target for the previous i vertices
     * @param candidates sets of candidates for each query vertex
     * @return the query next vertex to be checked
     */
    public static Vertex getNextVertex(Graph<Vertex, DefaultEdge> query, Graph<Vertex, DefaultEdge> target,
                                       ArrayList<Vertex> order, int i, Map<Vertex, Vertex> currentFunction,
                                       Map<Vertex, Set<Vertex>>candidates){
        if(algorithmNamePO.equals(DYNAMIC_ORDER)) {
            // otherwise get the next candidate in the order
            Vertex uNext = dynamicProcessingOrder(target, query, currentFunction, order, candidates);
            dynamicOrder.add(uNext);
            order.remove(uNext);
            return uNext;
        }
        return order.get(i);
    }

    /**
     * Get the possible target vertices for a given query vertex and isomorphism
     * @param target the target graph
     * @param candidates sets of candidates for each query vertex
     * @param currentFunction the current matching between the query and target for the previous i vertices
     * @param i the current vertex within the order
     * @param u the current vertex
     * @return the possible target vertex to map to for a given query vertex
     */
    public static Set<Vertex> getPossibleVertices(Graph<Vertex, DefaultEdge> target, Map<Vertex, Set<Vertex>> candidates,
                                                  Map<Vertex, Vertex> currentFunction, int i,Vertex u){
        Set<Vertex> possibleVertices = new HashSet<>(candidates.get(u));
        int initialSize = possibleVertices.size();

        // if quickSI recompute candidates
        if(algorithmNameB.equals(QUICKSI) && i!=0){
            // remove candidates that are not neighbors to the parent's candidate
            Vertex p = SEQq.getParent(u);
            Vertex pC = currentFunction.get(p);

            Set<Vertex> newPossibleVertices = new HashSet<>();

            // iterate through the vertex candidates
            for(Vertex uC: candidates.get(u)){
                // only include if edge exists between two candidates
                if(target.containsEdge(pC, uC)){
                    newPossibleVertices.add(uC);
                }
                else{
                    // compared pair, so increase number of backtracking
                    numBackTracking++;
                    falseMatchingParents++;
                }
            }
            possibleVertices = newPossibleVertices;
        }
        else if(i!=0 && (algorithmNameB.equals(DAF)||algorithmNameB.equals(VEQS))){
            // iterate through the parents
            for(DefaultEdge e: queryDAG.incomingEdgesOf(u)){
                Vertex uP = queryDAG.getEdgeSource(e);
                Set<Vertex> CM = new HashSet<>();
                // if it is contained within the function
                if(currentFunction.containsKey(uP)) {
                    // find all of the possible vertices we can map to
                    Vertex vP = currentFunction.get(uP);
                    for (LabeledEdge e1 : cs.getEdgeSet()) {
                        if (vP == queryDAG.getEdgeSource(e1)
                                && e1.getLabel().equals(uP + "-" + u)) {
                            CM.add(queryDAG.getEdgeTarget(e1));
                        }
                    }
                    possibleVertices.retainAll(CM);
                }
            }
            // the number we were able to prune
            numBackTracking+=(initialSize-possibleVertices.size());
        }

        return possibleVertices;
    }

    /**
     * Performs subgraph isomorphism on the given graphs
     * @param query the query graph
     * @param target the target graph
     * @param candidates sets of candidates for each query vertex
     * @param order list of order which each vertex should be mapped
     * @param i the current vertex within the order
     * @param currentFunction the current matching between the query and target for the previous i vertices
     * @param allFunctionsFound all the solutions that were discovered
     * @param isInduced whether matching is induced
     */
    private static void subgraphIsomorphism(Graph<Vertex, DefaultEdge> query, Graph<Vertex, DefaultEdge> target,
                                            Map<Vertex, Set<Vertex>> candidates, ArrayList<Vertex> order, int i,
                                            Map<Vertex, Vertex> currentFunction,
                                            List<Map<Vertex, Vertex>> allFunctionsFound, boolean isInduced){
        // check if found solution
        if(currentFunction.size() == query.vertexSet().size()){
            allFunctionsFound.add(new HashMap<>(currentFunction));
        }
        else{
            // look at next node
            Vertex u = getNextVertex(query, target, order, i, currentFunction, candidates);
            Set<Vertex> possibleVertices = getPossibleVertices(target, candidates, currentFunction, i, u);

            // look at candidates
            for(Vertex v : possibleVertices){
                // looking at new element
                numBackTracking+=1;
                // check not in another mapping
                if(!currentFunction.containsValue(v) && isValid(query, target, currentFunction, u, v, isInduced)){
                    currentFunction.put(u, v);
                    // if dynamic program must make a copy of the vertex
                    if(algorithmNamePO.equals(DYNAMIC_ORDER)){
                        // reset the local candidates and order
                        Map<Vertex, Set<Vertex>> candidatesCopy = new HashMap<>();
                        for (Vertex uCopy : order) {
                            candidatesCopy.put(uCopy, new HashSet<>(candidates.get(uCopy)));
                        }

                        subgraphIsomorphism(query, target, candidatesCopy, order, i + 1, currentFunction,
                                allFunctionsFound, isInduced);
                    }
                    else {
                        subgraphIsomorphism(query, target, candidates, order, i + 1, currentFunction, allFunctionsFound,
                                isInduced);
                    }
                    currentFunction.remove(u);
                }
            }

            // must add the vertex back if dynamic processing order
            if(algorithmNamePO.equals(DYNAMIC_ORDER)){
                order.add(u);
                dynamicOrder.remove(u);
            }
        }
    }

    /**
     * Performs subgraph isomorphism on the given graphs
     * @param query the query graph
     * @param target the target graph
     * @param candidates sets of candidates for each query vertex
     * @param order list of order which each vertex should be mapped
     * @param i the current vertex within the order
     * @param currentFunction the current matching between the query and target for the previous i vertices
     * @param isInduced whether matching is induced
     */
    private static double subgraphIsomorphismNumeric(Graph<Vertex, DefaultEdge> query, Graph<Vertex, DefaultEdge> target,
                                            Map<Vertex, Set<Vertex>> candidates, ArrayList<Vertex> order, int i,
                                            Map<Vertex, Vertex> currentFunction, boolean isInduced){
        double totalNumberMatchings = 0;

        // check if found solution
        if(currentFunction.size() == query.vertexSet().size()){
            return 1;
        }
        else{
            // look at next node
            Vertex u = getNextVertex(query, target, order, i, currentFunction, candidates);
            Set<Vertex> possibleVertices = getPossibleVertices(target, candidates, currentFunction, i, u);

            // look at candidates
            for(Vertex v : possibleVertices){
                // looking at new element
                numBackTracking+=1;
                // check not in another mapping
                if(!currentFunction.containsValue(v) && isValid(query, target, currentFunction, u, v, isInduced)){
                    currentFunction.put(u, v);
                    // if dynamic program must make a copy of the vertex
                    if(algorithmNamePO.equals(DYNAMIC_ORDER)){
                        // reset the local candidates and order
                        Map<Vertex, Set<Vertex>> candidatesCopy = new HashMap<>();
                        for (Vertex uCopy : order) {
                            candidatesCopy.put(uCopy, new HashSet<>(candidates.get(uCopy)));
                        }

                        totalNumberMatchings+=subgraphIsomorphismNumeric(query, target, candidatesCopy, order, i + 1,
                                currentFunction, isInduced);
                    }
                    else {
                        totalNumberMatchings+=subgraphIsomorphismNumeric(query, target, candidates, order, i + 1,
                                currentFunction, isInduced);
                    }
                    currentFunction.remove(u);
                }
            }

            // must add the vertex back if dynamic processing order
            if(algorithmNamePO.equals(DYNAMIC_ORDER)){
                order.add(u);
                dynamicOrder.remove(u);
            }
        }

        return totalNumberMatchings;
    }

    /**
     * Calculates the symmetry within CS structure to use for VEQs
     * @param u the query vertex
     * @param v the target vertex
     * @param candidates the candidate set
     * @return a list of target vertices symmetric to v given u in the CS structure
     */
    public static List<Vertex> calcPi(Vertex u, Vertex v, Map<Vertex, Set<Vertex>> candidates){
        List<Vertex> pi = new ArrayList<>();
        for(Vertex vP: candidates.get(u)) {
            // don't want to include self because always equivalent
            if(vP.equals(v)){
                continue;
            }
            // find which are symmetric
            if(cs.neighborsOf(v).containsAll(cs.neighborsOf(vP))){
                pi.add(vP);
            }
        }
        return pi;
    }

    /**
     * Create a matching using symmetry
     * @param u the query vertex
     * @param v the target vertex
     * @param uP the parent vertex of u
     * @param currentFunction the current matchings
     * @param allFunctionsFound all possible matchings
     */
    public static void symmetricMatching(Vertex u, Vertex v, Vertex uP, Map<Vertex, Vertex> currentFunction,
                                         List<Map<Vertex, Vertex>> allFunctionsFound){
        // if there is no conflict
        if(uP != null){
            Map<Vertex, Vertex> newFunction = new HashMap<>(currentFunction);
            Vertex vP = newFunction.get(u);
            newFunction.put(u, v);
            newFunction.put(uP, vP);
            allFunctionsFound.add(newFunction);
        }
        // if there is a conflict
        else{
            Map<Vertex, Vertex> newFunction = new HashMap<>(currentFunction);
            newFunction.put(u, v);
            allFunctionsFound.add(newFunction);
        }
    }

    /**
     * Does backtracking with the addition of failing sets
     * @param query the query graph
     * @param target the target graph
     * @param candidates the candidate set
     * @param order the processing order
     * @param i  the current vertex within the order
     * @param currentFunction the current matching between the query and target for the previous i vertices
     * @param allFunctionsFound all the solutions that were discovered
     * @param isInduced whether the isomorphism is induced
     */
    private static void subgraphIsomorphismVEQs(Graph<Vertex, DefaultEdge> query,
                                                           Graph<Vertex, DefaultEdge> target,
                                                           Map<Vertex, Set<Vertex>> candidates, ArrayList<Vertex> order,
                                                           int i, Map<Vertex, Vertex> currentFunction,
                                                           List<Map<Vertex, Vertex>> allFunctionsFound,
                                                           boolean isInduced,
                                                           Map<Map<Vertex, Vertex>, List<Vertex>> piMinus,
                                                           Map<Map<Vertex, Vertex>, List<Vertex>> deltaM,
                                                           Map<Map<Vertex, Vertex>, List<Vertex>> equivalent,
                                                           Map<Map<Vertex, Vertex>, List<Map<Vertex, Vertex>>> TM){
        // check if found solution
        if(currentFunction.size() == query.vertexSet().size()){
            allFunctionsFound.add(new HashMap<>(currentFunction));

            // iterate through the vertices in order
            for(int k = 0; k<order.size(); k++){
                // if we have not seen root before then add a new one
                if(!TM.containsKey(Map.of(order.get(k), currentFunction.get(order.get(k))))){
                    TM.put(Map.of(order.get(k), currentFunction.get(order.get(k))), new ArrayList<>());
                }
                // add the following mapping
                for(int j = k; j<order.size(); j++){
                    TM.get(Map.of(order.get(k), currentFunction.get(order.get(k)))).add(new HashMap<>(currentFunction));
                }
            }
        }
        else{
            // look at next node
            Vertex u = getNextVertex(query, target, order, i, currentFunction, candidates);
            // compute C_M
            Set<Vertex> possibleVertices = getPossibleVertices(target, candidates, currentFunction, i, u);
            // set v - inequivalent for each v in C_M(u)
            for(Vertex v: possibleVertices){
                equivalent.put(Map.of(u, v), new ArrayList<>());
            }

            // iterate through C_M
            for(Vertex v: possibleVertices){
                numBackTracking++;
                // calculate the symmetry at beginning
                List<Vertex> pi = calcPi(u, v, candidates);
                List<Vertex> piM = new ArrayList<>();
                // check if v is equivalent
                if(!equivalent.get(Map.of(u,v)).isEmpty()){
                    // iterate through the equivalent vertices
                    for(Vertex vEq : equivalent.get(Map.of(u,v))){
                        // iterate through all of their possible matchings
                        for(Map<Vertex, Vertex> MStar : TM.get(Map.of(u,vEq))){
                            // find if there is a conflict previously, need to add differently
                            Vertex uP = null;
                            for(Vertex uVals : MStar.keySet()){
                                if(MStar.get(uVals) == v){
                                    uP = uVals;
                                    break;
                                }
                            }

                            numSymmetric++;
                            symmetricMatching(u, v, uP, currentFunction, allFunctionsFound);
                        }
                    }
                    continue;
                }


                // check not in another mapping
                if(!currentFunction.containsValue(v) && (!isInduced || isValid(query, target, currentFunction, u, v, isInduced))) {
                    currentFunction.put(u, v);

                    // calculate pi
                    piMinus.put(Map.of(u, v), pi);
                    deltaM.put(Map.of(u,v), new ArrayList<>());

                    // check the ancestors
                    for(Vertex ua: currentFunction.keySet()){
                        Vertex va = currentFunction.get(ua);
                        List<Vertex> pia = pi;
                        pia.retainAll(pi);

                        if(!pi.contains(va) && !pia.isEmpty()){
                            deltaM.get(Map.of(ua, va)).addAll(pi);
                        }
                    }
                    subgraphIsomorphismVEQs(query, target, candidates, order, i+1, currentFunction, allFunctionsFound,
                            isInduced, piMinus, deltaM, equivalent, TM);
                    currentFunction.remove(u);

                    piM = piMinus.get(Map.of(u,v));
                    if(!TM.containsKey(Map.of(u, v))){
                        TM.put(Map.of(u,v), new ArrayList<>());
                    }
                    if(!TM.get(Map.of(u, v)).isEmpty()){
                        piM.removeAll(deltaM.get(Map.of(u, v)));
                    }

                    // add the equivalent vertices
                    for(Vertex vP: piM){
                        if(!equivalent.containsKey(Map.of(u, vP))){
                            equivalent.put(Map.of(u, vP), new ArrayList<>());
                        }
                        equivalent.get(Map.of(u, vP)).add(v);
                    }

                }
                // there is a conflict
                else{
                    for(Vertex uP: currentFunction.keySet()){
                        // update piM
                        if(currentFunction.get(uP).equals(v)){
                            piMinus.get(Map.of(uP, v)).retainAll(pi);
                            break;
                        }
                    }
                }
            }
        }
    }

    /**
     * Does backtracking with the addition of failing sets
     * @param query the query graph
     * @param target the target graph
     * @param candidates the candidate set
     * @param order the processing order
     * @param i  the current vertex within the order
     * @param currentFunction the current matching between the query and target for the previous i vertices
     * @param isInduced whether the isomorphism is induced
     */
    private static double subgraphIsomorphismVEQsNumeric(Graph<Vertex, DefaultEdge> query,
                                                Graph<Vertex, DefaultEdge> target,
                                                Map<Vertex, Set<Vertex>> candidates, ArrayList<Vertex> order,
                                                int i, Map<Vertex, Vertex> currentFunction, boolean isInduced,
                                                Map<Map<Vertex, Vertex>, List<Vertex>> piMinus,
                                                Map<Map<Vertex, Vertex>, List<Vertex>> deltaM,
                                                Map<Map<Vertex, Vertex>, List<Vertex>> equivalent,
                                                Map<Map<Vertex, Vertex>, List<Map<Vertex, Vertex>>> TM){
        double totalNumberMatchings = 0;
        // check if found solution
        if(currentFunction.size() == query.vertexSet().size()){
            // iterate through the vertices in order
            for(int k = 0; k<order.size(); k++){
                // if we have not seen root before then add a new one
                if(!TM.containsKey(Map.of(order.get(k), currentFunction.get(order.get(k))))){
                    TM.put(Map.of(order.get(k), currentFunction.get(order.get(k))), new ArrayList<>());
                }
                // add the following mapping
                for(int j = k; j<order.size(); j++){
                    TM.get(Map.of(order.get(k), currentFunction.get(order.get(k)))).add(new HashMap<>(currentFunction));
                }
            }
            return 1;
        }
        else{
            // look at next node
            Vertex u = getNextVertex(query, target, order, i, currentFunction, candidates);
            // compute C_M
            Set<Vertex> possibleVertices = getPossibleVertices(target, candidates, currentFunction, i, u);
            // set v - equivalent for each v in C_M(u)
            for(Vertex v: possibleVertices){
                equivalent.put(Map.of(u, v), new ArrayList<>());
            }

            // iterate through C_M
            for(Vertex v: possibleVertices){
                numBackTracking++;
                // calculate the symmetry at beginning
                List<Vertex> pi = calcPi(u, v, candidates);
                List<Vertex> piM = new ArrayList<>();
                // check if v is equivalent
                if(!equivalent.get(Map.of(u,v)).isEmpty()){
                    // iterate through the equivalent vertices
                    for(Vertex vEq : equivalent.get(Map.of(u,v))){
                        // iterate through all of their possible matchings
                        for(Map<Vertex, Vertex> MStar : TM.get(Map.of(u,vEq))){
                            // find if there is a conflict previously, need to add differently
                            Vertex uP = null;
                            for(Vertex uVals : MStar.keySet()){
                                if(MStar.get(uVals) == v){
                                    uP = uVals;
                                    break;
                                }
                            }

                            numSymmetric++;
                            totalNumberMatchings++;
                        }
                    }
                    continue;
                }


                // check not in another mapping
                if(!currentFunction.containsValue(v) && (!isInduced || isValid(query, target, currentFunction, u, v, isInduced))) {
                    currentFunction.put(u, v);

                    // calculate pi
                    piMinus.put(Map.of(u, v), pi);
                    deltaM.put(Map.of(u,v), new ArrayList<>());

                    // check the ancestors
                    for(Vertex ua: currentFunction.keySet()){
                        Vertex va = currentFunction.get(ua);
                        List<Vertex> pia = pi;
                        pia.retainAll(pi);

                        if(!pi.contains(va) && !pia.isEmpty()){
                            deltaM.get(Map.of(ua, va)).addAll(pi);
                        }
                    }
                    totalNumberMatchings+=subgraphIsomorphismVEQsNumeric(query, target, candidates, order, i+1,
                            currentFunction, isInduced, piMinus, deltaM, equivalent, TM);
                    currentFunction.remove(u);

                    piM = piMinus.get(Map.of(u,v));
                    if(!TM.containsKey(Map.of(u, v))){
                        TM.put(Map.of(u,v), new ArrayList<>());
                    }
                    if(!TM.get(Map.of(u, v)).isEmpty()){
                        piM.removeAll(deltaM.get(Map.of(u, v)));
                    }

                    // add the equivalent vertices
                    for(Vertex vP: piM){
                        if(!equivalent.containsKey(Map.of(u, vP))){
                            equivalent.put(Map.of(u, vP), new ArrayList<>());
                        }
                        equivalent.get(Map.of(u, vP)).add(v);
                    }

                }
                // there is a conflict
                else{
                    for(Vertex uP: currentFunction.keySet()){
                        // update piM
                        if(currentFunction.get(uP).equals(v)){
                            piMinus.get(Map.of(uP, v)).retainAll(pi);
                            break;
                        }
                    }
                }
            }
        }
        return totalNumberMatchings;
    }

    /**
     * Does backtracking with the addition of failing sets
     * @param query the query graph
     * @param target the target graph
     * @param candidates the candidate set
     * @param order the processing order
     * @param i  the current vertex within the order
     * @param currentFunction the current matching between the query and target for the previous i vertices
     * @param allFunctionsFound all the solutions that were discovered
     * @param allFailingSets the failing sets
     * @param isInduced whether the isomorphism is induced
     */
    private static void subgraphIsomorphismWithFailingSets(Graph<Vertex, DefaultEdge> query,
                                                           Graph<Vertex, DefaultEdge> target,
                                                           Map<Vertex, Set<Vertex>> candidates, ArrayList<Vertex> order,
                                                           int i, Map<Vertex, Vertex> currentFunction,
                                                           List<Map<Vertex, Vertex>> allFunctionsFound,
                                                           Map<Integer, List<Set<Vertex>>> allFailingSets,
                                                           boolean isInduced){
        // check if found solution
        if(currentFunction.size() == query.vertexSet().size()){
            allFunctionsFound.add(new HashMap<>(currentFunction));
            allFailingSets.get(i).add(getFullSolution());
        }
        else{
            // look at next node
            Vertex u = getNextVertex(query, target, order, i, currentFunction, candidates);
            Set<Vertex> possibleVertices = getPossibleVertices(target, candidates, currentFunction, i, u);

            if(possibleVertices.size() == 0){
                allFailingSets.get(i).add(getEmptyCandidates(u));
            }

            // look at candidates
            for(Vertex v : possibleVertices){
                // looking at new element
                numBackTracking+=1;
                if(currentFunction.containsValue(v)){
                    allFailingSets.get(i).add(getConflict(u, v, currentFunction));
                    continue;
                }

                // check not in another mapping
                if(!isInduced || isValid(query, target, currentFunction, u, v, isInduced)){
                    currentFunction.put(u, v);
                    subgraphIsomorphismWithFailingSets(query, target, candidates, order, i+1, currentFunction,
                             allFunctionsFound, allFailingSets, isInduced);
                    currentFunction.remove(u);

                    // failing sets
                    List<Set<Vertex>> T = allFailingSets.get(i+1);
                    // Get next vertex.
                    Vertex un = i+1<order.size()?order.get(i+1):null;

                    Set<Vertex> current = new HashSet<>();
                    Set<Vertex> failingSetWithoutUn = null;
                    // check the three conditions
                    for(Set<Vertex> t : T){
                        // if find an empty set, them must continue
                        if(t.size()==0){
                            current = getPartialSolution();
                            break;
                        }
                        // keep track of conflicting vertex
                        else if(!t.contains(un)){
                            failingSetWithoutUn = t;
                        }
                        // otherwise just keep track of everything
                        else {
                            current.addAll(t);
                        }
                    }
                    if(current.size()!=0 && failingSetWithoutUn != null){
                        current = failingSetWithoutUn;
                    }
                    allFailingSets.get(i).add(current);

                    // clear subtree
                    T.clear();
                    if(current.size()!=0 && !current.contains(u)){
                        partialSolutions++;
                        break;
                    }
                }
                else{
                    allFailingSets.get(i).add(new HashSet<>());
                }
            }
        }
    }

    /**
     * Does backtracking with the addition of failing sets
     * @param query the query graph
     * @param target the target graph
     * @param candidates the candidate set
     * @param order the processing order
     * @param i  the current vertex within the order
     * @param currentFunction the current matching between the query and target for the previous i vertices
     * @param allFailingSets the failing sets
     * @param isInduced whether the isomorphism is induced
     */
    private static double subgraphIsomorphismWithFailingSetsNumeric(Graph<Vertex, DefaultEdge> query,
                                                           Graph<Vertex, DefaultEdge> target,
                                                           Map<Vertex, Set<Vertex>> candidates, ArrayList<Vertex> order,
                                                           int i, Map<Vertex, Vertex> currentFunction,
                                                           Map<Integer, List<Set<Vertex>>> allFailingSets,
                                                           boolean isInduced){
        double totalNumberMatchings = 0;
        // check if found solution
        if(currentFunction.size() == query.vertexSet().size()){
            allFailingSets.get(i).add(getFullSolution());
            return 1;
        }
        else{
            // look at next node
            Vertex u = getNextVertex(query, target, order, i, currentFunction, candidates);
            Set<Vertex> possibleVertices = getPossibleVertices(target, candidates, currentFunction, i, u);

            if(possibleVertices.size() == 0){
                allFailingSets.get(i).add(getEmptyCandidates(u));
            }

            // look at candidates
            for(Vertex v : possibleVertices){
                // looking at new element
                numBackTracking+=1;
                if(currentFunction.containsValue(v)){
                    allFailingSets.get(i).add(getConflict(u, v, currentFunction));
                    continue;
                }

                // check not in another mapping
                if(!isInduced || isValid(query, target, currentFunction, u, v, isInduced)){
                    currentFunction.put(u, v);
                    totalNumberMatchings+=subgraphIsomorphismWithFailingSetsNumeric(query, target, candidates, order,
                            i+1, currentFunction, allFailingSets, isInduced);
                    currentFunction.remove(u);

                    // failing sets
                    List<Set<Vertex>> T = allFailingSets.get(i+1);
                    // Get next vertex.
                    Vertex un = i+1<order.size()?order.get(i+1):null;

                    Set<Vertex> current = new HashSet<>();
                    Set<Vertex> failingSetWithoutUn = null;
                    // check the three conditions
                    for(Set<Vertex> t : T){
                        // if find an empty set, them must continue
                        if(t.size()==0){
                            current = getPartialSolution();
                            break;
                        }
                        // keep track of conflicting vertex
                        else if(!t.contains(un)){
                            failingSetWithoutUn = t;
                        }
                        // otherwise just keep track of everything
                        else {
                            current.addAll(t);
                        }
                    }
                    if(current.size()!=0 && failingSetWithoutUn != null){
                        current = failingSetWithoutUn;
                    }
                    allFailingSets.get(i).add(current);

                    // clear subtree
                    T.clear();
                    if(current.size()!=0 && !current.contains(u)){
                        partialSolutions++;
                        break;
                    }
                }
                else{
                    allFailingSets.get(i).add(new HashSet<>());
                }
            }
        }
        return totalNumberMatchings;
    }

    /**
     * A full solution was found
     * @return an empty set
     */
    private static Set<Vertex> getFullSolution(){
        fullSolutions++;
        return new HashSet<>();
    }

    /**
     * A partial solution was found
     * @return a empty set
     */
    private static Set<Vertex> getPartialSolution(){
        partialSolutions++;
        return new HashSet<>();
    }

    /**
     * If there is no candidates for the given vertex
     * @param u the given vertex
     * @return the set of ancestors
     */
    private static Set<Vertex> getEmptyCandidates(Vertex u){
        emptyCandidates++;
        return queryDAG.getAncestors(u);
    }

    /**
     * There is already a vertex that maps to v
     * @param u the query vertex
     * @param v the target vertex
     * @param currentFunction the current function
     * @return the ancestors of the conflicting vertices
     */
    private static Set<Vertex> getConflict(Vertex u, Vertex v, Map<Vertex, Vertex> currentFunction){
        conflicts++;

        // add the current ancestors to the vertex
        Set<Vertex> culprits = new HashSet<>(queryDAG.getAncestors(u));
        // find the conflicting vertex
        for(Vertex uP: currentFunction.keySet()){
            Vertex vP = currentFunction.get(uP);
            if(!u.equals(uP) && v.equals(vP)){
                culprits.addAll(queryDAG.getAncestors(uP));
                break;
            }
        }
        // add all the ancestors involved to failing sets
        return culprits;
    }

    /**
     * Compute the candidates for given query graph and target graph
     * @param query the query graph
     * @param target the target graph
     * @return the candidates
     */
    public static Map<Vertex, Set<Vertex>> computeCandidates(Graph<Vertex, DefaultEdge> query,
                                                             Graph<Vertex, DefaultEdge> target){
        Map<Vertex, Set<Vertex>> candidates;
        // compute the candidates
        switch (algorithmNameC) {
            // using ground truth
            case GROUNDTRUTH -> candidates = groundTruthComputeCandidates(query, target);
            case DAF -> candidates = groundTruthComputeCandidates(query, target);
            // using GraphQL
            case GRAPHQL -> candidates = graphQLComputeCandidates(query, target);
            // did not find a valid algorithm
            default -> {
                System.out.println("Candidates Algorithm:");
                System.out.println(noAlgorithmFound);
                return null;
            }
        }
        return candidates;
    }

    /**
     * Computes the processing order given a query graph and target graph
     * @param query the query graph
     * @param target the target graph
     * @param candidates the candidates of the query vertices
     * @param gamma the gamma value for GraphQL
     * @return the processing order
     */
    public static ArrayList<Vertex> computeProcessingOrder(Graph<Vertex, DefaultEdge> query,
                                                           Graph<Vertex, DefaultEdge> target,
                                                           Map<Vertex, Set<Vertex>> candidates, double gamma){
        ArrayList<Vertex> order = new ArrayList<>();
        switch (algorithmNamePO) {
            case GROUNDTRUTH -> order = groundTruthComputeProcessingOrder(query, candidates);
            case GRAPHQL -> order = graphQLComputeProcessingOrder(query, candidates, gamma);
            case QUICKSI -> order = quickSIComputeProcessingOrder(target, query, candidates);
            case DYNAMIC_ORDER -> order = new ArrayList<>(candidates.keySet());
            case DAF -> queryDAG = constructDAG(query, candidates, order);
            default -> {
                System.out.println("Processing Order Algorithm:");
                System.out.println(noAlgorithmFound);
                return null;
            }
        }
        return order;
    }

    /**
     * Computes the subgraph isomorphism and the necessary candidates and order using ground truth algorithm
     * @param query the query graph
     * @param target the target graph
     * @param isInduced whether matching is induced
     * @param gamma the gamma value for graphQL
     * @return the solutions to the subgraph isomorphism between the given graphs
     */
    public static List<Map<Vertex, Vertex>> matching(Graph<Vertex, DefaultEdge> query,
                                                     Graph<Vertex, DefaultEdge> target, boolean isInduced,
                                                     double gamma){
        List<Map<Vertex, Vertex>> results = new ArrayList<>();
        // compute the candidates
        Map<Vertex, Set<Vertex>> candidates = computeCandidates(query, target);
        if (candidates == null) {
            return null;
        }

        // compute the order
        ArrayList<Vertex> order = computeProcessingOrder(query, target, candidates, gamma);
        if(order == null){
            return null;
        }

        // keep track of number of backtracking
        numBackTracking = 0;
        if(algorithmNameB.equals(GROUNDTRUTH) || algorithmNameB.equals(GRAPHQL) ||
                (algorithmNameB.equals(QUICKSI)&&!algorithmNamePO.equals(DYNAMIC_ORDER))) {
            if(algorithmNameB.equals(QUICKSI)){
                falseMatchingParents = 0;
                falseMatchingExtraEdge = 0;
            }
            if(algorithmNameB.equals(QUICKSI) && SEQq == null){
                SEQq = buildSpanningTreeWithOrder(query, order);
            }
            subgraphIsomorphism(query, target, candidates, order, 0, new HashMap<>(), results, isInduced);
        }
        else if(algorithmNameB.equals(DAF) && !algorithmNamePO.equals(DYNAMIC_ORDER)){
            if(!algorithmNamePO.equals(DAF)){
                queryDAG = constructDAGWithOrder(query, order);
            }
            fullSolutions = 0;
            partialSolutions = 0;
            emptyCandidates = 0;
            conflicts = 0;

            cs = new CS(query, target, candidates, queryDAG);

            // For each query node in the order, we will create a list of failing sets to record i
            // information of the backtracking process.
            Map<Integer, List<Set<Vertex>>> allFailingSets = new HashMap<>();
            for (int i = 0; i <= order.size(); i++)
                allFailingSets.put(i, new ArrayList<>());


            subgraphIsomorphismWithFailingSets(query, target, candidates, order, 0, new HashMap<>(), results,
                    allFailingSets, isInduced);
        }
        else if(algorithmNameB.equals(VEQS) && !algorithmNamePO.equals(DYNAMIC_ORDER)){
            if(!algorithmNamePO.equals(DAF)){
                queryDAG = constructDAGWithOrder(query, order);
            }

            cs = new CS(query, target, candidates, queryDAG);

            numSymmetric = 0;
            subgraphIsomorphismVEQs(query, target, candidates, order, 0, new HashMap<>(), results, isInduced,
                    new HashMap<>(),new HashMap<>(),new HashMap<>(),new HashMap<>());
        }
        else{
            System.out.println("Backtracking Algorithm:");
            System.out.println(noAlgorithmFound);
            return null;
        }
        // reset the QI-Sequence
        SEQq = null;
        return results;
    }

    /**
     * Computes the subgraph isomorphism and the necessary candidates and order using ground truth algorithm
     * @param query the query graph
     * @param target the target graph
     * @param isInduced whether matching is induced
     * @param gamma the gamma value for graphQL
     * @return the solutions to the subgraph isomorphism between the given graphs
     */
    private static double matchingNumeric(Graph<Vertex, DefaultEdge> query,
                                                      Graph<Vertex, DefaultEdge> target, boolean isInduced,
                                                      double gamma){
        // compute the candidates
        Map<Vertex, Set<Vertex>> candidates = computeCandidates(query, target);
        if (candidates == null) {
            return -1;
        }

        // compute the order
        ArrayList<Vertex> order = computeProcessingOrder(query, target, candidates, gamma);
        if(order == null){
            return -1;
        }

        // keep track of number of backtracking
        numBackTracking = 0;
        double totalNumberMatchings = 0;
        if(algorithmNameB.equals(GROUNDTRUTH) || algorithmNameB.equals(GRAPHQL) ||
                (algorithmNameB.equals(QUICKSI)&&!algorithmNamePO.equals(DYNAMIC_ORDER))) {
            if(algorithmNameB.equals(QUICKSI)){
                falseMatchingParents = 0;
                falseMatchingExtraEdge = 0;
            }
            if(algorithmNameB.equals(QUICKSI) && SEQq == null){
                SEQq = buildSpanningTreeWithOrder(query, order);
            }
            totalNumberMatchings = subgraphIsomorphismNumeric(query, target, candidates, order, 0, new HashMap<>(),
                    isInduced);
        }
        else if(algorithmNameB.equals(DAF) && !algorithmNamePO.equals(DYNAMIC_ORDER)){
            if(!algorithmNamePO.equals(DAF)){
                queryDAG = constructDAGWithOrder(query, order);
            }
            fullSolutions = 0;
            partialSolutions = 0;
            emptyCandidates = 0;
            conflicts = 0;

            cs = new CS(query, target, candidates, queryDAG);

            // For each query node in the order, we will create a list of failing sets to record i
            // information of the backtracking process.
            Map<Integer, List<Set<Vertex>>> allFailingSets = new HashMap<>();
            for (int i = 0; i <= order.size(); i++)
                allFailingSets.put(i, new ArrayList<>());


            totalNumberMatchings = subgraphIsomorphismWithFailingSetsNumeric(query, target, candidates, order, 0, new HashMap<>(),
                    allFailingSets, isInduced);
        }
        else if(algorithmNameB.equals(VEQS) && !algorithmNamePO.equals(DYNAMIC_ORDER)){
            if(!algorithmNamePO.equals(DAF)){
                queryDAG = constructDAGWithOrder(query, order);
            }

            cs = new CS(query, target, candidates, queryDAG);

            numSymmetric = 0;
            totalNumberMatchings = subgraphIsomorphismVEQsNumeric(query, target, candidates, order, 0, new HashMap<>(), isInduced,
                    new HashMap<>(),new HashMap<>(),new HashMap<>(),new HashMap<>());
        }
        else{
            System.out.println("Backtracking Algorithm:");
            System.out.println(noAlgorithmFound);
            return -1;
        }
        // reset the QI-Sequence
        SEQq = null;
        return totalNumberMatchings;
    }

    /**
     * Orders the isomorphism found by sorting the string values ("u->v;...) so always displays same way
     * @param subgraphIsomorphism the subgraph isomorphism mapping
     * @return a string representation of the subgraph isomorphisms in order
     */
    private static List<String> isomorphismOrdered(List<Map<Vertex, Vertex>>  subgraphIsomorphism){
        // convert the isomorphisms to strings
        List<String> isomorphisms = new ArrayList<>();
        for(Map<Vertex, Vertex> next: subgraphIsomorphism){
            // keep track of the current isomorphism 'u->v;'
            StringBuilder currentIsomorphism = new StringBuilder();
            for(Vertex u: next.keySet()){
                currentIsomorphism.append(u.toString()).append("->").append(next.get(u).toString()).append(";");
            }
            isomorphisms.add(currentIsomorphism.toString());
        }

        // sort the isomorphism so doesn't matter which order found
        Collections.sort(isomorphisms);

        return isomorphisms;
    }

    /**
     * A uniform way to print the results of the isomorphisms.
     * @param subgraphIsomorphism the solutions to the isomorphism
     * @param queryGraphName the name of the query graph
     * @param targetGraphName the name of the target graph
     * @param isInduced whether isomorphisms are induced
     */
    public static void displayIsomorphism(List<Map<Vertex, Vertex>> subgraphIsomorphism,
                                          String queryGraphName, String targetGraphName, BufferedWriter writer,
                                          boolean isInduced) throws IOException {

        // print out particular graphs and type and number of isomorphisms
        System.out.print("Query Graph: "+queryGraphName);
        System.out.println(", Target Graph: "+targetGraphName);
        writer.append("Query Graph: ").append(queryGraphName).append(", Target Graph: ")
                .append(targetGraphName).append("\n");

        // print out the number of backjumps
        System.out.println("Number Backtracking: "+numBackTracking);
        writer.append("Number Backtracking: ").append(String.valueOf(numBackTracking)).append("\n");

        if(isInduced){
            System.out.println("Induced isomorphisms. Total number subgraph isomorphisms: "+subgraphIsomorphism.size());
            writer.append("Induced isomorphisms. Total number subgraph isomorphisms: ")
                    .append(String.valueOf(subgraphIsomorphism.size())).append("\n");
        }else{
            System.out.println("Non-induced isomorphisms. Total number subgraph isomorphisms: "+subgraphIsomorphism.size());
            writer.append("Non-induced isomorphisms. Total number subgraph isomorphisms: ")
                    .append(String.valueOf(subgraphIsomorphism.size())).append("\n");
        }

        String algorithmOutput = "# candidates algorithm: "+ algorithmNameC+"\n" +
                "# processing order algorithm: "+algorithmNamePO+"\n" +
                "# backtracking algorithm: "+algorithmNameB+"\n";

        System.out.println(algorithmOutput);
        writer.append(algorithmOutput);

        List<String> isomorphisms = isomorphismOrdered(subgraphIsomorphism);

        int i = 1; // keep track of which isomorphism was printed
        for(String iso: isomorphisms){
            writer.append("Isomorphism ").append(String.valueOf(i)).append(": ").append(iso).append("\n");
            i++;
        }
        System.out.println();
        writer.append("\n");
    }

    /**
     * Apply subgraph isomorphism if already know both graphs
     * @param queryFileLocation the location of the file containing the query graph information
     * @param targetFileLocation the location of file containing the target graph information
     * @param outputFileName the file which we will write the output to
     * @param isInduced if the isomorphism is induced
     * @param gamma the gamma value
     * @throws IOException for file writer
     */
    public static void subgraphIsomorphismKnownGraphs(String queryFileLocation, String targetFileLocation,
                                                      String outputFileName, String outputStatisticsName,
                                                      boolean isInduced, double gamma)
            throws IOException {
        // read the info from the file
        File queryFile = new File(queryFileLocation);
        String queryName = queryFile.getName();
        File targetFile = new File(targetFileLocation);
        String targetName = targetFile.getName();

        // create the graphs
        Graph<Vertex, DefaultEdge> queryGraph = readGraph(queryFile, formatQuery);
        if(queryGraph == null){
            System.out.println("Query File: ");
            System.out.println(noGraphFormat);
            return;
        }
        Graph<Vertex, DefaultEdge> targetGraph = readGraph(targetFile, formatTarget);
        if(targetGraph == null){
            System.out.println("Target File: ");
            System.out.println(noGraphFormat);
            return;
        }

        // find and display the isomorphisms
        List<Map<Vertex, Vertex>> subgraphIsomorphism = matching(queryGraph, targetGraph, isInduced, gamma);
        if(subgraphIsomorphism==null){
            // write to output files
            BufferedWriter writer = new BufferedWriter(new FileWriter(outputFileName));
            writer.write(noAlgorithmFound);
            writer.close();

            // write to output files
            writer = new BufferedWriter(new FileWriter(outputStatisticsName));
            writer.write(noAlgorithmFound);
            writer.close();
            return;
        }

        // write to output file
        BufferedWriter writer = new BufferedWriter(new FileWriter(outputFileName));
        writer.write("");
        displayIsomorphism(subgraphIsomorphism, queryName, targetName, writer, isInduced);
        System.out.println("============================");
        writer.append("============================\n");
        writer.close();

        // write to statistics file
        writer = new BufferedWriter(new FileWriter(outputStatisticsName));
        writer.write("");
        displayGraphStatistics(queryName, queryGraph, targetName, targetGraph, writer);
        writer.close();
    }

    /**
     * Finds an induced subgraph of the target graph using random node neighbor algorithm
     * @param target the target graph
     * @param sizeQuery the size of the query graph
     * @param seen the vertices we have seen
     * @return the induced subgraph
     */
    private static Graph<Vertex, DefaultEdge> randomGraphRandomNodeNeighbor(Graph<Vertex, DefaultEdge> target, int sizeQuery,
                                                                            Map<Vertex, Vertex> seen){
        Graph<Vertex, DefaultEdge> queryGraph = new SimpleGraph<>(DefaultEdge.class);

        // get a random vertex
        Vertex firstVertex = randomVertex(target.vertexSet());

        int currentId = 0;
        // get the starting vertex, and create a copy
        Vertex lastVertexCopy = copyVertex(firstVertex, currentId);
        seen.put(firstVertex, lastVertexCopy); // target, query

        // add the first vertex to the graph
        addVertex(queryGraph, lastVertexCopy); currentId++;

        // the set of possible vertices is initially the neighbors list
        Set<Vertex> possibleVertices = new HashSet<>(Graphs.neighborListOf(target, firstVertex));
        while(queryGraph.vertexSet().size()<sizeQuery){
            // haven't reached size and there are no more vertices to go to
            if(possibleVertices.isEmpty()){
                return null;
            }
            // pick a random vertex from the neighbors
            Vertex randVertex = randomVertex(possibleVertices);

            // create a copy of the vertex and add to graph
            lastVertexCopy = copyVertex(randVertex, currentId);
            seen.put(randVertex, lastVertexCopy); // target, query
            addVertex(queryGraph, lastVertexCopy); currentId++;

            // add the neighbors of the random vertex, and remove any that we have already visited
            possibleVertices.addAll(Graphs.neighborListOf(target, randVertex));
            possibleVertices.removeAll(seen.keySet());

            // add an edge between it and all existing vertices
            for(Vertex prevVertices: seen.keySet()){
                if(target.containsEdge(prevVertices, randVertex)){
                    addEdge(queryGraph, seen.get(prevVertices), seen.get(randVertex));
                }
            }
        }

        return queryGraph;
    }

    /**
     * Create a new graph by performing a random walk on the target graph
     * @param target target graph
     * @param sizeQuery the maximum number of vertices in the query
     * @param seen map that keeps track of equivalencies between query and target vertex
     * @return the random graph
     */
    private static Graph<Vertex, DefaultEdge> randomGraphRandomWalk(Graph<Vertex, DefaultEdge> target, int sizeQuery,
                                                          Map<Vertex, Vertex> seen) {
        Graph<Vertex, DefaultEdge> queryGraph = new SimpleGraph<>(DefaultEdge.class);
        // get a random vertex
        Vertex randVertex = randomVertex(target.vertexSet());

        // random walk starting at random vertex
        Iterator<Vertex> iter = new RandomWalkVertexIterator(target, randVertex);
        int currentId = 0;
        // get the starting vertex, and create a copy
        Vertex lastVertex = iter.next(); Vertex lastVertexCopy = copyVertex(lastVertex, currentId);
        seen.put(lastVertex, lastVertexCopy); // target, query

        // the maximum amount of vertices will check
        int maxIteration = 1000;
        // the maximum number of vertices that will be checked
        int maxTimesChecked = 100;

        // create a new vertex, by copying info
        addVertex(queryGraph, lastVertexCopy);

        for(int i = 0; i<maxTimesChecked; i++) {
            maxIteration = 1000;
            // perform the walk
            while (iter.hasNext()) {
                // keeps it from getting stuck in an infinite loop
                maxIteration--;
                if (maxIteration < 0) {
                    break;
                }

                currentId = seen.size();
                // stop when reach given size
                if (currentId >= sizeQuery) {
                    break;
                }

                // get the next vertex and its edge
                Vertex nextVertex = iter.next();
                Vertex nextVertexCopy = copyVertex(nextVertex, currentId);

                // if we have already seen it, then use the previously made copy vertex
                if (seen.containsKey(nextVertex)) {
                    nextVertexCopy = seen.get(nextVertex);
                }
                // if we haven't seen it, then add new vertex to query graph
                else {
                    seen.put(nextVertex, nextVertexCopy);
                    addVertex(queryGraph,nextVertexCopy);
                }

                // only add edge if haven't seen it before in query
                if (!queryGraph.containsEdge(lastVertexCopy, nextVertexCopy)) {
                    addEdge(queryGraph, lastVertexCopy, nextVertexCopy);
                }

                // keep track of last vertex to create edge
                lastVertexCopy = nextVertexCopy;
            }
            if(queryGraph.vertexSet().size()==sizeQuery){
                break;
            }
        }

        // if we are unable to find a vertex of that size
        if(queryGraph.vertexSet().size()!=sizeQuery){
            return null;
        }

        return queryGraph;
    }

    /**
     * Finds the number of distinct labels within the graph
     * @param graph the given graph
     * @return number of distinct labels in graph
     */
    public static int numberOfDistinctLabels(Graph<Vertex, DefaultEdge> graph){
        Set<String> labels = new HashSet<>();
        for(Vertex v: graph.vertexSet()){
            labels.add(v.getLabel());
        }
        return labels.size();
    }

    /**
     * Attempts to construct subgraph with average degree.  Return if successful.
     * @param target the target graph
     * @param seen the vertices we check in the target graph
     * @param n the number of vertices
     * @param avgD the desired average degree range
     * @param subgraphMethod the subgraph method we are using
     * @return if it is successful in constructing a graph with average degree
     */
    public static boolean randGraphWithDegree(Graph<Vertex, DefaultEdge> target, Map<Vertex, Vertex> seen, int n,
                                              List<Double> avgD, String subgraphMethod){
        Graph<Vertex, DefaultEdge> query;

        // keep track of average degree of graph
        double avgDActual = 0;
        switch (subgraphMethod) {
            case RANDOM_WALK -> query = randomGraphRandomWalk(target, n, seen);
            case RANDOM_NODE_NEIGHBOR -> query = randomGraphRandomNodeNeighbor(target, n, seen);
            default -> {
                System.out.println(noRandomSubgraphMethodFound);
                return false;
            }
        }

        // if there is a problem constructing the graph
        if (query == null) {
            return false;
        }

        // add all the edges within the target graph to the query graph
        for (Vertex u : seen.keySet()) {
            List<Vertex> possibleNeighbors = Graphs.neighborListOf(target, u);
            possibleNeighbors.retainAll(seen.keySet());
            avgDActual += possibleNeighbors.size();
            for (Vertex v : possibleNeighbors) {
                if (!query.containsEdge(seen.get(u), seen.get(v))) {
                    addEdge(query, seen.get(u), seen.get(v));
                }
            }
        }


        double vSize = query.vertexSet().size();
        // get the degree
        double largestDe = avgDActual/vSize;
        // get the smallest degree
        double smallestDe = (2*(vSize-1))/(vSize);

        // if it is possible to remove edges to get desired degree
        return Math.max(smallestDe, avgD.get(0))<Math.min(largestDe, avgD.get(1));
    }

    /**
     * Construct a random query graph which is a subgraph of given target graph with given properties
     * @param target the target graph
     * @param seen keep track of the mapping from query to target vertices
     * @param n the number of vertices in query graph
     * @param avgD the range of average degree of query graph
     * @param dia the range of diameter of query graph
     * @param den the range of density of query graph
     * @param numLabels the range of number of distinct labels
     * @return the query graph
     */
    public static Graph<Vertex, DefaultEdge> randomGraphWithProperties(Graph<Vertex, DefaultEdge> target,
                                                                       Map<Vertex, Vertex> seen,
                                                                       int n, List<Double> avgD, List<Double> dia,
                                                                       List<Double> den, List<Double> numLabels,
                                                                       String subgraphMethod){

        Graph<Vertex, DefaultEdge> query;

        // keep track of average degree of graph
        double avgDActual = 0;
        switch (subgraphMethod) {
            case RANDOM_WALK -> query = randomGraphRandomWalk(target, n, seen);
            case RANDOM_NODE_NEIGHBOR -> query = randomGraphRandomNodeNeighbor(target, n, seen);
            default -> {
                System.out.println(noRandomSubgraphMethodFound);
                return null;
            }
        }

        // if there is a problem constructing the graph
        if (query == null) {
            return null;
        }

        // since we are only changing edges, must check labels first
        double numLabelsActual = numberOfDistinctLabels(query);
        if (numLabels != null && (numLabelsActual < numLabels.get(0) || numLabels.get(1) < numLabelsActual)) {
            return null;
        }

        // add all the edges within the target graph to the query graph
        for (Vertex u : seen.keySet()) {
            List<Vertex> possibleNeighbors = Graphs.neighborListOf(target, u);
            possibleNeighbors.retainAll(seen.keySet());
            avgDActual += possibleNeighbors.size();
            for (Vertex v : possibleNeighbors) {
                if (!query.containsEdge(seen.get(u), seen.get(v))) {
                    addEdge(query, seen.get(u), seen.get(v));
                }
            }
        }

        // check if matches properties
        double vSize = query.vertexSet().size();
        double eSize = query.edgeSet().size();
        avgDActual = avgDActual/vSize;
        GraphMeasurer<Vertex, DefaultEdge> graphMeasurer = new GraphMeasurer<>(query);
        double diaActual = graphMeasurer.getDiameter();
        double denActual = 2*eSize/(vSize*(vSize-1)); // assuming it is undirected and simple
        if((avgD==null || (avgD.get(0)<=avgDActual&&avgDActual<=avgD.get(1)))
                && (dia==null || (dia.get(0)<=diaActual&&diaActual<=dia.get(1)))
                && (den==null || (den.get(0)<=denActual&&denActual<=den.get(1)))){
            return query;
        }

        // possible edges we can remove
        List<DefaultEdge> possibleEdges = new ArrayList<>(query.edgeSet());
        while((avgD==null || avgDActual>=avgD.get(0))
                && (dia==null || dia.get(1)>=diaActual)
                && (den==null || denActual>=den.get(0))
                && (possibleEdges.size()>0)){
            // pick a random edge
            int eIndex = (int) Math.floor(Math.random()*possibleEdges.size());
            DefaultEdge e = possibleEdges.get(eIndex);
            // get the source and target from edge
            Vertex s = query.getEdgeSource(e); Vertex t = query.getEdgeTarget(e);

            // check if connected when remove edge
            removeEdge(query, s, t);
            ConnectivityInspector<Vertex,DefaultEdge> connectivityInspector = new ConnectivityInspector<>(query);
            if(!connectivityInspector.isConnected()){
                addEdge(query, s, t);
                // cant use this edge in the future
                possibleEdges.remove(eIndex);
                continue;
            }

            // recalculate properties
            eSize-=1;
            avgDActual = (avgDActual*vSize-2)/vSize;

            graphMeasurer = new GraphMeasurer<>(query);
            diaActual = graphMeasurer.getDiameter();

            denActual = 2*eSize/(vSize*(vSize-1));

            if((avgD==null || (avgD.get(0)<=avgDActual&&avgDActual<=avgD.get(1)))
                    && (dia==null || (dia.get(0)<=diaActual&&diaActual<=dia.get(1)))
                    && (den==null || (den.get(0)<=denActual&&denActual<=den.get(1)))){
                return query;
            }
        }
        return null;
    }

    /**
     * Checks to see if the isomorphism is working, by performing subgraph isomorphism on a ground truth file
     * @param groundTruth the ground truth containing the query/target graphs and their isomorphisms
     * @param queryFolderName the location of the query graph
     * @param targetFolderName the location of the target graph
     * @param outputFileName the output file where problems are written
     * @param gamma the gamma value
     * @throws IOException for reader
     */
    public static void testAgainstGroundTruth(String groundTruth, String queryFolderName, String targetFolderName,
                                                 String outputFileName, double gamma) throws IOException {
        // read from ground truth
        BufferedReader br = new BufferedReader(new FileReader(groundTruth));
        String line = br.readLine();

        // write to output file when find error
        BufferedWriter writer = new BufferedWriter(new FileWriter(outputFileName));
        writer.write("There were the following incorrect subgraph isomorphisms using:\n" +
                "Candidates algorithm: "+algorithmNameC+" \n" +
                "Processing order algorithm: "+algorithmNamePO+"\n" +
                "Backtracking algorithm: "+algorithmNameB+"\n\n");

        while(line!=null){
            // get rid of whitespace
            line = line.strip();

            // check if comment
            if(line.length()>0 && line.charAt(0) == '#'){
                line = br.readLine();
                continue;
            }
            // start of a new isomorphism
            if(line.contains("Query Graph:")){
                // keep track if we have seen a problem
                boolean graphProblem = false;

                String[] lineInfo = line.split(",");
                String queryGraphName = lineInfo[0].split(":")[1].strip();
                String targetGraphName = lineInfo[1].split(":")[1].strip();

                File queryGraphFile = new File(queryFolderName+queryGraphName);
                File targetGraphFile = new File(targetFolderName+targetGraphName);

                // construct the graphs
                Graph<Vertex, DefaultEdge> query = readGraph(queryGraphFile, formatQuery);
                if(query == null){
                    System.out.println("Query File: ");
                    System.out.println(noGraphFormat);
                    return;
                }
                Graph<Vertex, DefaultEdge> target = readGraph(targetGraphFile, formatTarget);
                if(target == null){
                    System.out.println("Target File: ");
                    System.out.println(noGraphFormat);
                    return;
                }


                // find if induced
                boolean isInduced = true;
                line = br.readLine();
                while(line.length()>0 && line.charAt(0) == '#' || !line.toLowerCase(Locale.ROOT).contains("induced")){
                    line = br.readLine();
                }
                // looking at a false induction
                if(line.strip().toLowerCase(Locale.ROOT).contains("non-induced")){
                    isInduced = false;
                }
                // keep track of string value
                String outputString = "Non-induced";
                if(isInduced){
                    outputString = "Induced";
                }


                // keep track of number of isomorphisms
                int numIsomorphisms = Integer.parseInt(line.split(":")[1].strip());

                // find isomorphisms and how they are displayed
                List<Map<Vertex, Vertex>> subgraphIsomorphism = matching(query, target, isInduced, gamma);
                if(subgraphIsomorphism==null){
                    writer.write(noAlgorithmFound);
                    br.close(); writer.close();
                    return;
                }
                if(numIsomorphisms!= subgraphIsomorphism.size()){
                    String output = "Incorrect number of Matching! \n"+
                            queryGraphFile.getName() + " : " + targetGraphFile.getName() + " - "+outputString+"\n";
                    writer.append(output);

                    System.out.println("Problem Here! ("+outputString+") "+queryGraphFile +": "+targetGraphFile);
                    graphProblem = true;
                }

                if(!graphProblem) {
                    List<String> isomorphisms = isomorphismOrdered(subgraphIsomorphism);

                    int i = 1; // keep track of which isomorphism was printed
                    line = br.readLine().strip();
                    for (String iso : isomorphisms) {
                        // skip comments
                        while (line.length() > 0 && line.charAt(0) == '#') {
                            line = br.readLine().strip();
                        }
                        String currentMatching = "Isomorphism " + i + ": " + iso;
                        i++;

                        // compare with ground truth
                        if (!currentMatching.equals(line)) {
                            writer.append("Incorrect ").append(outputString).append(" Matching! \n")
                                    .append(queryGraphFile.getName()).append(" : ")
                                    .append(targetGraphFile.getName()).append("\n");
                            // state the differences
                            writer.append("Correct : ").append(line).append("\n");
                            writer.append("Incorrect (found) : ").append(currentMatching).append("\n\n");

                            System.out.println("Problem Here! " + queryGraphFile + ": " + targetGraphFile);
                            graphProblem = true;
                        }
                        if (graphProblem) {
                            break;
                        }
                        line = br.readLine().strip();
                    }
                    if (!graphProblem) {
                        System.out.println("Correct " + outputString + " Matching! " +
                                queryGraphFile.getName() + ": " + targetGraphFile.getName());
                    }
                }
            }

            line = br.readLine();
        }
        writer.close();
    }

    /**
     * Creates a random graph from the target graph and performs subgraph isomorphism
     *
     * @param targetGraph the target graph
     * @param targetLocation the location of the target
     * @param size the size of the query graph
     * @param outputFolderName the folder we are writing the graph information to
     * @param queryName the name of the query graph
     * @param isInduced if the isomorphism is induced
     * @param gamma the gamma value
     * @throws IOException for the writer
     * @return if random walk was successful
     */
    public static int randomSubgraph(Graph<Vertex, DefaultEdge> targetGraph, String targetLocation, int size,
                                  String outputFolderName, String queryName, boolean isInduced, double gamma,
                                  String subgraphMethod)
            throws IOException {

        BufferedWriter writer = new BufferedWriter(new FileWriter(
                outputFolderName + "GenerationInfo\\" + queryName));

        // keep track of equivalencies, so know when see a target vertex again
        Map<Vertex, Vertex> seen = new HashMap<>();
        Graph<Vertex, DefaultEdge> queryGraph;
        switch (subgraphMethod) {
            case RANDOM_WALK -> queryGraph = randomGraphRandomWalk(targetGraph, size, seen);
            case RANDOM_NODE_NEIGHBOR -> queryGraph = randomGraphRandomNodeNeighbor(targetGraph, size, seen);
            default -> {
                System.out.println(noRandomSubgraphMethodFound);
                return -1;
            }
        }
        // problem with finding query graph
        if(queryGraph==null){
            return -1;
        }

        // write the mappings
        // write to output file info when constructing graph
        writer.write(targetLocation + " \n");
        writer.append(seen.toString()).append("\n");
        for (Vertex targetVertex : seen.keySet()) {
            writer.append(String.valueOf(targetVertex.getId())).append(" ")
                    .append(String.valueOf(targetVertex.getNumProfileSubsets())).append("\n");
        }

        // save the graph
        String queryFileName = writeGraph(queryGraph, outputFolderName + "Graphs\\", queryName);
        String targetName = new File(targetLocation).getName();

        displayGraphStatistics(queryName, queryGraph, targetName, targetGraph, writer);
        writer.close();

        // find and display the isomorphisms
        List<Map<Vertex, Vertex>> subgraphIsomorphism = matching(queryGraph, targetGraph, isInduced, gamma);
        if(subgraphIsomorphism == null){
            // write to output file
            writer = new BufferedWriter(new FileWriter(
                    outputFolderName + "Isomorphism\\" + queryName));
            writer.write(noAlgorithmFound);
            writer.close();

            return -1;
        }

        // write to output file
        writer = new BufferedWriter(new FileWriter(
                outputFolderName + "Isomorphism\\" + queryName));
        writer.write("");
        displayIsomorphism(subgraphIsomorphism, queryName, targetName, writer, isInduced);
        System.out.println("============================");
        writer.append("============================\n");
        writer.close();

        return 1;
    }

    /**
     * Display the statistics of the creation of the graph and the isomorphism when relevant
     * @param queryName the name of the query graph
     * @param query the query graph
     * @param targetName the name of the target graph
     * @param target the target graph
     * @param writer where we are writing the information to
     * @throws IOException writer exceptions
     */
    public static void displayGraphStatistics(String queryName, Graph<Vertex, DefaultEdge> query,
                                              String targetName, Graph<Vertex, DefaultEdge> target,
                                              BufferedWriter writer) throws IOException {
        // print out graph
        writer.write("Graph Statistics: \n"+
                "Query: "+ queryName + "\n"+
                "Target: " + targetName + "\n\n");

        // distribution of num subsets for each vertex
        /*
        Map<Integer, Integer> distributionTarget = new HashMap<>();
        for(Vertex v: target.vertexSet()){
            int numSubsets = v.calculateNumberProfileSubsets().size();
            if(!distributionTarget.containsKey(numSubsets)){
                distributionTarget.put(numSubsets, 0);
            }
            distributionTarget.put(numSubsets, distributionTarget.get(numSubsets)+1);
        }

        Map<Integer, Integer> distributionQuery = new HashMap<>();
        for(Vertex v: query.vertexSet()){
            int numSubsets = v.calculateNumberProfileSubsets().size();
            if(!distributionQuery.containsKey(numSubsets)){
                distributionQuery.put(numSubsets, 0);
            }
            distributionQuery.put(numSubsets, distributionQuery.get(numSubsets)+1);
        }


        // print out the distribution
        writer.append("Distribution: (number_profiles:frequency) \n");
        writer.append("Query Graph:\n");
        List<Integer> possibleSizes = new ArrayList<>(distributionQuery.keySet()); Collections.sort(possibleSizes);
        for(int d: possibleSizes){
            writer.append("\t"+d + ":" +distributionQuery.get(d) + "\n");
        }
        writer.append("Target Graph:\n");
        possibleSizes = new ArrayList<>(distributionTarget.keySet()); Collections.sort(possibleSizes);
        for(int d: possibleSizes){
            writer.append("\t").append(String.valueOf(d)).append(":")
                    .append(String.valueOf(distributionTarget.get(d))).append("\n");
        }
        writer.append("\n");
         */

        String algorithmOutput = "Used candidate algorithm: " +algorithmNameC+"\n" +
                "Used processing order algorithm: " +algorithmNamePO+"\n" +
                "Used backtracking algorithm: " +algorithmNameB+"\n";
        writer.append(algorithmOutput);
        // number of backtracking in isomorphism
        writer.append("Number backtracking calls: ").append(String.valueOf(numBackTracking)).append("\n");
        writer.append("\n");
        // number of possible matchings
        writer.append("Total number of possible matchings: "+target.vertexSet().size()*query.vertexSet().size()+"\n");
        // number pruned from local pruning
        writer.append("Number pruned from local pruning: ").append(String.valueOf(numLocalPruning)).append("\n");
        // number pruned from global pruning
        if(numGlobalPruned!=-1) {
            writer.append("Number pruned from global pruning: ").append(String.valueOf(numGlobalPruned)).append("\n");
        }
        writer.append("\n");
        // total cost from graphQL order
        if(totalCostGraphQL!=-1) {
            writer.append("Cost of order found by graphQL: ").append(String.valueOf(totalCostGraphQL)).append("\n");
        }
        if(falseMatchingParents!=-1){
            writer.append("False matchings removed using parents from quickSI: ").append(String.valueOf(falseMatchingParents))
                    .append("\n");
        }
        if(falseMatchingExtraEdge!=-1){
            writer.append("False matchings removed using extra edges from quickSI: ").append(String.valueOf(falseMatchingExtraEdge))
                    .append("\n");
        }
        if(algorithmNameB.equals(DAF)){
            String output = "\nFailing Sets Statistics:\n" +
                    "Number of full solutions: "+fullSolutions+"\n"+
                    "Number of partial solutions: "+partialSolutions+"\n"+
                    "Number of empty candidates: "+emptyCandidates+"\n"+
                    "Number of conflicts: "+conflicts+"\n"+
                    "Number Refined: "+cs.getNumRefined()+
                    "\n\n";
            writer.append(output);
        }

        if(numSymmetric !=-1){
            writer.append("Symmetric matchings found from VEQS: ").append(String.valueOf(numSymmetric))
                    .append("\n");
        }

        // the combination information if combined two graphs
        if(sg.getNumCombined()!=null){
            writer.append("Star Graph Combination:\n");
            for(List<Vertex> combine: sg.getNumCombined().keySet()){
                writer.append("\t").append(combine.toString()).append(":")
                        .append(String.valueOf(sg.getNumCombined().get(combine))).append("\n");
            }
        }
    }

    /**
     * Pick a random vertex from the set of vertices
     * @param vertices the set of vertices
     * @return a random vertex within the set
     */
    public static Vertex randomVertex(Set<Vertex> vertices){
        // get a random index within the vertices
        Random random = new Random();
        int randIndex = random.nextInt(vertices.size());
        // iterate through the vertices
        Iterator<Vertex> it = vertices.iterator();
        Vertex randomVertex = it.next();

        // keep picking elements until we have reached the index
        for(int i = 1; i<=randIndex; i++){
            randomVertex = it.next();
        }

        // return the random vertex
        return randomVertex;
    }

    /**
     * Finds the average of the given values
     * @param values double values
     * @return average of values
     */
    public static double calculateAverage(List<Double> values){
        // average the cost values
        double avg = 0;
        for(double cost : values){
            avg += cost;
        }
        avg = avg/values.size();
        return avg;
    }

    /**
     * Finds the squared difference between the points and the average
     * @param values double values
     * @return the MSE of the values
     */
    public static double calculateMeanSquareDifference(List<Double> values){
        // calculate average
        double average = calculateAverage(values);
        // calculate MSE
        double mse = 0;
        for(double val: values){
            // square difference
            mse += Math.pow(val-average,2);
        }

        return mse/(values.size()-1);
    }

    /**
     * Estimates the cardinality for a given query and target graph
     * @param queryFileLocation the file containing the query graph
     * @param targetFileLocation the file containing the target graph
     * @param gamma the gamma value for graphQL
     * @param tau the threshold for the confidence interval
     * @param maxEpoch the maximum number of random walks
     * @param zAlpha the z score for the confidence interval
     * @param outputFileName the output file
     * @param isInduced if the isomorphism is induced
     * @return an estimation for the number of matchings between a query and target graph
     * @throws IOException read/write to file
     */
    public static double estimateCardinality(String queryFileLocation, String targetFileLocation, double gamma, double tau,
                                          int maxEpoch, double zAlpha, String outputFileName, boolean isInduced)
            throws IOException {
        // read the info from the file
        File queryFile = new File(queryFileLocation);
        File targetFile = new File(targetFileLocation);

        // create the graphs
        Graph<Vertex, DefaultEdge> queryGraph = readGraph(queryFile, formatQuery);
        if(queryGraph == null){
            System.out.println("Query File: ");
            System.out.println(noGraphFormat);
            return -1;
        }
        Graph<Vertex, DefaultEdge> targetGraph = readGraph(targetFile, formatTarget);
        if(targetGraph == null){
            System.out.println("Target File: ");
            System.out.println(noGraphFormat);
            return -1;
        }

        // compute the estimation
        double estimation =  wj.wanderJoins(queryGraph, targetGraph, gamma, tau, maxEpoch, zAlpha, isInduced);
        if(estimation == -1){
            BufferedWriter writer = new BufferedWriter(new FileWriter(outputFileName));
            writer.write("Something went wrong");
            return -1;
        }

        // write to output file
        BufferedWriter writer = new BufferedWriter(new FileWriter(outputFileName));
        String output = "The matching estimation for the following is " + estimation +":"+
                "\nquery graph: "+queryFile.getName() +
                "\ntarget graph: "+targetFile.getName()+
                "\n# induced isomorphisms with " +
                "\n# candidates algorithm: "+algorithmNameC+
                "\n# processing order algorithm: "+algorithmNamePO+
                "\n\nEstimate Parameters:" +
                "\n tau: " +tau+
                "\n maxEpoch: " +maxEpoch+
                "\n zAlpha: "+zAlpha+
                "\n\n";
        writer.write(output);
        writer.close();
        // print output as well
        System.out.println(output);

        // find the estimated cardinality using wander joins
        return estimation;
    }

    /**
     * Compare the estimation of the isomorphisms to the actual number of matchings
     * @param isomorphismFolder folder that contains the isomorphisms
     * @param outputFile the file that we will output the information to
     * @param gamma the gamma value for GraphQL
     * @param tau the value we want our estimate within
     * @param maxEpoch the maximum number of random walk we will do in target graph
     * @param zScore the z score of a alpha value
     * @param queryFolder the folder containing the queries
     * @param targetFolder the folder containing the targets
     * @throws IOException error with reading/writing files
     */
    public static void testEstimations(String isomorphismFolder, String outputFile, double gamma, double tau,
                                       int maxEpoch, double zScore, String queryFolder, String targetFolder)
            throws IOException {
        File dir = new File(isomorphismFolder);
        // write to output file
        BufferedWriter writer = new BufferedWriter(new FileWriter(outputFile));
        String estimationParameters = "# Estimate Parameters (tau): "+tau+
                "\n# Estimate Parameters (maxEpoch): "+maxEpoch+
                "\n# Estimate Parameters (zScore): "+zScore+
                "\n\n";

        writer.write(estimationParameters);


        for(File isomorphism: dir.listFiles()){
            // reset query and target graph
            String queryFileName = null;
            String targetFileName = null;

            // reset the number of isomorphism
            int actualNumber = -1;

            String induceString = null;

            // read from ground truth
            BufferedReader br = new BufferedReader(new FileReader(isomorphism));
            String line = br.readLine();
            while (line != null){
                // check if comment
                if(line.length()>0 && line.charAt(0) == '#'){
                    line = br.readLine();
                    continue;
                }

                // get the query and target graph
                if(line.toLowerCase(Locale.ROOT).contains("query graph")){
                    String[] info = line.split(",");
                    queryFileName = queryFolder+info[0].strip().split(" ")[2].strip();
                    targetFileName = targetFolder+info[1].strip().split(" ")[2].strip();
                }

                // get the number of isomorphisms
                if(line.toLowerCase(Locale.ROOT).contains("subgraph isomorphisms")){
                    actualNumber = Integer.parseInt(line.split(":")[1].strip());
                    induceString = line.split(" ")[0].strip().toLowerCase(Locale.ROOT);
                }

                // we found all of the information
                if(queryFileName!= null && actualNumber!=-1){
                    break;
                }
                line = br.readLine();
            }
            br.close();

            if(queryFileName==null || targetFileName==null){
                System.out.println("Problem with query or target graph file");
                return;
            }

            File queryFile = new File(queryFileName);
            File targetFile = new File(targetFileName);
            Graph<Vertex, DefaultEdge> query = readGraph(queryFile, formatQuery);
            if(query == null){
                System.out.println("Query File: ");
                System.out.println(noGraphFormat);
                return;
            }
            Graph<Vertex, DefaultEdge> target = readGraph(targetFile, formatTarget);
            if(target == null){
                System.out.println("Target File: ");
                System.out.println(noGraphFormat);
                return;
            }

            if(induceString==null){
                System.out.println("Problem with knowing if induced");
                return;
            }
            boolean isInduced = induceString.equals("induced");

            double estimatedNumber = wj.wanderJoins(query, target, gamma, tau, maxEpoch, zScore, isInduced);
            if(estimatedNumber == -1){
                writer.append("Something went wrong!");
                return;
            }

            double error = Math.abs(actualNumber-estimatedNumber);
            if(actualNumber != 0){
                error = error/actualNumber;
            }
            // if the actual value equals zero and the estimated is not, then we bound the error at 1
            else if(error!=0){
                error = 1;
            }

            String output = "Query Graph: "+queryFile.getName()+", Target Graph: "+targetFile.getName() +
                    "\n# candidates algorithm: "+algorithmNameC+
                    "\n# processing order algorithm: "+algorithmNamePO+
                    "\n\tActual Number Matchings: "+actualNumber+
                    "\n\tEstimated Number Matchings: "+estimatedNumber+
                    "\n\tError: "+error+"\n";

            writer.append(output);
            writer.append("\n===========================\n\n");

            System.out.println(output+"\n===========================\n");
        }

        writer.close();
    }


    /**
     * Calculate the average number of backtracking and matchings for a given graph
     * @param isomorphismFolder the folder containing the isomorphisms
     * @throws IOException if file reader error
     */
    public static void averageBacktrackingMatching(String isomorphismFolder) throws IOException {
        // find the isomorphism directory
        File dir = new File(isomorphismFolder);

        List<Double> allMatchings =  new ArrayList<>();
        List<Double> allBacktrackings = new ArrayList<>();

        // iterate through the isomorphisms
        for(File isomorphism: dir.listFiles()) {
            // reset the values for each isomorphism
            int numMatchings = -1;
            int numBacktracking = -1;

            // read from ground truth
            BufferedReader br = new BufferedReader(new FileReader(isomorphism));
            String line = br.readLine();
            while (line != null){
                // check if comment
                if(line.length()>0 && line.charAt(0) == '#'){
                    line = br.readLine();
                    continue;
                }

                // get the number of isomorphisms
                if(line.toLowerCase(Locale.ROOT).contains("subgraph isomorphisms")){
                    numMatchings = Integer.parseInt(line.split(":")[1].strip());
                }

                // get the number of backtracking
                if(line.toLowerCase(Locale.ROOT).contains("number backtracking")){
                    numBacktracking = Integer.parseInt(line.split(":")[1].strip());
                }

                if(numBacktracking != -1 && numMatchings != -1){
                    break;
                }

                line = br.readLine();
            }
            br.close();

            // keep track of the number of matchings and backtracking
            allMatchings.add((double) numMatchings);
            allBacktrackings.add((double) numBacktracking);
        }

        double averageMatchings = calculateAverage(allMatchings);
        double averageBacktracking = calculateAverage(allBacktrackings);

        System.out.println("Average number matchings: "+averageMatchings +
                "\nAverage number backtracking: "+averageBacktracking);
    }

    /**
     * Rewrites the name of the graphs from the location to the name (without the directory it is under)
     * @param isomorphismFolder the folder containing the isomorphisms
     * @throws IOException for read/write errors
     */
    public static void rewriteName(String isomorphismFolder) throws IOException {
        // find the isomorphism directory
        File dir = new File(isomorphismFolder);

        // iterate through the isomorphisms
        for (File inputFile : dir.listFiles()) {
            // read from isomorphism
            BufferedReader br = new BufferedReader(new FileReader(inputFile));
            // new file we will copy to
            File outputFile = new File(isomorphismFolder+inputFile.getName().replace(".txt", "")+"N.txt");
            BufferedWriter writer = new BufferedWriter(new FileWriter(outputFile));


            String line = br.readLine();
            while (line != null) {
                // check if comment
                if (line.length() > 0 && line.charAt(0) == '#') {
                    writer.append(line).append("\n");
                    line = br.readLine();
                    continue;
                }

                // get the query and target graph
                if(line.toLowerCase(Locale.ROOT).contains("query graph")){
                    String[] info = line.split(",");

                    // change the name
                    String originalQueryName = info[0].strip().split(" ")[2].strip();
                    String newQueryName = new File(originalQueryName).getName();
                    String originalTargetName = info[1].strip().split(" ")[2].strip();
                    String newTargetName = new File(originalTargetName).getName();
                    writer.append("Query Graph: "+newQueryName+", Target Graph: "+newTargetName+"\n");
                }
                // write the line exactly
                else{
                    writer.append(line).append("\n");
                }
                line = br.readLine();
            }
            br.close();
            writer.close();

            // delete the input file
            inputFile.delete();

            // rename output file
            File rename = new File(isomorphismFolder+outputFile.getName().replace("N", ""));
            outputFile.renameTo(rename);
        }
    }

    /**
     * Finds random query graphs and performs subgraph isomorphism
     * @param targetLocation the location of the target graph
     * @param outputFolderName the output folder
     * @param size the size of the query graph
     * @param gamma the gamma for graphQL
     * @param isInduced if the isomorphism is induced
     * @param maxNumQueryGraphs the maximum number of query graphs we will check
     * @throws IOException read/write errors
     */
    public static void randomGeneration(String targetLocation, String outputFolderName, int size, double gamma,
                                        boolean isInduced, int maxNumQueryGraphs, String subgraphMethod)
            throws IOException {
        // create the target graph and random query graph
        Graph<Vertex, DefaultEdge> targetGraph = readGraph(new File(targetLocation), formatTarget);
        if(targetGraph == null){
            System.out.println("Target File: ");
            System.out.println(noGraphFormat);
            return;
        }
        //calculateStatistics(targetGraph);

        for(int i = 1; i<=maxNumQueryGraphs; i++) {
            File outputGraphFolder = new File(outputFolderName + "Graphs\\");
            int numGraphs = 0;
            if (outputGraphFolder.list() != null) {
                numGraphs = outputGraphFolder.list().length;
            }
            String graphName = "graph" + (numGraphs + 1) + ".txt";

            if(randomSubgraph(targetGraph, targetLocation, size, outputFolderName, graphName, isInduced, gamma,
                    subgraphMethod) == -1){
                return;
            }
        }
    }

    /**
     * Check a set of graphs and get rid of any isomorphic graphs that are not the same instance.  We are checking
     * isomorphism so it is induced and the gamma value will just be set to 0.5
     * @param graphs the set of graphs
     */
    public static void removeIsomorphicGraphs(Map<Graph<Vertex, DefaultEdge>, Double> graphs){
        Set<Graph<Vertex, DefaultEdge>> toRemove = new HashSet<>();
        Set<Graph<Vertex, DefaultEdge>> q2Values = new HashSet<>(graphs.keySet());
        // combine query graphs that are equivalent
        for (Graph<Vertex, DefaultEdge>q1: graphs.keySet()){
            q2Values.remove(q1);
            for(Graph<Vertex, DefaultEdge>q2: q2Values){
                // same instance
                if(q1==q2){
                    continue;
                }
                if(!toRemove.contains(q1) && matching(q1, q2, true, 0.5).size()>=1){
                    // increment the number that are isomorphic
                    if(!numIsomorphic.containsKey(q1)){
                        numIsomorphic.put(q1, 0);
                    }
                    numIsomorphic.put(q1, numIsomorphic.get(q1)+1);
                    double m1 = graphs.get(q1);
                    double m2 = graphs.get(q2);
                    int i = numIsomorphic.get(q1);
                    double averageNumberMatchings = (m1*i+m2)/(i+1);
                    graphs.put(q1, averageNumberMatchings);
                    toRemove.add(q2);
                }
            }
        }
        for(Graph<Vertex, DefaultEdge>q:toRemove){
            graphs.remove(q);
        }
    }

    /**
     * Write the graph information from attempting to find hard to find instance
     * @param target the query graph
     * @param hardToFind whether the graph is hard to find or potentially hard to find
     * @param graphs the set of distinct query graphs
     * @param outputFolderName the output folder
     * @param targetLocation the location of the target graph
     * @param induce if the isomorphism is induced
     * @param outlier the outlier value
     * @param tau the tau value for wander joins
     * @param maxEpoch the max epoch for wander joins
     * @param zScore the z score for wander joins
     * @param size the size of the query graph
     * @param avgD the average degree range of the query graphs
     * @param dia the diameter range of the query graphs
     * @param den the density range of the query graphs
     * @param numLabels the number of label range for the query graphs
     * @param stats the data set containing other query graph estimates we used to find hard-to-find instances
     * @throws IOException writing to a file
     */
    public static void writeGraphsInformation(Graph<Vertex, DefaultEdge> target, String hardToFind,
                                             Map<Graph<Vertex, DefaultEdge>, Double> graphs, String outputFolderName,
                                             File targetLocation, String induce, double outlier,
                                             double tau, int maxEpoch, double zScore,
                                             int size, List<Double> avgD, List<Double> dia, List<Double> den,
                                             List<Double> numLabels, DescriptiveStatistics stats) throws IOException {
        // remove isomorphic graphs
        numIsomorphic = new HashMap<>();
        removeIsomorphicGraphs(graphs);

        String prefix = "size_"+size+"_de_"+Math.round(avgD.get(0))+"_di_"+Math.round(dia.get(0));

        // Find the next graph index.
        int numGraphs = -1;
        for (File f : new File(outputFolderName).listFiles())
            if (f.getName().startsWith(prefix + "_graph_")) {
                int current = Integer.valueOf(f.getName().replace(prefix + "_graph_", "").replace(".txt", ""));
                if (numGraphs < current)
                    numGraphs = current;
            }
        numGraphs++;

        // iterate through the query graphs
        for (Graph<Vertex, DefaultEdge> query : graphs.keySet()) {
            double estimate = graphs.get(query);

            // store what the graph looks like
            String queryName = "_graph_" + numGraphs + ".txt", statsName = "_stats_" + numGraphs + ".txt";
            writeGraph(query, outputFolderName, prefix + queryName);

            // write statistics of the graph
            BufferedWriter writer = new BufferedWriter(new FileWriter(new File(outputFolderName + prefix + statsName)));

            // write hard-to-find information first
            writer.write(hardToFind+"\n");
            String output = "\nEstimated Number "+induce+" Matchings: " + estimate+"\n" +
                    "Number of Isomorphic Graphs Found: "+numIsomorphic.get(query)+"\n"+
                    "Outlier minimum value: " + outlier + "\n"+
                    "\ttau: " +tau+ "\n"+
                    "\tmaxEpoch: " +maxEpoch+"\n"+
                    "\tzAlpha: "+zScore+ "\n\n" +
                    "The total number of query graphs found: "+stats.getN()+"\n" +
                    stats.toString()+"\n\n"+
                    "Number of Vertices: "+size+"\n"+
                    "Average Degree Range: "+avgD+"\n"+
                    "Diameter Range: "+dia+"\n"+
                    "Density Range: "+den+"\n" +
                    "Number of Distinct Labels: "+numLabels+"\n\n";
            writer.append(output);
            displayGraphStatistics(queryName, query, targetLocation.getName(), target, writer);

            writer.close();
            numGraphs++;
        }
    }

    /**
     * Finds hard-to-find query graph for the target graph by finding outliers based on the estimation from wander joins
     * @param target the target graph
     * @param targetLocation the location of the target graph
     * @param outputFolderName the output folder
     * @param size the size of the query graph
     * @param gamma the gamma for graphQL
     * @param tau the threshold for the confidence interval
     * @param maxEpoch the maximum number of random walks for wander joins
     * @param zScore zScore the zScore for the confidence interval calculated from wander joins
     * @param isInduced if the isomorphism is induced
     * @param maxNumQueryGraphs the size of the sample which we will look for an outlier
     * @param maxNumAttempts the number of times we will will try to find outlier in a dataset
     * @param maxNumFailedProp the number of times we will look for a query with given properties
     * @param avgD the range of average degree we want our graph to be
     * @param dia the range of diameter we want our graph to be
     * @param den den the range of density we want our graph to be
     * @param numLabels the range of number of distinct labels
     * @param subgraphMethods the methods we will use to construct the graphs
     * @throws IOException IOException read/write errors
     */
    public static void randomGenerationWithEstimate(Graph<Vertex, DefaultEdge> target, File targetLocation,
                                                    String outputFolderName, int size, double gamma,
                                                    double tau, int maxEpoch, double zScore, boolean isInduced,
                                                    int maxNumQueryGraphs, int maxNumAttempts, int maxNumFailedProp,
                                                    List<Double> avgD, List<Double> dia, List<Double> den,
                                                    List<Double> numLabels, List<String> subgraphMethods)
            throws IOException {

        Random random = new Random();

        // if the processing order is dynamic ordering the break
        if(algorithmNamePO.equals(DYNAMIC_ORDER)){
            System.out.println("Cannot use "+DYNAMIC_ORDER+" for estimations.");
            System.out.println(noAlgorithmFound);
            return;
        }

        // check if all the subgraph methods are valid
        for(String method : subgraphMethods){
            if(!method.equals(RANDOM_WALK) && !method.equals(RANDOM_NODE_NEIGHBOR)){
                System.out.println("Cannot use "+method+" for constructing query graphs.");
                System.out.println(noRandomSubgraphMethodFound);
                return;
            }
        }

        // keep track estimation and the random walks associated with it
        Map<Double, Set<Graph<Vertex, DefaultEdge>>> estimationRandomWalk = new HashMap<>();
        // keep track of estimate values
        DescriptiveStatistics stats = new DescriptiveStatistics();

        // keep track estimation and the random walks associated with it
        Map<Double, Set<Graph<Vertex, DefaultEdge>>> lastEstimateFound = null;
        // keep track of estimate values
        DescriptiveStatistics lastStatsFound = null;

        double outlier = 0;
        boolean hardToFind = false;

        // string value if induced
        String induce = "Non-induce";
        if(isInduced){
            induce = "Induce";
        }

        // keep track if we found hard-to-find instance
        Map<Graph<Vertex, DefaultEdge>, Double> hardToFindGraphs = new HashMap<>();


        for(int i = 0; i < maxNumAttempts; i++) {
            System.out.print("Attempt "+ (i+1)+". Graphs Created: ");
            // reset values
            estimationRandomWalk = new HashMap<>();
            stats = new DescriptiveStatistics();

            // keep track of the failed attempts
            int failedAttempts = 0;

            // construct a 100 random walks
            for (int j = 0; j < maxNumQueryGraphs; j++) {
                if(failedAttempts >= maxNumFailedProp){
                    System.out.println(" - Could not find a graph with the given properties");
                    break;
                }

                // keep track of equivalencies, so know when see a target vertex again
                Map<Vertex, Vertex> seen = new HashMap<>();

                // create graph of given size from the target, with a random method
                Graph<Vertex, DefaultEdge> query = randomGraphWithProperties(target, seen, size, avgD, dia, den,
                        numLabels, subgraphMethods.get(random.nextInt(subgraphMethods.size())));
                if(query == null){
                    failedAttempts++;
                    j--;
                    continue;
                }
                failedAttempts = 0;

                // estimate the number of matchings
                double estimate = wj.wanderJoins(query, target, gamma, tau, maxEpoch, zScore, isInduced);

                // add to estimate random walks map
                if (!estimationRandomWalk.containsKey(estimate)) {
                    estimationRandomWalk.put(estimate, new HashSet<>());
                }
                estimationRandomWalk.get(estimate).add(query);
                stats.addValue(estimate);

                if(j%100==0){
                    System.out.print(j+", ");
                }
            }
            if(stats.getN() == maxNumQueryGraphs) {
                lastEstimateFound = new HashMap<>(estimationRandomWalk);
                lastStatsFound = stats;

                System.out.println(stats.getN());
                // find if hard-to-find instance
                // calculate outliers:
                double q1 = stats.getPercentile(25);
                double q3 = stats.getPercentile(75);
                double iqr = q3 - q1;

                outlier = q3 + outlierValue * iqr;

                if (stats.getMax() > outlier) {
                    hardToFind = true;
                    break;
                }
            }
        }

        if(hardToFind){
            // add the outliers as graphs
            for (double estimate : estimationRandomWalk.keySet()) {
                if (estimate > outlier) {
                    // iterate through the query graphs
                    for(Graph<Vertex, DefaultEdge> query : estimationRandomWalk.get(estimate)) {
                        hardToFindGraphs.put(query, estimate);
                    }
                }
            }

            System.out.println("Found hard-to-find instance\n" +
                    "================");

            writeGraphsInformation(target, "Hard-to-find", hardToFindGraphs, outputFolderName, targetLocation,
                    induce, outlier, tau, maxEpoch, zScore, size, avgD, dia,  den, numLabels, stats);
        }
        else if(stats.getN()==maxNumQueryGraphs || lastEstimateFound != null){
            if(stats.getN()!=maxNumQueryGraphs){
                estimationRandomWalk = lastEstimateFound;
                stats = lastStatsFound;
            }

            System.out.println("Could not find any hard-to-find instances.  Returned graphs with maximum number of matchings\n" +
                    "================");

            // iterate through the query graphs
            double maxValue = stats.getMax();
            for (Graph<Vertex, DefaultEdge> query : estimationRandomWalk.get(maxValue)) {
                hardToFindGraphs.put(query, maxValue);
            }

            writeGraphsInformation( target,  "Possibly Hard-to-find", hardToFindGraphs, outputFolderName,
                    targetLocation, induce, outlier, tau, maxEpoch, zScore, size, avgD,  dia, den, numLabels, stats);
        }
        else{
            System.out.println("Could not find graphs with property\n" +
                    "================");
            String prefix = "size_"+size+"_de_"+Math.round(avgD.get(0))+"_di_"+Math.round(dia.get(0));

            // store what the graph looks like
            String statsName = "_stats.txt";

            // write statistics of the graph
            BufferedWriter writer = new BufferedWriter(new FileWriter(new File(outputFolderName + prefix + statsName)));

            // write hard-to-find information first
            writer.write("No graphs of family\n");

            writer.close();
        }
    }

    /**
     * Creates random graphs with given properties
     * @param target the target graph
     * @param outputFolderName the output folder we will write the queries to
     * @param maxNumQueryGraphs the maximum number of query graphs we are constructing
     * @param maxNumFailedProp the maximum number of times we will try to construct the query with properties
     * @param size the size of the query
     * @param avgD the range of average degree of query
     * @param dia the diameter of query
     * @param subgraphMethods the subgraph isomorphism methods we are using
     * @throws IOException
     */
    public static void constructRandomGraphWithProp(Graph<Vertex, DefaultEdge> target,String outputFolderName,
                                                    int maxNumQueryGraphs, int maxNumFailedProp,
                                                    int size, List<Double> avgD, List<Double> dia,
                                                    List<String> subgraphMethods) throws IOException {
        Random random = new Random();

         // keep track of the failed attempts
        int failedAttempts = 0;
        int j = 0;

        // construct a 100 random graphs
        for (j = 0; j < maxNumQueryGraphs; j++) {
            if (failedAttempts >= maxNumFailedProp) {
                System.out.println(" - Could not find a graph with the given properties");
                break;
            }

            // keep track of equivalencies, so know when see a target vertex again
            Map<Vertex, Vertex> seen = new HashMap<>();
            // create graph of given size from the target, with a random method
            Graph<Vertex, DefaultEdge> query = randomGraphWithProperties(target, seen, size, avgD, dia, null,
                    null, subgraphMethods.get(random.nextInt(subgraphMethods.size())));
            if (query == null) {
                failedAttempts++;
                j--;
                continue;
            }
            failedAttempts = 0;
            // write query file
            writeGraph(query, outputFolderName, "size_"+size+"_graph"+j+".txt");


            if(j%100==0){
                System.out.print(j+", ");
            }
        }
    }

    /**
     * Finds an average number of matchings and backtracking for graphs given certain properties.  These values can be
     * compared with other algorithms.
     * @param target the target graph
     * @param queryGraphFolder the folder containing the queries
     * @param outputFileName the output file
     * @param isInduced if the isomorphism is induced
     * @param gamma the gamma value for graphql
     * @param maxNumQueryGraphs the maximum number of query graphs we will construct
     * @param size the size of the query graph
     * @throws IOException problems writing to file
     */
    public static void graphComparisonProperties(Graph<Vertex, DefaultEdge> target, String queryGraphFolder,
                                                 String outputFileName, boolean isInduced, double gamma,
                                                 int maxNumQueryGraphs, int size) throws IOException {
        double totalNumMatchings = 0;
        double totalNumBacktracking = 0;

        int j = 0;
        // read through the query graphs
        for (j = 0; j < maxNumQueryGraphs; j++) {
            // keep track of equivalencies, so know when see a target vertex again
            Map<Vertex, Vertex> seen = new HashMap<>();

            Graph<Vertex, DefaultEdge> query;
            // create graph of given size from the target, with a random method
            try {
                query = readGraph(new File(queryGraphFolder+"size_"+size+"_graph"+j+".txt"),
                        formatQuery);
            }catch (Exception e){
                break;
            }

            // find and display the isomorphisms
            double numMatchings = matchingNumeric(query, target, isInduced, gamma);
            if(numMatchings==-1){
                // write to output files
                BufferedWriter writer = new BufferedWriter(new FileWriter(outputFileName));
                writer.write(noAlgorithmFound);
                writer.close();
            }
            totalNumMatchings += numMatchings;
            totalNumBacktracking+=numBackTracking;

            if(j%50==0){
                System.out.print(j+", ");
            }
        }

        // write to output file
        BufferedWriter writer = new BufferedWriter(new FileWriter(outputFileName));
        writer.write("");
        writer.write("Average Number of Matchings: "+totalNumMatchings/j+"\n");
        writer.write("Average Number of Backtracking: "+totalNumBacktracking/j+"\n");
        writer.write("Total Number of Graphs: "+j);
        writer.close();
    }

    /**
     * Returns the number of graphs found with given properties divided by number of attempts
     * @param target the target graph
     * @param size the size of the query graph
     * @param maxNumQueryGraphs the number of query graphs we will check
     * @param avgD the average degree range
     * @param subgraphMethods the different random graph construction methods
     * @return the probability we will construct a graph with the properties
     */
    public static double probabilityCanFindRandomGraph(Graph<Vertex,DefaultEdge> target, int size, int maxNumQueryGraphs,
                                                     List<Double> avgD, List<String> subgraphMethods){
        Random random = new Random();

        // if the processing order is dynamic ordering the break
        if(algorithmNamePO.equals(DYNAMIC_ORDER)){
            System.out.println("Cannot use "+DYNAMIC_ORDER+" for estimations.");
            System.out.println(noAlgorithmFound);
            return -1;
        }

        // check if all the subgraph methods are valid
        for(String method : subgraphMethods){
            if(!method.equals(RANDOM_WALK) && !method.equals(RANDOM_NODE_NEIGHBOR)){
                System.out.println("Cannot use "+method+" for constructing query graphs.");
                System.out.println(noRandomSubgraphMethodFound);
                return -1;
            }
        }

        double count = 0;
        // construct a 100 random walks
        for (int j = 0; j < maxNumQueryGraphs; j++) {
            // keep track of equivalencies, so know when see a target vertex again
            Map<Vertex, Vertex> seen = new HashMap<>();
            // create graph of given size from the target, with a random method
            if(randGraphWithDegree(target, seen, size, avgD, subgraphMethods.get(random.nextInt(subgraphMethods.size())))){
                count++;
            }
        }
        return count/maxNumQueryGraphs;
    }

    /**
     * Main function where the graphs are constructed and we find the subgraph isomorphisms
     * @param args the command line arguments
     * @throws IOException for reader and writer
     */
    public static void main(String[] args) throws IOException {
        String mainMethod = "";
        if(args.length>0) {
            // get the info on the folder and file
            mainMethod = args[0];
        }
        // basic information for isomorphism
        algorithmNameC = GRAPHQL;
        algorithmNamePO = GRAPHQL;
        algorithmNameB = QUICKSI;

        // isomorphism
        final boolean isInduced = true;
        double gamma = 0.5;

        // estimation
        double tau = 100;
        int maxEpoch = 100;
        double zScore = 1.96; // z-score for 95% confidence

        // create query graph
        int minSize = 5;
        int maxSize = 25;
        int maxNumQueries = 100;
        int maxNumAttempts = 1;
        int maxNumFailedProp = 10;
        final List<String> subgraphMethods = new ArrayList<>(List.of(RANDOM_NODE_NEIGHBOR, RANDOM_WALK));

        // calculate outlier
        outlierValue = 3;

        // format of the graphs
        formatTarget = PROTEINS;
        formatQuery = PROTEINS;

        // if we are going to check if the labels are equivalent or subsets
        labelCheck = SUBSETS;
        // star graphs, and frequent dataset mining, separate file
        sg = new HardToFindStarGraphs(formatTarget);

        // keep track of time
        Date startDate = new Date();

        // if the two graphs are known
        if(mainMethod.equals("KnownGraphs") && args.length == 5) {
            final String queryLocation = args[1];
            final String targetLocation = args[2];
            final String isomorphismsFileName = args[3];
            final String statisticsFileName = args[4];

            subgraphIsomorphismKnownGraphs(queryLocation, targetLocation, isomorphismsFileName, statisticsFileName, isInduced,
                    gamma);
        }
        // if finding estimate for cardinality estimation
        else if(mainMethod.equals("Estimate") && args.length == 4) {
            final String queryLocation = args[1];
            final String targetLocation = args[2];
            final String outputFileName = args[3];

            estimateCardinality(queryLocation, targetLocation, gamma, tau, maxEpoch, zScore, outputFileName, isInduced);
        }
        // check the estimations
        else if(mainMethod.equals("TestEstimations") && args.length == 5){
            // isomorphism folder is constructed by methods (random walk, FDMQuery,...)
            final String isomorphismFolder = args[1];
            String queryFolder = args[2];
            String targetFolder = args[3];
            if(queryFolder.equals("_")){
                queryFolder = "";
            }
            if(targetFolder.equals("_")){
                targetFolder = "";
            }
            final String outputFile = args[4];

            testEstimations(isomorphismFolder, outputFile, gamma, tau, maxEpoch, zScore, queryFolder, targetFolder);
        }
        // find the frequent profiles
        else if(mainMethod.equals("FrequentDatasets") && args.length == 4){
            final String targetFolderLocation = args[1];
            final String outputFolderName = args[2];
            double minSup = Double.parseDouble(args[3]);

            // iterate through the possible target graphs
            File [] files = new File(targetFolderLocation).listFiles();
            for (File file : files) {
                if (file.isFile()) { //this line weeds out other directories/folders
                    String targetLocation = String.valueOf(file);
                    String outputFileName = outputFolderName + file.getName();

                    sg.frequentDatasetMining(targetLocation, outputFileName, minSup);
                    System.out.println("=================");
                }
            }
        }
        // create a query graph from frequent profiles
        else if(mainMethod.equals("FDMQuery") && args.length == 4){

            // connecting star graphs
            // MERGE, EDGE, NONE
            final String connectionMethod = sg.EDGE;


            final String fdmFile = args[1];
            final String outputFolderName = args[2];
            // keep track of the minimum profile size while creating graph
            int profileSize = Integer.parseInt(args[3]);// itemsets must be this size

            // get the information from the fdm file
            sg.fdmGraph(fdmFile, outputFolderName, isInduced, profileSize, gamma, connectionMethod);
        }
        // create query graph from random walk
        else if(mainMethod.equals("RandomWalk")  && args.length == 3) {
            // random subgraph generator
            final String subgraphMethod = RANDOM_NODE_NEIGHBOR;

            final String targetLocation = args[1];
            final String outputFolderName = args[2];

            // iterate through the different size of graphs (from min to max)
            for(int size = minSize; size<=maxSize; size++) {
                // attempt maxNumQueries times for each size
                randomGeneration(targetLocation, outputFolderName, size, gamma, isInduced, maxNumQueries,
                        subgraphMethod);
            }
        }
        else if(mainMethod.equals("RandomGraphWithProp") && args.length == 5){
            final String targetLocationName = args[1];
            String outputFolderName = args[2]; // NOTE: output is different than previous functions

            // properties of query graph
            double de = Double.parseDouble(args[3]);
            double di = Double.parseDouble(args[4]);
            List<Double> avgD = new ArrayList<>(List.of(de, de + 1));
            List<Double> dia = new ArrayList<>(List.of(di, di + 1));

            File targetLocation = new File(targetLocationName);
            Graph<Vertex, DefaultEdge> target = readGraph(targetLocation, formatTarget);
            if (target == null) {
                System.out.println("Target File: ");
                System.out.println(noGraphFormat);
                return;
            }

            BufferedWriter writer = new BufferedWriter(new FileWriter(
                    outputFolderName+"info.txt"));
            writer.write("Target Graph: "+ targetLocation+"\n");
            writer.append("Degree: "+ de+", Diameter: "+di+"\n");
            writer.close();

            for(int x=minSize; x<maxSize; x++) {
                // the number of nodes between 10 and given value, with 10 increments (total given value/10)
                int size = x%(maxSize);;

                System.out.println(size +"======");
                constructRandomGraphWithProp(target, outputFolderName, maxNumQueries, maxNumFailedProp, size,
                        avgD, dia, subgraphMethods);
                System.out.println();
            }
        }
        // find graphs that are outliers when comparing number of matchings
        else if(mainMethod.equals("ConstructHardToFindGraphs") && args.length == 3){
            final String targetLocationName = args[1];
            String outputFolderName = args[2];

            // create the target graph and random query graph
            File targetLocation = new File(targetLocationName);
            Graph<Vertex, DefaultEdge> target = readGraph(targetLocation, formatTarget);
            if(target == null){
                System.out.println("Target File: ");
                System.out.println(noGraphFormat);
                return;
            }
            //calculateStatistics(target);

            // iterate through the different size of graphs (from min to max)
            for(int size = minSize; size<=maxSize; size+=10) {
                System.out.println("Graph Size : "+size+"\n================================");

                for(double de = 1; de<=6; de++) {
                    for(double di = 1; di<=10; di++) {
                        System.out.println("Degree: "+de+", Diameter: "+di+"\n================");

                        // properties of query graph
                        List<Double> avgD = new ArrayList<>(List.of(de, de+1));
                        List<Double> dia = new ArrayList<>(List.of(di, di+1));
                        List<Double> den = null;
                        List<Double> numLabels = null;

                        randomGenerationWithEstimate(target, targetLocation, outputFolderName, size, gamma, tau, maxEpoch,
                                zScore, isInduced, maxNumQueries, maxNumAttempts, maxNumFailedProp, avgD, dia, den, numLabels,
                                subgraphMethods);
                    }
                }
            }
        }
        else if (mainMethod.equals("PropRandomWalkEstimation")  && args.length == 4){
            final String targetLocationName = args[1];
            String outputFolderName = args[2];
            int x = Integer.parseInt(args[3]); //give a value between 0 and 899

            // the number of nodes between 10 and given value, with 10 increments (total given value/10)
            int size = 150;
            for (int i = 60; i < 60 * size; i += 60) {
                if (x < i) {
                    size = i / 60 * 10;
                    break;
                }
            }
            // the average degree between 1 and 6
            double de = 6;
            if (x % 60 < 10) {
                de = 1;
            } else if (x % 60 < 20) {
                de = 2;
            } else if (x % 60 < 30) {
                de = 3;
            } else if (x % 60 < 40) {
                de = 4;
            } else if (x % 60 < 50) {
                de = 5;
            }
            // the diameter between 1 and 10
            double di = x % 10 + 1;

            File targetLocation = new File(targetLocationName);
            Graph<Vertex, DefaultEdge> target = readGraph(targetLocation, formatTarget);
            if (target == null) {
                System.out.println("Target File: ");
                System.out.println(noGraphFormat);
                return;
            }

            // properties of query graph
            List<Double> avgD = new ArrayList<>(List.of(de, de + 1));
            List<Double> dia = new ArrayList<>(List.of(di, di + 1));
            List<Double> den = null;
            List<Double> numLabels = null;

            System.out.println("Size:"+size+", Diameter: "+di+", Degree: "+de);

            randomGenerationWithEstimate(target, targetLocation, outputFolderName, size, gamma, tau, maxEpoch,
                    zScore, isInduced, maxNumQueries, maxNumAttempts, maxNumFailedProp, avgD, dia, den, numLabels,
                    subgraphMethods);
        }
        else if(mainMethod.equals("ProbGraphWithProps")  && args.length == 3){
            final String targetLocationName = args[1];
            String outputFileName = args[2];
            //int x = Integer.parseInt(args[3]); //give a value between 0 and 899

            BufferedWriter writer = new BufferedWriter(new FileWriter(
                    outputFileName));
            writer.write("Total Number Queries "+ maxNumQueries+"\n");
            System.out.print("Total Number Queries "+ maxNumQueries+"\n");

            for(int x=0; x<360; x++) {
                // the number of nodes between 10 and given value, with 10 increments (total given value/10)
                int size = 600;
                for (int i = 6; i < 6 * size; i += 6) {
                    if (x < i) {
                        size = i / 6 * 10;
                        break;
                    }
                }
                // the average degree between 1 and 6
                double de = x%6+1;
                File targetLocation = new File(targetLocationName);
                Graph<Vertex, DefaultEdge> target = readGraph(targetLocation, formatTarget);
                if (target == null) {
                    System.out.println("Target File: ");
                    System.out.println(noGraphFormat);
                    return;
                }
                // properties of query graph
                List<Double> avgD = new ArrayList<>(List.of(de, de + 1));
                String output = "Size:" + size + ", Degree: " + de+ "---"+
                        probabilityCanFindRandomGraph(target, size, maxNumQueries, avgD, subgraphMethods)+"\n";
                System.out.print(output);
                writer.append(output);
            }
            writer.close();
        }


        // test against ground truth
        else if(mainMethod.equals("TestIsomorphism")  && args.length == 5){
            final String groundTruthFile = args[1];
            String queryFolderName = args[2];
            if(queryFolderName.equals("_")){
                queryFolderName = "";
            }
            String targetFolderName = args[3];
            if(targetFolderName.equals("_")){
                targetFolderName = "";
            }
            final String outputFileName = args[4];

            testAgainstGroundTruth(groundTruthFile, queryFolderName, targetFolderName, outputFileName, gamma);
        }

        // extra functions to fix previous values
        else if(mainMethod.equals("Average") && args.length == 2){
            final String isomorphismFolder = args[1];

            averageBacktrackingMatching(isomorphismFolder);
        }
        else if(mainMethod.equals("RewriteNames")  && args.length == 2){
            final String isomorphismFolder = args[1];

            rewriteName(isomorphismFolder);
        }

        else if(mainMethod.equals("Comparison") && args.length == 4){
            final String targetLocationName = args[1];
            String outputFolderName = args[2];
            String queryGraphFolder = args[3]; // use the query graphs created by RandomGraphWithProp

            File targetLocation = new File(targetLocationName);
            Graph<Vertex, DefaultEdge> target = readGraph(targetLocation, formatTarget);
            if (target == null) {
                System.out.println("Target File: ");
                System.out.println(noGraphFormat);
                return;
            }

            for(int x=0; x<(maxSize-minSize)*6; x++) {
                algorithmNameB = GRAPHQL;
                algorithmNamePO = GRAPHQL;
                algorithmNameC = GRAPHQL;
                // Backtracking
                if (x < (maxSize-minSize)) {
                    algorithmNameB = GRAPHQL;
                } else if (x < (maxSize-minSize)*2) {
                    algorithmNameB = QUICKSI;
                } else if (x < (maxSize-minSize)*3) {
                    algorithmNameB = DAF;
                } else if(x<(maxSize-minSize)*4) {
                    algorithmNameB = VEQS;
                }
                // Processing order
                else if (x<(maxSize-minSize)*5) {
                    algorithmNamePO = QUICKSI;
                } else {
                    algorithmNamePO = DYNAMIC_ORDER;
                }
                // the number of nodes between 10 and given value, with 10 increments (total given value/10)
                int size = x%(maxSize-minSize)+minSize;

                String runInfo = "B_" + algorithmNameB + "_PO_" + algorithmNamePO + "_C_" + algorithmNameC +
                        "_size_" + size;
                String outputFile = outputFolderName + runInfo+  ".txt";

                System.out.println(x+": "+runInfo);
                graphComparisonProperties(target, queryGraphFolder, outputFile, isInduced, gamma, maxNumQueries, size);
                System.out.println();
            }
        }
        else{
            System.out.println("Unknown Command.  Please use one of the following:"+
                    "\nKnownGraphs <queryFile> <targetFile> <isomorphismsFileName> <statisticsFile>"+
                    "\n\t Find the subgraph isomorphism between two know graphs."+
                    "\n\t Writes Isomorphisms to isomorphismsFileName and statistics to statisticsFile."+
                    "\nEstimate <queryFile> <targetFile> <outputFile>" +
                    "\n\t Find the estimate of the number of matchings between two graphs" +
                    "\n\t Writes estimation to outputFile"+
                    "\nTestEstimations <isomorphismFolder> <queryFolder> <targetFolder> <outputFile>" +
                    "\n\t Find the estimate of the number of matchings for all of the isomorphisms within the folder and compare with the actual" +
                    "\n\t Writes information to outputFile"+
                    "\n\t Must provide the location of the query and target folders.  If path is contained within " +
                    "isomorphism files, then give argument '_'."+
                    "\nFrequentDatasets <targetFile> <outputFile> <minSup>"+
                    "\n\t Finds the frequent profile subsets from the given graphs and minimum support."+
                    "\nFDMQuery <FDMFile> <outputFolder> <profileSize> <connectionMethod>"+
                    "\n\t Creates a query graph from the frequent dataset mining on a target graph of a given profile size."+
                    "\n\t Information on the frequent dataset mining within folder, which can be created with FrequentDatasets."+
                    "\n\t Find the subgraph isomorphism between given target graph and new query graph."+
                    "\n\t Output folder must contain folders: \"GenerationInfo\", \"Graphs\", \"Isomorphism\"."+
                    "\nRandomWalk <targetFile> <outputFolder>"+
                    "\n\t Creates a query graph from the target graph using a random walk." +
                    "\n\t Find the subgraph isomorphism between given target graph and random query graph"+
                    "\n\t Output folder must contain folders: \"GenerationInfo\", \"Graphs\", \"Isomorphism\""+
                    "\nRandomWalkWithProp <targetFile> <outputFolder> <de> <di>"+
                    "\n\t Creates query graphs from the target graph with given properties. " +
                    "\n\t The output folder will contain all the text files containing the query graphs. " +
                    "\n\t Will create maxNumQueries query graphs of different sizes." +
                    "\n\t NOTE: will output a lot of text file to output folder, does not follow the same convention as RandomWalk!"+
                    "\nConstructHardToFindGraphs <targetFile> <outputFolder>"+
                    "\n\t Creates a query graph from the target graph using a random walk and estimation." +
                    "\n\t Graphs who's estimation is an outlier compare to other random walks will be created."+
                    "\nConstructHardToFindGraphs <targetFile> <outputFolder>"+
                    "\n\t Creates a query graph from the target graph using a random walk and estimation. " +
                    "\n\t Graphs who's estimation is an outlier compare to other random walks will be created."+
                    "\nProbGraphWithProps <targetLocationName> <outputFileName>"+
                    "\n\t Finds the probability that we will be able to find query graphs of given size and average degree. " +
                    "\n\t Size will be between 10 and 600 in increments of 10, and degree will be between 1 and 7. " +
                    "\n\t Output the probabilities to the outputFile." +
                    "\nAverage <isomorphismFolder>"+
                    "\n\t Finds the average number of backtracking and matchings for given isomorphisms." +
                    "\nTestIsomorphism <groundTruthFile> <queryFolder> <targetFolder> <outputFile>"+
                    "\n\t Test the subgraph isomorphisms within the ground truth file."+
                    "\n\t Must provide the location of the query and target folders.  If path is contained within " +
                    "ground truth folder, then give argument '_'."+
                    "\n\t If there is any errors in the isomorphism it will be recorded in the output file."+
                    "\n Comparison <targetLocationName> <outputFolderName> <queryGraphsFolder>" +
                    "\n\t Compares the algorithms against each other, once for processing order and again for backtracking" +
                    "\n\t targetLocationName is the target graph and outputFolderName is where we will output the comparisons to." +
                    "\n\t The queryGraphsFolder contains all of the query graphs (Note: best to use RandomGraphWithProp output).");
        }

        // finish time
        Date endDate = new Date();

        System.out.println();
        System.out.println(mainMethod + " started at "+startDate);
        System.out.println(mainMethod + " ended at "+ endDate);
    }
}
