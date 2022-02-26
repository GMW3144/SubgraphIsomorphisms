// Graph Implementation
import org.jgrapht.*;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.alg.interfaces.MatchingAlgorithm;
import org.jgrapht.graph.*;
import org.jgrapht.traverse.BreadthFirstIterator;
import org.jgrapht.traverse.DepthFirstIterator;
import org.jgrapht.traverse.RandomWalkVertexIterator;
import org.jgrapht.alg.matching.HopcroftKarpMaximumCardinalityBipartiteMatching;

import java.io.*;
import java.util.*;

public class SubgraphIsomorphism {
    // the statistics
    private static int numBackTracking = -1; // keep track of backtracking calls
    private static int numLocalPruning = -1; // keep track of how much pruned locally
    private static int numGlobalPruned = -1; // keep track of how much pruned globally
    private static double totalCostGraphQL = -1; // keep track of the total cost when computing the order for GraphQL
    private static double falseMatchingParents = -1; // keep track of the vertices removed from parent in SEQq
    private static double falseMatchingExtraEdge = -1; // keep track of the vertices removed from extra edge in SEQq
    private static Map<List<Vertex>, Integer> numCombined = null; // keep track of the statistics when combine graphs
    private static String algorithmNameC = ""; // algorithm in use for candidates
    private static String algorithmNamePO = ""; // algorithm in use for processing order
    private static String algorithmNameB = ""; // algorithm in use for backtracking

    // algorithms
    // isomorphisms
    private static final String GROUNDTRUTH = "groundTruth";
    private static final String GRAPHQL = "graphQL";
    private static final String QUICKSI = "quickSI";
    // creating graphs
    private static final String MERGE = "merge";
    private static final String EDGE = "edge";
    private static final String NONE = "none";

    // error messages
    // error message if didn't find isomorphism algorithm
    private static final String noAlgorithmFound = "Algorithm specified is not valid.\n" +
            "Specify one of the following algorithms: \n" +
            "\t "+GROUNDTRUTH+": finds the ground truth isomorphism.  Only uses LDA in pruning and BFS for ordering.\n" +
            "\t "+GRAPHQL+": uses the GraphQL algorithm.\n" +
            "\t "+QUICKSI+": uses the QuickSI algorithm. (Note: cannot be used for processing candidates)\n";
    // error message if didn't find connection algorithm
    private static final String noConnectionMethodFound = "Connection type of graphs specified is not valid.\n " +
            "Specify one of the following connections methods: \n" +
            "\t "+MERGE+": merge two vertices of the same label.\n" +
            "\t "+EDGE+": create an edge between two vertices.\n " +
            "\t "+NONE+": use star graph of largest size.\n";
    // error message if threshold is too high
    private static final String thresholdToHigh = "Threshold too large for graph or graphs not connectable";
    // error message if minimum support is too high
    private static final String minSupToHigh = "Minimum support too large for graph";
    // the format for the graph files
    private static final String graphFileFormat = "Graph: <graphLocation> " +
            "\n Number of Nodes: <numberNodesInGraph> " +
            "\n Minsup (integer): <integerMinsup> " +
            "\n Minsup (percentage): <percentMinsup> " +
            "\n Attribute Label " +
            "\n <largeProfile> appears in <numAppearances> vertex profiles: " +
            "\n <listVerticesIds>";

    // keep track of axillary structures
    private static QISequence SEQq;

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
    private static String writeGraph(Graph<Vertex, DefaultEdge> graph, String outputFolderName,
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
    private static Graph<Vertex, DefaultEdge> createProteinGraph(File graphFile) throws IOException {
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
            g.addVertex(v);
            idToVertex.put(vID, v);

            // build the profile to include own label
            v.addToProfile(v);

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
                    g.addEdge(v1, v2);

                    // build the profile of each
                    v1.addToProfile(v2);
                    v2.addToProfile(v1);
                }

            }
            line = br.readLine();
        }
        br.close();

        return g;
    }

    /**
     * Checks if the main contains all of the subset elements.  Accounts for duplicates.
     * @param main the main array that contents is being checked
     * @param subset the subset array that is being check if subset of main
     * @return if main contains all the elements in subset
     */
    private static boolean listContainsAll(List<String> main, List<String> subset){
        // if there isn't enough elements in main
        if(main.size()<subset.size()){
            return false;
        }

        // assume that queryNodeProfile contained within profile
        boolean contains = true;
        int i = 0;
        int j = 0;

        // iterate through list
        while(j<main.size() && i<subset.size()){
            // if the query node label is greater then database label then exit
            // since well never find matching label
            if(subset.get(i).compareTo(main.get(j))<0){
                contains = false;
                break;
            }

            // if two values are equal then increment both, since we should consider next element
            else if(main.get(j).compareTo(subset.get(i))==0){
                i++; j++;
            }

            // there still may exist the value in set, so only increment database label
            else {
                j++;
            }

        }
        // if all values are contained within the profile of database node
        return contains && i == subset.size();
    }

    /**
     * Calculates the statistics for a given graph.
     * The number of subsets for a profile for each vertex
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
        return vDegree>=uDegree && u.sameLabel(v);
    }

    /**
     * Local Pruning: v is a candidate of u if u's profile is a subset of v's profile.  A profile is a lexicographically
     * sorted set of labels of the vertex
     * @param u a vertex from the query graph
     * @param v a vertex from the target graph
     * @return true if v is a candidate of u
     */
    private static boolean localPruning(Vertex u, Vertex v){
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
        List<Vertex> neighborsU = Graphs.neighborListOf(query, u); int sizeNeighbors = neighborsU.size();
        // if quickSI only look at extra edges
        if(algorithmNameB.equals(QUICKSI)){
            neighborsU = SEQq.getExtraEdges(u);
            falseMatchingExtraEdge+= (sizeNeighbors-neighborsU.size());
        }

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
            Set<Vertex> toCheck = currentFunction.keySet();
            // if quickSI already have information
            if(algorithmNameB.equals(QUICKSI)){
                toCheck = new HashSet<>(SEQq.getNoExtraEdges(u));
            }

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
    private static void subgraphIsomorphism(Graph<Vertex, DefaultEdge> query,
                                           Graph<Vertex, DefaultEdge> target,
                                           Map<Vertex, Set<Vertex>> candidates,
                                           ArrayList<Vertex> order, int i,
                                           Map<Vertex, Vertex> currentFunction,
                                           List<Map<Vertex, Vertex>> allFunctionsFound, boolean isInduced){
        // check if found solution
        if(currentFunction.size() == query.vertexSet().size()){
            allFunctionsFound.add(new HashMap<>(currentFunction));
        }
        else{
            // look at next node
            Vertex u = order.get(i);
            Set<Vertex> possibleVertices = new HashSet<>(candidates.get(u));

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

            // look at candidates
            for(Vertex v : possibleVertices){
                // looking at new element
                numBackTracking+=1;
                // check not in another mapping
                if(!currentFunction.containsValue(v) && isValid(query, target, currentFunction, u, v, isInduced)){
                    currentFunction.put(u, v);
                    subgraphIsomorphism(query, target, candidates, order, i+1, currentFunction, allFunctionsFound,
                            isInduced);
                    currentFunction.remove(u);
                }
            }
        }
    }

    /**
     * Compute the candidates for given query graph and target graph
     * @param query the query graph
     * @param target the target graph
     * @return the candidates
     */
    private static Map<Vertex, Set<Vertex>> computeCandidates(Graph<Vertex, DefaultEdge> query,
                                                              Graph<Vertex, DefaultEdge> target){
        Map<Vertex, Set<Vertex>> candidates;
        // compute the candidates
        switch (algorithmNameC) {
            // using ground truth
            case GROUNDTRUTH -> candidates = groundTruthComputeCandidates(query, target);
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
                                                           Map<Vertex, Set<Vertex>> candidates,
                                                           double gamma){
        ArrayList<Vertex> order;
        switch (algorithmNamePO) {
            case GROUNDTRUTH -> order = groundTruthComputeProcessingOrder(query, candidates);
            case GRAPHQL -> order = graphQLComputeProcessingOrder(query, candidates, gamma);
            case QUICKSI -> order = quickSIComputeProcessingOrder(target, query, candidates);
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
     * @return the solutions to the subgraph isomorphism between the given graphs
     */
    private static List<Map<Vertex, Vertex>> matching(Graph<Vertex, DefaultEdge> query,
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
        if(algorithmNameB.equals(GROUNDTRUTH) || algorithmNameB.equals(GRAPHQL) || algorithmNameB.equals(QUICKSI)) {
            if(algorithmNameB.equals(QUICKSI)){
                falseMatchingParents = 0;
                falseMatchingExtraEdge = 0;
            }
            if(algorithmNameB.equals(QUICKSI) && SEQq == null){
                SEQq = buildSpanningTreeWithOrder(query, order);
            }
            subgraphIsomorphism(query, target, candidates, order, 0, new HashMap<>(), results, isInduced);
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
    private static void displayIsomorphism(List<Map<Vertex, Vertex>>  subgraphIsomorphism,
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
        File targetFile = new File(targetFileLocation);

        // create the graphs
        Graph<Vertex, DefaultEdge> queryGraph = createProteinGraph(queryFile);
        Graph<Vertex, DefaultEdge> targetGraph = createProteinGraph(targetFile);

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
        displayIsomorphism(subgraphIsomorphism, queryFileLocation, targetFileLocation, writer, isInduced);
        System.out.println("============================");
        writer.append("============================\n");
        writer.close();

        // write to statistics file
        writer = new BufferedWriter(new FileWriter(outputStatisticsName));
        writer.write("");
        displayGraphStatistics(queryFileLocation, queryGraph, targetFileLocation, targetGraph, writer);
        writer.close();
    }

    /**
     * A function that will copy a vertex and create a new one
     * @param vertex the vertex we are copying
     * @param newId the id of the new vertex
     * @return the copied vertex
     */
    private static Vertex copyVertex(Vertex vertex, int newId){
        // copy the attributes
        return new Vertex(newId, vertex.getLabel());
    }

    /**
     * Create a new graph by performing a random walk on the target graph
     * @param target target graph
     * @param targetLocation the location of the target graph
     * @param sizeQuery the maximum number of vertices in the query
     * @param writer where we'll write information about the graph construction
     * @return the random graph
     * @throws IOException for file writer
     */
    private static Graph<Vertex, DefaultEdge> randomGraph(Graph<Vertex, DefaultEdge> target, String targetLocation,
                                                         int sizeQuery, BufferedWriter writer) throws IOException {
        Graph<Vertex, DefaultEdge> queryGraph = new SimpleGraph<>(DefaultEdge.class);
        // get a random vertex
        Random rand = new Random();
        int randVertexID = rand.nextInt(target.vertexSet().size());
        Vertex randVertex = target.vertexSet().stream().filter(vertex -> vertex.getId() == randVertexID).findAny().get();

        // keep track of equivalencies, so know when see a target vertex again
        Map<Vertex, Vertex> seen = new HashMap<>();

        // random walk starting at random vertex
        Iterator<Vertex> iter = new RandomWalkVertexIterator(target, randVertex);
        int currentId = 0;
        // get the starting vertex, and create a copy
        Vertex lastVertex = iter.next(); Vertex lastVertexCopy = copyVertex(lastVertex, currentId);
        seen.put(lastVertex, lastVertexCopy);

        // the maximum amount of vertices will check
        int maxIteration = 100000;

        // create a new vertex, by copying info
        queryGraph.addVertex(lastVertexCopy);
        // build the profile to include own label
        lastVertexCopy.addToProfile(lastVertexCopy);

        // perform the walk
        while(iter.hasNext()) {
            // keeps it from getting stuck in an infinite loop
            maxIteration--;
            if(maxIteration<0){
                break;
            }

            currentId = seen.size();
            // stop when reach given size
            if(currentId>=sizeQuery){
                break;
            }

            // get the next vertex and its edge
            Vertex nextVertex = iter.next(); Vertex nextVertexCopy = copyVertex(nextVertex, currentId);

            // if we have already seen it, then use the previously made copy vertex
            if(seen.containsKey(nextVertex)){
                nextVertexCopy = seen.get(nextVertex);
            }
            // if we haven't seen it, then add new vertex to query graph
            else {
                seen.put(nextVertex, nextVertexCopy);
                queryGraph.addVertex(nextVertexCopy);
                // build the profile to include own label
                nextVertexCopy.addToProfile(nextVertexCopy);
            }

            // only add edge if haven't seen it before in query
            if(!queryGraph.containsEdge(lastVertexCopy, nextVertexCopy)) {
                queryGraph.addEdge(lastVertexCopy, nextVertexCopy);

                // build the profile of each
                lastVertexCopy.addToProfile(nextVertexCopy);
                nextVertexCopy.addToProfile(lastVertexCopy);
            }

            // keep track of last vertex to create edge
            lastVertexCopy = nextVertexCopy;
        }

        // write the mappings
        // write to output file info when constructing graph
        writer.write(targetLocation + " \n");
        writer.append(seen.toString()).append("\n");
        for(Vertex targetVertex: seen.keySet()){
            writer.append(String.valueOf(targetVertex.getId())).append(" ")
                    .append(String.valueOf(targetVertex.getNumProfileSubsets())).append("\n");
        }

        return queryGraph;
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
                Graph<Vertex, DefaultEdge> query = createProteinGraph(queryGraphFile);
                Graph<Vertex, DefaultEdge> target = createProteinGraph(targetGraphFile);


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
     * Performs apriori generation on a given large itemset.  Given that the large itemsets are of size k-1, it will
     * create candidates of size k
     * @param LkMin1 large itemsets of size k-1
     * @return the candidates generated from the large itemsets
     */
    private static List<List<String>> aprioriGen(List<List<String>> LkMin1){
        List<List<String>>Ck = new ArrayList<>();

        // iterate through the possible joins
        for(int i = 0; i< LkMin1.size(); i++){
            List<String> itemsetI = LkMin1.get(i);
            for(int j = i; j< LkMin1.size(); j++){
                List<String> itemsetJ = LkMin1.get(j);

                // already in order so combine two
                List<String> newItemset = new ArrayList<>();

                boolean equivalentStart = (itemsetI.size() == itemsetJ.size());
                // make sure the first elements are equivalent
                for(int k = 0; k<itemsetI.size()-1; k++){
                    // if find an element not equivalent
                    if(!itemsetI.get(k).equals(itemsetJ.get(k))){
                        equivalentStart = false;
                        break;
                    }
                    newItemset.add(itemsetI.get(k));
                }

                // if the beginning isn't equal then the rest of the itemsetJ cannot be either
                if(!equivalentStart){
                    break;
                }

                // add from itemsetI
                newItemset.add(itemsetI.get(itemsetI.size()-1));
                // add from itemsetJ
                newItemset.add(itemsetJ.get(itemsetJ.size()-1));

                // then add to potentially large itemsets
                Ck.add(newItemset);
            }
        }

        return Ck;
    }

    /**
     * Prune the large itemset candidates based off of the previous large itemsets.
     * @param LkMin1 The large itemsets of size k-1
     * @param Ck the candidate set containing itemsets of size k
     */
    private static void aprioriPrune(List<List<String>> LkMin1, List<List<String>>Ck){

        // keep track of which candidates to remove
        List<List<String>> toRemove = new ArrayList<>();
        // check each cK subsets to see if in LkMin1
        for (List<String> C : Ck) {
            List<String> subset = new ArrayList<>(C);
            // build subsets of size k-1
            for (String element : C) {
                // remove one of the elements
                subset.remove(element);
                // check if subset is in previous large itemises
                if (!LkMin1.contains(subset)) {
                    toRemove.add(C);
                    break;
                }
                // add the element back in
                subset.add(element);
                // sort it back in correctly
                Collections.sort(subset);
            }
        }

        // now remove the candidates
        for(List<String> c:toRemove){
            Ck.remove(c);
        }

    }

    /**
     * Perform apriori algorithm on the given transactions and attributes.  Also must provide the possible items and
     * minimum support
     * @param transactions the set of transactions within the database
     * @param items the set of possible items within the transactions
     * @param minSup the minim support for the association rules
     * @return the large itemsets (profiles)
     */
    private static Map<List<String>, Set<Integer>>  aprioriAlgo(Map<Integer, List<String>> transactions,
                                                               Set<String> items, double minSup){
        // make minSup related to a number of vertices
        if(minSup<=1){
            minSup = minSup*transactions.size();
        }

        // find large profile itemsets (Profile, Vertices containing profile)
        Map<List<String>, Set<Integer>> L = new HashMap<>();

        // L1
        List<List<String>> LkMin1 = new ArrayList<>();
        // iterate through the items
        for(String item: items){
            ArrayList<String> c1 = new ArrayList<>();
            c1.add(item);

            Set<Integer> transactionsContainC1 = new HashSet<>();

            // iterate through the transactions
            for(int tid: transactions.keySet()){
                List<String> t = transactions.get(tid);

                if(listContainsAll(t, c1)){
                    transactionsContainC1.add(tid);
                }
            }
            if(transactionsContainC1.size()>minSup){
                L.put(c1, transactionsContainC1);
                LkMin1.add(c1);
            }
        }

        // now continue until no more large datasets of a given size
        while(LkMin1.size() != 0){
            // iterate through the previous L_k-1 values to generate new set
            List<List<String>> Ck = aprioriGen(LkMin1);
            // prune the candidates
            aprioriPrune(LkMin1, Ck);
            // reset the past LkMin1
            LkMin1 = new ArrayList<>();

            // iterate through the candidates
            for(List<String> C: Ck) {

                Set<Integer> transactionsContainC = new HashSet<>();

                // iterate through the transactions
                for (int tid : transactions.keySet()) {
                    List<String> t = transactions.get(tid);

                    if (listContainsAll(t, C)) {
                        transactionsContainC.add(tid);
                    }
                }
                if(transactionsContainC.size()>minSup){
                    L.put(C, transactionsContainC);
                    LkMin1.add(C);
                }
            }

        }

        return L;
    }

    /**
     * Convert the graphs profiles into a transactional database.  Then perform apriori algorithm on the new database
     * @param targetFileLocation the location of the target graph
     * @param outputFileName where we will output the findings
     * @param minSup the minimum support
     * @throws IOException for read/write files
     */
    private static void frequentDatasetMining(String targetFileLocation, String outputFileName, double minSup)
            throws IOException {
        // read the info from the file
        File targetFile = new File(targetFileLocation);

        // write to output file
        BufferedWriter writer = new BufferedWriter(new FileWriter(outputFileName));
        writer.write("");

        // create the graphs
        Graph<Vertex, DefaultEdge> targetGraph = createProteinGraph(targetFile);

        // retrieve the profile information from the target graph
        // vertex and profile - transaction
        Map<Integer, List<String>> transactions = new HashMap<>();
        // keep track of itemset
        Set<String> possibleItems = new HashSet<>();

        // iterate through the vertices
        Iterator<Vertex> iter = new DepthFirstIterator<>(targetGraph);
        while (iter.hasNext()) {
            // get the graph vertex
            Vertex v = iter.next();
            int vid = v.getId();

            List<String> vProfile= v.getProfile();
            transactions.put(vid, vProfile);

            // iterate through the vertex attributes
            // add to the possible label set
            possibleItems.addAll(vProfile);
        }

        Map<List<String>, Set<Integer>>  frequentItemsets = aprioriAlgo(transactions, possibleItems, minSup);

        // print out the information about the variables
        if(minSup<=1){
            minSup = minSup*transactions.size();
        }
        String graphInfo = "Graph: "+targetFile.getName()+ "("+targetFileLocation+")"+
                "\nNumber of Nodes: "+transactions.size()+
                "\nMinimum Support (integer): "+minSup+
                "\nMinimum Support (percentage): "+minSup/transactions.size();
        System.out.println(graphInfo);
        writer.append(graphInfo).append("\n");

        if(frequentItemsets.isEmpty()){
            System.out.println(minSupToHigh);
            writer.write(minSupToHigh);
            writer.close();
            return;
        }

        // keep track of the union of all the frequent profiles
        List<String> outputValues = new ArrayList<>();
        for(List<String> itemset : frequentItemsets.keySet()){
            outputValues.add(itemset + " appears in " +frequentItemsets.get(itemset).size()+" vertex profiles:\n"
                    +frequentItemsets.get(itemset)+" \n\n");
        }
        // sort the frequent profiles and print in order
        Collections.sort(outputValues);
        for(String output: outputValues){
            for(int i = 0; i<output.length(); i++){
                char c = output.charAt(i);
                if(c == ']'){
                    break;
                }
                System.out.print(c);
            }
            int numOccurrences = 0;
            for(String word: output.split(" ")){
                try{
                    numOccurrences = Integer.parseInt(word);
                    break;
                }
                catch (NumberFormatException ignored){
                }
            }
            System.out.println("]"+":"+numOccurrences);
            writer.append(output);
        }

        writer.close();
    }

    /**
     * Given star graphs and the number of times they occur within the target graph, return the index of the most
     * frequent star graph
     * @param starGraphs the star graphs
     * @param starGraphsProfiles the profile of the root of the star graph
     * @param numberTimesRootOccurs the number of times the star graph of a given profile occurs
     * @return the index of the most frequent star graph
     */
    public static int findMostFrequentStructure(List<Graph<Vertex, DefaultEdge>> starGraphs,
                                                List<List<String>> starGraphsProfiles,
                                                Map<List<String>, List<Vertex>> numberTimesRootOccurs){

        // keep track of most frequent graph
        Graph<Vertex, DefaultEdge> mostFrequentStarGraph = null;
        int mostFrequent = -1;
        int location = -1;

        // iterate through the graphs and appropriate information
        for(int i = 0; i<starGraphs.size(); i++){
            Graph<Vertex, DefaultEdge> graph = starGraphs.get(i);
            List<String> profile = starGraphsProfiles.get(i);
            int numberOccurrences = numberTimesRootOccurs.get(profile).size();

            if(mostFrequentStarGraph == null || numberOccurrences>mostFrequent){
                mostFrequentStarGraph = graph;
                mostFrequent = numberOccurrences;
                location = i;
            }
        }

        return location;
    }

    /**
     * For a given graph find the leaf nodes, which are vertices with only one neighbor
     * @param graph the graph in question
     * @return leaf nodes of the graph
     */
    public static List<Vertex> findLeafNodes(Graph<Vertex, DefaultEdge> graph){
        // the leaf nodes
        List<Vertex> leaf = new ArrayList<>();
        // iterate through vertices and only included vertices of degree 1
        for(Vertex u: graph.vertexSet()) {
            if(graph.degreeOf(u) == 1){
                leaf.add(u);
            }
        }
        return leaf;
    }

    /**
     * Add graph to existing graph by copying vertices and edges
     * @param combinedGraph the graph we are adding to
     * @param graph the graph we are adding
     * @param id the next free node id we may use
     * @param oldToNew a mapping from the vertices in the previous graph to the new graph
     * @return the last id used
     */
    public static int addSubgraph(Graph<Vertex, DefaultEdge> combinedGraph, Graph<Vertex, DefaultEdge> graph, int id,
                                     Map<Vertex, Vertex> oldToNew){

        // add vertices to graph
        for(Vertex v: graph.vertexSet()){
            Vertex copyVertex = copyVertex(v, id);
            combinedGraph.addVertex(copyVertex); copyVertex.addToProfile(copyVertex);
            oldToNew.put(v, copyVertex);
            id++;
        }

        // add original edges back in
        for(Vertex v: graph.vertexSet()){
            for(Vertex u: Graphs.neighborListOf(graph, v)) {
                Vertex vP = oldToNew.get(v);
                Vertex uP = oldToNew.get(u);
                if(!combinedGraph.containsEdge(vP, uP)) {
                    combinedGraph.addEdge(vP, uP);

                    vP.addToProfile(uP);
                    uP.addToProfile(vP);
                }
            }
        }
        return id;
    }

    /**
     * Union two graphs by combining two vertices of the same label into one
     * @param target the target graph
     * @param graph1 the first graph to merge
     * @param graph2 the other graph to merge
     * @param graph1Roots the vertices in the target graph that are the root of stargraph1
     * @param graph2Roots the vertices in the target graph that are the root of stargraph2
     * @param threshold the number of edges that must exist in order to be included
     * @return a new graph that merges the two given graphs
     */
    public static Graph<Vertex, DefaultEdge> unionGraphsByMerge(Graph<Vertex, DefaultEdge> target,
                                                                Graph<Vertex, DefaultEdge> graph1,
                                                                Graph<Vertex, DefaultEdge> graph2,
                                                                List<Vertex> graph1Roots, List<Vertex> graph2Roots,
                                                                double threshold){
        Graph<Vertex, DefaultEdge> combinedGraph = new SimpleGraph<>(DefaultEdge.class);
        Map<Vertex, Vertex> oldToNew = new HashMap<>();
        // add the vertices and edges of individual graphs to the combined graph
        int id = 0;
        id = addSubgraph(combinedGraph,  graph1,  id, oldToNew);
        addSubgraph(combinedGraph, graph2, id, oldToNew);

        List<Vertex> leaf1 = findLeafNodes(graph1);
        // iterate through vertices of graph1
        List<Vertex> leaf2 = findLeafNodes(graph2);
        List<List<Vertex>> possibleMerge = new ArrayList<>();
        // iterate through the possible leaf merging
        for(Vertex l1: leaf1) {
            for (Vertex l2 : leaf2) {
                if (!l1.sameLabel(l2)) {
                    continue;
                }
                possibleMerge.add(Arrays.asList(oldToNew.get(l1), oldToNew.get(l2)));
            }
        }

        // keep track of the vertices to merge (possibly)
        Map<List<Vertex>, Integer> possibleVerticesToMerge = new HashMap<>();

        // iterate through the two roots
        for(Vertex root1: graph1Roots){
            Set<Vertex> neighbors1 = Graphs.neighborSetOf(target, root1);
            for(Vertex root2: graph2Roots){
                // each star graph should be mapped to individual roots
                if(root1==root2){
                    continue;
                }
                Set<Vertex> neighbors2 = Graphs.neighborSetOf(target, root2);

                // get their common vertices
                Set<Vertex> commonNeighbors = new HashSet<>(neighbors1);
                commonNeighbors.retainAll(neighbors2);

                // if there are no common neighbors then continue
                if(commonNeighbors.size() == 0) continue;

                // iterate through the possible leaf pairings
                for(List<Vertex> merge: possibleMerge) {
                    Vertex l1 = merge.get(0);
                    // iterate through common neighbors
                    for (Vertex n : commonNeighbors) {
                        // check that the common neighbor has the same label
                        if (!n.sameLabel(l1)) {
                            continue;
                        }

                        // count the number of times can merge a given vertex
                        if (!possibleVerticesToMerge.containsKey(merge)) {
                            possibleVerticesToMerge.put(merge, 1);
                        } else {
                            possibleVerticesToMerge.put(merge, possibleVerticesToMerge.get(merge) + 1);
                        }
                    }
                }
            }
        }

        if(possibleVerticesToMerge.size() == 0){
            return null;
        }

        HashMap<List<Vertex>, Integer> verticesToMerge = new HashMap<>();
        // clean up vertices to merge
        for(List<Vertex> merge: possibleVerticesToMerge.keySet()){
            Vertex v1 = merge.get(0);
            Vertex v2 = merge.get(1);

            boolean conflict = false;
            // iterate through previous merges
            for(List<Vertex> previousMerge: verticesToMerge.keySet()){
                if(previousMerge.contains(v1) || previousMerge.contains(v2)){
                    if(verticesToMerge.get(previousMerge)<possibleVerticesToMerge.get(merge)){
                        verticesToMerge.remove(previousMerge);
                        verticesToMerge.put(merge, possibleVerticesToMerge.get(merge));
                    }
                    conflict = true;
                }
            }
            if(!conflict && possibleVerticesToMerge.get(merge)>threshold){
                verticesToMerge.put(merge, possibleVerticesToMerge.get(merge));
            }
        }

        if(verticesToMerge.size() == 0){
            return null;
        }

        // union the two most likely vertices
        // update the neighbors profiles from removing the vertex
        // add in new edge
        for(List<Vertex> merge : verticesToMerge.keySet()) {
            Vertex v1 = merge.get(0);
            Vertex v2 = merge.get(1);
            for (Vertex v : Graphs.neighborListOf(combinedGraph, v1)) {
                // remove maxV1 the profile
                v.removeFromProfile(v1);

                // add new edge between vertex and maxV2, update profile
                combinedGraph.addEdge(v2, v);
                v.addToProfile(v2);
                v2.addToProfile(v);
            }
            // remove the vertex in each
            combinedGraph.removeVertex(v1);
            numCombined.put(merge, verticesToMerge.get(merge));
        }

        return combinedGraph;
    }


    /**
     * Union two graphs by combining two vertices of the same label into one
     * @param target the target graph
     * @param graph1 the first graph to merge
     * @param graph2 the other graph to merge
     * @param graph1Roots the vertices in the target graph that are the root of stargraph1
     * @param graph2Roots the vertices in the target graph that are the root of stargraph2
     * @param threshold the number of edges that must exist in order to be included
     * @return a new graph that merges the two given graphs
     */
    public static Graph<Vertex, DefaultEdge> unionGraphsByEdge(Graph<Vertex, DefaultEdge> target,
                                                               Graph<Vertex, DefaultEdge> graph1,
                                                               Graph<Vertex, DefaultEdge> graph2,
                                                               List<Vertex> graph1Roots, List<Vertex> graph2Roots,
                                                               double threshold){
        Graph<Vertex, DefaultEdge> combinedGraph = new SimpleGraph<>(DefaultEdge.class);
        Map<Vertex, Vertex> oldToNew = new HashMap<>();
        // add the vertices and edges to the combined graph
        int id = 0;
        id = addSubgraph(combinedGraph,  graph1,  id, oldToNew);
        addSubgraph(combinedGraph, graph2, id, oldToNew);

        List<Vertex> leaf1 = findLeafNodes(graph1);
        // keep track of the vertices of a given label
        Map<String, List<Vertex>> vertexOfLabel1 = new HashMap<>();
        for(Vertex l1: leaf1){
            if(!vertexOfLabel1.containsKey(l1.getLabel())){
                vertexOfLabel1.put(l1.getLabel(), new ArrayList<>());
            }
            vertexOfLabel1.get(l1.getLabel()).add(oldToNew.get(l1));
        }
        // iterate through vertices of graph1
        List<Vertex> leaf2 = findLeafNodes(graph2);
        // keep track of the vertices of a given label
        Map<String, List<Vertex>> vertexOfLabel2 = new HashMap<>();
        for(Vertex l2: leaf2){
            if(!vertexOfLabel2.containsKey(l2.getLabel())){
                vertexOfLabel2.put(l2.getLabel(), new ArrayList<>());
            }
            vertexOfLabel2.get(l2.getLabel()).add(oldToNew.get(l2));
        }

        // keep track of the vertices to merge (possibly)
        Map<List<String>, Integer> possibleEdges = new HashMap<>();

        // iterate through the two roots
        for(Vertex root1: graph1Roots) {
            Set<Vertex> neighbors1 = Graphs.neighborSetOf(target, root1);
            // only keep the neighbors with the profile of graph1
            neighbors1.removeIf(n1 -> !vertexOfLabel1.containsKey(n1.getLabel()));

            // get the neighbors of
            for (Vertex root2 : graph2Roots) {
                Set<Vertex> neighbors2 = Graphs.neighborSetOf(target, root2);
                // only keep the neighbors with the profile of graph1
                neighbors2.removeIf(n2 -> !vertexOfLabel2.containsKey(n2.getLabel()));

                // now we must iterate through possible edges
                for(Vertex n1: neighbors1){
                    for(Vertex n2: neighbors2){
                        // avoid double counting
                        if(n1 == root2 || n2 == root1){
                            continue;
                        }

                        // if there exists an edge
                        if(target.containsEdge(n1, n2)){
                            // add an edge with the two labels
                            List<String> newEdge = new ArrayList<>();
                            newEdge.add(n1.getLabel());
                            newEdge.add(n2.getLabel());

                            // if a new edge
                            if(!possibleEdges.containsKey(newEdge)){
                                possibleEdges.put(newEdge, 1);
                            }
                            // if we have seen the edge before
                            else{
                                possibleEdges.put(newEdge, possibleEdges.get(newEdge)+1);
                            }

                        }
                    }
                }
            }
        }

        // if there are no edges then return null
        if(possibleEdges.isEmpty()){
            return null;
        }

        // only keep edges past a threshold
        for(List<String> edge : new HashSet<>(possibleEdges.keySet())) {
            if (possibleEdges.get(edge) < threshold) {
                possibleEdges.remove(edge);
            }
        }

        // if there are no edges then return null
        if(possibleEdges.isEmpty()){
            return null;
        }

        // otherwise update the graph
        List<List<String>> sortedEdges = new ArrayList<>();
        possibleEdges.entrySet().stream()
                .sorted(Map.Entry.comparingByValue(Comparator.reverseOrder())).forEachOrdered(x->sortedEdges.add(x.getKey()));
        for(List<String> edge: sortedEdges){
            List<Vertex> v1Choices = vertexOfLabel1.get(edge.get(0));
            if(v1Choices.isEmpty()){
                continue;
            }
            List<Vertex> v2Choices = vertexOfLabel2.get(edge.get(1));
            if(v2Choices.isEmpty()){
                continue;
            }

            Vertex v1 = v1Choices.remove(0);
            Vertex v2 = v2Choices.remove(0);

            combinedGraph.addEdge(v1, v2);
            v1.addToProfile(v2);
            v2.addToProfile(v1);

            List<Vertex> edgeInfo = new ArrayList<>();
            edgeInfo.add(v1); edgeInfo.add(v2);
            numCombined.put(edgeInfo, possibleEdges.get(edge));
        }

        return combinedGraph;
    }

    /**
     * Creates a graph from the frequent dataset mining and performs subgraph isomorphism on the new query graph and
     * target graph from the frequent dataset mining
     *
     * @param fdmFileLocation the information from the frequent dataset mining
     * @param outputFolderName location where saving graph information
     * @param isInduced if the isomorphism is induced
     * @param profileSize the size of the profile for the frequent itemset
     * @param gamma the gamma value
     * @param connectionMethod the method we will connect the two graphs (merge/edge)
     * @throws IOException for reader
     */
    public static void fdmGraph(String fdmFileLocation, String outputFolderName, boolean isInduced, int profileSize,
                                double gamma, String connectionMethod) throws IOException {
        // get the information from the frequent dataset mining file
        Graph<Vertex, DefaultEdge> target = null; // target graph
        String graphLocation = ""; // location of target graph
        Map<List<String>, List<Integer>> frequentProfiles = new HashMap<>(); // the frequent profiles of a given size
        double minsup = 0.0; // the minimum support

        BufferedReader br = new BufferedReader(new FileReader(fdmFileLocation));
        String line = br.readLine().strip();
        while(line!=null){
            line = line.strip();
            // check if comment
            if(line.length()>0 && line.charAt(0) == '#'){
                line = br.readLine();
                continue;
            }

            // start of a new isomorphism
            else if(line.toLowerCase(Locale.ROOT).contains("graph:")){
                String graphInfo = line.split(" ")[1];
                graphLocation = graphInfo.split("\\(")[1].replace(")", "");
                target = createProteinGraph(new File(graphLocation));
            }

            // information on the maximum support
            else if(line.toLowerCase(Locale.ROOT).contains("minsup (integer):")) {
                minsup = Double.parseDouble(line.split(":")[1].strip());
            }

            // start of new itemset
            else if(line.length()>0 && line.charAt(0) == '['){
                List<String> currentItemset = new ArrayList<>();
                // iterate through the words within the line
                for(String item: line.split(" ")){
                    // found the end of the itemset
                    if(item.contains("]")){
                       // remove the separator
                       item = item.strip().replace("]", "").replace(",","");
                       currentItemset.add(item);
                       break;
                    }
                    // remove the separator
                    item = item.strip().replace("[", "").replace(",","");
                    currentItemset.add(item);
                }
                // get the vertices that contain profile
                line = br.readLine().strip();
                // check if comment
                while(line.length()>0 &&  line.charAt(0) == '#'){
                    line = br.readLine().strip();
                }

                List<Integer> verticesId = new ArrayList<>();
                // iterate through the words within the line
                for(String v: line.split(" ")){
                    // found the end of the itemset
                    if(v.contains("]")){
                        // remove the separator
                        v = v.strip().replace("]", "").replace(",","");
                        verticesId.add(Integer.parseInt(v));
                        break;
                    }
                    // remove the separator
                    v = v.strip().replace("[", "").replace(",","");
                    verticesId.add(Integer.parseInt(v));
                }

                // only add if the size of the items (profile) is equivalent the the profile size we are looking for
                if(currentItemset.size() == profileSize) {
                    frequentProfiles.put(currentItemset, verticesId);
                }
            }
            line = br.readLine();
        }

        // check if found a target
        if(target == null){
            System.out.println("No target graph found.  Format as follows:\n" +graphFileFormat);
            return;
        }

        // keep track of the vertices we have seen
        Map<Integer, Vertex> seen = new HashMap<>();

        // keep track of the structure of the frequent profiles
        Map<List<String>, String> frequentProfileShapes = new HashMap<>();
        // keep track of the number of times the root occurs
        Map<List<String>, List<Vertex>> verticesRootOccurs = new HashMap<>();

        // look through the graph for each profile (and their vertices to see the structure)
        // iterate through the frequent profiles
        for(List<String> profile: frequentProfiles.keySet()){
            Map<String, List<Vertex>> rootVertices = new HashMap<>();

            // iterate through the vertices it appears in
            for(Integer vID: frequentProfiles.get(profile)){
                // convert the id to a vertex
                Vertex v;
                // if seen before then get the vertex
                if(seen.containsKey(vID)){
                    v = seen.get(vID);
                }
                else{
                    v =  target.vertexSet().stream().filter(vertex -> vertex.getId() == vID).findAny().get();
                    seen.put(vID, v);
                }

                // keep track of the attribute of the vertex, and number of times it occurs
                String label = v.getLabel();

                // if haven't seen root attribute, then add to map
                if(!rootVertices.containsKey(label)){
                    List<Vertex> vertexWithRoot = new ArrayList<>();
                    vertexWithRoot.add(v);
                    rootVertices.put(label, vertexWithRoot);
                }
                // if have seen root, then increment number of occurrences
                else{
                    rootVertices.get(label).add(v);
                }
            }

            // select the attribute (root) that occurs the most
            String root = rootVertices.keySet().iterator().next();
            for(String currentRoot: rootVertices.keySet()){
                // if there are more of the current root then replace
                if(rootVertices.get(root).size()<rootVertices.get(currentRoot).size()){
                    root = currentRoot;
                }
            }

            // add the root that is most frequent to the frequent profile shapes if it meets the maximum support
            if(rootVertices.get(root).size()>=minsup) {
                frequentProfileShapes.put(profile, root);
                verticesRootOccurs.put(profile, rootVertices.get(root));
            }
        }

        // now we have the star shapes of the profiles
        System.out.println(frequentProfileShapes);
        // store the graphs to union
        List<Graph<Vertex, DefaultEdge>> starGraphs = new ArrayList<>();
        List<List<String>> starGraphsProfiles = new ArrayList<>();
        // keep track of the vertex id, want all to be different
        int currentId = 0;

        // build query graphs from the star shaped query graphs
        for(List<String> profile : frequentProfileShapes.keySet()) {
            // get the root vertex
            String rootLabel = frequentProfileShapes.get(profile);
            // get the neighbor vertex
            List<String> neighbors = new ArrayList<>(profile);
            neighbors.remove(rootLabel);

            Graph<Vertex, DefaultEdge> query = new SimpleGraph<>(DefaultEdge.class);

            // add the root
            Vertex root = new Vertex(currentId, rootLabel);
            query.addVertex(root);
            root.addToProfile(root);

            currentId++;
            // add the other vertices and their edges
            for (String neighborLabel : neighbors) {
                // add the vertex, update profile
                Vertex neighbor = new Vertex(currentId, neighborLabel);
                query.addVertex(neighbor);
                neighbor.addToProfile(neighbor);

                // add the edge, update profile
                query.addEdge(root, neighbor);
                root.addToProfile(neighbor);
                neighbor.addToProfile(root);

                currentId++;
            }

            starGraphs.add(query); starGraphsProfiles.add(profile);
        }

        // store important information when using query graph
        File outputGraphFolder = new File(outputFolderName + "Graphs\\");
        int numGraphs = 0;
        if (outputGraphFolder.list() != null) {
            numGraphs = outputGraphFolder.list().length;
        }
        String graphName = "graph" + (numGraphs + 1) + ".txt";


        // keep track of two most frequent graph
        int locationStarGraph1 = findMostFrequentStructure(starGraphs, starGraphsProfiles, verticesRootOccurs);
        // if we couldn't find a star graph
        if(locationStarGraph1 == -1){
            System.out.println("No star graphs found");
            return;
        }
        Graph<Vertex, DefaultEdge> starGraph1 = starGraphs.remove(locationStarGraph1);
        List<String> starGraph1Profile = starGraphsProfiles.remove(locationStarGraph1);
        List<Vertex> starGraph1Roots = verticesRootOccurs.get(starGraph1Profile);
        int starGraph1NumOccurrences = verticesRootOccurs.remove(starGraph1Profile).size();

        int locationStarGraph2  = findMostFrequentStructure(starGraphs, starGraphsProfiles, verticesRootOccurs);
        // if we couldn't find a star graph
        if(locationStarGraph2 == -1 && !connectionMethod.equals("none")){
            // write to graph file that couldn't find a connection (because of threshold or not connectable)
            BufferedWriter writer = new BufferedWriter(new FileWriter(outputFolderName+"Graphs\\"+graphName));
            writer.write(thresholdToHigh);
            writer.append("Only one profile of given size.\n");
            writer.close();
            System.out.println(thresholdToHigh);
            System.out.println("Only one profile of given size.");
            return;
        }
        Graph<Vertex, DefaultEdge> starGraph2 = starGraphs.remove(locationStarGraph2);
        List<String> starGraph2Profile = starGraphsProfiles.remove(locationStarGraph2);
        List<Vertex> starGraph2Roots = verticesRootOccurs.get(starGraph2Profile);
        int starGraph2NumOccurrences = verticesRootOccurs.remove(starGraph2Profile).size();

        // union two star graphs
        Graph<Vertex, DefaultEdge> query = null; numCombined = new HashMap<>();
        switch (connectionMethod) {
            // union by merge
            case MERGE -> query = unionGraphsByMerge(target, starGraph1, starGraph2, starGraph1Roots,
                    starGraph2Roots, 100);
            // union by edge
            case EDGE -> query = unionGraphsByEdge(target, starGraph1, starGraph2, starGraph1Roots,
                    starGraph2Roots, 100);
            // no merging
            case NONE -> query = starGraph1;
            // not a correct merging method
            default -> {
                // write to graph file that couldn't find a connection method
                BufferedWriter writer = new BufferedWriter(new FileWriter(outputFolderName + "Graphs\\" + graphName));
                writer.write(noConnectionMethodFound);
                writer.close();
                System.out.println(noConnectionMethodFound);
                return;
            }
        }

        // if we couldn't connect the graphs anywhere
        if(query == null){
            // write to graph file that couldn't find a connection (because of threshold or not connectable)
            BufferedWriter writer = new BufferedWriter(new FileWriter(outputFolderName+"Graphs\\"+graphName));
            writer.write(thresholdToHigh);
            writer.close();
            System.out.println(thresholdToHigh);
            return;
        }

        // save the graph
        String queryFileName = writeGraph(query, outputFolderName + "Graphs\\", graphName);

        // now write the information to build the graph
        BufferedWriter writer = new BufferedWriter(new FileWriter(outputFolderName+"GenerationInfo\\"+graphName));
        writer.write("Used "+fdmFileLocation+" frequent dataset mining \n"+
                "Combined two graphs with method "+connectionMethod+": \n"+
                "Vertex with attribute "+ frequentProfileShapes.get(starGraph1Profile)
                + " and profile "+ starGraph1Profile +" occurs "+starGraph1NumOccurrences
                + " times within the graph \n"
                +"Vertex with attribute "+ frequentProfileShapes.get(starGraph2Profile)
                + " and profile "+ starGraph2Profile +" occurs "+starGraph2NumOccurrences
                + " times within the graph \n");

        // now perform subgraph isomorphism
        List<Map<Vertex, Vertex>> subgraphIsomorphism = matching(query, target, isInduced, gamma);

        writer.append("\n");
        // write to statistics file
        displayGraphStatistics(queryFileName, query, graphLocation, target, writer);
        writer.close();

        if(subgraphIsomorphism == null){
            // write to output files
            writer = new BufferedWriter(new FileWriter(
                    outputFolderName + "Isomorphism\\" + graphName));
            writer.write(noAlgorithmFound);
            writer.close();
            return;
        }
        // write to output file
        writer = new BufferedWriter(new FileWriter(
                outputFolderName + "Isomorphism\\" + graphName));
        writer.write("");
        displayIsomorphism(subgraphIsomorphism, queryFileName, graphLocation, writer, isInduced);
        System.out.println("============================");
        writer.append("============================\n");

        writer.close();
    }

    /**
     * Creates a random graph from the target graph and performs subgraph isomorphism
     *
     * @param targetGraph the target graph
     * @param targetLocation the location of the target
     * @param size the size of the query graph
     * @param outputFolderName the folder we are writing the graph information to
     * @param graphName the name of the query graph
     * @param isInduced if the isomorphism is induced
     * @param gamma the gamma value
     * @throws IOException for the writer
     * @return if random walk was successful
     */
    public static int randomWalk(Graph<Vertex, DefaultEdge> targetGraph, String targetLocation, int size,
                                  String outputFolderName, String graphName, boolean isInduced, double gamma)
            throws IOException {

        BufferedWriter writer = new BufferedWriter(new FileWriter(
                outputFolderName + "GenerationInfo\\" + graphName));
        Graph<Vertex, DefaultEdge> queryGraph = randomGraph(targetGraph, targetLocation, size, writer);
        // save the graph
        String queryFileName = writeGraph(queryGraph, outputFolderName + "Graphs\\", graphName);

        displayGraphStatistics(queryFileName, queryGraph, targetLocation, targetGraph, writer);
        writer.close();


        // find and display the isomorphisms
        List<Map<Vertex, Vertex>> subgraphIsomorphism = matching(queryGraph, targetGraph, isInduced, gamma);
        if(subgraphIsomorphism == null){
            // write to output file
            writer = new BufferedWriter(new FileWriter(
                    outputFolderName + "Isomorphism\\" + graphName));
            writer.write(noAlgorithmFound);
            writer.close();

            return -1;
        }

        // write to output file
        writer = new BufferedWriter(new FileWriter(
                outputFolderName + "Isomorphism\\" + graphName));
        writer.write("");
        displayIsomorphism(subgraphIsomorphism, queryFileName, new File(targetLocation).getName(), writer, isInduced);
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

        // the combination information if combined two graphs
        if(numCombined!=null){
            writer.append("Star Graph Combination:\n");
            for(List<Vertex> combine: numCombined.keySet()){
                writer.append("\t").append(combine.toString()).append(":")
                        .append(String.valueOf(numCombined.get(combine))).append("\n");
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
     * Finds the probability of a given walk
     * @param order the processing order for the query graph
     * @param candidates the candidates of the query vertices
     * @param SEQq the QI-Sequence, tree and extra edge information
     * @param i the current vertex in the walk that we are adding
     * @param walk the current random walk
     * @param target the target graph
     * @return the probability of a random walk (0 if invalid walk)
     */
    public static double randomWalkWJ(ArrayList<Vertex> order, Map<Vertex, Set<Vertex>> candidates , QISequence SEQq,
                                      int i, List<Vertex> walk, Graph<Vertex, DefaultEdge> target){
        // we have reached the end of the walk
        if(walk.size() == order.size()){
            // multiply by identity
            return 1;
        }
        // get the next vertex in the order
        Vertex u = order.get(i);
        // if we are at the start of the walk
        if(i == 0){
            Set<Vertex> possibleVertices = new HashSet<>(candidates.get(u));
            // if there are no possible vertices for the first vertex
            if(possibleVertices.size() == 0){
                return 0;
            }
            // pick a random vertex add to walk
            Vertex vNext = randomVertex(possibleVertices);
            walk.add(vNext);
            // the cost is currently the number of vertices we could have chosen from
            return (possibleVertices.size()) * randomWalkWJ( order, candidates, SEQq, i+1, walk, target);
        }

        // get the parent of the current vertex
        Vertex up = SEQq.getParent(u); int p = order.indexOf(up);
        // get the parent of the vertex within the graph
        Vertex vp = walk.get(p);
        Set<Vertex> possibleVertices = new HashSet<>(candidates.get(u));
        // get the children of the parent and see if they are within the current candidate set
        possibleVertices.retainAll(Graphs.neighborListOf(target, vp));
        possibleVertices.removeAll(walk);

        // if we could not find any vertices to go to next
        if(possibleVertices.size() == 0){
            return 0;
        }

        // pick the next random vertex
        Vertex vNext = randomVertex(possibleVertices);
        walk.add(vNext);
        return randomWalkWJ(order, candidates, SEQq, i+1, walk, target)*possibleVertices.size();
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
     * Finds the confidence interval for a given set of values
     * @param costValues the cost values
     * @param zScore the alpha+1/2 quantile of the normal distribution with mean 0 and variance 1
     * @return the confidence interval
     */
    public static double computeConfidenceInterval(List<Double> costValues, double zScore){
        // the average
        double tn = calculateMeanSquareDifference(costValues);


        return zScore * tn / Math.sqrt(costValues.size());
    }

    /**
     * Performs Wander Join to estimate the matchings or backtrackings for a given isomorphism
     * @param query the query graph
     * @param target the target graph
     * @param gamma the gamma value for GraphQL
     * @param tau the confidence interval threshold
     * @param maxEpoch the maximum number of random walks
     * @param zScore the z score for confidence interval
     * @param isInduced if the isomorphism is induced
     * @return the overall estimation for the subgraph isomorphism
     */
    public static int wanderJoins(Graph<Vertex, DefaultEdge> query, Graph<Vertex, DefaultEdge> target, double gamma,
                                  double tau, int maxEpoch, double zScore, boolean isInduced){
        // compute candidates
        Map<Vertex, Set<Vertex>> candidates = computeCandidates(query, target);
        if(candidates == null){
            System.out.println("Invalid Candidates.  Might be invalid algorithm:");
            System.out.println(noAlgorithmFound);
            // something went wrong
            return -1;
        }
        // compute processing order
        ArrayList<Vertex> order = computeProcessingOrder(query, target, candidates, gamma);
        if(order == null){
            System.out.println("Invalid Processing Order.  Might be invalid algorithm:");
            System.out.println(noAlgorithmFound);
            // something went wrong
            return -1;
        }

        // compute the spanning tree
        QISequence SEQq = buildSpanningTreeWithOrder(query, order);

        // keep track of the costs we have seen
        List<Double> costValues = new ArrayList<>();

        while (costValues.size()<maxEpoch){
            // the walk is originally empty
            List<Vertex> walk = new ArrayList<>();
            // get the cost of the walk
            double cost = randomWalkWJ(order, candidates, SEQq, 0, walk, target);

            if (cost != 0) {
                // if it is not an invalid walk, need to check extra edges
                Map<Vertex, List<Vertex>> extraEdges = SEQq.getEdge();

                for (Vertex u1 : extraEdges.keySet()) {
                    for (Vertex u2 : extraEdges.get(u1)) {
                        // get the location of the vertices in the edge within the order and walk
                        int i1 = order.indexOf(u1);
                        int i2 = order.indexOf(u2);
                        // get the corresponding vertices within the walk
                        Vertex v1 = walk.get(i1);
                        Vertex v2 = walk.get(i2);

                        // if there is not a corresponding edge
                        if (!target.containsEdge(v1, v2)) {
                            cost = 0;
                            break;
                        }
                    }
                }

                // also check for induced
                if (isInduced) {
                    Map<Vertex, List<Vertex>> noEdge = SEQq.getNoEdge();
                    for (Vertex u1 : noEdge.keySet()) {
                        for (Vertex u2 : noEdge.get(u1)) {
                            // get the location of the vertices in the edge within the order and walk
                            int i1 = order.indexOf(u1);
                            int i2 = order.indexOf(u2);
                            // get the corresponding vertices within the walk
                            Vertex v1 = walk.get(i1);
                            Vertex v2 = walk.get(i2);

                            // if there is not a corresponding edge
                            if (target.containsEdge(v1, v2)) {
                                cost = 0;
                                break;
                            }
                        }
                    }
                }
            }


            // add the cost to the cost values
            costValues.add(cost);

            // every 20 check the confidence value
            if(costValues.size()%25 == 0){
                double conf = computeConfidenceInterval(costValues, zScore);
                if(conf<tau) {
                    break;
                }
            }
        }

        // average the cost values
        double avgCost = calculateAverage(costValues);

        // round to nearest integer
        return (int) Math.round(avgCost);
    }

    public static int estimateCardinality(String queryFileLocation, String targetFileLocation, double gamma, double tau,
                                          int maxEpoch, double zAlpha, String outputFileName, boolean isInduced) throws IOException {
        // read the info from the file
        File queryFile = new File(queryFileLocation);
        File targetFile = new File(targetFileLocation);

        // create the graphs
        Graph<Vertex, DefaultEdge> queryGraph = createProteinGraph(queryFile);
        Graph<Vertex, DefaultEdge> targetGraph = createProteinGraph(targetFile);

        // compute the estimation
        int estimation =  wanderJoins(queryGraph, targetGraph, gamma, tau, maxEpoch, zAlpha, isInduced);
        if(estimation == -1){
            BufferedWriter writer = new BufferedWriter(new FileWriter(outputFileName));
            writer.write("Something went wrong");
            return -1;
        }

        // write to output file
        BufferedWriter writer = new BufferedWriter(new FileWriter(outputFileName));
        String output = "The matching estimation for the following is " + estimation +":"+
                "\nquery graph: "+queryFile +
                "\ntarget graph: "+targetFile+
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
                                       int maxEpoch, double zScore, String queryFolder, String targetFolder) throws IOException {
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
            String queryName = null;
            String targetName = null;

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
                    queryName = queryFolder+info[0].strip().split(" ")[2].strip();
                    targetName = targetFolder+info[1].strip().split(" ")[2].strip();
                }

                // get the number of isomorphisms
                if(line.toLowerCase(Locale.ROOT).contains("subgraph isomorphisms")){
                    actualNumber = Integer.parseInt(line.split(":")[1].strip());
                    induceString = line.split(" ")[0].strip().toLowerCase(Locale.ROOT);
                }

                // we found all of the information
                if(queryName!= null && targetName!=null && actualNumber!=-1 && induceString!= null){
                    break;
                }
                line = br.readLine();
            }
            Graph<Vertex, DefaultEdge> query = createProteinGraph(new File(queryName));
            Graph<Vertex, DefaultEdge> target = createProteinGraph(new File(targetName));

            boolean isInduced;
            if(induceString.equals("induced")){
                isInduced = true;
            }
            else{
                isInduced = false;
            }

            int estimatedNumber = wanderJoins(query, target, gamma, tau, maxEpoch, zScore, isInduced);
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

            String output = "Query Graph: "+queryName+", Target Graph: "+targetName +
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
        int maxEpoch = 1000;
        double zScore = 1.96; // z-score for 95% confidence

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
            for (int i = 0; i < files.length; i++){
                if (files[i].isFile()){ //this line weeds out other directories/folders
                    String targetLocation = String.valueOf(files[i]);
                    String outputFileName = outputFolderName+files[i].getName();

                    frequentDatasetMining(targetLocation, outputFileName, minSup);
                    System.out.println("=================");
                }
            }
        }
        // create a query graph from frequent profiles
        else if(mainMethod.equals("FDMQuery") && args.length == 4){
            final String fdmFile = args[1];
            final String outputFolderName = args[2];
            // keep track of the minimum profile size while creating graph
            int profileSize = Integer.parseInt(args[3]);// itemsets must be this size
            final String connectionMethod = MERGE;

            // get the information from the fdm file
            fdmGraph(fdmFile, outputFolderName, isInduced, profileSize, gamma, connectionMethod);
        }
        // create query graph from random walk
        else if(mainMethod.equals("RandomWalk")  && args.length == 3) {
            final String targetLocation = args[1];
            final String outputFolderName = args[2];

            // create the target graph and random query graph
            Graph<Vertex, DefaultEdge> targetGraph = createProteinGraph(new File(targetLocation));
            calculateStatistics(targetGraph);

            // iterate through the different size of graphs
            for(int size = 5; size<25; size++) {
                // attempt 100 times for each size
                for(int i = 1; i<10; i++) {
                    File outputGraphFolder = new File(outputFolderName + "Graphs\\");
                    int numGraphs = 0;
                    if (outputGraphFolder.list() != null) {
                        numGraphs = outputGraphFolder.list().length;
                    }
                    String graphName = "graph" + (numGraphs + 1) + ".txt";

                    if(randomWalk(targetGraph, targetLocation, size, outputFolderName, graphName, isInduced, gamma) == -1){
                        return;
                    }
                }
            }
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
                    "\nTestIsomorphism <groundTruthFile> <queryFolder> <targetFolder> <outputFile>"+
                    "\n\t Test the subgraph isomorphisms within the ground truth file."+
                    "\n\t Must provide the location of the query and target folders.  If path is contained within " +
                    "ground truth folder, then give argument '_'."+
                    "\n\t If there is any errors in the isomorphism it will be recorded in the output file.");
        }

    }
}
