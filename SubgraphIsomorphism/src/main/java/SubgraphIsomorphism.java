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
import java.util.stream.Collectors;

public class SubgraphIsomorphism {
    private static int numBackTracking = -1; // keep track of backtracking calls
    private static int numLocalPruning = -1; // keep track of how much pruned locally
    private static int numGlobalPruned = -1; // keep track of how much pruned globally
    private static double totalCostGraphQL = -1; // keep track of the total cost when computing the order for GraphQL
    private static Map<List<Vertex>, Integer> numCombined = null; // keep track of the statistics when combine graphs
    private static String algorithmNameC = ""; // algorithm in use for candidates
    private static String algorithmNamePO = ""; // algorithm in use for processing order

    // error message if didn't find isomorphism algorithm
    private static final String noAlgorithmFound = "Algorithm specified is not valid.\n" +
            "Specify one of the following algorithms: \n" +
            "\t groundTruth: finds the ground truth isomorphism.  Only uses LDA in pruning and BFS for ordering.\n" +
            "\t graphQL: uses the GraphQL algorithm.\n" +
            "\t quickSI: uses the QuickSI algorithm. (Note: only used for processing order)\n";
    // error message if didn't find connection algorithm
    private static final String noConnectionMethodFound = "Connection type of graphs specified is not valid.\n " +
            "Specify one of the following connections methods: \n" +
            "\t merge: merge two vertices of the same label.\n" +
            "\t edge: create an edge between two vertices.\n " +
            "\t none: use star graph of largest size.\n";
    // error message if threshold is too high
    private static final String thresholdToHigh = "Threshold too large for graph or graphs not connectable";
    // error message if minimum support is too high
    private static final String minSupToHigh = "Minimum support too large for graph";


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
     * Compares two edges and returns based on weight
     * @param e1 first edge
     * @param e2 second edge
     * @param graph graph that contains the edges
     * @return comparison of two edges based on weight
     */
    public int compareWeightedEdges(DefaultWeightedEdge e1, DefaultWeightedEdge e2,
                                    Graph<Vertex, DefaultWeightedEdge> graph){
        double weight1 = graph.getEdgeWeight(e1);
        double weight2 = graph.getEdgeWeight(e2);

        return Double.compare(weight1, weight2);
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

        // get the edges of minimum weights
        for(DefaultWeightedEdge e: possibleEdges){
            if(weightedQuery.getEdgeWeight(e)>minimumWeight){
                possibleEdges.remove(e);
            }
        }

        // get the edge with minim degree
        DefaultWeightedEdge minEdge = possibleEdges.iterator().next();
        double minimumDegree = weightedQuery.degreeOf(weightedQuery.getEdgeSource(minEdge)) +
                weightedQuery.degreeOf(weightedQuery.getEdgeTarget(minEdge));
        // find minimum weight
        for(DefaultWeightedEdge e: possibleEdges){
            double currentDegree =  weightedQuery.degreeOf(weightedQuery.getEdgeSource(e)) +
                    weightedQuery.degreeOf(weightedQuery.getEdgeTarget(e));
            if(currentDegree<minimumDegree){
                minimumDegree = currentDegree;
            }
        }

        // get the edges of minimum degree
        for(DefaultWeightedEdge e: possibleEdges){
            double currentDegree =  weightedQuery.degreeOf(weightedQuery.getEdgeSource(e)) +
                    weightedQuery.degreeOf(weightedQuery.getEdgeTarget(e));
            if(currentDegree>minimumDegree){
                possibleEdges.remove(e);
            }
        }

        // get a random edge from the chosen
        Random random = new Random();
        // random index
        int index = random.nextInt(possibleEdges.size());
        // get corresponding edge
        Iterator<DefaultWeightedEdge> edgeIter = possibleEdges.iterator();
        DefaultWeightedEdge randomEdge = edgeIter.next();
        for(int i = 0; i< index-1; i++){
            randomEdge = edgeIter.next();
        }

        return randomEdge;
    }

    public static QISequence buildSpanningTree(Graph<Vertex, DefaultWeightedEdge> weightedQuery){
        QISequence SEQq = new QISequence();



        return SEQq;
    }

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
        QISequence SEQq = buildSpanningTree(weightedQuery);

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
        for(Vertex uPrime: Graphs.neighborListOf(query, u)){
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
            for(Vertex uPrime: currentFunction.keySet()){
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
            // look at candidates
            for(Vertex v : candidates.get(u)){
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
        Map<Vertex, Set<Vertex>> candidates;
        ArrayList<Vertex> order;
        if(algorithmNameC.equals("groundTruth")) {
            candidates = groundTruthComputeCandidates(query, target);
        }
        else if(algorithmNameC.equals("graphQL")){
            candidates = graphQLComputeCandidates(query, target);
        }
        else{
            System.out.println("Candidates Algorithm:");
            System.out.println(noAlgorithmFound);
            return null;
        }

        if(algorithmNamePO.equals("groundTruth")){
            order = groundTruthComputeProcessingOrder(query, candidates);
        }
        else if(algorithmNamePO.equals("graphQL")){
            order = graphQLComputeProcessingOrder(query, candidates, gamma);
        }
        else if(algorithmNamePO.equals("quickSI")){
            order = quickSIComputeProcessingOrder(target, query, candidates);
        }
        else{
            System.out.println("Processing Order Algorithm:");
            System.out.println(noAlgorithmFound);
            return null;
        }

        // keep track of number of backtracking
        numBackTracking = 0;
        subgraphIsomorphism(query, target, candidates, order, 0, new HashMap<>(), results, isInduced);
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

        System.out.println("# candidates algorithm: "+algorithmNameC);
        System.out.println("# processing order algorithm: "+algorithmNamePO);
        writer.append("# candidates algorithm: "+ algorithmNameC+"\n" +
                "# processing order algorithm: "+algorithmNamePO+"\n");

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
        int currentId = seen.size();
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
                "Candidates algorithm: "+algorithmNameC+": \n" +
                "Processing order algorithm: "+algorithmNamePO+"\n");

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


                // find isomorphisms and how they are displayed
                List<Map<Vertex, Vertex>> subgraphIsomorphism = matching(query, target, isInduced, gamma);
                if(subgraphIsomorphism==null){
                    writer.write(noAlgorithmFound);
                    br.close(); writer.close();
                    return;
                }

                List<String> isomorphisms = isomorphismOrdered(subgraphIsomorphism);

                int i = 1; // keep track of which isomorphism was printed
                line = br.readLine().strip();
                for(String iso: isomorphisms){
                    // skip comments
                    while(line.length()>0 && line.charAt(0) == '#'){
                        line = br.readLine().strip();
                    }
                    String currentMatching = "Isomorphism "+ i + ": " +iso;
                    i++;

                    // compare with ground truth
                    if(!currentMatching.equals(line)){
                        writer.append("Incorrect ").append(outputString).append(" Matching! \n")
                                .append(queryGraphFile.getName()).append(" : ")
                                .append(targetGraphFile.getName()).append("\n");
                        // state the differences
                        writer.append("Correct : ").append(line).append("\n");
                        writer.append("Incorrect (found) : ").append(currentMatching).append("\n\n");

                        System.out.println("Problem Here! "+queryGraphFile +": "+targetGraphFile);
                        graphProblem = true;
                    }
                    if(graphProblem){
                        break;
                    }
                    line = br.readLine().strip();
                }
                if(!graphProblem) {
                    System.out.println("Correct " + outputString + " Matching! " +
                            queryGraphFile.getName() + ": " + targetGraphFile.getName());
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
     * @throws IOException
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
                catch (NumberFormatException nfe){
                    continue;
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
            System.out.println("No target graph found.  Format as follows :" +
                    "\n Graph: <graphLocation> " +
                    "\n Number of Nodes: <numberNodesInGraph> " +
                    "\n Minsup (integer): <integerMinsup> " +
                    "\n Minsup (percentage): <percentMinsup> " +
                    "\n Attribute Label " +
                    "\n <largeProfile> appears in <numAppearances> vertex profiles: " +
                    "\n <listVerticesIds>");
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
                    v =  target.vertexSet().stream().filter(vertex -> vertex.getId() == vID).findAny()
                            .get();
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
        // union by merge
        if(connectionMethod.equals("merge")){
            query = unionGraphsByMerge(target, starGraph1, starGraph2, starGraph1Roots,
                    starGraph2Roots, 100);
        }
        // union by edge
        else if(connectionMethod.equals("edge")) {
            query = unionGraphsByEdge(target, starGraph1, starGraph2, starGraph1Roots,
                    starGraph2Roots, 100);
        }
        else if(connectionMethod.equals("none")){
            query = starGraph1;
        }
        // not a correct merging method
        else{
            // write to graph file that couldn't find a connection method
            BufferedWriter writer = new BufferedWriter(new FileWriter(outputFolderName+"Graphs\\"+graphName));
            writer.write(noConnectionMethodFound);
            writer.close();
            System.out.println(noConnectionMethodFound);
            return;
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

        writer.append("Used candidate algorithm: " +algorithmNameC+"\n");
        writer.append("Used processing order algorithm: " +algorithmNamePO+"\n");
        // number of backtracking in isomorphism
        writer.append("Number backtracking calls: ").append(String.valueOf(numBackTracking)).append("\n");
        // number of possible matchings
        writer.append("Total number of possible matchings: "+target.vertexSet().size()*query.vertexSet().size()+"\n");

        writer.append("\n");
        // number pruned from local pruning
        writer.append("Number pruned from local pruning: ").append(String.valueOf(numLocalPruning)).append("\n");
        // number pruned from global pruning
        if(numGlobalPruned!=-1) {
            writer.append("Number pruned from global pruning: ").append(String.valueOf(numGlobalPruned)).append("\n");
        }
        // total cost from graphQL order
        if(totalCostGraphQL!=-1) {
            writer.append("Cost of order found by graphQL: ").append(String.valueOf(totalCostGraphQL)).append("\n");
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
        algorithmNameC = "graphQL";
        algorithmNamePO = "quickSI";
        // groundTruth, graphQL
        final boolean isInduced = true;
        double gamma = 0.5;

        // if the two graphs are known
        if(mainMethod.equals("KnownGraphs") && args.length == 5) {
            final String queryLocation = args[1];
            final String targetLocation = args[2];
            final String outputFileName = args[3];
            final String statisticsFileName = args[4];

            subgraphIsomorphismKnownGraphs(queryLocation, targetLocation, outputFileName, statisticsFileName, isInduced,
                    gamma);
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
        else if(mainMethod.equals("FDMQuery") && args.length == 5){
            final String fdmFile = args[1];
            final String outputFolderName = args[2];
            // keep track of the minimum profile size while creating graph
            int profileSize = Integer.parseInt(args[3]);// itemsets must be this size
            final String connectionMethod = args[4];

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
        else if(mainMethod.equals("Test")  && args.length == 5){
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
                    "\nKnownGraphs <queryFile> <targetFile> <outputFile> <statisticsFile>"+
                    "\n\t Find the subgraph isomorphism between two know graphs."+
                    "\n\t Prints Isomorphisms to output file and statistics to StatisticsFile."+
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
                    "\nTest <groundTruthFile> <queryFolder> <targetFolder> <outputFile>"+
                    "\n\t Test the subgraph isomorphisms within the ground truth file."+
                    "\n\t Must provide the location of the query and target folders.  If path is contained within " +
                    "ground truth folder, then give argument '_'."+
                    "\n\t If there is any errors in the isomorphism it will be recorded in the output file.");
        }

    }
}
