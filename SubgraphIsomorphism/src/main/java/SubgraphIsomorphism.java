import org.jgrapht.*;
import org.jgrapht.alg.interfaces.MatchingAlgorithm;
import org.jgrapht.graph.*;
import org.jgrapht.traverse.BreadthFirstIterator;
import org.jgrapht.traverse.DepthFirstIterator;
import org.jgrapht.traverse.RandomWalkVertexIterator;
import org.jgrapht.alg.matching.HopcroftKarpMaximumCardinalityBipartiteMatching;

import java.io.*;
import java.util.*;

public class SubgraphIsomorphism {
    private static int numBackTracking; // keep track of backtracking calls


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
     * @throws IOException
     */
    public static String writeGraph(Graph<Vertex, DefaultEdge> graph, String outputFolderName,
                                    String graphName) throws IOException {
        // write to output file
        BufferedWriter writer = new BufferedWriter(new FileWriter(
                outputFolderName+graphName));
        writer.write("");

        writer.append("# vertex information \n");
        int numVertices = graph.vertexSet().size();
        writer.append(numVertices+"\n");
        Iterator<Vertex> iter = new DepthFirstIterator<>(graph);
        while (iter.hasNext()) {
            // get the next vertex and its edge
            Vertex vertex = iter.next();
            writer.append(vertex.getId() + " " + vertex.getAttributes().get("Label")+"\n");
        }

        writer.append("# edge information \n");
        iter = new DepthFirstIterator<>(graph);
        while (iter.hasNext()) {
            // get the next vertex and its edge
            Vertex vertex = iter.next();
            writer.append(graph.degreeOf(vertex)+"\n");

            for(Vertex neighbor: Graphs.neighborListOf(graph, vertex)){
                writer.append(vertex.getId() + " " + neighbor.getId()+"\n");
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
     * @throws IOException
     */
    private static Graph<Vertex, DefaultEdge> createProteinGraph(File graphFile) throws IOException {
        // keep track of the vertices for easy access
        Map<Integer, Vertex> idToVertex = new LinkedHashMap<>();

        // create a new graph
        Graph<Vertex, DefaultEdge> g = new SimpleGraph<>(DefaultEdge.class);
        BufferedReader br = new BufferedReader(new FileReader(graphFile));
        String line = br.readLine().strip();

        // skip lines starting with "#"
        while (line.charAt(0) == '#') {
            line = br.readLine().strip();
        }

        // get the number of vertices first
        int numberVertices = Integer.parseInt(line);
        line = br.readLine();

        // iterate through the vertices
        for(int i = 0; i < numberVertices; i++) {
            line = line.strip();
            // skip lines starting with "#"
            if (line.charAt(0) == '#') {
                i--;
                continue;
            }

            // get the id and chemical from the line
            String[] vertexInfo = line.split(" ");
            // store the key
            int vID = Integer.parseInt(vertexInfo[0]);
            // store the attributes
            String vChemical = vertexInfo[1];
            Map<String, String> attributes = new HashMap<>();
            attributes.put("Label", vChemical);

            // create/add new vertex
            Vertex v = new Vertex(vID, attributes);
            g.addVertex(v);
            idToVertex.put(vID, v);


            // build the profile to include own label
            v.addToProfile(v);

            line = br.readLine();
        }

        //iterate through the edges of each vertex
        while(line != null) {
            //skip lines starting with "#"
            if (line.charAt(0) == '#') {
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
     * Calculates the statistics for a given graph.
     * The number of subsets for a profile for each vertex
     * @param graph the graph to calculate the statistics
     * @param attributes the attributes we are looking at
     */
    public static void calculateStatistics(Graph<Vertex, DefaultEdge> graph, String[] attributes){
        // keep track of a the possible values for a given attribute
        Map<String, Set<String>> possibleValues = new HashMap<>();
        for(String attribute: attributes){
            possibleValues.put(attribute, new HashSet<>());
        }
        // keep track of the maximum degree of the graph
        int maxDegree = 0;

        // iterate through the vertices and calculate the possible combinations for the profiles
        Iterator<Vertex> iter = new DepthFirstIterator<>(graph);
        while(iter.hasNext()){
            // get the graph vertex
            Vertex v = iter.next();

            // find the maximum degree
            int degree = graph.degreeOf(v);
            if(degree>maxDegree){
                maxDegree = degree;
            }

            // find the possible subsets of each and the values of each of the attributes
            Map<String, Set<String>> possibleValuesCurrent = v.calculateNumberProfileSubsets(attributes);
            for(String attribute: attributes){
                // keep track of the attribute values we have seen
                possibleValues.get(attribute).addAll(possibleValuesCurrent.get(attribute));
            }
        }

        // todo having difficulty finding all the possible subsets given the labels and max degree - frequency test
    }

    /**
     * Uses Label and Degree Filtering Technique (LDF): v is a candidate of u if they are the same labels and the degree
     * of v is larger or equal to the degree of u
     * @param query the query graph
     * @param target the target graph
     * @param attributes the attributes (labels) that we are comparing
     * @param u a vertex from the query graph
     * @param v a vertex from the target graph
     * @return true if v is a candidate of u
     */
    public static boolean labelDegreeFiltering(Graph<Vertex, DefaultEdge> query,
                                               Graph<Vertex, DefaultEdge> target, String[] attributes,
                                               Vertex u, Vertex v){
        int vDegree = target.degreeOf(v);
        int uDegree = query.degreeOf(u);
        return vDegree>=uDegree && u.sameAttributes(attributes, v);
    }

    /**
     * Local Pruning: v is a candidate of u if u's profile is a subset of v's profile.  A profile is a lexicographically
     * sorted set of labels of the vertex
     * @param attributes the attributes (labels) that we are comparing
     * @param u a vertex from the query graph
     * @param v a vertex from the target graph
     * @return true if v is a candidate of u
     */
    public static boolean localPruning(String[] attributes, Vertex u, Vertex v){
        return u.profileSubset(v, attributes);
    }

    public static void pruneGlobally(Graph<Vertex, DefaultEdge> query, Graph<Vertex, DefaultEdge> target,
                                     Map<Vertex, Set<Vertex>> candidates){
        // keep track of the previous candidates by their query/target vertex pair
        Set<List<Vertex>> T = new HashSet<>();

        // iterate through the query vertices
        Iterator<Vertex> qIter = new DepthFirstIterator<>(query);
        while(qIter.hasNext()){
            // get the query vertex
            Vertex u = qIter.next();
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

                // create a new graph, which will be the biparite graph
                Graph<Vertex, DefaultEdge> B = new SimpleGraph<>(DefaultEdge.class);
                // keep track of where the copy came from
                Map<Vertex, Vertex> copyToOrignial = new HashMap<>();
                int id = 0; // keep track of the current id being added
                // keep track of u neighbors added
                Set<Vertex> uPVertices = new HashSet<>();
                // add copy of the neighbors of u
                for(Vertex uP : Graphs.neighborListOf(query, u)){
                    Vertex uPCopy = copyVertex(uP, id); id++;
                    copyToOrignial.put(uPCopy, uP);
                    B.addVertex(uPCopy);
                    uPVertices.add(uPCopy);
                }
                // keep track of the v neighbors added
                Set<Vertex> vPVertices = new HashSet<>();
                // add the neighbors of v
                for(Vertex vP : Graphs.neighborListOf(target, v)){
                    Vertex vPCopy = copyVertex(vP, id); id++; // create copy so target vertices with same id can be added
                    copyToOrignial.put(vPCopy, vP);
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
                        if(candidates.get(copyToOrignial.get(uP)).contains(copyToOrignial.get(vP))){
                            // add edge between two values
                            B.addEdge(uP, vP);

                            // add to T''
                            List<Vertex> elementPrime = new ArrayList<>();
                            elementPrime.add(copyToOrignial.get(uP));
                            elementPrime.add(copyToOrignial.get(vP));
                            TPrimePrime.add(elementPrime);
                        }
                    }
                }
                // find the maximum matching of B
                HopcroftKarpMaximumCardinalityBipartiteMatching<Vertex, DefaultEdge> matchingAlgorithm =
                        new HopcroftKarpMaximumCardinalityBipartiteMatching<Vertex, DefaultEdge>(B, uPVertices, vPVertices);
                MatchingAlgorithm.Matching<Vertex, DefaultEdge> matching = matchingAlgorithm.getMatching();

                // matching does not contain all query vertices
                if(matching.getEdges().size() != uPVertices.size()){
                    candidates.get(u).remove(v);

                    // build T'
                    for(List<Vertex> pairPP: TPrimePrime) {
                        // add to T' if not already there
                        if(!TPrime.contains(pairPP)) {
                            TPrime.add(pairPP);
                        }
                    }
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
     * @param attributes the attributes (labels) that we are comparing
     * @return a candidates for each vertex within the query graph
     */
    public static Map<Vertex, Set<Vertex>> computeCandidates(Graph<Vertex, DefaultEdge> query,
                                                             Graph<Vertex, DefaultEdge> target,
                                                             String[] attributes, boolean groundTruth){
        // keep track of the candidates for a given vertex
        Map<Vertex, Set<Vertex>> candidates = new HashMap<>();

        // find the possible candidates given vertex label and degree
        // iterate through the query vertices
        Iterator<Vertex> qIter = new DepthFirstIterator<>(query);
        while(qIter.hasNext()){
            // get the query vertex
            Vertex u = qIter.next();
            // create a new set
            Set<Vertex> uCandidates = new HashSet<>();

            // iterate through the target vertices
            Iterator<Vertex> tIter = new DepthFirstIterator<>(target);
            while(tIter.hasNext()){
                // get the target vertex
                Vertex v = tIter.next();

                // Label and Degree Filtering (LDF)
                // check that the target vertex has appropriate attributes and degree
                if(labelDegreeFiltering(query, target, attributes, u, v) && (groundTruth ||
                        // if ground truth will only perform labelDegreeFiltering
                        localPruning(attributes, u, v))){
                    uCandidates.add(v);
                }
            }
            // store u candidates
            candidates.put(u, uCandidates);
        }
        if(!groundTruth) {
            pruneGlobally(query, target, candidates);
        }

        return candidates;
    }

    /**
     * Calculate the size of the joins between current order and u.
     * Calculation from GraphQL.
     * @param query the query graph
     * @param leftSize the previous order size of joins
     * @param candididates the possible target vertices for the query vertices
     * @param order the order we are checking the query vertices
     * @param u the possible query vertex we are adding
     * @param gamma the gamma value
     * @return the size of joining u to the current order
     */
    public static double calculateSize(Graph<Vertex, DefaultEdge> query, double leftSize,
                                       Map<Vertex, Set<Vertex>> candididates, ArrayList<Vertex> order, Vertex u,
                                       double gamma){
        // size(i) = size(i.left)*size(i.right)*gamma^connection(order, u)
        double size = leftSize*candididates.get(u).size();
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
     * @param candididates sets of candidates for each query vertex
     * @param gamma
     * @return a list of the vertices in the order they should be checked
     */
    public static ArrayList<Vertex> computeProcessingOrder(Graph<Vertex, DefaultEdge> query,
                                                           Map<Vertex, Set<Vertex>> candididates,
                                                           double gamma, boolean groundTruth){
        ArrayList<Vertex> order = new ArrayList<>();
        if(groundTruth) {
            // if we're looking for the ground truth then order is by BFS TODO change when create new ordering
            while (order.size() < candididates.size()) {
                Iterator<Vertex> nodeIterator = candididates.keySet().iterator();
                // find the node with the fewest amount of candidates
                Vertex startingNode = nodeIterator.next();
                // find the next vertex that is not in the order
                while (order.contains(startingNode)) {
                    startingNode = nodeIterator.next();
                }

                for (Vertex currentNode : candididates.keySet()) {
                    // update it when find a node with smaller candidate size and not yet in order
                    if (candididates.get(startingNode).size() > candididates.get(currentNode).size()
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
        }
        else{
            Iterator<Vertex> iter = new DepthFirstIterator<>(query);
            // we do not know the next element or minimum candidate size so take first one we see
            Vertex uNext = iter.next();
            double min = candididates.get(uNext).size();

            // keep track of the vertices we need to check, originally all the vertices in query graph
            ArrayList<Vertex> toCheck = new ArrayList<>();
            toCheck.add(uNext);

            while(iter.hasNext()) {
                // get the graph vertex
                Vertex u = iter.next(); toCheck.add(u);
                if(candididates.get(u).size() < min){
                    uNext = u;
                    min = candididates.get(u).size();
                }
            }

            // add the vertex with the smallest candidate set
            order.add(uNext);
            toCheck.remove(uNext);
            // keep track of cost and total
            double cost = min;
            double total = cost;

            // while there are still nodes to add
            while(toCheck.size()>0){
                Iterator<Vertex> toCheckIter = toCheck.iterator();
                uNext = toCheckIter.next();
                // don't know minimum
                min = calculateSize(query, cost, candididates, order, uNext, gamma);

                while(toCheckIter.hasNext()){
                    Vertex u = toCheckIter.next();
                    double currentSize = calculateSize(query, cost, candididates, order, u, gamma);
                    // choose the minim size
                    if(currentSize<min){
                        uNext = u;
                        min = currentSize;
                    }
                }

                order.add(uNext);
                toCheck.remove(uNext);
                cost = min;
                total += cost;
            }
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
    public static boolean isValid(Graph<Vertex, DefaultEdge> query, Graph<Vertex, DefaultEdge> target,
                                  Map<Vertex, Vertex> currentFunction, Vertex u, Vertex v,
                                  boolean isInduced){
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

        // we didn't find any problems
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
     * @param allFunctionsFound all the solutions that were discoverd
     * @param isInduced whether matching is induced
     */
    public static void subgraphIsomorphism(Graph<Vertex, DefaultEdge> query,
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
     * Computes the subgraph isomorphism and the necessary candidates and order
     * @param query the query graph
     * @param target the target graph
     * @param attributes the attributes (labels) that we are comparing
     * @param isInduced whether matching is induced
     * @param gamma
     * @return the solutions to the subgraph isomorphism between the given graphs
     */
    public static List<Map<Vertex, Vertex>> matching(Graph<Vertex, DefaultEdge> query,
                                                     Graph<Vertex, DefaultEdge> target,
                                                     String[] attributes, boolean isInduced, double gamma,
                                                     boolean groundTruth){
        List<Map<Vertex, Vertex>> results = new ArrayList<>();
        Map<Vertex, Set<Vertex>> candididates = computeCandidates(query, target, attributes, groundTruth);
        ArrayList<Vertex> order = computeProcessingOrder(query, candididates, gamma, groundTruth);
        // keep track of number of backtracking
        numBackTracking = 0;
        subgraphIsomorphism(query, target, candididates, order, 0, new HashMap<>(), results, isInduced);
        return results;
    }

    public static List<String> isomorphismOrdered(List<Map<Vertex, Vertex>>  subgraphIsomorphism){
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
     * @param isInduced whiter isomorphisms are induced
     */
    public static void displayIsomorphism(List<Map<Vertex, Vertex>>  subgraphIsomorphism,
                                          String queryGraphName, String targetGraphName, BufferedWriter writer,
                                          boolean isInduced) throws IOException {

        // print out particular graphs and type and number of isomorphisms
        System.out.print("Query Graph: "+queryGraphName);
        System.out.println(", Target Graph: "+targetGraphName);
        writer.append("Query Graph: "+queryGraphName + ", Target Graph: "+targetGraphName +"\n");

        // print out the number of backjumps
        System.out.println("Number Backtracking: "+numBackTracking);
        writer.append("Number Backtracking: "+numBackTracking +"\n");

        if(isInduced){
            System.out.println("Induced isomorphisms. Total number subgraph isomorphisms: "+subgraphIsomorphism.size());
            writer.append("Induced isomorphisms. Total number subgraph isomorphisms: "+subgraphIsomorphism.size()+"\n");
        }else{
            System.out.println("Non-induced isomorphisms. Total number subgraph isomorphisms: "+subgraphIsomorphism.size());
            writer.append("Non-induced isomorphisms. Total number subgraph isomorphisms: "+subgraphIsomorphism.size()+"\n");
        }

        List<String> isomorphisms = isomorphismOrdered(subgraphIsomorphism);

        int i = 1; // keep track of which isomorphism was printed
        for(String iso: isomorphisms){
            System.out.println("Isomorphism "+ i + ": " +iso);
            writer.append("Isomorphism "+ i + ": " +iso+"\n");
            i++;
        }
        System.out.println();
        writer.append("\n");
    }

    /**
     * Appy subgraph isomorphism if already know both graphs
     * @param queryFileLocation the location of the file containing the query graph information
     * @param targetFileLocation the location of file containing the target graph information
     * @param outputFileName the file which we will write the output to
     * @throws IOException
     */
    public static void subgraphIsomorphismKnownGraphs(String queryFileLocation, String targetFileLocation,
                                                      String outputFileName) throws IOException {
        // read the info from the file
        File queryFile = new File(queryFileLocation);
        File targetFile = new File(targetFileLocation);

        // if we're trying to find the ground truth
        boolean groundTruth = false;
        // write to output file
        BufferedWriter writer = new BufferedWriter(new FileWriter(outputFileName));
        writer.write("");

        // create the graphs
        Graph<Vertex, DefaultEdge> queryGraph = createProteinGraph(queryFile);
        Graph<Vertex, DefaultEdge> targetGraph = createProteinGraph(targetFile);

        boolean isInduced = true;
        // find and display the isomorphisms
        List<Map<Vertex, Vertex>>  subgraphIsomorphismInduced = matching(queryGraph, targetGraph,
                new String[]{"Label"}, isInduced, 0.5, groundTruth);

        displayIsomorphism(subgraphIsomorphismInduced, queryFile.getName(), targetFile.getName(), writer, isInduced);
        System.out.println("============================");
        writer.append("============================\n");

        writer.close();
    }

    /**
     * A function that will copy a vertex and create a new one
     * @param vertex the vertex we are copying
     * @param newId the id of the new vertex
     * @return the copied vertex
     */
    public static Vertex copyVertex(Vertex vertex, int newId){
        // copy the attributes
        Map<String, String> newAttributes = new HashMap<>(vertex.getAttributes());
        return new Vertex(newId, newAttributes);
    }

    /**
     * Create a new graph by performing a random walk on the target graph
     * @param target target graph
     * @param sizeQuery the maximum number of vertices in the query
     * @param outputFileName the file we'll store the information while creating the graph
     * @return the random graph
     * @throws IOException
     */
    public static Graph<Vertex, DefaultEdge> randomGraph(Graph<Vertex, DefaultEdge> target, String targetLocation,
                                                         int sizeQuery, String outputFileName) throws IOException {
        Graph<Vertex, DefaultEdge> queryGraph = new SimpleGraph<>(DefaultEdge.class);
        // get a random vertex
        Random rand = new Random();
        int randVertexID = rand.nextInt(target.vertexSet().size());
        Vertex randVertex = target.vertexSet().stream().filter(vertex -> vertex.getId() == randVertexID).findAny()
                .get();

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
            lastVertex = nextVertex;
        }

        // write the mappings
        // write to output file info when constructing graph
        BufferedWriter writer = new BufferedWriter(new FileWriter(outputFileName));
        writer.write(targetLocation + " \n");
        writer.append(seen.toString()+"\n");
        for(Vertex targetVertex: seen.keySet()){
            writer.append(targetVertex.getId() + " " + targetVertex.getNumProfileSubsets()+"\n");
        }
        writer.close();

        return queryGraph;
    }

    /**
     * Checks to see if the isomorphism is working, by performing subgraph isomorphism on a ground truth file
     * @param groundTruth the ground truth containing the query/target graphs and their isomorphisms
     * @param queryFolderName the location of the query graph
     * @param targetFolderName the location of the target graph
     * @param outputFileName the output file where problems are written
     * @throws IOException
     */
    public static void testAgainstGroundTruth(String groundTruth, String queryFolderName, String targetFolderName,
                                                 String outputFileName) throws IOException {
        // read from ground truth
        BufferedReader br = new BufferedReader(new FileReader(groundTruth));
        String line = br.readLine();

        // write to output file when find error
        BufferedWriter writer = new BufferedWriter(new FileWriter(outputFileName));
        writer.write("There were the following incorrect subgraph isomorphisms: \n");

        while(line!=null){
            // get rid of whitespace
            line = line.strip();

            // check if comment
            if(line.charAt(0) == '#'){
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
                while(line.charAt(0) == '#' || !line.toLowerCase(Locale.ROOT).contains("induced")){
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
                List<Map<Vertex, Vertex>> subgraphIsomorphism = matching(query, target,
                        new String[]{"Label"}, isInduced, 0.5, false);
                List<String> isomorphisms = isomorphismOrdered(subgraphIsomorphism);

                int i = 1; // keep track of which isomorphism was printed
                line = br.readLine().strip();
                for(String iso: isomorphisms){
                    // skip comments
                    while(line.charAt(0) == '#'){
                        line = br.readLine().strip();
                    }
                    String currentMatching = "Isomorphism "+ i + ": " +iso;
                    i++;

                    // compare with ground truth
                    if(!currentMatching.equals(line)){
                        writer.append("Incorrect "+outputString+" Matching! \n"
                                +queryGraphFile.getName() +" : "+targetGraphFile.getName() +"\n");
                        // state the differences
                        writer.append("Correct : "+line+"\n");
                        writer.append("Incorrect (found) : "+currentMatching+"\n");

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
    }

    /**
     * Main function where the graphs are constructed and we find the subgraph isomorphisms
     * @param args the command line arguments
     * @throws IOException
     */
    public static void main(String[] args) throws IOException {
        // get the info on the folder and file
        final String method = args[0];

        // if the two graphs are known
        if(method.equals("KnownGraphs") && args.length == 4) {
            final String queryLocation = args[1];
            final String targetLocation = args[2];
            final String outputFileName = args[3];

            subgraphIsomorphismKnownGraphs(queryLocation, targetLocation, outputFileName);
        }

        else if(method.equals("RandomWalk")  && args.length == 3) {
            // random Walk
            // if we're trying to find the ground truth
            boolean groundTruth = true;
            boolean isInduced = true;

            final String targetLocation = args[1];
            final String outputFolderName = args[2];

            // create the target graph and random query graph
            Graph<Vertex, DefaultEdge> targetGraph = createProteinGraph(new File(targetLocation));
            calculateStatistics(targetGraph, new String[]{"Label"});

            // iterate through the different size of graphs
            for(int size = 5; size<25; size++) {
                // attemt 100 times for each size
                for(int i = 1; i<10; i++) {
                    File outputGraphFolder = new File(outputFolderName + "Graphs\\");
                    int numGraphs = 0;
                    if (outputGraphFolder.list() != null) {
                        numGraphs = outputGraphFolder.list().length;
                    }
                    String graphName = "graph" + (numGraphs + 1) + ".txt";

                    Graph<Vertex, DefaultEdge> queryGraph = randomGraph(targetGraph, targetLocation,
                            size,outputFolderName + "GenerationInfo\\" + graphName);
                    // save the graph
                    String queryFileName = writeGraph(queryGraph, outputFolderName + "Graphs\\", graphName);

                    // find and display the isomorphisms
                    List<Map<Vertex, Vertex>> subgraphIsomorphismInduced = matching(queryGraph, targetGraph,
                            new String[]{"Label"}, isInduced, 0.5, groundTruth);


                    // write to output file
                    BufferedWriter writer = new BufferedWriter(new FileWriter(
                            outputFolderName + "Isomorphism\\" + graphName));
                    writer.write("");
                    displayIsomorphism(subgraphIsomorphismInduced, queryFileName, new File(targetLocation).getName(),
                            writer, isInduced);
                    System.out.println("============================");
                    writer.append("============================\n");

                    writer.close();
                }
            }
        }

        else if(method.equals("Test")  && args.length == 5){
            final String groundTruthFile = args[1];
            final String queryFolderName = args[2];
            final String targetFolderName = args[3];
            final String outputFileName = args[4];

            testAgainstGroundTruth(groundTruthFile, queryFolderName, targetFolderName, outputFileName);
        }

        else{
            System.out.println("Unknown Command.  Please use one of the following:");
            System.out.println("KnownGraphs <queryFile> <targetFile> <outputFile>");
            System.out.println("\t Find the subgraph isomorphism between two know graphs");
            System.out.println("RandomWalk <targetFile> <outputFolder>");
            System.out.println("\t Creates a query graph from the target graph using a random walk.");
            System.out.println("\t Find the subgraph isomorphism between given target graph and random query graph");
            System.out.println("\t Output folder must contain folders: \"GenerationInfo\", \"Graphs\", \"Isomorphism\"");
            System.out.println("Test <groundTruthFile> <queryFolder> <targetFolder> <outputFile>");
            System.out.println("\t Test the subgraph isomorphisms within the ground truth file.");
            System.out.println("\t Must provide the location of the query and target folders.");
            System.out.println("\t If there is any errors in the isomorphism it will be recorded in the output file.");
        }

    }
}
