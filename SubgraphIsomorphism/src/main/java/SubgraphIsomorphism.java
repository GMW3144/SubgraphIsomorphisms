import org.jgrapht.*;
import org.jgrapht.graph.*;
import org.jgrapht.traverse.BreadthFirstIterator;
import org.jgrapht.traverse.DepthFirstIterator;
import org.jgrapht.traverse.RandomWalkVertexIterator;

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
        String line = br.readLine();

        // get the number of vertices first
        int numberVertices = Integer.parseInt(line);
        line = br.readLine();

        // iterate through the vertices
        for(int i = 0; i < numberVertices; i++) {
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

        // todo having difficulty finding all the possible subsets given the labels and max degree
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


        return candidates;
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
     * @param queryFileName the file containing the query graph information
     * @param targetFileName the file containing the target graph information
     * @param outputFolderName the file which we will write the output to
     * @param mainFolder the main folder that contains the graphs
     * @throws IOException
     */
    public static void subgraphIsomorphismKnownGraphs(String queryFileName, String targetFileName,
                                                      String outputFolderName, String mainFolder) throws IOException {
        // find the individual folder for each
        File queryFolder = new File(mainFolder + "query/");
        File targetFolder = new File(mainFolder + "target/");
        String outputFileName = outputFolderName + "test.txt";

        // read the info from the file
        File queryFile = new File(queryFolder, queryFileName);
        File targetFile = new File(targetFolder, targetFileName);

        // if we're trying to find the ground truth
        boolean groundTruth = true;
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

        displayIsomorphism(subgraphIsomorphismInduced, queryFileName, targetFileName, writer, isInduced);
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
    public static Graph<Vertex, DefaultEdge> randomGraph(Graph<Vertex, DefaultEdge> target, int sizeQuery,
                                                         String outputFileName) throws IOException {
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
        writer.write(seen.toString()+"\n");
        for(Vertex targetVertex: seen.keySet()){
            writer.append(targetVertex.getId() + " " + targetVertex.getNumProfileSubsets()+"\n");
        }
        writer.close();

        return queryGraph;
    }

    /**
     * Main function where the graphs are constructed and we find the subgraph isomorphisms
     * @param args the command line arguments
     * @throws IOException
     */
    public static void main(String[] args) throws IOException {
        // get the info on the folder and file
        final String proteinsFolder = args[0];
        final String outputFolderName = args[1];
        final String targetFileName = args[2];

        // if the two graphs are known
        if(args.length == 4) {
            final String queryFileName = args[3];
            subgraphIsomorphismKnownGraphs(queryFileName, targetFileName, outputFolderName, proteinsFolder);
            return;
        }

        // random Walk
        boolean randomWalk = true;
        // if we're trying to find the ground truth
        boolean groundTruth = false;
        boolean isInduced = true;

        if(randomWalk) {
            // create the target graph and random query graph
            Graph<Vertex, DefaultEdge> targetGraph = createProteinGraph(
                    new File(proteinsFolder + "target/" + targetFileName));
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

                    Graph<Vertex, DefaultEdge> queryGraph = randomGraph(targetGraph, size,
                            outputFolderName + "GenerationInfo\\" + graphName);
                    // save the graph
                    String queryFileName = writeGraph(queryGraph, outputFolderName + "Graphs\\", graphName);

                    // find and display the isomorphisms
                    List<Map<Vertex, Vertex>> subgraphIsomorphismInduced = matching(queryGraph, targetGraph,
                            new String[]{"Label"}, isInduced, 0.5, groundTruth);


                    // write to output file
                    BufferedWriter writer = new BufferedWriter(new FileWriter(
                            outputFolderName + "Isomorphism\\" + graphName));
                    writer.write("");
                    displayIsomorphism(subgraphIsomorphismInduced, queryFileName, targetFileName, writer, isInduced);
                    System.out.println("============================");
                    writer.append("============================\n");

                    writer.close();
                }
            }
        }

    }
}
