import org.jgrapht.Graph;
import org.jgrapht.Graphs;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.SimpleGraph;
import org.jgrapht.traverse.DepthFirstIterator;

import java.io.*;
import java.util.*;

public class HardToFindStarGraphs {
    private Map<List<Vertex>, Integer> numCombined = null; // keep track of the statistics when combine graphs
    private final String formatTarget;

    // creating graphs from star graph
    public final String MERGE = "merge";
    public final String EDGE = "edge";
    public final String NONE = "none";

    // error message if didn't find connection algorithm
    private final String noConnectionMethodFound = "Connection type of graphs specified is not valid.\n " +
            "Specify one of the following connections methods: \n" +
            "\t "+MERGE+": merge two vertices of the same label.\n" +
            "\t "+EDGE+": create an edge between two vertices.\n " +
            "\t "+NONE+": use star graph of largest size.\n";
    // error message if threshold is too high
    private final String thresholdToHigh = "Threshold too large for graph or graphs not connectable";
    // error message if minimum support is too high
    private static final String minSupToHigh = "Minimum support too large for graph";

    public HardToFindStarGraphs(String formatTarget){
        this.formatTarget = formatTarget;
    }

    /**
     * Performs apriori generation on a given large itemset.  Given that the large itemsets are of size k-1, it will
     * create candidates of size k
     * @param LkMin1 large itemsets of size k-1
     * @return the candidates generated from the large itemsets
     */
    private List<List<String>> aprioriGen(List<List<String>> LkMin1){
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
    private void aprioriPrune(List<List<String>> LkMin1, List<List<String>>Ck){

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
     * Checks if the main contains all of the subset elements.  Accounts for duplicates.
     * @param main the main array that contents is being checked
     * @param subset the subset array that is being check if subset of main
     * @return if main contains all the elements in subset
     */
    public boolean listContainsAll(List<String> main, List<String> subset){
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
     * Perform apriori algorithm on the given transactions and attributes.  Also must provide the possible items and
     * minimum support
     * @param transactions the set of transactions within the database
     * @param items the set of possible items within the transactions
     * @param minSup the minim support for the association rules
     * @return the large itemsets (profiles)
     */
    private Map<List<String>, Set<Integer>> aprioriAlgo(Map<Integer, List<String>> transactions,
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
     * Given star graphs and the number of times they occur within the target graph, return the index of the most
     * frequent star graph
     * @param starGraphs the star graphs
     * @param starGraphsProfiles the profile of the root of the star graph
     * @param numberTimesRootOccurs the number of times the star graph of a given profile occurs
     * @return the index of the most frequent star graph
     */
    public int findMostFrequentStructure(List<Graph<Vertex, DefaultEdge>> starGraphs,
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
    public List<Vertex> findLeafNodes(Graph<Vertex, DefaultEdge> graph){
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
    public int addSubgraph(Graph<Vertex, DefaultEdge> combinedGraph, Graph<Vertex, DefaultEdge> graph, int id,
                                  Map<Vertex, Vertex> oldToNew){

        // add vertices to graph
        for(Vertex v: graph.vertexSet()){
            Vertex copyVertex = SubgraphIsomorphism.copyVertex(v, id);
            SubgraphIsomorphism.addVertex(combinedGraph, copyVertex);
            oldToNew.put(v, copyVertex);
            id++;
        }

        // add original edges back in
        for(Vertex v: graph.vertexSet()){
            for(Vertex u: Graphs.neighborListOf(graph, v)) {
                Vertex vP = oldToNew.get(v);
                Vertex uP = oldToNew.get(u);
                if(!combinedGraph.containsEdge(vP, uP)) {
                    SubgraphIsomorphism.addEdge(combinedGraph, vP, uP);
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
    public Graph<Vertex, DefaultEdge> unionGraphsByMerge(Graph<Vertex, DefaultEdge> target,
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
                SubgraphIsomorphism.addEdge(combinedGraph, v2, v);
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
    public Graph<Vertex, DefaultEdge> unionGraphsByEdge(Graph<Vertex, DefaultEdge> target,
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

            SubgraphIsomorphism.addEdge(combinedGraph, v1, v2);

            List<Vertex> edgeInfo = new ArrayList<>();
            edgeInfo.add(v1); edgeInfo.add(v2);
            numCombined.put(edgeInfo, possibleEdges.get(edge));
        }

        return combinedGraph;
    }

    /**
     * Convert the graphs profiles into a transactional database.  Then perform apriori algorithm on the new database
     * @param targetFileLocation the location of the target graph
     * @param outputFileName where we will output the findings
     * @param minSup the minimum support
     * @throws IOException for read/write files
     */
    public void frequentDatasetMining(String targetFileLocation, String outputFileName, double minSup)
            throws IOException {
        // read the info from the file
        File targetFile = new File(targetFileLocation);

        // write to output file
        BufferedWriter writer = new BufferedWriter(new FileWriter(outputFileName));
        writer.write("");

        // create the graphs
        Graph<Vertex, DefaultEdge> targetGraph = SubgraphIsomorphism.readGraph(targetFile, formatTarget);
        if (targetGraph == null) {
            System.out.println("Target File: ");
            System.out.println(SubgraphIsomorphism.noGraphFormat);
            return;
        }

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

            List<String> vProfile = v.getProfile();
            transactions.put(vid, vProfile);

            // iterate through the vertex attributes
            // add to the possible label set
            possibleItems.addAll(vProfile);
        }

        Map<List<String>, Set<Integer>> frequentItemsets = aprioriAlgo(transactions, possibleItems, minSup);

        // print out the information about the variables
        if (minSup <= 1) {
            minSup = minSup * transactions.size();
        }
        String graphInfo = "Graph: " + targetFile.getName() + "(" + targetFileLocation + ")" +
                "\nNumber of Nodes: " + transactions.size() +
                "\nMinimum Support (integer): " + minSup +
                "\nMinimum Support (percentage): " + minSup / transactions.size();
        System.out.println(graphInfo);
        writer.append(graphInfo).append("\n");

        if (frequentItemsets.isEmpty()) {
            System.out.println(minSupToHigh);
            writer.write(minSupToHigh);
            writer.close();
            return;
        }

        // keep track of the union of all the frequent profiles
        List<String> outputValues = new ArrayList<>();
        for (List<String> itemset : frequentItemsets.keySet()) {
            outputValues.add(itemset + " appears in " + frequentItemsets.get(itemset).size() + " vertex profiles:\n"
                    + frequentItemsets.get(itemset) + " \n\n");
        }
        // sort the frequent profiles and print in order
        Collections.sort(outputValues);
        for (String output : outputValues) {
            for (int i = 0; i < output.length(); i++) {
                char c = output.charAt(i);
                if (c == ']') {
                    break;
                }
                System.out.print(c);
            }
            int numOccurrences = 0;
            for (String word : output.split(" ")) {
                try {
                    numOccurrences = Integer.parseInt(word);
                    break;
                } catch (NumberFormatException ignored) {
                }
            }
            System.out.println("]" + ":" + numOccurrences);
            writer.append(output);
        }

        writer.close();
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
    public void fdmGraph(String fdmFileLocation, String outputFolderName, boolean isInduced, int profileSize,
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
                target = SubgraphIsomorphism.readGraph(new File(graphLocation), formatTarget);
                if(target == null){
                    System.out.println("Target File: ");
                    System.out.println(SubgraphIsomorphism.noGraphFormat);
                    return;
                }
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
            System.out.println("No target graph found.  Format as follows:\n" +SubgraphIsomorphism.graphProteinsFileFormat);
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
            SubgraphIsomorphism.addVertex(query, root);

            currentId++;
            // add the other vertices and their edges
            for (String neighborLabel : neighbors) {
                // add the vertex, update profile
                Vertex neighbor = new Vertex(currentId, neighborLabel);
                SubgraphIsomorphism.addVertex(query, neighbor);

                // add the edge, update profile
                SubgraphIsomorphism.addEdge(query, root, neighbor);
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
        Graph<Vertex, DefaultEdge> query; numCombined = new HashMap<>();
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
        String queryFileName = SubgraphIsomorphism.writeGraph(query, outputFolderName + "Graphs\\", graphName);
        String queryName = new File(queryFileName).getName();
        String targetName = new File(graphLocation).getName();

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
        List<Map<Vertex, Vertex>> subgraphIsomorphism = SubgraphIsomorphism.matching(query, target, isInduced, gamma);

        writer.append("\n");
        // write to statistics file
        SubgraphIsomorphism.displayGraphStatistics(queryName, query, targetName, target, writer);
        writer.close();

        if(subgraphIsomorphism == null){
            // write to output files
            writer = new BufferedWriter(new FileWriter(
                    outputFolderName + "Isomorphism\\" + graphName));
            writer.write(SubgraphIsomorphism.noAlgorithmFound);
            writer.close();
            return;
        }
        // write to output file
        writer = new BufferedWriter(new FileWriter(
                outputFolderName + "Isomorphism\\" + graphName));
        writer.write("");
        SubgraphIsomorphism.displayIsomorphism(subgraphIsomorphism, queryName, targetName, writer, isInduced);
        System.out.println("============================");
        writer.append("============================\n");

        writer.close();
    }

    /**
     * Get the combination information of two graphs
     * @return the combination information
     */
    public Map<List<Vertex>, Integer> getNumCombined(){
        return numCombined;
    }
}
