import org.apache.commons.math3.stat.descriptive.StatisticalSummary;
import org.apache.commons.math3.stat.descriptive.SummaryStatistics;
import org.jgrapht.Graph;
import org.jgrapht.Graphs;
import org.jgrapht.graph.DefaultEdge;

import java.util.*;

public class WanderJoins {

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
    public double randomWalkWJ(ArrayList<Vertex> order, Map<Vertex, Set<Vertex>> candidates , QISequence SEQq,
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
            Vertex vNext = SubgraphIsomorphism.randomVertex(possibleVertices);
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
        Vertex vNext = SubgraphIsomorphism.randomVertex(possibleVertices);
        walk.add(vNext);
        return randomWalkWJ(order, candidates, SEQq, i+1, walk, target)*possibleVertices.size();
    }

    /**
     * Finds the confidence interval for a Egiven set of values
     * @param stats the cost values
     * @param zScore the alpha+1/2 quantile of the normal distribution with mean 0 and variance 1
     * @return the confidence interval
     */
    public static double computeConfidenceInterval(StatisticalSummary stats, double zScore){
        // the average
        double variance = Math.sqrt(stats.getVariance());

        return zScore * variance / Math.sqrt(stats.getN());
    }

    /**
     * Performs Wander Join to estimate the number of matchings or backtrackings for a given isomorphism
     * @param query the query graph
     * @param target the target graph
     * @param gamma the gamma value for GraphQL
     * @param tau the confidence interval threshold
     * @param maxEpoch the maximum number of random walks
     * @param zScore the z score for confidence interval
     * @param isInduced if the isomorphism is induced
     * @return the overall estimation for the subgraph isomorphism
     */
    public double wanderJoins(Graph<Vertex, DefaultEdge> query, Graph<Vertex, DefaultEdge> target, double gamma,
                                     double tau, int maxEpoch, double zScore, boolean isInduced){
        // compute candidates
        Map<Vertex, Set<Vertex>> candidates = SubgraphIsomorphism.computeCandidates(query, target);
        if(candidates == null){
            System.out.println("Invalid Candidates.  Might be invalid algorithm:");
            System.out.println(SubgraphIsomorphism.noAlgorithmFound);
            // something went wrong
            return -1;
        }
        // compute processing order
        ArrayList<Vertex> order = SubgraphIsomorphism.computeProcessingOrder(query, target, candidates, gamma);
        if(order == null){
            System.out.println("Invalid Processing Order.  Might be invalid algorithm:");
            System.out.println(SubgraphIsomorphism.noAlgorithmFound);
            // something went wrong
            return -1;
        }

        // compute the spanning tree, must have one root
        QISequence SEQq = SubgraphIsomorphism.buildSpanningTreeWithOrder(query, order);

        // keep track of the costs we have seen
        SummaryStatistics stats = new SummaryStatistics();

        while (stats.getN()<maxEpoch){
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
            stats.addValue(cost);

            // every 20 check the confidence value
            if(stats.getN()%1000 == 0){
                double conf = computeConfidenceInterval(stats, zScore);
                if(conf<tau) {
                    break;
                }
            }
        }

        // average the cost values
        double avgCost = stats.getMean();

        // round to nearest integer
        return Math.round(avgCost);
    }
}
