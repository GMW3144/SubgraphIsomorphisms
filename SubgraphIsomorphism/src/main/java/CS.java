import org.jgrapht.Graph;
import org.jgrapht.Graphs;
import org.jgrapht.alg.interfaces.MatchingAlgorithm;
import org.jgrapht.alg.matching.HopcroftKarpMaximumCardinalityBipartiteMatching;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.DirectedAcyclicGraph;
import org.jgrapht.graph.Multigraph;
import org.jgrapht.graph.SimpleGraph;

import java.util.*;

public class CS {
    private Graph<Vertex, LabeledEdge> cs; // the CS structure
    private DirectedAcyclicGraph<Vertex, DefaultEdge> queryDAG; // the DAG
    private int numRefined; // the number refined from CS structure

    /**
     * Create the CS structure from the DAG
     * @param query the query graph
     * @param target the target graph
     * @param candidates the candidates
     * @param queryDAG the queryDAG
     */
    public CS(Graph<Vertex, DefaultEdge> query, Graph<Vertex, DefaultEdge> target, Map<Vertex, Set<Vertex>> candidates,
              DirectedAcyclicGraph<Vertex, DefaultEdge> queryDAG){
        this.queryDAG = queryDAG;
        numRefined = 0;

        refineCS(query, target, candidates);
        materializeCS(target, candidates);
    }

    /**
     * Refine the candidate set for the CS structure
     * @param query the query graph
     * @param target the target graph
     * @param candidates the candidate set
     */
    public void refineCS(Graph<Vertex, DefaultEdge> query, Graph<Vertex, DefaultEdge> target,
                                Map<Vertex, Set<Vertex>> candidates){
        boolean isRefined = true;
        int count = 0;

        // keep refining until we don't any more
        while(isRefined){
            isRefined = false;

            // alternate between children and parent
            boolean reverse = count % 2 != 0;
            count++;

            // set the parents/children to empty sets initially
            Map<Vertex, Set<Vertex>> toCheck = new HashMap<>();
            for(Vertex u : query.vertexSet()){
                toCheck.put(u, new HashSet<>());
            }

            // add the parents/children
            for(Vertex u: queryDAG.vertexSet()){
                if(reverse){
                    for(DefaultEdge e:queryDAG.incomingEdgesOf(u)){
                        Vertex uP = queryDAG.getEdgeSource(e);
                        toCheck.get(u).add(uP);
                    }
                }
                else{
                    for(DefaultEdge e:queryDAG.outgoingEdgesOf(u)){
                        Vertex uP = queryDAG.getEdgeTarget(e);
                        toCheck.get(u).add(uP);
                    }
                }
            }

            Set<Vertex> processed = new HashSet<>();
            while(processed.size()<query.vertexSet().size()){
                for(Vertex u: query.vertexSet()){
                    if(processed.containsAll(toCheck.get(u))){
                        processed.add(u);
                        Set<Vertex> toRemove = new HashSet<>();
                        for(Vertex v: candidates.get(u)){
                            // create a new graph, which will be the bipartite graph
                            Graph<Vertex, DefaultEdge> B = new SimpleGraph<>(DefaultEdge.class);
                            // keep track of where the copy came from
                            Map<Vertex, Vertex> copyToOriginal = new HashMap<>(); int id = 0;

                            // keep track of u neighbors added
                            Set<Vertex> uPVertices = new HashSet<>();
                            Set<Vertex> vPVertices = new HashSet<>();

                            // add the neighbors of v
                            for(Vertex vP: Graphs.neighborListOf(target,v)){
                                Vertex vPCopy = SubgraphIsomorphism.copyVertex(vP, id); id++;
                                copyToOriginal.put(vPCopy, vP);

                                B.addVertex(vPCopy);
                                vPVertices.add(vPCopy);
                            }

                            // add the vertices to check
                            for(Vertex uP: toCheck.get(u)) {
                                Vertex uPCopy = SubgraphIsomorphism.copyVertex(uP, id);
                                id++;
                                copyToOriginal.put(uPCopy, uP);

                                B.addVertex(uPCopy);
                                uPVertices.add(uPCopy);
                            }

                            // add the edges
                            for(Vertex uP: uPVertices){
                                for(Vertex vP: vPVertices){
                                    if(candidates.get(copyToOriginal.get(uP)).contains(copyToOriginal.get(vP))){
                                        B.addEdge(uP, vP);
                                    }
                                }
                            }

                            // find the maximum matching of B
                            HopcroftKarpMaximumCardinalityBipartiteMatching<Vertex, DefaultEdge> matchingAlgorithm =
                                    new HopcroftKarpMaximumCardinalityBipartiteMatching<>(B, uPVertices, vPVertices);
                            MatchingAlgorithm.Matching<Vertex, DefaultEdge> bipartiteMatching = matchingAlgorithm.getMatching();

                            // matching does not contain all query vertices
                            if(bipartiteMatching.getEdges().size() != uPVertices.size()){
                                toRemove.add(v);
                                isRefined = true;
                            }

                        }
                        numRefined+=toRemove.size();
                        candidates.get(u).removeAll(toRemove);
                    }
                }
            }
        }
    }

    /**
     * Construct the CS structure
     * @param target the target graph
     * @param candidates the candidates
     */
    public void materializeCS(Graph<Vertex, DefaultEdge> target, Map<Vertex, Set<Vertex>> candidates){
        // CS is initially a graph with multiple edges between two vertices
        cs = new Multigraph<>(LabeledEdge.class);
        // iterate through the vertices
        for(Vertex u: queryDAG.vertexSet()){
            // and their parents
            for(DefaultEdge e: queryDAG.incomingEdgesOf(u)){
                Vertex uP = queryDAG.getEdgeSource(e);
                // iterate through their candidates
                for(Vertex vP : candidates.get(uP)){
                    for(Vertex v: candidates.get(u)){
                        // add new edge if there exists one within target graph
                        if(target.containsEdge(v, vP)){
                            if(!cs.containsVertex(v)){
                                cs.addVertex(v);
                            }
                            if(!cs.containsVertex(vP)){
                                cs.addVertex(vP);
                            }

                            cs.addEdge(vP, v, new LabeledEdge(uP+"-"+u));
                        }
                    }
                }
            }
        }
    }

    /**
     * Get the edge set from the CS structure
     * @return the edges of the cs structure
     */
    public Set<LabeledEdge> getEdgeSet(){
        return cs.edgeSet();
    }

    /**
     * Get the neighbors of the vertex from the CS structure
     * @param v the vertex within cs structure
     * @return the neighbors of v in cs
     */
    public List<Vertex> neighborsOf(Vertex v){
        return Graphs.neighborListOf(cs, v);
    }

    /**
     * Get the number of vertices that are refined within CS structure
     * @return numRefined
     */
    public int getNumRefined(){
        return numRefined;
    }
}
