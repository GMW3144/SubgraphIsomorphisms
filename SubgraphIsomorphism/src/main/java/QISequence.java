import org.jgrapht.Graph;
import org.jgrapht.Graphs;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.SimpleGraph;

import java.util.*;

public class QISequence {
    // tree information
    private Graph<Vertex, DefaultEdge> T; // the tree structure
    private Map<Vertex, Integer> parent; // the child/parent pairs
    private Map<Integer, Vertex> order; // the order the vertex are in the tree

    // extra topology information
    private Map<Vertex, Integer> deg; // the degree information (if greater than 2)
    private Map<Vertex, List<Vertex>> edge; // the edge information (if j<i)
    private Map<Vertex, List<Vertex>> noEdge; // the values where there is no edges (j<i)

    /**
     * Constructor for QI-Sequence.
     * Everything initially empty
     */
    public QISequence(){
        T = new SimpleGraph<>(DefaultEdge.class);
        parent = new HashMap<>();
        order = new HashMap<>();

        deg = new HashMap<>();
        edge = new HashMap<>();
        noEdge = new HashMap<>();
    }

    /**
     * Add a vertex to the QI-Sequence
     * @param u the vertex to be added
     * @param uP the parent of the vertex
     * @return position of the vertex within the QI-Sequence
     */
    public int addVertex(Vertex u, Integer uP){
        // add vertex to the tree structure
        T.addVertex(u);
        // add the edge between the parent and child if not the root
        if(uP!=-1) {
            T.addEdge(u, order.get(uP));
        }

        // add the parent
        parent.put(u, uP);

        // add to order
        order.put(order.size(), u);

        return order.size()-1;
    }

    /**
     * Add the extra edge information to the QI-Sequence.  Note u will contain v, so u should come first in the order.
     * @param u the first vertex
     * @param v the second (adjacent) vertex
     */
    public void extraEdge(Vertex u, Vertex v){
        // only add edge once
        // first time seeing vertex
        if(!edge.containsKey(u)){
            edge.put(u, new ArrayList<>());
        }
        // add the edge
        edge.get(u).add(v);
    }

    /**
     * Add the no extra edge information to the QI-Sequence. Note u will contain v, so u should come first in the order.
     * @param u the first vertex
     * @param v the second (adjacent) vertex
     */
    public void noExtraEdge(Vertex u, Vertex v){
        // first check if it is contained within the tree
        if(T.containsEdge(u, v)){
            return;
        }
        // only add edge once
        // first time seeing vertex
        if(!noEdge.containsKey(u)){
            noEdge.put(u, new ArrayList<>());
        }
        // add the edge
        noEdge.get(u).add(v);
    }

    /**
     * Add extra degree information
     * @param u the vertex
     * @param d the degree of the vertex
     */
    public void extraDeg(Vertex u, int d){
        deg.put(u, d);
    }

    /**
     * Check to see if a vertex is contained in the QI-Sequence
     * @param u the vertex
     * @return check if the vertex is contained within the QI-Sequence
     */
    public boolean containsVertex(Vertex u){
        for(Vertex v: parent.keySet()){
            if(u.equals(v)){
                return true;
            }
        }
        return false;
    }

    /**
     * Get the current vertices within the QI-Sequence
     * @return the vertices within the QI-Sequence
     */
    public Set<Vertex> currentVertices(){
        return parent.keySet();
    }

    /**
     * Finds and returns the order
     * @return the order of the QI-Sequence
     */
    public Map<Integer, Vertex> getOrder(){
        return order;
    }

    /**
     * Finds and returns the tree structure
     * @return the tree structure
     */
    public Graph<Vertex, DefaultEdge> getT(){
        return T;
    }

    /**
     * Find and return the extra edge topology given a vertex
     * @param u the given vertex
     * @return the extra edges
     */
    public List<Vertex> getExtraEdges(Vertex u){
        if(edge.containsKey(u)) {
            return edge.get(u);
        }
        else{
            return new ArrayList<>();
        }
    }

    /**
     * Get the extra edge information for the QI-sequence
     * @return the extra edge information
     */
    public Map<Vertex, List<Vertex>> getEdge(){ return edge; }

    /**
     * Finds the parent of the given vertex
     * @param u the vertex
     * @return parent vertex of u
     */
    public Vertex getParent(Vertex u){
        return order.get(parent.get(u));
    }

    /**
     * Gets the neighbors for a particular vertex
     * @param u the vertex we would like to get the neighbors
     * @return the neighbor of u
     */
    public List<Vertex> getNeighbors(Vertex u){
        List<Vertex> neighbors = Graphs.neighborListOf(T, u);
        return neighbors;
    }
}
