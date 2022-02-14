import org.jgrapht.Graph;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.SimpleGraph;

import java.util.HashMap;
import java.util.Map;

public class QISequence {
    // tree information
    private Graph<Vertex, DefaultEdge> T; // the tree structure
    private Map<Vertex, Vertex> parent; // the child/parent pairs
    private Map<Integer, Vertex> order; // the order the vertex are in the tree

    // extra topology information
    private Map<Vertex, Integer> deg; // the degree information (if greater than 2)
    private Map<Vertex, Vertex> edge; // the edge information (if j<i)

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
    }

    /**
     * Add a vertex to the QI-Sequence
     * @param u the vertex to be added
     * @param uP the parent of the vertex
     * @return position of the vertex within the QI-Sequence
     */
    public int addVertex(Vertex u, Vertex uP){
        // add vertex to the tree structure
        T.addVertex(u);
        // add the edge between the parent and child
        T.addEdge(u, uP);

        // add the parent
        parent.put(u, uP);

        // add to order
        order.put(order.size(), u);

        return order.size()-1;
    }

    /**
     * Add the extra edge information to the QI-Sequence
     * @param u the first vertex
     * @param v the second (adjacent) vertex
     */
    public void extraEdge(Vertex u, Vertex v){
        if(u.getId()<v.getId()){
            edge.put(u, v);
        }
        else{
            edge.put(v, u);
        }
    }

    /**
     * Add extra degree information
     * @param u the vertex
     * @param d the degree of the vertex
     */
    public void extraDeg(Vertex u, int d){
        deg.put(u, d);
    }
}
