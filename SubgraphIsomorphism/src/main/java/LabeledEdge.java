import org.jgrapht.graph.DefaultEdge;

public class LabeledEdge extends DefaultEdge {
    private String label; // the label of the edge

    /**
     * Constructor for labeled edge.  Must keep track label
     * @param label the attribute of the edge
     */
    public LabeledEdge(String label){
        this.label = label;
    }

    /**
     * Finds the label of the edge
     * @return the label of the edge
     */
    public String getLabel(){
        return label;
    }

    /**
     * Finds corresponding vertices and label
     * @return a string representation of the edge
     */
    public String toString(){
        return "("+getSource() +":'"+label+"':"+getTarget()+")";
    }
}
