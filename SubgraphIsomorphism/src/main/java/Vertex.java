import java.util.*;

public class Vertex {
    private final int id;
    private Map<String, String> attributes;
    private ArrayList<Map<String, String>> profile;
    private Map<String, Integer> numProfileSubsets;

    /**
     * Constructor for vertex.  Must keep track of key and type of chemical
     * @param id the key for the individual vertex (must be unique)
     * @param attributes the attributes of the vertex
     */
    public Vertex(int id, Map<String, String> attributes){
        this.id = id;
        this.attributes = attributes;
        // keeps track of neighbors attributes
        profile = new ArrayList<>();
        numProfileSubsets = new HashMap<>();
    }

    /**
     * Finds the vertex and corresponding chemical
     * @return the chemical
     */
    public String toString(){
        return String.valueOf(id);
    }

    /**
     * Overrides the Hashcode to be dependent on the key
     * @return the hashcode for the vertex
     */
    public int hashCode(){
        return id;
    }

    /**
     * An individual vertex is determined by its ID
     * @param o the other object being compared
     * @return if the two objects are equal
     */
    public boolean equals(Object o){
        return (o instanceof Vertex) && (id == (((Vertex) o).id));
    }

    /**
     * Check if the desired attributes are equivalent
     * @param attributesToCheck attributes to be checked
     * @return if all of the attributes are equal
     */
    public boolean sameAttributes(String[] attributesToCheck, Object o){
        // check both are vertices
        if(o instanceof Vertex){
            for(String a: attributesToCheck){
                // if any of the attributes differ, then not equal
                if(!(attributes.get(a)).equals((((Vertex) o).getAttributes()).get(a))){
                    return false;
                }
            }
            // all desired attributes equal
            return true;
        }
        return false;
    }

    public int getId(){return id;}

    public Map<String, String> getAttributes() {
        return attributes;
    }

    public ArrayList<Map<String, String>> getProfile() {
        return profile;
    }

    public Map<String, Integer> getNumProfileSubsets(){ return numProfileSubsets;}

    public void addToProfile(Vertex neighbor){
        profile.add(neighbor.getAttributes());
    }

    public Map<String, Set<String>> calculateNumberProfileSubsets(String[] attributesToCheck){
        // keep track of the possible values for each attributes
        Map<String, Set<String>> possibleValues = new HashMap<>();

        // iterate through the attributes
        for(String attribute: attributesToCheck){
            // build up individual profiles for current attribute
            ArrayList<String> attributeProfile = new ArrayList<>();
            // Current vertex labels for specific attribute
            for(Map<String, String> currentP: profile){
                attributeProfile.add(currentP.get(attribute));
            }
            Collections.sort(attributeProfile);

            // keep track of the possible profile subsets
            ArrayList<ArrayList<String>> possibleSubsets = new ArrayList<>();
            // base case, size of 0
            possibleSubsets.add(new ArrayList<>());

            // iterate through all of the attributes, order does not matter so add alphabetically
            for(String a: attributeProfile){
                // keep track of the previous subsets before adding next element and iterate through them
                ArrayList<ArrayList<String>> savedSubsets = new ArrayList<>(possibleSubsets);
                for(ArrayList<String> previousSubsets: savedSubsets){
                    // create a copy of the subset to add the attribute to
                    ArrayList<String> newSubset = new ArrayList<>(previousSubsets);
                    newSubset.add(a);

                    // check if already subset
                    if(!possibleSubsets.contains(newSubset)) {
                        possibleSubsets.add(newSubset);
                    }
                }
            }
            numProfileSubsets.put(attribute, possibleSubsets.size());
            possibleValues.put(attribute, new HashSet<>(attributeProfile));
        }

        // return the possible values it can be
        return possibleValues;
    }

    public boolean profileSubset(Vertex neighbor, String[] attributesToCheck){
        // check each attribute
        for(String a: attributesToCheck){
            // build up individual profiles for current attribute
            ArrayList<String> attributeProfileCurrent = new ArrayList<>();
            ArrayList<String> attributeProfileNeighbor = new ArrayList<>();

            // Current vertex labels for specific attribute
            for(Map<String, String> currentP: profile){
                attributeProfileCurrent.add(currentP.get(a));
            }

            // Neigbhor labels for specific attribute
            for(Map<String, String> currentN: neighbor.getProfile()){
                attributeProfileNeighbor.add(currentN.get(a));
            }

            if(!attributeProfileNeighbor.containsAll(attributeProfileCurrent)){
                return false;
            }
        }
        // all desired attributes equal
        return true;
    }
}