import java.util.*;

public class Vertex {
    private final int id;
    private String label;
    private ArrayList<String> profile;
    private int numProfileSubsets;

    /**
     * Constructor for vertex.  Must keep track of key and type of chemical
     * @param id the key for the individual vertex (must be unique)
     * @param label the attribute of the vertex
     */
    public Vertex(int id, String label){
        this.id = id;
        this.label = label;
        // keeps track of neighbors attributes
        profile = new ArrayList<>();
        numProfileSubsets = 0;
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
        return (o instanceof Vertex) && (this.getId() == (((Vertex) o).getId()));
    }

    /**
     * Compares current vertex with given vertex based on id
     * @param v vertex to compare to
     * @return how the id compares (0 - equal, 1 - greater than, -1 - less than)
     */
    public int compareTo(Vertex v){
        if(this.id == v.getId()){
            return 0;
        }
        if(this.id < v.getId()){
            return -1;
        }
        return 1;
    }

    /**
     * Check if the desired attributes are equivalent
     * @return if all of the attributes are equal
     */
    public boolean sameLabel(Object o){
        // check both are vertices
        if(o instanceof Vertex){
            // if any of the attributes differ, then not equal
            if(!(label).equals((((Vertex) o).getLabel()))){
                return false;
            }
            // all desired attributes equal
            return true;
        }
        return false;
    }

    /**
     * Find the id
     * @return id of current vertex
     */
    public int getId(){return id;}

    /**
     * Find the attributes
     * @return attributes of current vertex
     */
    public String getLabel() {
        return label;
    }

    /**
     * Find the profile
     * @return profile of current vertex
     */
    public ArrayList<String> getProfile() {
        return profile;
    }

    /**
     * Find the number of profile subsets
     * @return numProfileSubsets of current vertex
     */
    public int getNumProfileSubsets(){ return numProfileSubsets;}

    /**
     * Add the given vertex attribute to the profile of the current vertex.  Profile is always lexicographically sorted
     * @param neighbor the vertex who's attribute is being added to the current vertex profile
     */
    public void addToProfile(Vertex neighbor){
        profile.add(neighbor.getLabel());
        Collections.sort(profile);
    }

    /**
     * Removes the neighbors label from the current vertex profile
     * @param neighbor the vertex being removed
     */
    public void removeFromProfile(Vertex neighbor){
        profile.remove(neighbor.getLabel()); // should remain sorted
    }

    /**
     * Calculates the number of possible subsets for a given vertex profile.  Includes the empty set and each entry must
     * be unique.
     * @return all the possible subsets
     */
    public ArrayList<ArrayList<String>> calculateNumberProfileSubsets(){
        // keep track of the possible profile subsets
        ArrayList<ArrayList<String>> possibleSubsets = new ArrayList<>();
        // base case, size of 0
        possibleSubsets.add(new ArrayList<>());

        // iterate through all of the attributes, order does not matter so add alphabetically
        for(String a: profile) {
            // keep track of the previous subsets before adding next element and iterate through them
            ArrayList<ArrayList<String>> savedSubsets = new ArrayList<>(possibleSubsets);
            for (ArrayList<String> previousSubsets : savedSubsets) {
                // create a copy of the subset to add the attribute to
                ArrayList<String> newSubset = new ArrayList<>(previousSubsets);
                newSubset.add(a);

                // check if already subset
                if (!possibleSubsets.contains(newSubset)) {
                    possibleSubsets.add(newSubset);
                }
            }
        }
        numProfileSubsets=possibleSubsets.size();

        // return the possible values it can be
        return possibleSubsets;
    }

    /**
     * Checks if the main contains all of the subset elements.  Accounts for duplicates.
     * @param main the main array that contents is being checked
     * @param subset the subset array that is being check if subset of main
     * @return if main contains all the elements in subset
     */
    private boolean listContainsAll(List<String> main, List<String> subset){
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
        if(contains && i == subset.size()){
            return true;
        }
        return false;
    }

    /**
     * Checks if the given vertex profile is a subset of the current vertex profile, given some attributes
     * @param neighbor the vertex who's being compared to the current vertex profile
     * @return if it is a subset
     */
    public boolean profileSubset(Vertex neighbor){
        // build up individual profiles for current attribute
        ArrayList<String> attributeProfileCurrent = profile;
        ArrayList<String> attributeProfileNeighbor = neighbor.getProfile();

        if(!listContainsAll(attributeProfileNeighbor, attributeProfileCurrent)){
            return false;
        }

        // all desired attributes equal
        return true;
    }
}
