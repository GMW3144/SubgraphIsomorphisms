# SubgraphIsomorphisms

Subgraph Isomorphism is finding instances of a query graph in a larger target graph.  This program does a number of tasks relating to subgraph matching, and the main function exists within "SubgraphIsomorphism.java" (within SubgraphIsomorphism folder).  It is used as follows: <br />
- **KnownGraphs \<queryFile\> \<targetFile\> \<isomorphismsFileName\> \<statisticsFile\> -**
Find the subgraph isomorphism between two know graphs. Writes Isomorphisms to isomorphismsFileName and statistics to statisticsFile.<br />
- **Estimate \<queryFile\> \<targetFile\> \<outputFile\> -**
Find the estimate of the number of matchings between two graphs. Writes estimation to outputFile. <br />
- **TestEstimations \<isomorphismFolder\> \<queryFolder\> \<targetFolder\> \<outputFile\> -**
Find the estimate of the number of matchings for all of the isomorphisms within the folder and compare with the actual. Writes information to outputFile. Must provide the location of the query and target folders.  If path is contained within 
isomorphism files, then give argument '\_'. <br />
- **FrequentDatasets \<targetFile\> \<outputFile\> \<minSup\> -**
Finds the frequent profile subsets from the given graphs and minimum support. <br /> 
- **FDMQuery \<FDMFile\> \<outputFolder\> \<profileSize\> \<connectionMethod\> -**
Creates a query graph from the frequent dataset mining on a target graph of a given profile size. Information on the frequent dataset mining within folder, which can be created with FrequentDatasets.
Find the subgraph isomorphism between given target graph and new query graph. Output folder must contain folders: "GenerationInfo", "Graphs", "Isomorphism".<br />
- **RandomWalk \<targetFile\> \<outputFolder\> -**
Creates a query graph from the target graph using a random walk. Find the subgraph isomorphism between given target graph and random query graph.
Output folder must contain folders: "GenerationInfo", "Graphs", "Isomorphism"<br />
- **RandomWalkWithProp \<targetFile\> \<outputFolder\> \<de\> \<di\> -**
Creates query graphs from the target graph with given properties.  The output folder will contain all the text files containing the query graphs. Will create maxNumQueries query graphs of different sizes.  <br />
**NOTE: will output a lot of text file to outputfolder, does not follow the same convention as RandomWalk!** <br/>
- **ConstructHardToFindGraphs \<targetFile\> \<outputFolder\> -**
Creates a query graph from the target graph using a random walk and estimation. Graphs who's estimation is an outlier compare to other random walks will be created.<br />
- **ProbGraphWithProps \<targetLocationName\> \<outputFileName\> -**
Finds the probability that we will be able to find query graphs of given size and average degree.  Size will be between 10 and 600 in increments of 10, and degree will be between 1 and 7.  Output the probabilities to the outputFile. <br/>
- **Average \<isomorphismFolder\> -**
Finds the average number of backtracking and matchings for given isomorphisms.<br />
- **TestIsomorphism \<groundTruthFile\> \<queryFolder\> \<targetFolder\> \<outputFile\> -**
Test the subgraph isomorphisms within the ground truth file. Must provide the location of the query and target folders.  If path is contained within ground truth folder, then give argument '\_'. If there is any errors in the isomorphism it will be recorded in the output file. <br />
- **Comparison \<targetLocationName\> \<outputFolderName\> \<queryGraphsFolder\> -**
Compares the algorithms against each other, once for processing order and again for backtracking. targetLocationName is the target graph and outputFolderName is where we will output the comparisons to.  The queryGraphsFolder contains all of the query graphs (Note: best to use RandomGraphWithProp output).

We must give an algorithm for the pruning, ordering, and backtracking.  We set these within fields in the main function.  We also must set any values within the main function such as gamma for graphQL and if we want the subgraph isomorhism to be induced.  We can choose from one of the following:<br />
- **GROUNDTRUTH**: finds the ground truth isomorphism.  Only uses LDA in pruning and BFS for ordering.<br />
- **GRAPHQL**: uses the GraphQL algorithm.<br />
- **QUICKSI**: uses the QuickSI algorithm. (Note: cannot be used for processing candidates)<br />
- **DYNAMIC_ORDER**: uses the dynamic ordering for process order. (Note: cannot only be used for ordering and cannot use QUICKSI isomorphism)<br />
- **DAF**: uses the DAF algorithm. (Note: equivalent to GROUNDTRUTH for processing candidates and cannot use DYNAMIC_ORDER)<br />
- **VEQS**: uses the VEQs algorithm (Note: only can be used for backtracking and cannot use dynamic ordering)<br />

The format of the graphs must also be included whenever a target or query graph is given.  There are two choices: igraph or protein.  Protein has the following format:<br />

The constructHeatMap.py is a file to construct heat maps based on the hard-to-find cases.  It works with the output provided by   Enter the field 
Formatted :<br />
{Number of Vertex}<br />
{id} {label} <br />
... <br />
{Number of edges for Vertex}<br />
{id outgoing vertex} {id incoming vertex}<br />
...<br />
\# - comments to skip

For estimating the number of matchings we must set the fields tau, maxEpoch, and zScore.  Since we are implementing wander joins we will be finding the confidence interval.  Tau is the confidence interval, which means the number we want the estimate we found with confidence zScore to be within.  The maxEpoch field is the maximum number of random walks we will perform in Wander Joins.
The fields for which pruning and ordering algorithm used should be included, since we will be modifying Wander Joins to use the resulting candidate set and ordering.

To construct graphs using Frequent Dataset Mining (FDM) we must first perform FDM on the graph.  We must provide the field connection method, which is found within the if statement.  <br />
- **MERGE:** merge two vertices of the same label.
- **EDGE:** create an edge between two vertices.
- **NONE:** use star graph of largest size.

To construct a random subgraph we must provide the method: 
- **RANDOM_WALK**: constructs non-induced subgraph using random walk algorithm. 
- **RANDOM_NODE_NEIGHBOR**: constructs induced subgraph using random node neighbor algorithm.

If we are constructing it with an estimate, then we must provide field outlierValue, which will give us the threshold for the outlier.  We also will provide a list of random subgraph methods.  These are contained within the corresponding if statements.

The "constructHeatMap.py" (within HeatMap folder) will create heatmaps for the hard-to-find instances found by ConstructHardToFindGraphs (heatMapType = "probability") and the probabilites function found by ProbGraphWithProps (heatMapType = "hardToFind").  We must provide the location of folder containing these files as a field within the main function.

The "CompareAlgorithms.py" (within Comparision folder) will create line charts for comparing the different algorithms.  Takes the file created by comparison as input.
