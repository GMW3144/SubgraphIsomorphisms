import os # read file
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
from textwrap import wrap

def readInputDataOneFolder(dataFolder):
    graphInformation = {}  # size - graph info

    maxDe = 6
    maxDi = 10

    # iterate through the graph stats
    for statsFile in os.listdir(dataFolder):
        if(statsFile.split("_")[6]!="stats"):
            continue
        n = statsFile.split("_")[1]
        density = statsFile.split("_")[3]
        diameter = statsFile.split("_")[5]

        # if the list is 0 then set all values to 0
        graphStructureInformation = "n" + n + "_de" + density + "_di" + diameter

        if (graphStructureInformation in graphInformation and graphInformation[graphStructureInformation] != 0):
            I = graphInformation[graphStructureInformation]["I"]
            M = graphInformation[graphStructureInformation]["M"]*I
        else:
            M = None
            I = None
        # iterate through the graphs constructed
        foundM = False
        foundI = False

        # read through graph information
        file = open(dataFolder+statsFile, 'r')
        count = 0

        M_current = 0
        I_current = 0
        for line in file.readlines():
            line = line.strip().lower()
            if (count == 0 and line != "hard-to-find"):
                break

            if ("matchings" in line):
                M_current = float(line.split(":")[1].strip())
                foundM = True

            if ("isomorphic graphs" in line):
                if (line.split(":")[1].strip() == "null"):
                    I_current = 1
                else:
                    I_current = (int(line.split(":")[1].strip()) + 1)
                    M_current = M_current*I_current
                foundI = True

            if (foundM and foundI):
                break

            count += 1

        file.close()

        if (foundM and foundI):
            if (M == None or I == None):
                M = 0
                I = 0
            M += M_current
            I += I_current

        if (M != None):
            graphInformation[graphStructureInformation] = {"M": M / I, "I": I}
        else:
            graphInformation[graphStructureInformation] = {"M": M, "I": I}

    for n in range(10, 51, 10):
        for density in range(1, 7):
            for diameter in range(1, 11):
                # if the list is 0 then set all values to 0
                graphStructureInformation = "n" + str(n) + "_de" + str(density) + "_di" + str(diameter)

                if(graphStructureInformation not in graphInformation):
                    graphInformation[graphStructureInformation] = {"M": None, "I":None}

    return (graphInformation, maxDe, maxDi)

def readInputData(dataFolder):
    graphInformation = {} # size - graph info
    maxDe = 0
    maxDi = 0
    # iterate through the graph sizes
    for dataSubfolder in os.listdir(dataFolder):
        if(".txt" in dataSubfolder or not dataSubfolder.isnumeric()):
            continue

        n = dataSubfolder # number of nodes
        # iterate through the graph densities and diameters
        graphStructure = dataFolder+dataSubfolder+"\\"
        for graphStructSubfolder in os.listdir(graphStructure):
            density = graphStructSubfolder.split("_")[0][2:]
            diameter = graphStructSubfolder.split("_")[1][2:]
            if(int(density)>maxDe):
                maxDe = int(density)
            if(float(diameter)>maxDi):
                maxDi = int(diameter)


            # iterate through the information for graphs
            graphData = graphStructure+graphStructSubfolder+"\\GenerationInfo\\"

            # if the list is 0 then set all values to 0
            graphStructureInformation = "n"+n+"_de"+density+"_di"+diameter

            if(len(os.listdir(graphData))==0):
                graphInformation[graphStructureInformation] = {"M": None, "I":None}
            else:
                M = None
                I = None
                # iterate through the graphs constructed
                for graphConstruction in os.listdir(graphData):
                    foundM = False
                    foundI = False

                    # read through graph information
                    file = open(graphData+graphConstruction, 'r')
                    count = 0

                    M_current = 0
                    I_current = 0
                    for line in file.readlines():
                        line = line.strip().lower()
                        if(count == 0 and line != "hard-to-find"):
                            break

                        if("matchings" in line):
                            M_current = float(line.split(":")[1].strip())
                            foundM = True

                        if("isomorphic graphs" in line):
                            if(line.split(":")[1].strip() == "null"):
                                I_current = 1
                            else:
                                I_current = (int(line.split(":")[1].strip())+1)
                                M_current = M_current*I_current
                            foundI = True

                        if(foundM and foundI):
                            break

                        count+=1

                    file.close()

                    if(foundM and foundI):
                        if(M==None or I==None):
                            M=0
                            I=0
                        M+=M_current
                        I+=I_current

                if (M != None):
                    graphInformation[graphStructureInformation] = {"M": M/I, "I": I}
                else:
                    graphInformation[graphStructureInformation] = {"M": M, "I":I}

    return (graphInformation, maxDe, maxDi)

def constructHeatMap(size, datapoints, minM, maxM, trueMax, folder, outlierMaxPointsX, outlierMaxPointsY,
                             outlierMaxM, type):
    # plot the histogram
    sns.heatmap(datapoints, cmap='viridis', cbar=True, vmin=minM, vmax=maxM)
    plt.ylim(1, datapoints.shape[0]+1)
    plt.xlim(1, datapoints.shape[1]+1)
    plt.xlabel('diameter (range x to x+1)')
    plt.ylabel('average degree (range x to x+1)')
    if(type == "M"):
        title = "Average Number of Matchings for Hard-to-find Graphs Size " + size
    else:
        title ="Number of Hard-to-find Graphs Size "+size
    plt.title('\n'.join(wrap(title, 40)))

    # plot the outliers
    if(len(outlierMaxM)>0):
        plt.scatter(outlierMaxPointsX, outlierMaxPointsY, vmin=maxM, vmax=trueMax, c=outlierMaxM, cmap = "gist_heat")
        plt.colorbar()

    # save and close the plot
    if(type == "M"):
        plt.savefig(folder+"size"+size+"_avgMatching.png")
    else:
        plt.savefig(folder+"size"+size+"_count.png")
    plt.close()

def plotValues(graphInformation, maxDe, maxDi, folder, type):
    heatMapsInfo = {}
    capMax = 10000000
    maxM = 0
    trueMax = 0
    minM = -1

    outlierMaxInfo = {}
    outlierMinInfo = {}
    for key in graphInformation:
        n = key.split("_")[0][1:]
        if (n not in heatMapsInfo):
            heatMapsInfo[n] = np.zeros((maxDe+1,maxDi+1))
            outlierMaxInfo[n] = ([], [], [])
            outlierMinInfo[n] = ([], [], [])
        de = int(key.split("_")[1][2:])
        di = int(key.split("_")[2][2:])

        val = graphInformation[key][type]
        if(val!= None and val>capMax):
            if(val>trueMax):
                trueMax = val
            outlierMaxInfo[n][0].append(di+.5)
            outlierMaxInfo[n][1].append(de+.5)
            outlierMaxInfo[n][2].append(val)
            val = capMax
        if (val!= None and val>maxM):
            maxM = val
        if(val!=None and (minM==-1 or val<minM)):
            minM = val

        heatMapsInfo[n][de][di] = val



    for key in heatMapsInfo:
        constructHeatMap(key, heatMapsInfo[key], minM, maxM, trueMax, folder, outlierMaxInfo[key][0], outlierMaxInfo[key][1],
                         outlierMaxInfo[key][2], type)

if __name__ == '__main__':
    dataFolder = "C:\\Users\\Gabi\\Desktop\\IndependentStudy\\GitHubProject\\Data\\Output\\HeatMap\\Yeast\\NonInduced\\"
    (graphInformation, maxDe, maxDi) = readInputDataOneFolder(dataFolder+"Yeast\\")

    #textSize = 25
    #plt.rc('xtick', labelsize=textSize)
    #plt.rc('ytick', labelsize=textSize)

    plotValues(graphInformation, maxDe, maxDi, dataFolder+"HeatMaps\\", "M")
    plotValues(graphInformation, maxDe, maxDi, dataFolder+"HeatMaps\\", "I")
        