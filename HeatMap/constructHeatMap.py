import os # read file
import numpy as np
import matplotlib.pyplot as plt

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
                graphInformation[graphStructureInformation] = {"M": 0, "I":0}
            else:
                M = 0
                I = 0
                # iterate through the graphs constructed
                for graphConstruction in os.listdir(graphData):
                    foundM = False
                    foundI = False

                    # read through graph information
                    file = open(graphData+graphConstruction, 'r')
                    count = 0
                    for line in file.readlines():
                        line = line.strip().lower()
                        if(count == 0 and line != "hard-to-find"):
                            break

                        if("matchings" in line):
                            M += int(line.split(":")[1].strip())
                            foundM = True

                        if("isomorphic graphs" in line):
                            if(line.split(":")[1].strip() == "null"):
                                I += 1
                            else:
                                I += int(line.split(":")[1].strip())
                            foundI = True

                        if(foundM and foundI):
                            break

                        count+=1

                    file.close()

                M = M/len(os.listdir(graphData))
                graphInformation[graphStructureInformation] = {"M": M, "I":I}

    return (graphInformation, maxDe, maxDi)

def constructHeatMap(size, datapoints, maxM, folder):
    plt.imshow(datapoints, cmap='viridis', extent=[1, datapoints.shape[0]+1, 1, datapoints.shape[1]+1],
               vmin = 0, vmax = maxM)
    plt.colorbar()
    plt.xlabel('diameter (range x to x+1)')
    plt.ylabel('average degree (range x to x+1)')
    plt.title("Number of Hard-to-find Graphs of Size "+size)
    plt.savefig(folder+"size"+size+".png")

    plt.close()

def plotValues(graphInformation, maxDe, maxDi, folder):
    heatMapsInfo = {}
    maxM = 0;
    for key in graphInformation:
        n = key.split("_")[0][1:]
        if (n not in heatMapsInfo):
            heatMapsInfo[n] = np.zeros((maxDe,maxDi))
        de = int(key.split("_")[1][2:])
        di = int(key.split("_")[2][2:])

        M = graphInformation[key]["I"]
        if M>maxM:
            maxM = M

        heatMapsInfo[n][maxDe-de][di-1] = M


    for key in heatMapsInfo:
        constructHeatMap(key, heatMapsInfo[key], maxM, folder)

if __name__ == '__main__':
    dataFolder = "C:\\Users\\Gabi\\Desktop\\IndependentStudy\\GitHubProject\\Data\\Output\\HeatMap\\SecondAttempt\\"
    (graphInformation, maxDe, maxDi) = readInputData(dataFolder)
    plotValues(graphInformation, maxDe, maxDi, dataFolder+"HeatMaps\\")
        