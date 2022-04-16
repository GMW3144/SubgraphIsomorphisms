import os # read file
import numpy as np
import matplotlib.cm as cm
import matplotlib.pyplot as plt
import matplotlib.colors as colors
import matplotlib.colorbar as colorbar
import seaborn as sns
from textwrap import wrap

def readInputDataOneFile(dataFolder):
    graphInformation = {}  # size - graph info

    maxDe = 6
    maxDi = 10

    # iterate through the graph stats
    for statsFile in os.listdir(dataFolder):
        if (statsFile.split("_")[6] != "stats.txt"):
            continue

        n = statsFile.split("_")[1]
        if(n==60):
            print("here")
        density = statsFile.split("_")[3]
        diameter = statsFile.split("_")[5]

        # if the list is 0 then set all values to 0
        graphStructureInformation = "n" + n + "_de" + density + "_di" + diameter

        # read through graph information
        file = open(dataFolder + statsFile, 'r')
        count = 0

        M = 0
        I = 0
        M_current = 0
        I_current = 0

        # iterate through the graphs constructed
        foundM = False
        foundI = False

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
                    I_current += (int(line.split(":")[1].strip()) + 1)
                    M_current = M_current * I_current
                foundI = True

            if(foundM and foundI):
                M +=M_current
                I +=I_current

                foundM = False
                foundI = False
                M_current = 0
                I_current = 0

            count += 1
        file.close()

        if (M != None):
            graphInformation[graphStructureInformation] = {"M": M / I, "I": I}
        else:
            graphInformation[graphStructureInformation] = {"M": M, "I": I}

    for n in range(10, 101, 10):
        for density in range(1, 7):
            for diameter in range(1, 11):
                # if the list is 0 then set all values to 0
                graphStructureInformation = "n" + str(n) + "_de" + str(density) + "_di" + str(diameter)

                if(graphStructureInformation not in graphInformation):
                    graphInformation[graphStructureInformation] = {"M": None, "I":None}

    return (graphInformation, maxDe, maxDi)

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
                             outlierMaxM, type, i, ax):
    if(i<5):
        row = 0
    else:
        row = 1
    col = i%5

    # plot the histogram
    sns.heatmap(datapoints, cmap='viridis', cbar=False, vmin=minM, vmax=maxM, ax=ax[row, col])
    plt.ylim(1, datapoints.shape[0]+1)
    plt.xlim(1, datapoints.shape[1]+1)
    ax[row,col].set_title("Size " + str(size), fontsize = 12)

    # plot the outliers
    if(len(outlierMaxM)>0):
        ax[row,col].scatter(outlierMaxPointsX, outlierMaxPointsY, vmin=maxM, vmax=trueMax, c=outlierMaxM,
                            cmap = "gist_heat", s=10)
        return True

def plotValues(graphInformation, maxDe, maxDi, minSize, maxSize, folder, type):
    heatMapsInfo = {}
    capMax = 10000000
    maxM = 0
    trueMax = 0
    minM = -1

    outlierMaxInfo = {}
    outlierMinInfo = {}
    for key in graphInformation:
        n = int(key.split("_")[0][1:])
        if(n<minSize or n>maxSize):
            continue
        if (n not in heatMapsInfo):
            heatMapsInfo[n] = np.zeros((maxDi+1,maxDe+1))
            outlierMaxInfo[n] = ([], [], [])
            outlierMinInfo[n] = ([], [], [])
        de = int(key.split("_")[1][2:])
        di = int(key.split("_")[2][2:])


        val = graphInformation[key][type]

        if(val!= None and val>capMax):
            if(val>trueMax):
                trueMax = val
            outlierMaxInfo[n][1].append(di+.5)
            outlierMaxInfo[n][0].append(de+.5)
            outlierMaxInfo[n][2].append(val)
            val = capMax
        if (val!= None and val>maxM):
            maxM = val
        if(val!=None and (minM==-1 or val<minM)):
            minM = val

        heatMapsInfo[n][di][de] = val


    fig, ax = plt.subplots(nrows=2, ncols=5, sharey=True, sharex=True)

    # add each plot
    i = 0
    for key in sorted(heatMapsInfo):
        setColorBar=constructHeatMap(key, heatMapsInfo[key], minM, maxM, trueMax, folder, outlierMaxInfo[key][0], outlierMaxInfo[key][1],
                         outlierMaxInfo[key][2], type, i, ax)
        i+=1

    # overall color bar
    cbar_ax = fig.add_axes([.91, .61, .02, .3])
    norm = colors.Normalize(vmin=minM, vmax=maxM)
    colorbar.ColorbarBase(cbar_ax, cmap=cm.get_cmap("viridis"), norm=norm)

    # color bar for dots
    cbarDOT_ax = fig.add_axes([.91, .11, .02, .3])
    norm = colors.Normalize(vmin=maxM, vmax=trueMax)
    colorbar.ColorbarBase(cbarDOT_ax, cmap=cm.get_cmap("gist_heat"), norm=norm)

    # adjust plots
    fig.tight_layout(rect=[0.05, 0.05, .9, 0.9])
    fig.subplots_adjust(wspace=0)

    # add labels
    fig.supylabel('diameter (range x to x+1)')
    fig.supxlabel('average degree (range x to x+1)')

    # save and close the plot
    endOfString = "_min"+str(minSize)+"_max"+str(maxSize)
    if (type == "M"):
        title = "Average Number of Matchings for Hard-to-find Graphs"
        fig.suptitle(title)
        plt.savefig(folder  + "avgMatching"+endOfString+".pdf")
    else:
        title = "Number of Hard-to-find Graphs"
        fig.suptitle(title)
        plt.savefig(folder + "count"+endOfString+".pdf")
    plt.close()

if __name__ == '__main__':
    dataFolder = "C:\\Users\\Gabi\\Desktop\\IndependentStudy\\GitHubProject\\Data\\Output\\HeatMap\\Yeast\\Attempt5\\"
    (graphInformation, maxDe, maxDi) = readInputDataOneFile(dataFolder+"Yeast_Induced\\")

    #textSize = 10
    #plt.rc('xtick', labelsize=textSize)
    #plt.rc('ytick', labelsize=textSize)
    #plt.rcParams.update({'font.size': textSize})

    # will only put 10 graphs at a time in figure, so must adjust
    # right now set for graphs between 10 and 100 with increments of 10
    inc = 10
    minSize=10
    maxSize=100
    for n in range(minSize, maxSize, inc*10):
        plotValues(graphInformation, maxDe, maxDi, n, n+inc*10, dataFolder+"HeatMaps\\Matchings\\", "M")
        plotValues(graphInformation, maxDe, maxDi, n, n+inc*10, dataFolder+"HeatMaps\\Isomorphisms\\", "I")
        