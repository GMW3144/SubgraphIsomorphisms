import os # read file
import numpy as np
import matplotlib.cm as cm
import matplotlib.pyplot as plt
import matplotlib.colors as colors
import matplotlib.colorbar as colorbar
import seaborn as sns
from textwrap import wrap


"""
Read the output that is contained in an individual file
"""
def readInputDataOneFile(dataFolder, minSize, maxSize, inc):
    graphInformation = {}  # size - graph info


    # the maximum degree and diameter value
    maxDe = 6
    maxDi = 10

    # iterate through the stats, ignore the other files
    for statsFile in os.listdir(dataFolder):
        if ("stats" not in statsFile):
            continue
        # get the size of the graph
        n = statsFile.split("_")[1]
        # get the density and diameter
        density = statsFile.split("_")[3]
        diameter = statsFile.split("_")[5]

        # key
        graphStructureInformation = "n" + n + "_de" + density + "_di" + diameter

        # read through graph information
        file = open(dataFolder + statsFile, 'r')
        count = 0

        # number of matchings and graphs
        M = 0
        I = 0
        # keep track of the current values too
        M_current = 0
        I_current = 0

        # iterate through the graphs constructed
        foundM = False
        foundI = False

        # iterate through file
        for line in file.readlines():
            line = line.strip().lower()
            # if there isn't any hard-to-find instances, set number of matchings and number hard-to-find cases to None
            if (count == 0 and line != "hard-to-find"):
                M = None
                I = None
                break

            # find the number of matchings (for given query graph)
            if ("matchings" in line):
                M_current = float(line.split(":")[1].strip())
                foundM = True

            # find the number of hard-to-find cases (add up number isomorphic)
            if ("isomorphic graphs" in line):
                # null - no isomorphic cases, so one
                if (line.split(":")[1].strip() == "null"):
                    I_current = 1
                else:
                    I_current += (int(line.split(":")[1].strip()) + 1)
                    M_current = M_current * I_current
                foundI = True

            # if found both M and I, then find next hard-to-find instance
            if(foundM and foundI):
                M +=M_current
                I +=I_current

                foundM = False
                foundI = False
                M_current = 0
                I_current = 0

            count += 1
        file.close()

        # find the average number of matchings, and the number of hard-to-find instances
        if (M != None ):
            graphInformation[graphStructureInformation] = {"M": M / I, "I": I}
        else:
            graphInformation[graphStructureInformation] = {"M": None, "I": None}

    # set all the cases where it did not run in time, or stopped while running to -1
    for n in range(minSize, maxSize+1, inc):
        for density in range(1, maxDe+1):
            for diameter in range(1, maxDi+1):
                # if the list is 0 then set all values to 0
                graphStructureInformation = "n" + str(n) + "_de" + str(density) + "_di" + str(diameter)

                if(graphStructureInformation not in graphInformation):
                    graphInformation[graphStructureInformation] = {"M": -1, "I":-1}

    return (graphInformation, maxDe, maxDi)

"""
Read the data when all information is in one file (one folder per hard-to-find instance)
"""
def readInputDataOneFolder(dataFolder, minSize, maxSize, inc):
    graphInformation = {}  # size - graph info

    # the maximum degree and diameter
    maxDe = 6
    maxDi = 10

    # iterate through the graph stats
    for statsFile in os.listdir(dataFolder):
        if(statsFile.split("_")[6]!="stats"):
            continue
        # size of graph, density, and diameter
        n = statsFile.split("_")[1]
        density = statsFile.split("_")[3]
        diameter = statsFile.split("_")[5]

        # if the list is 0 then set all values to 0
        graphStructureInformation = "n" + n + "_de" + density + "_di" + diameter

        # get the previous total number of matchings and hard-to-find instances, if one exists
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

        # keep track of the current number of matchings and hard-to-find cases
        M_current = 0
        I_current = 0
        # iterate through the file
        for line in file.readlines():
            line = line.strip().lower()
            # only keep track of hard-to-find cases
            if (count == 0 and line != "hard-to-find"):
                break

            # get the number of matchings
            if ("matchings" in line):
                M_current = float(line.split(":")[1].strip())
                foundM = True

            # get the number of hard-to-find cases
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

        # add the current to the running total
        if (foundM and foundI):
            if (M == None or I == None):
                M = 0
                I = 0
            M += M_current
            I += I_current

        # store the current information (average number of matchings and total number of hard-to-find instances)
        if (M != None):
            graphInformation[graphStructureInformation] = {"M": M / I, "I": I}
        else:
            graphInformation[graphStructureInformation] = {"M": M, "I": I}

    # add -1 for all of the cases that don't run in time
    for n in range(minSize, maxSize+1, inc):
        for density in range(1, maxDe+1):
            for diameter in range(1, maxDi+1):
                # if the list is 0 then set all values to 0
                graphStructureInformation = "n" + str(n) + "_de" + str(density) + "_di" + str(diameter)

                if(graphStructureInformation not in graphInformation):
                    graphInformation[graphStructureInformation] = {"M": -1, "I":-1}

    return (graphInformation, maxDe, maxDi)

"""
Read input when all data is in separate folders
"""
def readInputData(dataFolder):
    graphInformation = {} # size - graph info
    # find the maximum degree and diameter
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
            # get the density and diameter, find the maximum
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

            # if there are no hard-to-find instances
            if(len(os.listdir(graphData))==0):
                graphInformation[graphStructureInformation] = {"M": None, "I":None}
            else:
                # average number of matchings and hard-to-find instances
                M = None
                I = None
                # iterate through the graphs constructed
                for graphConstruction in os.listdir(graphData):
                    foundM = False
                    foundI = False

                    # read through graph information
                    file = open(graphData+graphConstruction, 'r')
                    count = 0

                    # keep track of the current matchings and hard-to-find cases
                    M_current = 0
                    I_current = 0
                    # read through the file
                    for line in file.readlines():
                        line = line.strip().lower()
                        # only keep if hard-to-find
                        if(count == 0 and line != "hard-to-find"):
                            break

                        # find the number of matchings
                        if("matchings" in line):
                            M_current = float(line.split(":")[1].strip())
                            foundM = True

                        # find the number of hard-to-find instances
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

                    # update the running totals
                    if(foundM and foundI):
                        if(M==None or I==None):
                            M=0
                            I=0
                        M+=M_current
                        I+=I_current

                # find the average number of matchings and hard-to-find instances
                if (M != None):
                    graphInformation[graphStructureInformation] = {"M": M/I, "I": I}
                else:
                    graphInformation[graphStructureInformation] = {"M": M, "I":I}

    return (graphInformation, maxDe, maxDi)

"""
Construct the heat map given the lower and larger values, and the values that did not output in time
"""
def constructHeatMap(size, datapoints, minM, maxM, trueMax, folder, outlierMaxPointsX, outlierMaxPointsY,
                             outlierMaxM, noOuputx, noOuputy, type, i, ax):
    # the location of the sub plot
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

    # plot if did not compute
    ax[row, col].scatter(noOuputx,  noOuputy, marker='x', s=10, color="black")

    # plot the outliers
    if(len(outlierMaxM)>0):
        ax[row,col].scatter(outlierMaxPointsX, outlierMaxPointsY, vmin=maxM, vmax=trueMax, c=outlierMaxM,
                            cmap = "gist_heat", s=10)
        return True

"""
Create the super heat map with different subplots
"""
def plotSuperHeatMap(heatMapsInfo, minM, maxM, trueMax, folder, outlierMaxInfo, noOutput, type):
    fig, ax = plt.subplots(nrows=2, ncols=5, sharey=True, sharex=True)

    # add each plot
    i = 0
    for key in sorted(heatMapsInfo):
        setColorBar = constructHeatMap(key, heatMapsInfo[key], minM, maxM, trueMax, folder, outlierMaxInfo[key][0],
                                       outlierMaxInfo[key][1], outlierMaxInfo[key][2], noOutput[key][0], noOutput[key][1],
                                       type, i, ax)
        i += 1

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
    endOfString = "_min" + str(minSize) + "_max" + str(maxSize)
    if (type == "M"):
        title = "Average Number of Matchings for Hard-to-find Graphs"
        fig.suptitle(title)
        plt.savefig(folder + "avgMatching" + endOfString + ".pdf")
    else:
        title = "Number of Hard-to-find Graphs"
        fig.suptitle(title)
        plt.savefig(folder + "count" + endOfString + ".pdf")
    plt.close()

"""
Extract and plot the values
"""
def plotValues(graphInformation, maxDe, maxDi, minSize, maxSize, folder, type):
    # the heat map values
    heatMapsInfo = {}
    # the max number of matchings (or hard-to-find cases)
    capMax = 10000000
    # keep track of the maximum values for heat map and larger values, for color bar
    maxM = 0
    trueMax = 0
    minM = -1

    # keep track of the outlier values
    outlierMaxInfo = {}
    # keep track of properties did not run in time
    noOuput = {}

    # iterate through the information
    for key in graphInformation:
        # size of graph
        n = int(key.split("_")[0][1:])
        # must be within parameters (only 10 graphs can be outputed)
        if(n<minSize or n>maxSize):
            continue
        if (n not in heatMapsInfo):
            # set up the heat map data
            heatMapsInfo[n] = np.zeros((maxDi+1,maxDe+1))
            outlierMaxInfo[n] = ([], [], [])

            noOuput[n] = ([], [])
        # get the degree and diameter
        de = int(key.split("_")[1][2:])
        di = int(key.split("_")[2][2:])

        # average number matching or number hard-to-find
        val = graphInformation[key][type]
        # if didn't compute in time
        if(val==-1):
            noOuput[n][1].append(di+.5)
            noOuput[n][0].append(de+.5)
            heatMapsInfo[n][di][de] = None
            continue

        # get the value information, cap if too large
        if(val!= None and val>capMax):
            # keep track of maximum values
            if(val>trueMax):
                trueMax = val
            outlierMaxInfo[n][1].append(di+.5)
            outlierMaxInfo[n][0].append(de+.5)
            outlierMaxInfo[n][2].append(val)
            val = capMax
        # keep track of maximum values
        if (val!= None and val>maxM):
            maxM = val
        if(val!=None and (minM==-1 or val<minM)):
            minM = val

        # store heat map data
        heatMapsInfo[n][di][de] = val

    # plot heat maps
    plotSuperHeatMap(heatMapsInfo, minM, maxM, trueMax, folder, outlierMaxInfo, noOuput, type)


"""
Create a heat map that keep track of probability that we are able to construct query graph
"""
def constructProbHeatMap(inputFile, folder, type, maxSize, maxDegree):
    # read through graph information
    file = open(inputFile, 'r')
    # keep track of data for heat map
    heatMapsInfo = np.zeros((maxSize+1, maxDegree+1))

    cnt = 0
    # read through the lines in the file
    for line in file.readlines():
        if(cnt==0):
            cnt+=1
            continue
        line = line.strip().lower()
        info = line.split(",")
        # get the number of vertices, degree, and probability
        n = int(info[0].split(":")[1])
        de = int(float(info[1].split(":")[1].split('---')[0]))

        # store to display in heat map
        prob = float(info[1].split(":")[1].split('---')[1])
        heatMapsInfo[(n)//10][de] = prob

    # create the heat map
    sns.heatmap(heatMapsInfo, cmap='viridis', cbar=True, vmin=0, vmax=1)
    plt.ylim(1, heatMapsInfo.shape[0] + 1)
    plt.xlim(1, heatMapsInfo.shape[1] + 1)

    # add labels
    plt.ylabel('size (times 10 for true size)')
    plt.xlabel('average degree (range x to x+1)')

    # title
    title = "Probability find graph of given properties"
    plt.title(title)
    plt.savefig(folder+"prob.pdf")


if __name__ == '__main__':
    # what heat map are we trying to create?
    heatMapType = "probability"
    if(heatMapType == "probability"):
        #PROBABILITY HEAT MAPS
        inputFile = 'C:\\Users\\Gabi\\Desktop\\IndependentStudy\\GitHubProject\\Data\\Output\\HeatMap\\Yeast\\Probability\\degreeComp.txt'
        folder ='C:\\Users\\Gabi\\Desktop\\IndependentStudy\\GitHubProject\\Data\\Output\\HeatMap\\Yeast\\Probability\\'

        # the maximum size and degree
        maxSize = 600
        maxDegree = 6

        constructProbHeatMap(inputFile, folder+"Matchings\\", "M", maxSize//10, maxDegree)
    if(heatMapType == "hardToFind"):
        #HARD-TO-FIND heatmaps

        # will only put 10 graphs at a time in figure, so must adjust
        # right now set for graphs between 10 and 100 with increments of 10
        inc = 10
        minSize = 10
        maxSize = 100

        dataFolder = "C:\\Users\\Gabi\\Desktop\\IndependentStudy\\GitHubProject\\Data\\Output\\HeatMap\\Yeast\\Attempt5\\Yeast_Induced_Copy\\"
        # recommended to stick with this one with current java file
        (graphInformation, maxDe, maxDi) = readInputDataOneFile(dataFolder+"Yeast_Induced\\", minSize, maxSize, inc)
        for n in range(minSize, maxSize, inc*10):
            plotValues(graphInformation, maxDe, maxDi, n, n+inc*10, dataFolder+"HeatMaps\\Matchings\\", "M")
            plotValues(graphInformation, maxDe, maxDi, n, n+inc*10, dataFolder+"HeatMaps\\Isomorphisms\\", "I")
