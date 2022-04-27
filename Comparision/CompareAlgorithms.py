import os # read file
import matplotlib.pyplot as plt
import itertools
import math

"""
Get the algorithm information from how we store it
"""
def getAlgorithmAndGraphInfo(name):
    info = name.split("_")
    # algo info
    algoB = info[1]
    algoPO = info[3]
    algoC = info[5]

    # size info
    size = info[7]

    return (algoB, algoPO, algoC, size)

"""
Print table in latex form and store information for later use
"""
def constructTableSize(folder, comparing):
    # table in latex format
    table = ""
    # the information we are retrieving
    storeInfo = {}
    # iterate through the files
    for fileName in os.listdir(dataFolder):
        if(".txt" not in fileName):
            continue
        # read through graph information
        file = open(folder + fileName, 'r')

        (algoB, algoPO, algoC, size) = getAlgorithmAndGraphInfo(fileName[:-4])

        # add information to the table
        if(comparing == "backtracking"):
            if(algoPO != "graphQL"):
                continue
            table = table + algoB
        if (comparing == "processing order"):
            if (algoB != "graphQL"):
                continue
            table = table + algoPO

        table = table+ "& " + size

        # get the number of backtracking and matchings
        results = []
        # read through file
        for line in file.readlines():
            line = line.strip().lower()
            if(line == 'ran out of memory'):
                table = table + "&No Result&No Result&No Result"
                results = [None, None, None]
            else:
                info = line.split(":")
                table = table + "&" + info[1]
                results.append(info[1])

        table = table + "\\\\ \\hline \n"

        storeInfo[fileName[:-4]] = results
    # rows within LaTex file
    print(table)
    return storeInfo

"""
Create the line plot that compares different algorithms
"""
def plotLine(datapoints, algo, uselog):
    sortedVals = {}
    # sort datapoints
    for i in range(0, len(datapoints[algo][0])):
        # take the log
        if(uselog):
            sortedVals[datapoints[algo][0][i]] = math.log(datapoints[algo][1][i])
        else:
            sortedVals[datapoints[algo][0][i]] = datapoints[algo][1][i]

    x = []
    y = []
    for xVal in sorted(sortedVals):
        x.append(xVal)
        y.append(sortedVals[xVal])

    # plot sorted data points
    plt.plot(x, y, label=algo)

"""
Create a datapoint for a given algorithm
"""
def addDataPoint(algo, plotValues, size, backtracking):
    if (algo not in plotValues):
        plotValues[algo] = ([], [])
    if (backtracking == None):
        return
    plotValues[algo][0].append(float(size))
    plotValues[algo][1].append(float(backtracking))

"""
Plot the information comparing the algorithm
"""
def plotCharts(storeInfo, comparing, outputFolder):
    datapoints = {}

    if(comparing == "backtracking"):
        uselog = True
    else:
        uselog = False

    for key in sorted(storeInfo):
        # get algo and graph info
        (algoB, algoPO, algoC, size) = getAlgorithmAndGraphInfo(key)
        matching = storeInfo[key][0]
        backtracking = storeInfo[key][1]
        numGraphs = storeInfo[key][2]

        # add the datapoint
        if (comparing == "backtracking"):
            addDataPoint(algoB, datapoints, size, backtracking)

        if (comparing == "processing order"):
            addDataPoint(algoPO, datapoints, size, backtracking)

    for key in datapoints:
        plotLine(datapoints, key, uselog)

    # give title and axis
    plt.title("Comparing "+comparing+" algorithms")
    plt.xlabel("Size of Graph")
    if(uselog):
        plt.ylabel("Average Number of Backtracking (log)")
    else:
        plt.ylabel("Average Number of Backtracking")
    plt.legend()
    plt.savefig(outputFolder + "comparing_" + comparing.replace(" ", "_") + ".pdf")
    plt.close()

if __name__ == '__main__':
    dataFolder = "C:\\Users\\Gabi\\Desktop\\IndependentStudy\\GitHubProject\\Data\\Output\\CompareAlgo\\Attempt2\\induced2\\"
    outputFolder = "C:\\Users\\Gabi\\Desktop\\IndependentStudy\\GitHubProject\\Data\\Output\\CompareAlgo\\Attempt2\\induced2\\output\\"

    storeInfo = constructTableSize(dataFolder, "backtracking")
    plotCharts(storeInfo, "backtracking", outputFolder)

    print("==================")

    storeInfo =constructTableSize(dataFolder, "processing order")
    plotCharts(storeInfo, "processing order", outputFolder)