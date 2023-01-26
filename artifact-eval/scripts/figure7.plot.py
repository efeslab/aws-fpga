#!/usr/bin/python3
import numpy as np
import matplotlib.pyplot as plt

from pylab import rcParams
rcParams['figure.figsize'] = 6.8, 4.5

data = [["sda",1.639478413,1.590136435,1.548205489,136,100,36],
    ["sda+ocl",1.961120424,1.81467238,1.923528032,272,200,72],
    ["sda+ocl+bar1",2.462017128,2.085234964,2.251935257,408,300,108],
    ["pcim",2.556166758,2.31067508,3.589021816,1324,549,775],
    ["sda+pcim",2.87634441,2.639362981,3.870513723,1460,649,811],
    ["sda+ocl+pcim",3.480004617,2.887105996,4.198920948,1596,749,847],
    ["sda+ocl+bar1+pcim",4.014667703,3.252046872,4.433497537,1732,849,883],
    ["pcim+pcis",4.663206187,3.585600077,5.958245367,2648,1324,1324],
    ["sda+pcim+pcis",5.004057134,3.831879196,6.286652592,2784,1424,1360],
    ["sda+ocl+pcim+pcis",5.702728358,4.318409622,6.615059817,2920,1524,1396],
    ["sda+ocl+bar1+pcim+pcis",6.423106542,4.619627929,6.920009383,3056,1624,1432]]
print(data)

t = []
lut = []
ff = []
bram = []
name = []
textdelta = [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20]
texty = [2.15, 2.45, 2.76, 4.02, 4.23, 4.55, 4.79, 1.45, 0.60, 0.15, 0.15]

for entry in data:
    t.append(entry[4])
    lut.append(entry[1])
    ff.append(entry[2])
    bram.append(entry[3])
    name.append(entry[0])

fig, ax = plt.subplots(1, 1)

for i in range(0, len(t)):
    ax.axvline(x=t[i], ymin=0, ymax=100, color='gray', linewidth=1, dashes=(5,3))
    ax.text(x=t[i]+textdelta[i], y=texty[i], s=name[i], rotation="vertical", fontsize=12)

ax.plot(t, lut, "o-", label="LUT")
ax.plot(t, ff, "o-", label="FF")
ax.plot(t, bram, "o-", label="BRAM")
ax.set_xlabel('Total Monitored Width (bits)', fontsize=16)
ax.set_ylabel('Resource Overhead (%)', fontsize=16)
ax.set_ylim([0, 9.2])
ax.tick_params(axis="y", labelsize=13)
ax.tick_params(axis="x", labelsize=13)

handles, labels = ax.get_legend_handles_labels()
leg = ax.legend(handles, labels, fontsize=12, ncol=1, loc='upper left')

fig.tight_layout()
plt.savefig("resource_overhead_sweep.pdf")
#plt.show()
