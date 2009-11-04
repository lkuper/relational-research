#!/usr/bin/env python
# todo: 
#  - correct names
#  - add second graph
import numpy as np
import matplotlib.pyplot as plt
import pylab

from graph_input1 import *

N=len(tests)
M=len(tests[0])
ind=np.arange(M)
w=.7

wid_adj = [1500,0,200,900,1200,200]
#colors = ['#%02x%02x%02x'%((i*120)%255,(i*57)%255,(i*5)%255) for i in range(M)]
colors = {}
for i in range(M):
   #colors[tests[0][i][0]] = ['#%02x%02x%02x'%((i*123)%255,(i*1337)%255,(i*37)%255)]
   colors[mktests[i][0]] = ['#%02x%02x%02x'%((i*123)%255,(i*1337)%255,(i*37)%255)]

def mkplot(n):
   f = plt.subplot(321+n)
   plt.title(test_names[n])
   nm = [x[0] for x in tests[n]]
   d = [x[1] for x in tests[n]]
   err = [x[2] for x in tests[n]]
   for i in range(len(d)):
     plt.barh(ind[i]+w*3/2., d[i], w, label=nm[i], color=colors[nm[i]])#, xerr=err)
   #plt.yticks(ind+w*3/2., nm, fontsize=9)
   f.yaxis.set_major_locator(plt.NullLocator())
   plt.xlabel('time (ms)', fontsize=10)
   plt.xticks(fontsize=8)
   plt.xlim(xmax=plt.xlim()[1]+wid_adj[n])
   for i in range(len(d)):
     f.text(d[i], ind[i]+w*6/5., '  (%s)'%d[i], fontsize=8)

bars = []
plt.figure(figsize=(10,8))
for i in range(N):
   mkplot(i)
plt.subplots_adjust(hspace=.5, wspace=.1, bottom=.16)
plt.legend([x[0] for x in tests[-1]], loc=8, bbox_to_anchor=(-.05,-.7), ncol=M/2, prop={'size':11})
#plt.show()
pylab.savefig("graph1.png")
