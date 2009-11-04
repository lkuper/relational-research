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
#colors = [(i/float(M), i/float(M)) for i in range(M)]

def mkplot(n):
   f = plt.subplot(321+n)
   plt.title(test_names[n])
   nm = [x[0] for x in tests[n]]
   d = [x[1] for x in tests[n]]
   err = [x[2] for x in tests[n]]
   for i in range(len(d)):
     plt.barh(ind[i]+w, d[i], w, label=nm[i], color=(1.,1.,1.,1.))#, xerr=err)
   plt.yticks(ind+w*3/2., nm, fontsize=9)
   plt.xlabel('time (ms)', fontsize=9)
   plt.xticks(fontsize=7)
   plt.xlim(xmax=plt.xlim()[1]+wid_adj[n])
   for i in range(len(d)):
     f.text(d[i], ind[i]+w, '  (%s)'%d[i], fontsize=7)

bars = []
plt.figure(figsize=(10,8))
for i in range(N):
   mkplot(i)
plt.subplots_adjust(hspace=.6, wspace=.4)
plt.legend([x[0] for x in tests[0]])
plt.show()
pylab.savefig("graph1.png")
