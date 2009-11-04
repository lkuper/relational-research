#!/usr/bin/env python
import numpy as np
import matplotlib.pyplot as plt
import pylab

from graph_input2 import *

N=len(tests)
M=len(tests[0])
ind=np.arange(M)
w=.7

#wid_adj = [1500,0,200,900,1200,200]
wid_adj = [1000,200]

def mkplot(n):
   f = plt.subplot(211+n)
   plt.title(test_names[n])
   nm = [x[0] for x in tests[n]]
   d = [x[1] for x in tests[n]]
   err = [x[2] for x in tests[n]]
   plt.barh(ind+w, d, w)#, xerr=err)
   plt.yticks(ind+w*3/2., nm, fontsize=9)
   plt.xlabel('time (ms)', fontsize=9)
   plt.xticks(fontsize=7)
   plt.xlim(xmax=plt.xlim()[1]+wid_adj[n])
   for i in range(len(d)):
     f.text(d[i], ind[i]+w, '  (%s)'%d[i], fontsize=7)

bars = []
plt.figure(figsize=(6,6))
for i in range(N):
   mkplot(i)
plt.subplots_adjust(left=.20, hspace=.5, wspace=.2)
plt.show()
plt.savefig("graph2.png")
