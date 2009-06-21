import sys
n=3000
s=sys.stdout
s.write("(import (mk))\n(run 1 (q)\n  (exist (")
for i in range(n):
   if i:
      s.write(" v%d" % i)
   else:
      s.write("v%d" % i)
s.write(")\n")
#for i in range(n):
   #if i==0:
      #s.write("    (== v%d q)\n" % i)
   #else:
      #s.write("    (==/var v%d v%d)\n" % (i, i-1))
   #if i==n-1: s.write("))\n")
for i in range(n):
   if i==n-1:
      s.write("    (== v%d q)))\n" % i)
   else:
      s.write("    (==/var v%d v%d)\n" % (i, i+1))
