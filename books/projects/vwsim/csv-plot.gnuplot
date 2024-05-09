# comma-separated file
set datafile separator ','
# print statements in this file will go to standard output
set print "-"
# places the legend (key) outside of the figure
set key outside
# "default and podo colors are chosen to be more easily distinguished
# in print and in particular by people with color vision problems."
set colorsequence podo

# simulation variables to plot.
if (!exists("vars")) \
   print "No simulation variables provided for plotting"; quit

if (!exists("filename")) \
   print "File not provided"; quit

# assume that the $time$ values are the first column in the CSV file
time_index = 1

plot for [i=1:words(vars)] \
     filename \
     using time_index:(column(word(vars,i))) title word(vars,i) with lines \
     lw 2

# pause mouse close waits until close for the shell process to end.
# This is what allows you to zoom in/out of the figure.
# If you use gnuplot -p (i.e. persistent mode), then you cannot zoom
pause mouse close
# pause -1   # doesn't work when calling from ACL2 prompt