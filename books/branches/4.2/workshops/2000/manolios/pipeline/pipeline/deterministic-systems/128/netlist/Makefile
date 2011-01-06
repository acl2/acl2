include ../../../../../../../../Makefile-generic


# Dependencies:

netlist.cert: netlist.lisp
netlist.cert: ../serial/serial.cert
netlist.cert: ../../../top/alist-thms.cert

ma128net.cert: ma128net.lisp
ma128net.cert: netlist.cert
ma128net.cert: ../serial/ma128serial.cert                       

ma128net-ma128serial.cert: ma128net-ma128serial.lisp
ma128net-ma128serial.cert: ma128net.cert
