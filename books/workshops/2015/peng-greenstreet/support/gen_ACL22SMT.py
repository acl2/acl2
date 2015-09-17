# Copyright (C) 2015, University of British Columbia
# Written (originally) by Yan Peng (13th March, 2014)

# License: A 3-clause BSD license.
# See the LICENSE file distributed with this software



# This python script generates a LISP file called ACL22SMT.lisp.
# ACL22SMT.lisp contains a function called ACL22SMT that produces
# the ACL2_to_Z3.py string.
# This is a string that stands for the interface class between
# ACL2 and Z3.

# The way we generate ACL22SMT.lisp:
# We take the python file we've already written ACL2_to_Z3.py
# and the name of the LISP file we want to write to, which is
# ACL22SMT.lisp
# The user need to pass in the class name

import io
import re
import sys

specialChar = {
    r',' : r'#\,',
    r':' : r'#\:',
    r'(' : r'#\(',
    r')' : r'#\)',
    r' ' : r'#\Space',
    r'.' : r'#\.',
    r"'" : r"#\'",
    r'"' : r"#\"",
    r'#' : r'#\#'
}

def gen_LISPList(line):
    strLISPList = "    (list "
    for word in line:
        if word in specialChar:
            strLISPList += specialChar[word] + " "
        elif word == '':
            continue
        else:
            strLISPList += r'"' + word + r'"' + " "
    strLISPList += " #\Newline )\n"
    return strLISPList


def gen(fromPyFile, toLispFile):
    wt = open(toLispFile, 'w')
    wfile = []

    head = "(in-package \"ACL2\")\n(defun ACL22SMT () \n  (list\n"
    with open(fromPyFile, 'r') as rf:
        rfile = rf.readlines()
    for rline in rfile:
        rline = rline.rstrip()
        rline = re.split('(\W)' , rline)
        #print rline
        wline = gen_LISPList(rline)     # a string that ends with a \n
        wfile.append(wline)
    tail = "))"

    wt.writelines(head)
    wt.writelines(wfile)
    wt.writelines(tail)

    wt.close()

def main(argv):
    inf = ''
    outf = ''
    if(len(argv) != 2):
        print "Wrong number of input arguments:"
        print "gen_ACL22SMT.py <inputfile> <outputfile>"
        exit(2)
    else:
        inf = argv[0]
        outf = argv[1]
        gen(inf,outf)
        print "Finish generating file %s from file %s." % ( inf, outf )

if __name__ == "__main__":
    main(sys.argv[1:])

