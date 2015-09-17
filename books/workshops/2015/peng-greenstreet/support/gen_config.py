# Copyright (C) 2015, University of British Columbia
# Written (originally) by Yan Peng (13th March, 2014)
#
# License: A 3-clause BSD license.
# See the LICENSE file distributed with this software


# This file generates config.lisp which sets the default
# settings of Smtlink.
#
# Usage:
#   python gen_config.py -i <inputfile>
#                        -o <outputfile>
#                        -p <dir-to-py-exe>
#                        -z <dir-to-py-files>
#                        -e <dir-to-expand-files>
#
# This file can only access default settings for
#
#   1. <dir-to-py-exe> :       The absolute path to where the
#                              Python executable is.
#                              If not set, it gets nil and
#                              the program will report an error.
#
#   2. <dir-to-py-files> :     The path to where the generated
#                              Python files will be stored.
#                              If not set, it will get nil
#                              and Python files will be
#                              generated at /tmp/py_file.
#                              The files will get deleted
#                              every time Smtlink finishes a proof.
#                              Unsuccessful proof will stay
#                              for users to check.
#
#   3. <dir-to-expand-files> : The path to where the generated
#                              log files for function expansion
#                              will be stored.
#                              If not set, it gets nil and
#                              no log files will be generated.
#                              This directory is used while debugging
#                              Smtlink. Typical users of Smtlink
#                              won't need to use it.


import io
import sys
import getopt
import re

def is_marker(mk):
    if (mk == ";; Insert-code-for-default-smtlink-config\n"):
        return True
    else:
        return False

def gen_code(py_exe, py_file, ex_file):
    code = []

    code.append("(defconst *default-smtlink-config*\n")
    code.append("  (make-smtlink-config :dir-interface nil\n")
    if (py_file == "nil"):
        code.append("                       :dir-files " + py_file + "\n")
    else:
        code.append("                       :dir-files \"" + py_file + "\"\n")
    code.append("                       :SMT-module \"ACL2_to_Z3\"\n")
    code.append("                       :SMT-class \"ACL22SMT\"\n")
    if (py_exe == "nil"):
        print "Error: Python executable is not set yet ..."
        exit(1)
    else:
        code.append("                       :smt-cmd \"" + py_exe + "\"\n")
    if (ex_file == "nil"):
        code.append("                       :dir-expanded " + ex_file + "))\n")
    else:
        code.append("                       :dir-expanded \"" + ex_file + "\"))\n")

    return code

def gen(inf, outf, py_exe, py_file, ex_file):
    wt = open(outf, 'w')
    wlines = []

    with open(inf, 'r') as rf:
        rlines = rf.readlines()
    for rline in rlines:
        if (is_marker(rline)):
            wlines += gen_code(py_exe, py_file, ex_file)
        else:
            wlines.append(rline)

    wt.writelines(wlines)
    wt.close()

def main(argv):
    inf = "config-template.lisp"
    outf = "config.lisp"
    py_exe = "nil"
    py_file = "nil"
    ex_file = "nil"
    try:
        opts, args = getopt.getopt(argv, "i:o:p:z:e:")
        print opts, args
    except getopt.GetoptError:
        print "gen_config.py -i <input-file> -o <output-file> -p <python-executable> -z <generated-python-files> -e <generated-expanded-files>"
        sys.exit(2)
    for opt, arg in opts:
        if opt == '-i':
            inf = arg
        elif opt == '-o':
            outf = arg
        elif opt == '-p':
            py_exe = arg
        elif opt == '-z':
            py_file = arg
        elif opt == '-e':
            ex_file = arg
    
    gen(inf, outf, py_exe, py_file, ex_file)
    print "Finished generating %s file from %s file..." % (outf, inf)


if __name__ == "__main__":
    main(sys.argv[1:])
