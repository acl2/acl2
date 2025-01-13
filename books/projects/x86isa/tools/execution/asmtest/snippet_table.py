#!/usr/bin/python3
# x86isa assembly snippet testing framework
#
# X86ISA Library
# Copyright (C) 2024 Kestrel Technology, LLC
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Sol Swords (sswords@gmail.com)

# Snippet table parsing and output
# Run with argument "h" to write out snippets.h so we can build asmtest executable
# Run with argument "lsp" after asmtest executable is built to write out snippets.lsp

import subprocess
import sys

usage = """
snippet_table.py h     -- build snippets.h
snippet_table.py lsp   -- build snippets.lsp, requires asmtest executable to be built
"""

if (len(sys.argv) != 2):
    print("Wrong number of arguments\n" + usage, file=sys.stderr)

if (sys.argv[1] != "h" and sys.argv[1] != "lsp"):
    print("Invalid argument: %s\n%s" % (sys.argv[1], usage), file=sys.stderr)

write_lsp = sys.argv[1] == "lsp"
    

    
# Parse the snippets-combined.txt file into snips, a list of triples [name, inbytes, outbytes]
snips = []
with open("snippets-combined.txt", "r", encoding="utf-8") as infile:
    for line in infile:
        line = line.strip()
        if (len(line) == 0):
            continue
        if (line[0] == "#"):
            continue

        triple = line.split()

        if (len(triple) != 3):
            print("Bad line: " + line, file=sys.stderr)
            exit(1)
            
        name = triple[0]
        inbytes = int(triple[1])
        outbytes = int(triple[2])

        snips.append([name, inbytes, outbytes])

if (write_lsp):        
    # Parse the output of readelf -s
    readelf = subprocess.run(['readelf', '-s', 'asmtest'], stdout=subprocess.PIPE)
    readelf_lines = readelf.stdout.decode('ASCII').split("\n")

    addr_table = {}

    for line in readelf_lines:
        # lines look like:
        #     72: 0000000000400ca0     0 NOTYPE  GLOBAL DEFAULT   14 blsi32
        octup = line.split();
        if (len(octup) != 8):
            continue
        try:
            addr = int(octup[1], 16)
        except ValueError:
            continue

        label = octup[7]

        addr_table[label] = addr

    # for key, val in addr_table.items():
    #     print(key + ": " + hex(val))


    # Pair up the snips data with the entry points from the addr_table

    snipdata = []
    for name, inbytes, outbytes in snips:
        if (not name in addr_table):
            print("Entry point not found for " + name, file=sys.stderr)
            exit(1)

        snipdata.append([name, inbytes, outbytes, addr_table[name]])

    # for name, inbytes, outbytes, addr in snipdata:
    #     print("name: " + name + " inbytes: " + str(inbytes) + " outbytes: " + str(outbytes) + " addr: " + hex(addr))


    # Write the snippets.lsp file
    with open("snippets.lsp", "w", encoding="utf-8") as outfile:
        outfile.write(';; Automatically generated -- do not edit\n')

        for name, inbytes, outbytes, addr in snipdata:
            outfile.write('("%s" %i %i #x%x)\n' % (name, inbytes, outbytes, addr))

else:
    # Write the snippets.h file
    with open("snippets.h", "w", encoding="utf-8") as outfile:
        outfile.write('// Automatically generated -- do not edit\n#include "snippets_type.h"\n')
        outfile.write("int snippet_count = " + str(len(snips)) + ";\n\n")

        for snip in snips:
            outfile.write("extern void " + snip[0] + "(void *, void *);\n")

        outfile.write("\n")

        outfile.write("const snippet_data snippets[] = {\n")

        entries = []
        for name, inbytes, outbytes in snips:
            entries.append('  { "%s", %i, %i, %s }' % (name, inbytes, outbytes, name))

        outfile.write(",\n".join(entries))
        outfile.write("\n};\n")
