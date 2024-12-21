#!/usr/bin/python3
# x86isa assembly snippet testing framework
#
# X86ISA Library
# Copyright (C) 2024 Kestrel Technology, LLC
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Sol Swords (sswords@gmail.com)

import sys

usage = """Usage:
   text_to_binary.py infile.txt outfile.bin
 -- reads text from infile.txt, writes binary to outfile.bin

# Begin sample input file:

# If first character is #, line is a comment
# If first character is ;, line is a format specifier (number of bytes for each entry)
; 4, 4, 2
# A format specifier must come before any regular lines like the following:
abcde, 12345, ba34
0, 0, 0
1, a, b

# Blank lines are ignored

# The following line would cause an error if uncommented because it
# has the wrong number of entries:
# ab, cd

# as would:
# ab, cd, ef

# The following line would cause an error if uncommented because one
# of the entries is out of both the signed and unsigned integer range
# (in fact, all of the entries are:
# 100000000, -80000001, -ffff

# Another format specifier will change how the following lines are read:
; 2, 2, 1
abcd, defg, ab

# Multibyte integers are always written least-significant first (little-endian,
# as in x86), data entries are always parsed in hex, and format specifier
# entries are always parsed in decimal.
"""

if (len(sys.argv) != 3):
    print(usage, file=sys.stderr)

inname = sys.argv[1]
outname = sys.argv[2]


fmt = None
with open(inname, "r", encoding="utf-8") as infile:
    with open(outname, "wb") as outfile:
        for line in infile:
            line = line.strip()
            if (len(line) == 0):
                continue
            if (line[0] == "#"):
                continue
            if (line[0] == ";"):
                # Format specifier
                # Split by commas, parse integers and push into fmt list
                fmt = []
                line = line[1:]
                entries = line.split(",")
                for entry in entries:
                    entry = entry.strip()
                    val = int(entry)
                    fmt.append(val)
                continue

            # Regular line: split, then output according to format
            if (fmt is None):
                print("Format line beginning in semicolon must come before regular data lines", file=sys.stderr)
                print(usage, file=sys.stderr)
                exit(1)

            entries = line.split(",")
            if (len(entries) != len(fmt)):
                print("Data lines must have the same number of entries as the preceding format line", file=sys.stderr)
                print(usage, file=sys.stderr)
                exit(1)

            for entry, size in zip(entries, fmt):
                entry = entry.strip()
                val = int(entry, 16)
                if (val >= 2**(size*8) or val < -(2**((size*8)-1))):
                    print("Entry %s out of range of formatted size %d" % (entry, size), file=sys.stderr)
                    exit(1)
                val_bytes = val.to_bytes(size, byteorder='little', signed=val<0)
                outfile.write(val_bytes)

                
                
                      


            
            
