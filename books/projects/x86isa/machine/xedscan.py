#!/usr/bin/env python3
# X86ISA Library
# Copyright (C) 2024 Kestrel Technology, LLC
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Sol Swords (sswords@gmail.com)

import sys
import re

usage = """Usage: xedscan.py datafile.txt output.lsp

NOTE: (Sol Swords, 1/4/2025)

At the moment this is a small proof of concept for generating
inst-listing.lisp opcode map entries by parsing XED data files.
See the comments in this python script for more details.
"""


# This was designed to pick up the X87 instruction set which was
# missing from our opcode maps. These use the "escape" opcodes D8
# through DF so we look for these opcodes and ignore all others. While
# the SDM treats these instructions specially (has tables for them
# separate from the standard opcode maps), their decoding isn't much
# different -- they just pack a lot of instructions into 8 opcodes by
# using MOD and sometimes RM bits as opcode extensions.  These are
# denoted in xed-isa.txt (from the xed source distribution) as in the
# following examples:

# PATTERN   : 0xDC MOD[mm] MOD!=3 REG[0b110] RM[nnn] MODRM()

# This breaks down as:
# 0xDC -- the opcode (multibyte opcodes are formatted as e.g. 0x0F 0x01)
# MOD[mm] -- I think this notation just means that this field isn't fixed, maybe binds some variable mm to the decoded value?
# MOD!=3 -- signifies the MOD fiel of MODRM d can't be 3
# REG[0b110] -- REG field of MODRM must be 6
# RM[nnn] -- again signifies RM field isn't fixed, maybe bound to nnn
# MODRM() -- maybe signifies that a MODRM byte is required? not sure, not always present.

# PATTERN   : 0xD9 MOD[0b11] MOD=3 REG[0b100] RM[0b001]

# This breaks down as:
# 0xD9: opcode
# MOD[0b11] -- MOD field must be 3
# MOD=3     -- MOD field must be 3, not sure what difference is to the above -- they always coincide
# REG[0b100] -- REG field must be 4
# RM[0b001] -- RM field must be 1.

# Despite not understanding a fair amount about these, this is
# sufficient to make basic opcode map entries for these x87 instructions.

# One thing we haven't explored is generating ARG entries for better instruction decoding.

# Exception conditions don't seem to be covered by the XED data files
# unless I'm missing something. We've hardcoded exceptions common to
# x87 instructions.

# Further use of the XED data files to extend / check accuracy of our
# opcode maps would be a good idea.  This script maybe provides a
# starting point, though there are lots of cases it won't handle.



if (len(sys.argv) != 3):
    print(usage, file=sys.stderr)

inname = sys.argv[1]
outname = sys.argv[2]

# Integer constants in xed datafiles seem to be either decimal or
# prefixed 0x or 0b.  But many places can have either an integer or
# some other string value, e.g. the RM field may be an integer or
# 'nnn'. So in those cases we catch the execption and return the input string.
def maybe_parse_integer(tok):
    code = tok[0:2]
    val = tok
    try:
        if (code == "0x"):
            val = int(tok[2:], 16)
        elif (code == "0b"):
            val = int(tok[2:], 2)
        else:
            val = int(tok)
    except ValueError:
        None
    return val


# At the moment I'm recognizing patterns that contain the following sorts of elements:
# 0xAB -- opcode bytes (only at the beginning)
# KEY[val] where val is perhaps a number
# KEY=val where val is perhaps a number (not sure if there's any difference)
#  (note we don't include KEY!=val here -- we just say key can't end in !)
# Other strings, which are just stored as keys associated to True.
def parse_pattern(pat):
    obj = {}
    tokens = pat.split(" ")
    opcode = 0
    it = iter(tokens)
    for tok in it:
        if (tok[0:2] == "0x"):
            opcode = (opcode<<8) + int(tok[2:], 16)
        else:
            break
    obj['opcode'] = opcode
    for tok in it:
        if (m := re.search("^(?P<key>.*)\\[(?P<val>.*)\\]$", tok)):
            obj[m.group('key')] = maybe_parse_integer(m.group('val'))
        elif (m := re.search("^(?P<key>.*[^!])=(?P<val>.*)$", tok)):
            obj[m.group('key')] = maybe_parse_integer(m.group('val'))
        else:
            obj[tok] = True
    return obj
        
            
    
# This just reads lines of the form KEY : VAL until we reach a closing
# } (on its own line).  For the PATTERN key, we parse the value using
# parse_pattern above, otherwise we just store the value as a string.
def parse_inst(infile):
    obj = {}
    for line in infile:
        while ((len(line) >= 2) and (line[-2] == '\\')):
            # join subsequent lines while they end in \
            line = line[:-2] + next(infile)
        line = line.strip()
        if (line == "}"):
            return obj
        if (line == "" or line[0] == "#"):
            continue
        sides = line.split(":", 1)
        if (len(sides) != 2):
            print("bad line: " + line, file=sys.stderr)
            continue
        key = sides[0].strip()
        val = sides[1].strip()
        if (key == "PATTERN"):
            val = parse_pattern(val)
        obj[key] = val

# Read and parse the xed data file into a bunch of inst objects, which
# are just dictionaries; at the moment only the PATTERN entry is
# parsed further, the rest are just stored as strings.
insts = []
with open(inname, "r", encoding="utf-8") as infile:
    for line in infile:
        while ((len(line) >= 2) and (line[-2] == '\\')):
            # join subsequent lines while they end in \
            line = line[:-2] + next(infile)
        line = line.strip()
        if (line == "{"):
            insts.append(parse_inst(infile))

def parse_features(extension):
    if (extension == "X87"):
        return " :FEAT '(:FPU)"
    else:
        return ""
    # if (extension == "BASE"):
    #     return ""
    # elif
    # else:
    #     return " :FEAT '(:%s)" % extension

def lisp_comment(string):
    res = ""
    for line in string.splitlines(True): # keep line breaks
        res = res + ";; " + line
    return res

# Write out a list of INST forms (opcode map entries) based on what was read from the file
with open(outname, "w", encoding="utf-8") as outfile:
    outfile.write('''\
;; Generated using:
;; xedscan.py %s %s\n\n''' % (inname, outname))
    for inst in insts:
        opcode = inst["PATTERN"]['opcode']
        # print("opcode: %x opcode>>8: %x opcode&0xf8: %x" % (opcode, opcode>>8, opcode & 0xf8));
        if ((opcode & 0xf8 == 0xd8) and (opcode >> 8 == 0)):
            pattern = inst["PATTERN"]
            rm = pattern["RM"]
            inst_entry = '''\
    (INST "%s"
          (OP :OP #x%x :REG %s :MOD %s%s%s)
          (ARG) ;; bozo x87 conventions
          nil
          '((:UD (UD-LOCK-USED))
            (:NM (NM-CR0-TS-IS-1)
                 (NM-CR0-EM-IS-1))))\n''' % (inst["ICLASS"],
                                           opcode,
                                           str(pattern["REG"]),
                                           ":MEM" if ('MOD!=3' in pattern) else str(pattern["MOD"]),
                                           "" if (rm == 'nnn') else " :R/M " + str(rm),
                                           parse_features(inst["EXTENSION"]) if "EXTENSION" in inst else "")
            # Comment out the inst entry if it is marked UNDOCUMENTED.
            if ("ATTRIBUTES" in inst and inst["ATTRIBUTES"].find("UNDOCUMENTED") >= 0):
                inst_entry = ";; Undocumented (from xed-isa.txt):\n" + lisp_comment(inst_entry)
            
            outfile.write(inst_entry)
