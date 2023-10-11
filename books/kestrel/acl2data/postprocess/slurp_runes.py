import sys
import os.path
import pathlib
import json
import re
import logging

from parse_acl2 import get_sexpr

def strip_prefix (prefix, s):
    if s.startswith(prefix):
        return s[(len(prefix)):]
    else:
        return s

def recognize_command (pkg, tree, cmd, minargs=1, maxargs=None):
    return (tree is not None 
            and len(tree) > 0
            and len(tree) >= minargs
            and (maxargs is None or len(tree) <= maxargs)
            and strip_prefix(pkg+"::", tree[0]).lower() == cmd)

def slurp_runes_from_tree(pkg, tree, runes):
    if recognize_command(pkg, tree, "in-package", 2):
        if len(tree[1]) < 3 or tree[1][0] != '"' or tree[1][-1] != '"':
            raise ValueError("Invalid package name")
        pkg = tree[1][1:-1]
    elif recognize_command(pkg, tree, "defthm", 2) or recognize_command(pkg, tree, "defthmd", 2):
        runes[tree[1]] = tree
    elif recognize_command(pkg, tree, "encapsulate", 2):
        for subtree in tree[2:]:
            slurp_runes_from_tree(pkg, subtree, runes)
    elif recognize_command(pkg, tree, "defsection", 2):
        prev_keyword = False
        for subtree in tree[2:]:
            if prev_keyword:
                prev_keyword = False
            elif isinstance(subtree, str) and subtree.startswith(":"):
                prev_keyword = True
            else:
                slurp_runes_from_tree(pkg, subtree, runes)
    elif recognize_command(pkg, tree, "local", 1):
        slurp_runes_from_tree(pkg, tree[1], runes)
    return pkg

def slurp_runes(fname, runes):
    if not os.path.exists(fname):
        logging.error("LISP File not found: " + fname)
        return runes
    with open(fname, encoding='latin-1') as f:
        code = f.read()
        i = 0
        pkg = "ACL2"
        while i < len(code):
            sexp, tree, i = get_sexpr(pkg, code, i)
            # print(sexp)
            # print(tree)
            if (sexp.startswith(":") or
                (sexp.startswith("#") and sexp[1] not in "\\oOxX")):
                cmd = sexp
                sexp, tree, i = get_sexpr(pkg, code, i)
                if tree is None:
                    raise ValueError("Syntax error: :cmd or #-expr at end of file")
                sexp = cmd + " " + sexp
                tree = [cmd, tree]
            pkg = slurp_runes_from_tree(pkg, tree, runes)
    return runes

if __name__ == "__main__":
    args = sys.argv
    if len(args) == 1:
        print("Usage: slurp_runes file.lisp ...")
    runes = {}
    for fname in args[1:]:
        slurp_runes(fname, runes)
    print(runes)
