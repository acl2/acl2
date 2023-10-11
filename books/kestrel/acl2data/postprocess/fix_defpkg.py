import sys
import os.path
import pathlib
import json
import re
import argparse
import sqlite3
import logging


from parse_acl2 import get_sexpr
from pkg_consts import pkg_symbols

def strip_prefix (prefix, s):
    if not isinstance(s, str):
        print ("*** NOT A STRING ***")
        print(s)
    if s.startswith(prefix):
        return s[(len(prefix)):]
    else:
        return s

def strip_package (s):
    if not isinstance(s, str):
        print ("*** NOT A STRING ***")
        print(s)
    idx = s.find("::")
    if idx >= 0:
        return s[idx+2:]
    else:
        return s

def package_of (s, pkg):
    if not isinstance(s, str):
        print ("*** NOT A STRING ***")
        print(s)
    idx = s.find("::")
    if idx >= 0:
        return s[:idx]
    else:
        return pkg

def recognize_command (pkg, tree, cmd, minargs=1, maxargs=None):
    return (tree is not None 
            and isinstance(tree, list)
            and len(tree) > 0
            and isinstance(tree[0], str)
            and len(tree) >= minargs
            and (maxargs is None or len(tree) <= maxargs)
            and strip_prefix(pkg+"::", tree[0]).lower() == cmd)

def get_pkg_name(name):
    if name.startswith(":") or name.startswith("#:"):
        pkg = name
    elif len(name) >= 3 and name[0] == '"' and name[-1] == '"':
        pkg = name[1:-1]
    else:
        raise ValueError("Invalid package name")
    return pkg

def collect_pkgs_from_tree(pkg, tree, fname, pkgs):
    if recognize_command(pkg, tree, "in-package", 2):
        pkg = get_pkg_name (tree[1])
    elif recognize_command(pkg, tree, "defpkg", 3):
        newpkg = get_pkg_name (tree[1])
        logging.info ("New Package: " + newpkg)
        pkgs.append({"name": newpkg, "defn": tree[2], "file": fname})
    return pkg

def collect_pkgs(code, fname):
    pkgs = []
    i = 0
    pkg = "ACL2"
    while i < len(code):
        sexp, tree, i = get_sexpr(pkg, code, i)
        if tree is None:
            break
        # print(sexp)
        # print(tree)
        if (sexp.startswith(":") or
            (sexp.startswith("#") and sexp[1] not in "\\oOxX")):
            cmd = sexp
            if sexp.upper() in (":U", ":GOOD-BYE"):
                tree = [cmd]
            else:
                sexp, tree, i = get_sexpr(pkg, code, i)
                if tree is None:
                    raise ValueError("Syntax error: :cmd or #-expr at end of file:" + cmd)
                sexp = cmd + " " + sexp
                tree = [cmd, tree]
        pkg = collect_pkgs_from_tree(pkg, tree, fname, pkgs) 
    return pkgs

def process_file(fname):
    if os.path.isdir(fname):
        if fname == "quicklisp" or fname.endswith("/quicklisp"):
            logging.info(">>> Skipping " + fname + " because quicklisp directory has many non-ACL2 .lisp files")    
            return []
        logging.info(">>> " + fname)
        pkgs = []
        for filename in sorted(os.listdir(fname)):
            if filename.startswith('.'):
                continue
            f = os.path.join(fname, filename)
            pkgs.extend(process_file(f))
        return pkgs

    if pathlib.Path(fname).suffix not in (".lisp", ".lsp", ".acl2"):
        return []

    logging.info("> " + fname)
    with open(fname, encoding='latin-1') as f:
        content = f.read()
        try:
            return collect_pkgs(content, fname)
        except Exception as e:
            if str(pathlib.Path(fname)).endswith(".lsp"):
                logging.error ("PROBLEM PARSING: " + fname)
                print(e)
            else:
                logging.fatal ("PROBLEM PARSING: " + fname)
                raise e

    return []


def get_info(pkgs):
    dups = {}
    seen = {}
    conflicts = {}
    for pkg in pkgs:
        if pkg["name"] not in seen:
            seen[pkg["name"]] = []
        seen[pkg["name"]].append((pkg["file"], pkg["defn"]))

    for pkg in seen:
        if len(seen[pkg]) > 1:
            defns = []
            clusters = []
            for (fname, defn) in seen[pkg]:
                for i in range(len(defns)):
                    if defns[i] == defn:
                        break
                else:
                    defns.append(defn)
                    i = len(defns)-1
                if i >= len(clusters):
                    clusters.append([])
                clusters[i].append(fname)
            dups[pkg] = clusters
    return dups

if __name__ == "__main__":
    # logging.basicConfig(level=logging.DEBUG, filename='example.log', encoding='utf-8')
    logging.basicConfig(level=logging.DEBUG)

    sys.setrecursionlimit(1500)

    parser = argparse.ArgumentParser(description="Find duplicate/conflicted definitions of packages in ACL2 Community Books.")
    parser.add_argument("-d", "--data", default="pkgdefs.json", help="location of package database file")
    parser.add_argument("-b", "--build", nargs="*", default=[], help="use this to rebuild the package database from ACL2 sources (and use this only if you know what you're doing)")
    args = parser.parse_args()

    if args.build is not None and len(args.build) > 0:
        pkgs = []
        for fname in args.build:
            pkgs.extend(process_file(fname))
        if args.data is None or args.data == "-":
            print(json.dumps(pkgs, indent=2))
        else:
            with open(args.data, "w", encoding='utf-8') as out:
                json.dump(pkgs, out, indent=2)
    else:
        with open(args.data, "r", encoding='utf-8') as f:
            pkgs = json.load(f)
    info = get_info(pkgs)
    print(json.dumps(info, indent=2))
