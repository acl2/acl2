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

def get_info_pkg_defn_backquote(defn):
    ops = set()
    leaves = set()
    if isinstance(defn, list):
        if defn[0] == ",":
            new_ops, new_leaves = get_info_pkg_defn(defn[1])
            ops = ops | new_ops
            leaves = leaves | new_leaves
        else:
            for arg in defn[1:]:
                new_ops, new_leaves = get_info_pkg_defn_backquote(arg)
                ops = ops | new_ops
                leaves = leaves | new_leaves
    else:
        pass
    return ops, leaves

def get_info_pkg_defn(defn):
    ops = set()
    leaves = set()
    if isinstance(defn, list):
        ops.add(defn[0])
        if defn[0] == "'":
            pass
        elif defn[0] == "`":
            new_ops, new_leaves = get_info_pkg_defn_backquote(defn[1])
            ops = ops | new_ops
            leaves = leaves | new_leaves
        else:
            for arg in defn[1:]:
                new_ops, new_leaves = get_info_pkg_defn(arg)
                ops = ops | new_ops
                leaves = leaves | new_leaves
    else:
        leaves.add(defn)
    return ops, leaves

def get_info(pkgs):
    dups = set()
    ops = set()
    leaves = set()
    seen = {}
    for pkg in pkgs:
        if pkg["name"] in seen:
            dups.add(pkg["name"])
        seen[pkg["name"]] = True
        new_ops, new_leaves = get_info_pkg_defn(pkg["defn"])
        ops = ops | new_ops
        leaves = leaves | new_leaves
    return { "dups": list(dups), "ops": list(ops), "leaves": list(leaves) }


def expand_backquote(expr):
    if isinstance(expr, str):
        return False, expr
    if isinstance(expr, list):
        if len(expr) == 0:
            return False, expr
        if expr[0] == ",":
            item = expr[1]
            if isinstance(item, str):
                expect_list = False
                if item.startswith("@"):
                    expect_list = True
                    item = item[1:]
                if "::@" in item:
                    expect_list = True
                    item = item.replace("::@", "::", 1)
            return expect_list, expand_defn(item)
        retval = []
        for item in expr:
            expect_list, value = expand_backquote(item)
            if expect_list:
                retval.extend(value)
            else:
                retval.append(value)
        return False, retval
    raise ValueError("Unable to process backquote:", expr)

def expand_defn(defn):
    if isinstance(defn, str):
        if defn.startswith(":"):
            return defn
        if defn == 'ACL2::NIL':
            return []
        if defn in pkg_symbols:
            return pkg_symbols[defn]
        #raise ValueError ("Unrecognized Package Defconst:", defn)
        print ("Unrecognized Package Defconst:", defn)
        return []
    if isinstance(defn, list):
        if len(defn) == 0:
            return []
        if defn[0] == "'":
            if isinstance (defn[1], str):
                return defn[1]
            else:
                return defn[1]
        if defn[0] == "`":
            return expand_backquote (defn[1])[1]
        if defn[0] in ('ACL2::UNION-EQ-EXEC', 'ACL2::UNION-EQ', 'ACL2::UNION$', 'ACL2::APPEND', 'ACL2::REVAPPEND'):
            retval = set()
            for arg in defn[1:]:
                retval = retval | set(expand_defn(arg))
            return list(retval)
        if defn[0] in ('ACL2::SET-DIFFERENCE-EQ-EXEC', 'ACL2::SET-DIFFERENCE-EQ', 'ACL2::SET-DIFFERENCE-EQUAL'):
            fnargs0 = defn[1:]
            fnargs = []
            prev_keyword = False
            for fnarg in fnargs0:
                if prev_keyword:
                    continue
                if isinstance(fnarg, str) and fnarg.startswith(":"):
                    prev_keyword = True
                    continue
                prev_keyword = False
                fnargs.append(fnarg)
            x = set(expand_defn(fnargs[0]))
            y = set(expand_defn(fnargs[1]))
            return list(x - y)
        if defn[0] in ('ACL2::REMOVE', 'ACL2::REMOVE-EQ', 'ACL2::REMOVE1', 'ACL2::REMOVE1-EQ'):
            fnargs0 = defn[1:]
            fnargs = []
            prev_keyword = False
            for fnarg in fnargs0:
                if prev_keyword:
                    continue
                if isinstance(fnarg, str) and fnarg.startswith(":"):
                    prev_keyword = True
                    continue
                prev_keyword = False
                fnargs.append(fnarg)
            x = expand_defn(fnargs[0])
            l = set(expand_defn(fnargs[1]))
            if x in l:
                l.remove(x)
            return list(l)
        if defn[0] in ('ACL2::CONS'):
            x = expand_defn(defn[1])
            l = expand_defn(defn[2])
            l.insert(0, x)
            return l
        if defn[0] in ('ACL2::SHARED-SYMBOLS'):
            return pkg_symbols['(ACL2::SHARED-SYMBOLS)']
        if defn[0] in ('ACL2::SHARED-SYMBOLS-1'):
            return pkg_symbols['(ACL2::SHARED-SYMBOLS-1)']
    raise ValueError("Unable to process package definiition:", defn)

def get_imports(pkgs, check_dups = False):
    imports = {}
    files = {}
    dups = {}
    for pkg in pkgs:
        orig = set()
        if pkg["name"] in imports:
            orig = imports[pkg["name"]]
            if pkg["name"] not in dups:
                dups[pkg["name"]] = [(files[pkg["name"]], imports[pkg["name"]])]
            dups[pkg["name"]].append((pkg["file"], set(expand_defn(pkg["defn"]))))
        files[pkg["name"]] = pkg["file"]
        imports[pkg["name"]] = orig | set(expand_defn(pkg["defn"]))
    if check_dups:
        for pkg, entries in dups.items():
            print ("Package defined multiple times:", pkg)
            prev_defn = None
            for fname, defn in entries:
                if prev_defn is None or set(defn) == set(prev_defn):
                    print ("    " + fname)
                    prev_defn = defn
                else:
                    print ("    " + fname + " INCONSISTENT")
                prev_defn = prev_defn | defn
    return imports

class PackageDB:
    _pkgs = []
    _imports = {}

    def __init__(self, fname, verbose=False):
        with open(fname, "r", encoding='utf-8') as f:
            self._pkgs = json.load(f)
            self._imports = {}
            dups = []
            for pkg, symbols in get_imports(self._pkgs).items():
                d = {}
                for sym in symbols:
                    p, s = self._get_pkg(sym)
                    if s in d and p != d[s]:
                        dups.append((s, pkg, p, d[s]))
                    d[s] = p
                self._imports[pkg] = d

            for sym, pkg, pkg1, pkg2 in dups:
                if self.lookup_symbol(sym, pkg1) != self.lookup_symbol(sym, pkg2):
                    # if {pkg1, pkg2} != {"ACL2", "COMMON-LISP"}:
                    #     raise ValueError(f"Symbol {sym} duplicated in package {pkg} as {pkg1} (->{self.lookup_symbol(sym, pkg1)}) and {pkg2} (->{self.lookup_symbol(sym, pkg2)})")
                    if verbose:
                        print (f"Symbol {sym} DUPLICATED in package {pkg} as {pkg1} (->{self.lookup_symbol(sym, pkg1)}) and {pkg2} (->{self.lookup_symbol(sym, pkg2)})")
                else:
                    if verbose:
                        print(f"Symbol {sym} sort of duplicate in package {pkg} as {pkg1} (->{self.lookup_symbol(sym, pkg1)}) and {pkg2} (->{self.lookup_symbol(sym, pkg2)})")

    def pkg_info(self):
        return get_info(_pkgs)

    def _get_pkg(self, sym, pkg=None):
        quoted = False
        escaped = False
        for i in range(len(sym)):
            if escaped:
                escaped = False
                continue
            if sym[i] == "\\":
                escaped = True
                continue
            if quoted:
                if sym[i] == '|':
                    quoted = False
            else:
                if i+1<len(sym) and sym[i]==':' and sym[i+1]==":":
                    pkg = sym[0:i]
                    sym = sym[i+2:]
                    break
                if sym[i] == '|':
                    quoted = True
        if pkg is None:
            pkg = "ACL2"
        return pkg.upper(), sym.upper()

    def lookup_symbol (self, sym, pkg=None, strict=True):
        pkg, sym = self._get_pkg(sym, pkg)
        while True:
            if pkg in ("ACL2", "ACL2-USER", "COMMON-LISP", "ACL2-INPUT-CHANNEL", "ACL2-OUTPUT-CHANNEL"):
                if pkg == "ACL2-USER":
                    pkg = "ACL2"
                break
            if pkg not in self._imports:
                if not strict:
                    break
                raise ValueError ("Package is not defined:", pkg)
            if sym not in self._imports[pkg]:
                break
            pkg = self._imports[pkg][sym]
        if pkg == "ACL2":
            return sym
        return pkg + "::" + sym

if __name__ == "__main__":
    # logging.basicConfig(level=logging.DEBUG, filename='example.log', encoding='utf-8')
    logging.basicConfig(level=logging.DEBUG)

    sys.setrecursionlimit(1500)

    parser = argparse.ArgumentParser(description="Find definitions of packages in ACL2 Community Books.", epilog="Note: At least one of --lookup, --info, or --build must be specified")
    parser.add_argument("-d", "--data", default="pkgdefs.json", help="location of package database file")
    parser.add_argument("-l", "--lookup", nargs="*", default=[], help="symbol(s) to lookup")
    parser.add_argument("-i", "--info", action="store_true", help="print info about package database (useful for developers)")
    parser.add_argument("-b", "--build", nargs="*", default=[], help="use this to rebuild the package database from ACL2 sources (and use this only if you know what you're doing)")
    args = parser.parse_args()

    if not (args.build or args.info or args.lookup):
        parser.print_help ()
        sys.exit(1)

    if args.build is not None and len(args.build) > 0:
        for fname in args.build:
            pkgs = process_file(fname)
        if args.data is None or args.data == "-":
            print(json.dumps(pkgs, indent=2))
        else:
            with open(args.data, "w", encoding='utf-8') as out:
                json.dump(pkgs, out, indent=2)

    if args.info or args.lookup:
        if args.data is None or args.data == "-":
            print ("Database file must be specified with --data to run queries")
            args.print_help()
            sys.exit(1)
        db = PackageDB(args.data)
        if args.info:
            info = db.get_info()
            print(json.dumps(info, indent=2))
        for arg in args.lookup:
            orig = db.lookup_symbol(arg)
            print(f"{arg} -> {orig}")
