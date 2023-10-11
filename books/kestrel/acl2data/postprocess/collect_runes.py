import sys
import os.path
import pathlib
import json
import argparse
import re
import logging

from parse_acl2 import get_sexpr

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

def package_of (s, pkg=None):
    if not isinstance(s, str):
        print ("*** NOT A STRING ***")
        print(s)
    idx = s.find("::")
    if idx >= 0:
        return s[:idx]
    else:
        return pkg

def canonize_symbol (s, pkg):
    key = package_of(s, pkg).upper() + "::" + strip_package(s).upper()
    return key

def add_rune(rune, pkg, fname, is_local, command, runes):
    key = canonize_symbol(rune, pkg)
    entry = {"file": fname, 
             "local": is_local, 
             "command": command.lower()}
    if key not in runes:
        runes[key] = []
    if entry not in runes[key]:
        runes[key].append(entry)

def recognize_command (pkg, tree, cmd, minargs=1, maxargs=None):
    return (tree is not None 
            and len(tree) > 0
            and len(tree) >= minargs
            and (maxargs is None or len(tree) <= maxargs)
            and strip_prefix(pkg+"::", tree[0]).lower() == cmd)

def collect_runes_from_trees_and_keywords(forest, pkg, is_local, fname, runes, skip=0):
    prev_keyword = False
    for subtree in forest:
        if prev_keyword:
            prev_keyword = False
        elif isinstance(subtree, str):
            if subtree.startswith(":"):
                prev_keyword = True
        # elif len(subtree) == 0:
        #     pass # because (define ...) allows NIL as an inner form!?!?!?
        else:
            if skip > 0:
                skip = skip - 1
            else:
                collect_runes_from_tree(pkg, subtree, is_local, fname, runes)

def collect_runes_from_tree(pkg, tree, is_local, fname, runes):
    if recognize_command(pkg, tree, "in-package", 2):
        if tree[1].startswith(":") or tree[1].startswith("#:"):
            pkg = tree[1]
        elif len(tree[1]) >= 3 and tree[1][0] == '"' and tree[1][-1] == '"':
            pkg = tree[1][1:-1]
        else:
            raise ValueError("Invalid package name")
    elif recognize_command(pkg, tree, "local", 2):
        collect_runes_from_tree(pkg, tree[1], True, fname, runes)
    elif recognize_command(pkg, tree, "encapsulate", 2):
        for subtree in tree[2:]:
            collect_runes_from_tree(pkg, subtree, is_local, fname, runes)
    elif recognize_command(pkg, tree, "defsection", 2):
        add_rune(tree[1], pkg, fname, is_local, "defsection", runes)
        collect_runes_from_trees_and_keywords(tree[2:], pkg, is_local, fname, runes)
    elif recognize_command(pkg, tree, "define", 3):
        add_rune(tree[1], pkg, fname, is_local, "define", runes)
        collect_runes_from_trees_and_keywords(tree[2:], pkg, is_local, fname, runes, skip=2)
    elif recognize_command(pkg, tree, "defines", 2):
        add_rune(tree[1], pkg, fname, is_local, "defines", runes)
        collect_runes_from_trees_and_keywords(tree[2:], pkg, is_local, fname, runes)
    elif recognize_command(pkg, tree, "defuns", 1):
        for defn in tree[1:]:
            if isinstance(defn, list) and len(defn) > 0:
                add_rune(defn[0], pkg, fname, is_local, "defuns", runes)
    elif recognize_command(pkg, tree, "mutual-recursion", 1):
        collect_runes_from_trees_and_keywords(tree[1:], pkg, is_local, fname, runes)
    elif recognize_command(pkg, tree, "eval-when", 1):
        collect_runes_from_trees_and_keywords(tree[2:], pkg, is_local, fname, runes)
    elif recognize_command(pkg, tree, "deftest", 1):
        pass # Because we do not want to store RUNEs that are just tests
    elif recognize_command(pkg, tree, "with-upgradability", 1):
        collect_runes_from_trees_and_keywords(tree[2:], pkg, is_local, fname, runes)
    elif recognize_command(pkg, tree, "local", 1):
        collect_runes_from_tree(pkg, tree[1], True, fname, runes)
    elif recognize_command(pkg, tree, "defattach", 1):
        pass
    else:
        command = strip_package(tree[0]).lower()
        if command.startswith("def"):
            if command.startswith("defthm-") and ("-flag-" in command or command.endswith("-flag")):
                logging.info(f"... Descending into {tree[0]}")
                collect_runes_from_trees_and_keywords(tree[1:], pkg, is_local, fname, runes)
            else:
                if len(tree) <= 1:
                    logging.error(f"*** def.* has no arguments: ({tree[0]} )")
                elif isinstance(tree[1], str):
                    add_rune(tree[1], pkg, fname, is_local, command, runes)
                else:
                    logging.error(f"*** 1st argument of def.* is not a string: ({tree[0]} {tree[1]} ...)")
    return pkg

def collect_runes(code, fname, runes):
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
            sexp, tree, i = get_sexpr(pkg, code, i)
            if tree is None:
                raise ValueError("Syntax error: :cmd or #-expr at end of file")
            sexp = cmd + " " + sexp
            tree = [cmd, tree]
        pkg = collect_runes_from_tree(pkg, tree, False, fname, runes)
    return runes

def process_file(fname, runes):
    if os.path.isdir(fname):
        if fname == "quicklisp" or fname.endswith("/quicklisp"):
            logging.info(">>> Skipping " + fname + " because quicklisp directory has many non-ACL2 .lisp files")    
            return []
        logging.info(">>> " + fname)
        for filename in sorted(os.listdir(fname)):
            if filename.startswith('.'):
                continue
            f = os.path.join(fname, filename)
            process_file(f, runes)
        return runes

    if not str(pathlib.Path(fname)).endswith("lisp"):
        return []

    logging.info("> " + fname)
    with open(fname, encoding='latin-1') as f:
        content = f.read()
        collect_runes(content, fname, runes)
    return runes

class RuneDB:
    _runes = []

    def __init__(self, fnames):
        if isinstance(fnames, str):
            fnames = [fnames]
        for fname in fnames:
            with open(fname, "r", encoding='utf-8') as f:
                self._runes.append(json.load(f))

    def lookup_rune (self, rune, pkg=None, regex=False):
        idx = rune.find("::")
        if idx >= 0:
            pkg = rune[:idx]
            rune = rune[idx+2:]
        if regex:
            rune_regex = re.compile(rune)
        if not regex and pkg is not None and rune is not None:
            key = canonize_symbol(rune, pkg)
        else:
            key = None
        for db in self._runes:
            if key is not None:
                if key in db:
                    return [ {"rune": key, **row} for row in db[key] ]
            else:
                results = []
                for _key, rows in db.items():
                    key_sym = strip_package(_key)
                    key_pkg = package_of(_key)
                    if pkg is not None and pkg.upper() != key_pkg:
                        continue
                    if regex:
                        if not rune_regex.match(key_sym):
                            continue
                    else:
                        if rune.upper() != key_sym:
                            continue
                    print (results)
                    results.extend([ {"rune": _key, **row} for row in rows ])
                    print (results)
                if results:
                    return results
        return []

if __name__ == "__main__":
    # logging.basicConfig(level=logging.DEBUG, filename='example.log', encoding='utf-8')
    logging.basicConfig(level=logging.DEBUG)

    sys.setrecursionlimit(1500)

    parser = argparse.ArgumentParser(description="Collect RUNEs from ACL2 files.", epilog="Note: At least one of --lookup or --build must be specified")
    parser.add_argument("-d", "--data", nargs="*", default=["runes.json"], help="location of rune database file(s)")
    parser.add_argument("-l", "--lookup", nargs="*", default=[], help="symbol(s) to lookup")
    parser.add_argument("-r", "--regex", action="store_true", help="if specified, lookup symbols are treaded as regular expressions")
    parser.add_argument("-b", "--build", nargs="*", default=[], help="use this to rebuild the rune database from ACL2 sources (and use this only if you know what you're doing)")
    args = parser.parse_args()

    if not (args.build or args.lookup):
        parser.print_help ()
        sys.exit(1)

    if args.build:
        runes = {}
        for fname in args.build:
            process_file(fname, runes)
        if args.data is None or args.data == ["-"]:
            print(json.dumps(runes, indent=2))
        elif len(args.data) > 1:
            print ("Only one data file can be specified with --build")
            parser.print_help ()
            sys.exit(1)
        else:
            with open(args.data[0], "w", encoding='utf-8') as out:
                json.dump(runes, out, indent=2)

    if args.lookup:
        if args.data is None or args.data == ["-"]:
            print ("Data file must be specified with --lookup")
            parser.print_help ()
            sys.exit(1)
        else:
            rune_db = RuneDB(args.data)
            for rune in args.lookup:
                results = rune_db.lookup_rune(rune, regex=args.regex)
                print(rune.upper())
                print(json.dumps(results, indent=2))

