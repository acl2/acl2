from acl2_bridge import ACL2Bridge, ACL2Command, ACL2BridgeError

import sys
import os.path
import pathlib
import json
import re
import logging

from parse_file import get_sexpr

bridge = ACL2Bridge(log=logging)

response = bridge.acl2_command(ACL2Command.JSON, "(cdr (assoc 'acl2-version *initial-global-table*))")
print ("Connected to: " + response["RETURN"])
response = bridge.acl2_command(ACL2Command.LISP, "(set-slow-alist-action nil)")
# print(json.dumps(response, indent=2))
response = bridge.acl2_command(ACL2Command.LISP, "(assign slow-array-action nil)")
# print(json.dumps(response, indent=2))

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

def extract_summary (pkg, thm, response):
    summary = {}
    summary['name'] = thm[1]
    summary['form'] = thm[2]
    summary['enable'] = []
    summary['disable'] = []
    summary['runes'] = []
    summary['uses'] = []
    summary['runenames'] = []

    uses = set()
    runenames = set()
    if "STDOUT" not in response:
        return 
    stdout = response["STDOUT"].split("\n")
    i = 0
    while i < len(stdout):
        # print (">>>", stdout[i])
        if stdout[i].startswith("Rules: ("):
            content = stdout[i][6:]
            i += 1
            while i < len(stdout) and stdout[i][0].isspace():
                content += stdout[i]
                i += 1
            _, runes, _ = get_sexpr("ACL2", content, 0)
            summary['runes'] = []
            for rune in runes:
                if rune[0].lower() == "cons":
                    summary['runes'].append(f"({rune[1]} {rune[2][1]} . {rune[2][2]})")
                    runenames.add(rune[2][1])
                elif not rune[0].startswith(":FAKE-RUNE-"):
                    summary['runes'].append(f"({rune[0]} {rune[1]})")
                    runenames.add(rune[1])
        elif stdout[i].startswith("Hint-events: ("):
            content = stdout[i][12:]
            i += 1
            while i < len(stdout) and stdout[i][0].isspace():
                content += stdout[i]
                i += 1
            _, runes, _ = get_sexpr("ACL2", content, 0)
            for r in runes:
                if r[0] not in (':USE', ':BY'):
                    raise ValueError("Very strange rune type in Hint-events: " + str(r))
                rune = r[1]
                if isinstance(rune, str):
                    uses.add(rune)
                    runenames.add(rune)
                elif rune[0].lower() == "cons":
                    uses.add(rune[2][1])
                    runenames.add(rune[2][1])
                elif not rune[0].startswith(":FAKE-RUNE-"):
                    uses.add(rune[1])
                    runenames.add(rune[1])
        else:
            i += 1
    summary['uses'] = list(uses)
    summary['runenames'] = list(runenames)

    enable = set()
    disable = set()
    i = 3
    while i < len(thm):
        if thm[i].lower() == ":hints":
            hints = thm[i+1]
            for hint in hints:
                for j in range(1, len(hint), 2):
                    if not isinstance(hint[j], str):
                        # print("Suspicious string hint", hint[j])
                        continue
                    if hint[j].lower() == ":in-theory":
                        theory = hint[j+1]
                        if recognize_command(pkg, theory, "enable", 2):
                            for rune in theory[1:]:
                                if isinstance(rune, str):
                                    enable.add(rune)
                                elif len(rune) == 1:
                                    enable.add(rune[0])
                                else:
                                    enable.add(rune[1])
                        elif recognize_command(pkg, theory, "disable", 2):
                            for rune in theory[1:]:
                                if isinstance(rune, str):
                                    disable.add(rune)
                                elif len(rune) == 1:
                                    disable.add(rune[0])
                                else:
                                    disable.add(rune[1])
                        elif recognize_command(pkg, theory, "e/d", 3):
                            if isinstance(theory[1], list):
                                for rune in theory[1]:
                                    if isinstance(rune, str):
                                        enable.add(rune)
                                    elif len(rune) == 1:
                                        enable.add(rune[0])
                                    else:
                                        enable.add(rune[1])
                            if isinstance(theory[2], list):
                                for rune in theory[2]:
                                    if isinstance(rune, str):
                                        disable.add(rune)
                                    elif len(rune) == 1:
                                        disable.add(rune[0])
                                    else:
                                        disable.add(rune[1])

        break
    summary['enable'] = list(enable)
    summary['disable'] = list(disable)

    return summary

def parse_file(fname):
    if os.path.isdir(fname):
        print(">>>", fname)
        for filename in sorted(os.listdir(fname)):
            if filename.startswith('.'):
                continue
            f = os.path.join(fname, filename)
            parse_file(f)
        return

    if pathlib.Path(fname).suffix != '.lisp':
        return

    fullname = pathlib.Path(os.path.abspath(fname))

    summfile = fullname.with_suffix(".summ")
    if (os.path.exists(summfile)
        and os.path.getmtime(summfile) > os.path.getmtime(fname)):
        return

    print(">", fname)
    response = bridge.acl2_command(ACL2Command.LISP, "(ld '((defsnapshot from-the-top)))")

    custfile = fullname.with_suffix(".acl2")
    if not custfile.exists():
        custfile = fullname.with_name("cert.acl2")
        if not custfile.exists():
            custfile = fullname.with_name("acl2-customization.lsp")
    if custfile.exists():
        response = bridge.acl2_command(ACL2Command.LISP, f"(ld \"{custfile}\")")

    with open(fname) as f:
        summaries = []
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
            if recognize_command(pkg, tree, "in-package", 2):
                if len(tree[1]) < 3 or tree[1][0] != '"' or tree[1][-1] != '"':
                    raise ValueError("Invalid package name")
                pkg = tree[1][1:-1]
            # response = bridge.acl2_command(ACL2Command.LISP, f"(ld '( {sexp} (@ last-event-data)) :current-package \"{pkg}\")")
            # print("-"*50)
            # print(tree)
            response = bridge.acl2_command(ACL2Command.LISP, f"(ld '( {sexp} ) )")
            # print(json.dumps(response, indent=2))
            if recognize_command(pkg, tree, "defthm", 2) or recognize_command(pkg, tree, "defthmd", 2):
                summaries.append(extract_summary(pkg, tree, response))
    with open(summfile, "w") as f:
        json.dump(summaries, f, indent=2)

if __name__ == "__main__":
    args = sys.argv
    if len(args) == 1:
        args = ["."]
    for fname in args:
        response = bridge.acl2_command(ACL2Command.LISP, "(ld '((defsnapshot from-the-top)))")
        parse_file(fname)
