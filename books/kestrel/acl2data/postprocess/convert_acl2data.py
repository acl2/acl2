import sys
import os.path
import pathlib
import json
import copy
import re
import logging

from parse_acl2 import get_sexpr
import checkpoint_to_clause as ctc
from collect_defpkg import PackageDB
import collect_runes

TEST_CHECKPOINT_TO_CLAUSE = False
TESTS_PASSED = 0
TESTS_MADE = 0

rune_symtab = {}

def is_constant(expr):
    if isinstance(expr, str):
        fraction_regex = re.compile("^[-+]?\\d+(/\\d+)?$")
        if fraction_regex.match(expr):
            return True
        if expr.isnumeric():
            return True
        if expr.endswith("::T") or expr.endswith("::NIL"):
            return True
        if expr.startswith("#") or expr.startswith(":") or expr.startswith("\""):
            return True
    return False

def get_line(content, i):
    if i >= len(content):
        return None, i
    line = ""
    while i < len(content):
        if content[i] == '\n':
            return line, i+1
        line += content[i]
        i = i + 1
    return line, i

def normalize_vars_in_hint(sexpr, names={}):
    if isinstance(sexpr, str):
        return sexpr
    if isinstance(sexpr, list):
        if sexpr[0] == ":INSTANCE":
            seq = [sexpr[0], sexpr[1]]
            for pair in sexpr[2:]:
                seq.append([pair[0], normalize_vars(pair[1], names, "var")])
            return seq
        if sexpr[0] == ":INDUCT":
            seq = [sexpr[0]]
            for item in sexpr[1:]:
                seq.append(normalize_vars(item, names))
            return seq
        seq = []
        for item in sexpr:
            seq.append(normalize_vars_in_hint(item, names))
        return seq
    # logging.error("Unable to understand sexpr: " + str(sexpr))
    raise ValueError("Unable to understand sexpr: " + str(type(sexpr)) + " " + str(sexpr))

def normalize_vars(sexpr, names={}, context=None):
    if isinstance(sexpr, str):
        if context == "var" and not is_constant(sexpr):
            if sexpr not in names:
                names[sexpr] = "var-" + str(len(names))
            return names[sexpr]
        return sexpr
    if isinstance(sexpr, list):
        if len(sexpr) == 0:
            return "ACL2::NIL"
        if len(sexpr) == 2 and sexpr[0] in ("'", "`", ","):
            if context == "'":
                ctx = "'"
            else:
                if context == "`" and sexpr[0] == ",":
                    ctx = None
                else:
                    ctx = sexpr[0]
            return [sexpr[0], normalize_vars(sexpr[1], names, ctx)]
        if context == "'":
            ctx = "'"
        else:
            ctx = None
        seq = [normalize_vars(sexpr[0], names, ctx)]
        if context == "'" or sexpr[0] in ("QUOTE", "ACL2::QUOTE"):
            ctx = "'"
        else:
            ctx = "var"
        for s in sexpr[1:]:
            seq.append(normalize_vars(s, names, ctx))
        return seq
    # logging.error("Unable to understand sexpr: " + str(sexpr))
    raise ValueError("Unable to understand sexpr: " + str(type(sexpr)) + " " + str(sexpr))

def tokenize_sexpr(sexpr):
    if isinstance(sexpr, str):
        return [sexpr]
    if isinstance(sexpr, list):
        if len(sexpr) == 0:
            return ["ACL2::NIL"]
        if len(sexpr) == 2 and sexpr[0] in ("'", "`", ","):
            return [sexpr[0], tokenize_sexpr(sexpr[1])]
        seq = ["("]
        for s in sexpr:
            seq.extend(tokenize_sexpr(s))
        seq.append(")")
        return seq
    # logging.error("Unable to understand sexpr: " + str(sexpr))
    raise ValueError("Unable to understand sexpr: " + str(type(sexpr)) + " " + str(sexpr))

def stringify_sexpr(sexpr):
    if isinstance(sexpr, str):
        return sexpr
    if isinstance(sexpr, list):
        if len(sexpr) == 0:
            return "ACL2::NIL"
        if len(sexpr) == 2 and sexpr[0] in ("'", "`", ","):
            return sexpr[0] + stringify_sexpr(sexpr[1])
        txt = "("
        for s in sexpr:
            if len(txt) > 1:
                txt += " "
            txt += stringify_sexpr(s)
        txt += ")"
        return txt
    # logging.error("Unable to understand sexpr: " + str(sexpr))
    raise ValueError("Unable to understand sexpr: " + str(type(sexpr)) + " " + str(sexpr))
    return str(sexpr)

def add_runes(runes, datum, info, reason):
    for rune in runes:
        if isinstance(rune, str):
            datum['output']['action-obj'] = stringify_sexpr(rune)
            info.append(copy.copy(datum))
        elif len(rune) == 1:
            datum['output']['action-obj'] = stringify_sexpr(rune[0])
            info.append(copy.copy(datum))
        elif len(rune) > 1:
            datum['output']['action-obj'] = stringify_sexpr(rune[1])
            info.append(copy.copy(datum))
        else:
            logging.error("Unable to understand theory hint:" + stringify_sexpr(reason))

def strip_package(symbol):
    if "::" in symbol:
        pkg, raw = symbol.split('::', 1)
        return raw
    return symbol

def _first_diff(term1, term2):
    if term1 == "ABNF::*ALL-CONCRETE-SYNTAX-RULES*" or term2 == "ABNF::*ALL-CONCRETE-SYNTAX-RULES*":
        if term1 != term2:
            return "Something VS ABNF::*ALL-CONCRETE-SYNTAX-RULES*"
        return None
    # if term1 != term2:
    #     return f"\n{json.dumps(term1, indent=2)} VS\n{json.dumps(term1, indent=2)}"
    if isinstance(term1, str):
        if term1 != term2:
            return term1 + " VS " + str(term2)
        return None
    if isinstance(term2, str):
        if term1 != term2:
            return str(term1) + " VS " + term2
        return None
    if len(term1) == 0:
        if term1 != term2:
            return "[] VS" + str(term2)
        return None
    if len(term2) == 0:
        if term1 != term2:
            return str(term2) + "VS []"
        return None
    if term1[0] != term2[0]:
        if isinstance(term1[0], list) or isinstance(term2[0], list):
            return _first_diff(term1[0], term2[0])
        return "[ " + term1[0] + " ... ] VS [ " + term2[0] + " ... ]"
    if len(term1) != len(term2):
        return "LEN: " + json.dumps(term1) + " VS " + json.dumps(term2)
    for t1, t2 in zip(term1, term2):
        if t1 != t2:
            return _first_diff(t1, t2)
    return None

def combine_maps(map1, map2):
    if map1 is None or map1 in ('NIL', 'ACL2::NIL', ':UNAVAILABLE') or len(map1) == 0:
        return map2
    if map2 is None or map2 in ('NIL', 'ACL2::NIL', ':UNAVAILABLE') or len(map2) == 0:
        return map1
    result = copy.copy(map1)
    for item in map2:
        result.append(item)
    return result

def process_failed_proofs(file, event, rune, rule_classes, action, reason, loc, checkpoints, checkpoints_acl2, goal, goal_clauses, mod_event, names, advice=None):
    if checkpoints is None:
        return []
    if checkpoints in ("NIL", "ACL2::NIL"):
        return []
    if not isinstance(checkpoints, list):
        logging.error("List of checkpoints is not a list: " + stringify_sexpr(checkpoints))
        return []
    info = []
    for i in range(len(checkpoints)):
        ck0 = checkpoints[i]
        if isinstance(checkpoints_acl2, list) and len(checkpoints_acl2) > 0:
            ck0_acl2 = checkpoints_acl2[i]
        else:
            ck0_acl2 = []
        if isinstance(ck0, list) and len(ck0)>0:
            if len(ck0) == 1 and ck0[0] in ("<GOAL>", "ACL2::<GOAL>"):
                ck0 = [goal_clauses]
                ck0_acl2 = [goal]
            ck = [normalize_vars(pred, names) for pred in ck0]
            ck_acl2 = normalize_vars(ck0_acl2, names)
            datum = {}
            datum['metadata'] = {}
            datum['metadata']['file'] = file
            datum['metadata']['rune'] = rune
            datum['metadata']['rule-classes'] = rule_classes
            datum['metadata']['goal'] = event
            datum['metadata']['goal-str'] = stringify_sexpr(event)
            datum['metadata']['broken-goal'] = mod_event
            datum['metadata']['broken-goal-str'] = stringify_sexpr(mod_event)
            datum['input'] = {}
            datum['input']['checkpoint-type'] = loc
            datum['input']['checkpoint'] = [stringify_sexpr(pred) for pred in ck]
            datum['input']['checkpoint-acl2'] = ck_acl2
            datum['input']['checkpoint-structure'] = ck
            datum['input']['checkpoint-sequence'] = tokenize_sexpr(ck)
            datum['input']['symbol-map'] = names
            datum['output'] = {}
            if advice is not None and advice not in ('NIL', 'ACL2::NIL') and len(advice) > 0:
                for a in advice:
                    datum['input']['symbol-map'] = combine_maps (a[2], datum['input']['symbol-map'])
                    obj = a[1]
                    if a[0] == ':ADD-LIBRARY':
                        obj = a[1][1][1:-1]
                    datum['output']['action'] = f"advice {a[0]} {obj}"
                    datum['output']['action-type'] = a[0]
                    datum['output']['action-obj'] = stringify_sexpr(obj)
                    info.append(copy.copy(datum))
            elif action == ':HYP-ALIST':
                reason = normalize_vars(reason, names)
                datum['input']['symbol-map'] = names
                datum['output']['action'] = f"{action} {stringify_sexpr(reason)}"
                datum['output']['action-type'] = 'add-hyp'
                datum['output']['action-obj'] = stringify_sexpr(reason)
                info.append(copy.copy(datum))
            elif action == ":BOOK-RUNES-ALIST":
                reason = normalize_vars_in_hint(reason, names)
                datum['input']['symbol-map'] = names
                datum['output']['action'] = f"{action} {stringify_sexpr(reason)}"
                datum['output']['action-type'] = 'add-library'
                datum['output']['action-obj'] = reason
                info.append(copy.copy(datum))
            elif action == ":HINT-SETTING-ALIST":
                reason = normalize_vars_in_hint(reason, names)
                datum['input']['symbol-map'] = names
                datum['output']['action'] = f"{action} {stringify_sexpr(reason)}"
                datum['output']['action-type'] = 'add-hint'
                if reason[0] in (':DO-NOT', ':DO-NOT-1'):
                    datum['output']['action-type'] = 'add-do-not-hint'
                    term = reason[1]
                    if isinstance(term, list) and len(term) > 0 and term[0] == "'":
                        term = term[1]
                    if term in ("NIL", "ACL2::NIL"):
                        pass
                    elif isinstance(term, str):
                        datum['output']['action-obj'] = stringify_sexpr(term)
                        info.append(copy.copy(datum))
                    elif isinstance(term, list):
                        for t in term:
                            datum['output']['action-obj'] = stringify_sexpr(t)
                            info.append(copy.copy(datum))
                    else:
                        logging.error("Unable to understand do-not hint:" + stringify_sexpr(use_hint))
                elif reason[0] == ':NONLINEARP':
                    datum['output']['action-type'] = 'add-nonlinearp-hint'
                    datum['output']['action-obj'] = stringify_sexpr(reason[1])
                    info.append(copy.copy(datum))
                elif reason[0] == ':BY':
                    datum['output']['action-type'] = 'add-by-hint'
                    if isinstance(reason[1], list):
                        if reason[1][0] in (":INSTANCE", ":FUNCTIONAL-INSTANCE"):
                            use_hint = reason[1]
                            if isinstance(use_hint[1], str):
                                datum['output']['action-obj'] = stringify_sexpr(use_hint[1])
                                info.append(copy.copy(datum))
                            elif isinstance(use_hint[1], list) and len(use_hint[1])>0:
                                if use_hint[1][0] in (":INSTANCE", ":FUNCTIONAL-INSTANCE"):
                                    datum['output']['action-obj'] = stringify_sexpr(use_hint[1][1])
                                    info.append(copy.copy(datum))
                                elif use_hint[1][0] == ':THEOREM':
                                    pass
                                else:
                                    logging.error("Unable to understand by hint:" + stringify_sexpr(use_hint))
                            else:
                                logging.error("Unable to understand by hint:" + stringify_sexpr(use_hint))
                        else:
                            logging.error("Unable to understand by hint:" + stringify_sexpr(use_hint))
                    elif isinstance(reason[1], str):
                        datum['output']['action-obj'] = stringify_sexpr(reason[1])
                        info.append(copy.copy(datum))
                    else:
                        logging.error("Unable to understand by hint:" + stringify_sexpr(reason))
                elif reason[0] in (':USE', ':USE-1'):
                    datum['output']['action-type'] = 'add-use-hint'
                    if isinstance(reason[1], list):
                        if reason[1][0] in (":INSTANCE", ":FUNCTIONAL-INSTANCE"):
                            use_hint = reason[1]
                            if isinstance(use_hint[1], str):
                                datum['output']['action-obj'] = stringify_sexpr(use_hint[1])
                                info.append(copy.copy(datum))
                            elif isinstance(use_hint[1], list) and len(use_hint[1])>0:
                                if use_hint[1][0] in (":INSTANCE", ":FUNCTIONAL-INSTANCE"):
                                    datum['output']['action-obj'] = stringify_sexpr(use_hint[1][1])
                                    info.append(copy.copy(datum))
                                elif use_hint[1][0] == ':THEOREM':
                                    pass
                                else:
                                    logging.error("Unable to understand use hint:" + stringify_sexpr(use_hint))
                            else:
                                logging.error("Unable to understand use hint:" + stringify_sexpr(use_hint))
                        elif reason[1][0] == ':THEOREM':
                            pass
                        else:
                            for use_hint in reason[1]:
                                if isinstance(use_hint, str):
                                    datum['output']['action-obj'] = stringify_sexpr(reason[1])
                                    info.append(copy.copy(datum))
                                elif isinstance(use_hint, list) and len(use_hint)>0 and use_hint[0] in (":INSTANCE", ":FUNCTIONAL-INSTANCE", ":THEOREM"):
                                    if use_hint[0] ==':THEOREM':
                                        pass
                                    elif isinstance(use_hint[1], str):
                                        datum['output']['action-obj'] = stringify_sexpr(use_hint[1])
                                        info.append(copy.copy(datum))
                                    elif isinstance(use_hint[1], list) and len(use_hint[1])>0:
                                        if use_hint[1][0] in (":INSTANCE", ":FUNCTIONAL-INSTANCE"):
                                            datum['output']['action-obj'] = stringify_sexpr(use_hint[1][1])
                                            info.append(copy.copy(datum))
                                        elif use_hint[1][0] == ':THEOREM':
                                            pass
                                        else:
                                            logging.error("Unable to understand use hint:" + stringify_sexpr(use_hint))
                                    else:
                                        logging.error("Unable to understand use hint:" + stringify_sexpr(use_hint))
                                else:
                                    logging.error("Unable to understand use hint:" + stringify_sexpr(use_hint))
                    elif isinstance(reason[1], str):
                        datum['output']['action-obj'] = stringify_sexpr(reason[1])
                        info.append(copy.copy(datum))
                    else:
                        logging.error("Unable to understand use hint:" + stringify_sexpr(reason))
                elif reason[0] in (":EXPAND", ":EXPAND-1"):
                    datum['output']['action-type'] = 'add-expand-hint'
                    terms = reason[1]
                    if terms == ':LAMBDAS':
                        terme = [terms]
                    elif terms in ('NIL', 'ACL2::NIL'):
                        terms = []
                    elif isinstance(terms, list) and len(terms) > 0:
                        if isinstance(terms[0], str) and terms[0] != ':LAMBDAS':
                            terms = [terms]
                        elif isinstance(terms[0], list) and len(terms[0]) > 0 and terms[0][0] in ('LAMBDA', 'ACL2::LAMBDA'):
                            terms = [terms]
                    for term in terms:
                        if isinstance(term, str):
                            datum['output']['action-obj'] = stringify_sexpr(term)
                            info.append(copy.copy(datum))
                        elif isinstance(term, list) and len(reason[1]) > 0:
                            while isinstance(term, list) and term[0] in (':FREE', ':WITH'):
                                term = term[2]
                            if isinstance(term, str):
                                datum['output']['action-obj'] = stringify_sexpr(term)
                                info.append(copy.copy(datum))
                            elif term[0] in ('LET', 'ACL2::LET'):
                                datum['output']['action-obj'] = stringify_sexpr(term)
                                info.append(copy.copy(datum))
                            else:
                                datum['output']['action-obj'] = stringify_sexpr(term[0])
                                info.append(copy.copy(datum))
                        else:
                            logging.error("Unable to understand cases hint:" + stringify_sexpr(reason))
                            continue
                elif reason[0] == ":IN-THEORY":
                    if isinstance(reason[1], list) and len(reason)>0:
                        if reason[1][0] in ("'", "UNION-THEORIES", "ACL2::UNION-THEORIES"):
                            pass
                        elif strip_package(reason[1][0]) in ("ENABLE", "ENABLE*", "ENABLE**"):
                            # datum['output']['action-type'] = 'add-enable-hint'
                            # add_runes(reason[1][1:], datum, info, reason)
                            logging.error("NOT EXPECTING Enable in IN-THEORY:" + stringify_sexpr(reason))
                            pass
                        elif strip_package(reason[1][0]) in ("DISABLE", "DISABLE*", "DISNABLE**"):
                            # datum['output']['action-type'] = 'add-disable-hint'
                            # add_runes(reason[1][1:], datum, info, reason)
                            logging.error("NOT EXPECTING Disable in IN-THEORY:" + stringify_sexpr(reason))
                            pass
                        elif strip_package(reason[1][0]) in ("E/D", "E/D*", "E/D**"):
                            # if len(reason[1]) > 1 and isinstance(reason[1][1], list):
                            #     datum['output']['action-type'] = 'add-enable-hint'
                            #     add_runes(reason[1][1], datum, info, reason)
                            # if len(reason[1]) > 2 and isinstance(reason[1][2], list):
                            #     datum['output']['action-type'] = 'add-disable-hint'
                            logging.error("NOT EXPECTING Disable in IN-THEORY:" + stringify_sexpr(reason))
                            pass
                        else:
                            logging.error("Unable to understand theory hint:" + stringify_sexpr(reason))
                    elif reason[1] in ("NIL", "ACL2::NIL"):
                        pass
                    else:
                        logging.error("Unable to understand theory hint:" + stringify_sexpr(reason))
                elif reason[0] in (":ENABLE", ":ENABLE*"):
                    datum['output']['action-type'] = 'add-enable-hint'
                    add_runes(reason[1:], datum, info, reason)
                elif reason[0] in (":DISABLE", "DISABLE*"):
                    datum['output']['action-type'] = 'add-disable-hint'
                    add_runes(reason[1:], datum, info, reason)
                elif reason[0] == ":INDUCT":
                    if not (len(reason) == 2 and reason[1] in ("T", 'ACL2::T')):
                        datum['output']['action-type'] = 'add-induct-hint'
                        datum['output']['action-obj'] = '<INDUCTION-SCHEME>'
                        if len(reason) > 1 and isinstance(reason[1],list) and len(reason[1]) > 0:
                            datum['output']['action-obj'] = reason[1][0]
                        else:
                            logging.error("Unable to parse induction hint: " + stringify_sexpr(reason))
                        info.append(copy.copy(datum))
                elif reason[0] == ":CASES":
                    datum['output']['action-type'] = 'add-cases-hint'
                    datum['output']['action-obj'] = stringify_sexpr(reason[1])
                    info.append(copy.copy(datum))
                else:
                    logging.error("Unable to understand hint:" + stringify_sexpr(reason))
            elif action == ":RUNE-ALIST":
                datum['output']['action-type'] = 'use-lemma'
                if isinstance(reason, list) and len(reason)==2:
                    datum['output']['action-obj'] = stringify_sexpr(reason[1])
                else:
                    datum['output']['action-obj'] = stringify_sexpr(reason)
                info.append(copy.copy(datum))
            else:
                logging.error("Unknown action: " + stringify_sexpr(action))
        elif ck0 in ("NIL", "ACL2::NIL"):
            pass
        else:
            logging.error("Checkpoint is not a list: " + stringify_sexpr(ck0))
    return info

def process_sexpr(sexpr):
    global TESTS_PASSED, TESTS_MADE
    info = []
    if not (isinstance(sexpr, list) and len(sexpr)>0):
        logging.error("Invalid acl2data sexpr: " + stringify_sexpr(sexpr))
        return info

    if isinstance(sexpr[0], list) and len(sexpr[0]) == 3 and sexpr[0][0] == ":SYSTEM" and sexpr[0][1] == ".":
        file = "[books]/" + sexpr[0][2][1:-1]
    else:
        file = json.loads(sexpr[0])
        idx = file.index("/books/")
        file = "[books]/" + file[idx+6:]
    # TODO: HACK: Hardcoding the ACL2 Books directory here
    # all_runes = {}
    # slurp_runes(file.replace("[books]", "/Users/ruben/Kestrel/acl2/books"), all_runes)
    for item in sexpr[1:]:
        if not(isinstance(item, list) and len(item)>0):
            logging.error("Invalid item inside acl2data: " + stringify_sexpr(item))
            continue
        rune = item[0]
        names = {}
        goal = None
        goal_clauses = None
        event = None
        rule_classes = None
        used_induction = None
        for section in item[1:]:
            action = None
            if not(isinstance(section, list) and len(section)>0):
                logging.error("Invalid section inside acl2data: " + stringify_sexpr(section))
                continue
            action = section[0]
            if action not in (":GOAL", ":GOAL-CLAUSES", ":EVENT", ":RULE-CLASSES", ":USED-INDUCTION", ":HYP-ALIST", ":HINT-SETTING-ALIST", ":RUNE-ALIST", ":BOOK-RUNES-ALIST", ":SYMBOL-TABLE"):
                logging.error("Invalid action inside acl2data:" + stringify_sexpr(action))
                continue
            if len(section) != 2:
                logging.error("Length of section inside acl2data is not 2: " + stringify_sexpr(section))
                continue
            experiments = section[1]
            if action == ":GOAL":
                goal = experiments
                continue
            if action == ":GOAL-CLAUSES":
                goal_clauses = experiments
                continue
            if action == ":EVENT":
                event = experiments
                continue
            if action == ":RULE-CLASSES":
                rule_classes = experiments
                continue
            if action == ":USED-INDUCTION":
                used_induction = (experiments not in ("NIL", "ACL2::NIL"))
                continue
            if action == ":SYMBOL-TABLE":
                if experiments not in ("NIL", "ACL2::NIL"):
                    global rune_symtab
                    for exp in experiments:
                        if len(exp) == 3:
                            used_rune, dot, location = exp
                        elif len(exp)==4 and exp[1] == ":SYSTEM":
                            used_rune, superlocation, dot, location = exp
                        else:
                            print (rune, exp)
                            used_rune = dot = location = None
                        if used_rune.upper() in ['CONS', 'ACL2::CONS']:
                            used_rune, dot, location = dot, ".", location
                        if dot not in ("ACL2::.", "."):
                            logging.error("Symbol table entry is not dotted pair! " + stringify_sexpr(exp))
                            continue
                        if location.startswith("\""):
                            location =  location[1:-1]
                        if location.startswith("[books]/"):
                            location = "books/" + location[len("[books]/"):]
                        collect_runes.add_rune(used_rune, "ACL2", location, None, "ACL2 Data Extraction", rune_symtab)
                continue
            if experiments in ("NIL", "ACL2::NIL"):
                continue
            if not(isinstance(experiments, list)):
                logging.error("Invalid experiments inside acl2data: " + stringify_sexpr(section))
                continue
            for exp in experiments:
                reason = None
                ck_top = None
                ck_top_acl2 = None
                ck_induction = None
                ck_induction_acl2 = None
                mod_event = event
                advice = None
                if not(isinstance(exp, list) and len(exp)>1):
                    logging.error("Length of item in section inside acl2data is not at least 2: " + action + " " + stringify_sexpr(exp))
                    continue
                if ":REMOVE" in exp:
                    continue # TODO?
                elif ":FAIL" in exp:
                    reason = exp[0]
                    ck_top = [goal_clauses]
                    ck_top_acl2 = [goal]
                elif action == ":HYP-ALIST":
                    if len(exp) != 7:
                        logging.error("Length of item in section inside acl2data is not exactly 7: " + action + " " + stringify_sexpr(exp))
                        continue
                    reason, ck_top, ck_top_acl2, ck_induction, ck_induction_acl2, mod_event, reason2 = exp
                    # if reason != reason2:  NOw we know that reason2 is unstranslated, but reason is translated
                    #     logging.fatal("!!!!!Reason is not the same as reason2!!!!!")
                    #     print (file, rune, action, reason, reason2)
                    #     sys.exit(-1)
                elif action == ":HINT-SETTING-ALIST":
                    if len(exp) != 7:
                        logging.error("Length of item in section inside acl2data is not exactly 6: " + action + " " + stringify_sexpr(exp))
                        continue
                    reason, ck_top, ck_top_acl2, ck_induction, ck_induction_acl2, mod_event, advice = exp
                elif action in (":BOOK-RUNES-ALIST", ":RUNE-ALIST"):
                    if len(exp) != 5:
                        logging.error("Length of item in section inside acl2data is not exactly 5: " + action + " " + stringify_sexpr(exp))
                        continue
                    reason, ck_top, ck_top_acl2, ck_induction, ck_induction_acl2 = exp
                else:
                    logging.fatal ("Do not understand this section type: " + str(action))
                    sys.exit(-2)
                if TEST_CHECKPOINT_TO_CLAUSE:
                    if len(ck_top) > 0 and len(ck_top_acl2) > 0:
                        # print(rune)
                        TESTS_MADE += 1
                        for ck_trans, ck_untrans in zip(ck_top, ck_top_acl2):
                            untranslated_ck_top = ctc.checkpoints_to_clause ([ck_untrans])
                            untranslated_ck_top = untranslated_ck_top[0]
                            if untranslated_ck_top == ck_trans:
                                TESTS_PASSED += 1
                            else:
                                logging.error ("Checkpoint untranslate failed: " + file + " " + rune)
                                if (isinstance(ck_trans, list) and len(ck_trans)>0 and
                                    isinstance(ck_trans[0], list) and len(ck_trans[0])>0 and ck_trans[0][0] in ('IMPLIES', 'ACL2::IMPLIES')):
                                    logging.error ("   IMPLIES in checkpoint")
                                else:
                                    logging.error (_first_diff(ck_trans, untranslated_ck_top))
                                    # logging.error ("-----------")
                                    # logging.error ("ACL2:")
                                    # logging.error (json.dumps(ck_untrans, indent=2))
                                    # logging.error ("Expected:")
                                    # logging.error (json.dumps(ck_trans, indent=2))
                                    # logging.error ("Unstralation:")
                                    # logging.error (json.dumps(untranslated_ck_top, indent=2))
                                    # logging.error ("-----------")
                    continue
                info.extend(process_failed_proofs(file, event, rune, rule_classes, action, reason, "top",       ck_top,       ck_top_acl2,       goal, goal_clauses, mod_event, names))
                info.extend(process_failed_proofs(file, event, rune, rule_classes, action, reason, "induction", ck_induction, ck_induction_acl2, goal, goal_clauses, mod_event, names))
                if advice is not None:
                    info.extend(process_failed_proofs(file, event, rune, rule_classes, action, reason, "top",       ck_top,       ck_top_acl2,       goal, goal_clauses, mod_event, names, advice))
                    info.extend(process_failed_proofs(file, event, rune, rule_classes, action, reason, "induction", ck_induction, ck_induction_acl2, goal, goal_clauses, mod_event, names, advice))
    return info

def process_content(content, db):
    i = 0
    while True:
        line, next_i = get_line(content, i)
        if line is None:
            return []
        if line != "":
            if line[0] == "(":
                _, sexpr, _ = get_sexpr("ACL2", content, i, db)
                return process_sexpr(sexpr)
        i = next_i

def process_file(fname, db):
    if os.path.isdir(fname):
        logging.info(">>> " + fname)
        for filename in sorted(os.listdir(fname)):
            if filename.startswith('.'):
                continue
            f = os.path.join(fname, filename)
            process_file(f, db)
        return

    fullname = pathlib.Path(os.path.abspath(fname))
    mlifile = fullname.with_suffix(".mli")
    # if (os.path.exists(mlifile)
    #     and os.path.getmtime(mlifile) > os.path.getmtime(fname)):
    #     logging.info("skip>> " + fname)
    #     return

    if pathlib.Path(fname).suffix == '.tgz':
        logging.info(">> " + fname)
        info = []
        tar = tarfile.open(fname, "r:gz")
        for member in tar.getmembers():
            if not member.endswith("acl2data.out"):
                continue
            f = tar.extractfile(member)
            if f is not None:
                logging.info("> " + member)
                content = f.read()
                info.extend(process_content(content, db))
        if not TEST_CHECKPOINT_TO_CLAUSE:
            with open(mlifile, "w", encoding='latin-1') as out:
                json.dump(info, out, indent=2)
        return

    if not str(pathlib.Path(fname)).endswith("acl2data.out"):
        return

    logging.info("> " + fname)
    with open(fname, encoding='latin-1') as f:
        content = f.read()
        info = process_content(content, db)
    if not TEST_CHECKPOINT_TO_CLAUSE:
        with open(mlifile, "w", encoding='latin-1') as out:
            json.dump(info, out, indent=2)

if __name__ == "__main__":
    # logging.basicConfig(level=logging.DEBUG, filename='example.log', encoding='utf-8')
    logging.basicConfig(level=logging.DEBUG)

    sys.setrecursionlimit(1500)

    # db = PackageDB("pkgdefs.json")
    db = None

    args = sys.argv
    if len(args) == 1:
        args = ["acl2data"]
    for fname in args:
        process_file(fname, db)
    if TEST_CHECKPOINT_TO_CLAUSE:
        print(f"Tests passed: {TESTS_PASSED}/{TESTS_MADE} {100*TESTS_PASSED/TESTS_MADE:.2f}%")
    else:
        with open("runes-acl2data.json", "w", encoding='utf-8') as out:
            json.dump(rune_symtab, out, indent=2)
