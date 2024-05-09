import re

def get_sexpr (pkg, code, i, canon=None, level=0):
    fraction_regex = re.compile("^[-+]?\\d+(/\\d+)?$")
    decimal_regex = re.compile("^([-+]?)(\\d*)\\.(\\d*)$")
    tree = None
    sexp = ""
    i = skip_whitespace(code, i)
    if i >= len(code):
        return "", None, i
    if i+3 < len(code) and code[i] == ':' and code[i+1] == '#' and code[i+3] == '#':
        sexp = code[i:i+4]
        tree = sexp
        i += 4
        return sexp, tree, i
    elif token_letter(code[i]) or code[i] == "\\":
        token = ""
        pkg_index = None
        while i < len(code) and (token_letter(code[i]) or code[i] == "\\"):
            if code[i] == "\\":
                if i+1 < len(code):
                    token += code[i:i+2]
                    i += 2
                else:
                    raise ValueError("Found EOF while processinig escaped character")
            elif code[i] == '|':
                token += code[i]
                i += 1
                while i < len(code) and code[i] != '|':
                    token += code[i]
                    i += 1
                if i < len(code):
                    token += code[i]
                    i += 1
            elif code[i] == ':' and i+1<len(code) and code[i+1] == ':' and pkg_index is not None:
                pkg_index = i
                token += code[i:i+2]
                i += 2
            else:
                token += code[i].upper()
                i += 1
        m = decimal_regex.match(token)
        if m and len(m.group(2) + m.group(3)) > 0:
            token += m.group(1) + m.group(2) + m.group(3) + "/1" + (len(m.group(3)) * "0")
        elif not (fraction_regex.match(token) or token[0] == ':'):
            if pkg_index is not None:
                token = pkg + "::" + token
            if canon is not None:
                token = canon.lookup_symbol(token)
        sexp = token
        tree = token
        return sexp, tree, i
    elif code[i] == "#":
        token = ""
        if i+1<len(code):
            if code[i+1] == '\\':
                token += code[i:i+2]
                i += 2
                if i >= len(code):
                    raise ValueError("Found EOF while processinig #char")
                if alpha_letter(code[i]):
                    while i<len(code) and alpha_letter(code[i]):
                        token += code[i]
                        i += 1
                else:
                    token += code[i]
                    i += 1                    
            elif code[i+1] in ('x', 'X'):
                token += code[i:i+2]
                i += 2
                while i<len(code) and hex_letter(code[i]):
                    token += code[i]
                    i += 1
            elif code[i+1] in ('o', 'O'):
                token += code[i:i+2]
                i += 2
                while i<len(code) and octal_letter(code[i]):
                    token += code[i]
                    i += 1
            elif code[i+1] in ('c', 'C'):
                token += code[i:i+2]
                i += 2
                if i < len(code) and code[i] == '(':
                    token += code[i]
                    i += 1
                    x, child, i = get_sexpr(pkg, code, i, canon, level)
                    if isinstance(child, str) and fraction_regex.match(child):
                        token += x
                        token += " "
                        i = skip_whitespace(code, i)
                        y, child, i = get_sexpr(pkg, code, i, canon, level)
                        if isinstance(child, str) and fraction_regex.match(child):
                            token += y
                            if i < len(code) and code[i] == ')':
                                token += code[i]
                                i += 1
                            else:
                                raise ValueError("Syntax error: Missing ')' in #C(...) expression")
                        else:
                            raise ValueError("Syntax error: Invalid imagpart in #C(...) expression")
                    else:
                        raise ValueError("Syntax error: Invalid realpart in #C(...) expression")
                else:
                    raise ValueError("Syntax error: Missing '(' in #C(...) expression")
            elif i+2 < len(code) and code[i:i+2] == '#(':
                token += code[i:i+2]
                i += 2
                found = False
                nest = 1
                while i < len(code):
                    if code[i] == ')':
                        token += code[i]
                        i += 1
                        nest -= 1
                        if nest == 0:
                            found = True
                            break
                    elif i+1 < len(code) and code[i:i+2] == '#(':
                        token += code[i:i+2]
                        i += 2
                        nest += 1
                    else:
                        token += code[i]
                        i += 1
                if not found:
                    raise ValueError("Syntax error: Unterminated #{...} quoted expression")
            elif i+4 < len(code) and code[i:i+5] == '#{"""':
                token += code[i:i+5]
                i += 5
                found = False
                while i+3 < len(code):
                    if code[i:i+4] == '"""}':
                        token += code[i:i+4]
                        i += 4
                        found = True
                        break
                    token += code[i]
                    i += 1
                if not found:
                    raise ValueError("Syntax error: Unterminated #{...} quoted expression")
            elif token_letter(code[i+1]) or code[i+1]=="'":
                token += code[i]
                i += 1
                if code[i] == "'":
                    token += code[i]
                    i += 1
                while i<len(code) and token_letter(code[i]):
                    token += code[i]
                    i += 1
            else:
                raise ValueError("Syntax error: Unrecognized # expr", code[i:i+200])
        else:
            raise ValueError("Syntax error: # at end of file")
        if token.startswith("#!"):
            return get_sexpr(token[2:].upper(), code, i, canon, level)
        else:
            sexp = token
            tree = token
            return sexp, tree, i
    elif code[i] == '"':
        token = ""
        token += code[i]
        i += 1
        while i < len(code) and code[i] != '"':
            if code[i] == '\\' and i+1 < len(code):
                token += code[i:i+2]
                i += 2
            else:
                token += code[i]
                i += 1
        if i < len(code):
            token += code[i]
            i += 1
        else:
            raise ValueError("Syntax error: Unterminated string starting at", token)
        # print("STRING:", token)
        sexp = token
        tree = token
        return sexp, tree, i
    elif code[i] == '(':
        sexp += '('
        i += 1
        tree = []
        while True:
            token, child, i = get_sexpr(pkg, code, i, canon, level+1)
            if child is None:
                raise ValueError("Syntax error: Unterminated list", sexp, tree)
            if token == ')':
                return sexp+")", tree, i
            # elif token == '.':
            #     print ("Found dotted pair")
            #     if len(tree) == 0:
            #         raise ValueError("Syntax error: Headless cons pair")
            #     i = i + 1
            #     token, child, i = get_sexpr(pkg, code, i, canon, level+1)
            #     print ("Next token: ", token)
            #     if i >= len(code) or token == ')':
            #         raise ValueError("Syntax error: Unterminated cons pair")
            #     sexp += " . " + token
            #     tree.reverse()
            #     for branch in tree:
            #         child = ["cons", branch, child]
            #     tree = child
            #     token, child, i = get_sexpr(pkg, code, i, canon, level+1)
            #     print ("Next next token: ", token)
            #     if token is None:
            #         raise ValueError("Syntax error: Unterminated cons pair")
            #     if token == ')':
            #         return sexp+")", tree, i
            #     raise ValueError("Syntax error: Invalid cons pair")
            else:
                if sexp[-1] == '(':
                    sexp += token
                else:
                    sexp += " " + token
                tree.append(child)
    elif code[i] == ')':
        if level <= 0:
            raise ValueError("Syntax error: Unbalanced right parenthesis")
        token = code[i].upper()
        i += 1
        sexp = token
        tree = token
        return sexp, tree, i        
    elif code[i] in "'`,":
        esc = code[i]
        i += 1
        sexp, child, i = get_sexpr(pkg, code, i, canon, level)
        return esc+sexp, [esc, child], i
    else:
        token = code[i].upper()
        i += 1
        sexp = token
        tree = token
        return sexp, tree, i

def token_letter(letter):
    return (letter in "!$%&*+-./:<=>?@[]^_{}~|" or (letter >= "0" and letter <= "9")
            or (letter >= "a" and letter <= "z") or (letter >= "A" and letter <= "Z"))

def alpha_letter(letter):
    return ((letter >= "a" and letter <= "z") or (letter >= "A" and letter <= "Z"))

def hex_letter(letter):
    return ((letter >= "0" and letter <= "9") 
            or (letter >= "a" and letter <= "f") or (letter >= "A" and letter <= "F"))

def octal_letter(letter):
    return (letter >= "0" and letter <= "7") 

def skip_whitespace (code, i):
    while i < len(code):
        if code[i] == ';':
            i += 1
            while i < len(code) and code[i] != '\n':
                i += 1
        elif i+1 < len(code) and code[i] == '#' and code[i+1] == '|':
            level = 1
            i += 2
            while i+1 < len(code):
                if code[i]=='|' and code[i+1]=='#':
                    level -= 1
                    if level == 0:
                        break
                    i += 2
                elif code[i] == '#' and code[i+1] == '|':
                    level += 1
                    i += 2
                else:
                    i += 1
            if i+1 < len(code):
                i += 2
        elif code[i].isspace():
            i += 1
        else:
            break
    return i

