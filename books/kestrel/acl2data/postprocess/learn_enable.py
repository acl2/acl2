import sys
import random
import os.path
import pathlib
import json
import pandas as pd
from sklearn import tree
from sklearn.tree import DecisionTreeClassifier

def read_summaries(fname):
    if os.path.isdir(fname):
        print(">>>", fname)
        data = []
        for filename in sorted(os.listdir(fname)):
            if filename.startswith('.'):
                continue
            f = os.path.join(fname, filename)
            data.extend(read_summaries(f))
        return data

    if pathlib.Path(fname).suffix != '.summ':
        return []

    print(">", fname)
    with open(fname) as f:
        try:
            data = json.load(f)
            return (data)
        except:
            print ("! Skipping")
            return []

def equals_sans_pkg(pkgname, names):
    n = pkgname.find('::')
    if n >= 0:
        pkgname = pkgname[(n+2):]
    return pkgname.lower() in names

def ignore_fn(fnname):
    if not isinstance(fnname, str):
        print ("Weird Fnname:", fnname)
    n = fnname.find('::')
    if n >= 0:
        fnname = fnname[(n+2):]
    return fnname.lower() in ['implies', 'and', 'or', 'not', 
                              'if', 'iff', 'equal', 'quote', 
                              'mv']

def collect_functions(sexp, fnnames):
    if isinstance(sexp, list) and len(sexp) > 0:
        if equals_sans_pkg(sexp[0], {'quote', "'", "`"}):
            return
        if equals_sans_pkg(sexp[0], {'mv-let'}):
            collect_functions(sexp[-1], fnnames)
            return
        if equals_sans_pkg(sexp[0], {'let', 'let*', 'b*'}):
            bindings = sexp[1]
            for i in range(0, len(bindings)):
                collect_functions(bindings[i][1], fnnames)
            collect_functions(sexp[-1], fnnames)
            return
        if not ignore_fn(sexp[0]):
            if sexp[0] not in fnnames:
                fnnames[sexp[0]] = 0
            fnnames[sexp[0]] += 1
        for i in range(1, len(sexp)):
            collect_functions(sexp[i], fnnames)

if __name__ == "__main__":
    args = sys.argv
    if len(args) == 1:
        args = ["/Users/ruben/Kestrel/acl2/books/kestrel"]
    data = []
    for fname in args:
        data.extend(read_summaries(fname))
    print ("Total records:", len(data))
    all_names = {}
    enabled = set()
    disabled = set()
    training = []
    testing = []
    trainingnames = []
    testingnames = []
    for summ in data:
        try:
            if summ is not None:
                fnnames = {}
                collect_functions (summ['form'], fnnames)
                for name in fnnames:
                    if name not in all_names:
                        all_names[name] = len(all_names)
                row = {}
                row['symbols'] = [-1] * len(all_names)
                for name in fnnames:
                    row['symbols'][all_names[name]] = 1
                row['enable']  = summ['enable']
                row['disable'] = summ['disable']
                if random.random() < 0.9:
                    training.append(row)
                    trainingnames.append(summ['name'])
                else:
                    testing.append(row)
                    testingnames.append(summ['name'])
                enabled = enabled.union(row['enable'])
                disabled = disabled.union(row['disable'])
        except:
            print ("Can't find names in", summ['form'])
            raise ValueError("badf input")
    # for item in sorted(fnnames.items(), key=lambda item: -item[1])[:20]:
    #   print(item)

    print(len(enabled))
    print(len(disabled))

    dfdata = {}
    for name in all_names:
        col = []
        for row in training:
            if len(row['symbols']) <= all_names[name]:
                col.append(-1)
            else:
                col.append(row['symbols'][all_names[name]])
        dfdata[name] = col
    df = pd.DataFrame(dfdata)
    df.index = trainingnames
    print (df.head())

    dfdata = {}
    for name in all_names:
        col = []
        for row in testing:
            if len(row['symbols']) <= all_names[name]:
                col.append(-1)
            else:
                col.append(row['symbols'][all_names[name]])
        dfdata[name] = col
    df2 = pd.DataFrame(dfdata)
    df2.index = testingnames
    print (df.head())

    dfdata = {}

    cum_right_on = 0
    cum_wrong_on = 0
    cum_right_off = 0
    cum_wrong_off = 0
    for rule in enabled | disabled:
        y = []
        for row in training:
            if rule in row['enable']:
                y.append(1)
            else:
                y.append(-1)
        dtree1 = DecisionTreeClassifier()
        dtree1 = dtree1.fit(df, y)

        y = []
        for row in training:
            if rule in row['disable']:
                y.append(1)
            else:
                y.append(-1)
        dtree2 = DecisionTreeClassifier()
        dtree2 = dtree2.fit(df, y)

        y1 = dtree1.predict(df2)
        y2 = dtree2.predict(df2)
        right = 0
        wrong = 0
        right_on = 0
        wrong_on = 0
        right_off = 0
        wrong_off = 0
        i = 0
        for row in testing:
            result = 0
            if y1[i] > 0:
                if y2[i] < 0:
                    result = 1
            else:
                if y2[i] > 0:
                    result = -1
            if rule in row['enable']:
                if result > 0:
                    right_on += 1
                else:
                    wrong_on += 1
            elif rule in row['disable']:
                if result < 0:
                    right_on += 1
                else:
                    wrong_on += 1
            else:
                if result == 0:
                    right_off += 1
                else:
                    wrong_off += 1
            i += 1
        right = right_on + right_off
        wrong = wrong_on + wrong_off
        cum_right_on += right_on
        cum_wrong_on += wrong_on
        cum_right_off += right_off
        cum_wrong_off += wrong_off
        cum_right = cum_right_on + cum_right_off
        cum_wrong = cum_wrong_on + cum_wrong_off
        if right_on + wrong_on == 0:
            right_on = -1
        if right_off + wrong_off == 0:
            right_off = -1
        line =f"{rule}, "
        line += "ON, " 
        if right_on + wrong_on == 0:
            line += "0, 0, NA, "
        else:
            line += f"{right_on}, {wrong_on}, {100*right_on/(right_on+wrong_on):.2f}, "
        if right_off + wrong_off == 0:
            line += "0, 0, NA, "
        else:
            line += f"{right_off}, {wrong_off}, {100*right_off/(right_off+wrong_off):.2f}, "
        line += f"{right}, {wrong}, {100*right/(right+wrong):.2f}, "
        if cum_right_on + cum_wrong_on == 0:
            line += "0, 0, NA, "
        else:
            line += f"{cum_right_on}, {cum_wrong_on}, {100*cum_right_on/(cum_right_on+cum_wrong_on):.2f}, "
        if cum_right_off + cum_wrong_off == 0:
            line += "0, 0, NA, "
        else:
            line += f"{cum_right_off}, {cum_wrong_off}, {100*cum_right_off/(cum_right_off+cum_wrong_off):.2f}, "
        line += f"{cum_right}, {cum_wrong}, {100*cum_right/(cum_right+cum_wrong):.2f}, "
        print(line)


