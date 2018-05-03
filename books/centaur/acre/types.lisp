; Centaur regular expression library
; Copyright (C) 2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACRE")

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)


(defxdoc acre
  :parents (acl2::projects)
  :short "ACL2 Centaur Regular Expressions"
  :long
   #{"""<p>ACRE is a regular expression package with features somewhat similar
to Perl's regular expressions.</p>

<p>Important note for writing regular expressions: the Common Lisp string
reader treats backslashes as escape characters, so all backslashes in the parse
tree below need to be escaped.  A good way to work around this is to use the
@(see acl2::fancy-string-reader) instead of regular double-quoted strings.  For
example, to match a whitespace character (\s in regex syntax) followed by a
backslash (\\ in regex syntax) followed by a double quote, you'd need to enter
the following double-quoted string:</p>
@({
 "\\s\\\\\""
 })
<p>or the following \"fancy string\":</p>
<code>
 #{"""\s\\""""\}
</code>
<p>If you print either of these out as follows, you'll see what the string's actual contents are:</p>
<code>
 (cw "'~s0'~%" "\\s\\\\\"")       (prints '\s\\"')
 (cw "'~s0'~%" #{"""\s\\""""\})    (prints '\s\\"')
</code>
<p>So please either use fancy-strings or else keep in mind that, in regular
double-quoted strings, any backslash in the following grammar must really be
written as two backslashes.  It is best to debug your regular expressions by
printing them out as above to avoid this sort of confusion.</p>

<p>Here is the syntax for parsing regular expressions, and following it are descriptions of their semantics.</p>

@({
 regex = concat
         concat "|" regex              (Disjunction -- match either one)

 concat = ""                           (Empty string -- always matches)
          repeat concat

 repeat = atom
          atom repeatop

 atom = group
        primitive

 group = "(" regex ")"                 (positional capture)
         "(?:" regex ")"               (noncapturing)
         "(?i:" regex ")"              (noncapturing, case insensitive)
         "(?^i:" regex ")"             (noncapturing, case sensitive)
         "(?<" name ">" regex ")"      (named capture)
         "(?=" regex ")"               (zero-length lookahead)
         "(?!" regex ")"               (zero-length lookahead, negated)
         "(?<=" regex ")"              (zero-length lookbehind, constant width)
         "(?<!" regex ")"              (zero-length lookbehind, constant width, negated)

 primitive = non_meta_character        (matches the given character)
             "."                       (matches any character)
             "[" characterset "]"      (matches any character in the class)
             "[^" characterset "]"     (matches any character not in the class)
             "^"                       (matches beginning of string)
             "$"                       (matches end of string)
             backref
             "\" metacharacter         (escape)
             "\" charsetchar           (character set abbreviations)
             "\n"                      (newline)
             "\t"                      (tab)
             "\r"                      (carriage return)
             "\f"                      (form feed)
             "\o" NNN                  (octal character code)
             "\x" NN                   (hexadecimal character code)

 backref = "\" digit                   (matches nth capture group)
           "\g" digit
           "\g{" number "}"            (matches nth capture group -- may be greater than 9)
           "\g{" name "}"              (matches named capture group)
           "\k{" name "}"
           "\k<" name ">"
           "\k'" name "'"

 repeatop = repeatbase 
            repeatbase repeatmod

 repeatbase = "*"                      (0 or more times)
              "+"                      (1 or more times)
              "?"                      (0 or 1 times)
              "{" n "}"                (exactly n times)
              "{" n ",}"               (n or more times)
              "{" n "," m "}"          (minimum n and maximum m times)

 repeatmod = "?"                       (nongreedy)
             "+"                       (nonbacktracking)

 characterset = ""
                cset_elem characterset

 cset_elem = cset_set
             cset_atom "-" cset_atom   (range -- second must have higher char code)
             cset_atom

 cset_set = "\w"                       (word character -- alphanumeric or _)
            "\d"                       (decimal digit)
            "\s"                       (whitespace character)
            "\h"                       (horizontal whitespace character)
            "\v"                       (vertical whitespace character)

 cset_atom =  non_cset_metacharacter
              "\\"                     (backslash)
              "\]"                     (close bracket)
              "\-"                     (dash)
              "\n"                     (newline)
              "\t"                     (tab)
              "\r"                     (carriage return)
              "\f"                     (form feed)
              "\o" NNN                 (octal character code)
              "\x" NN                  (hexadecimal character code)
 })

<h3>API</h3>
<p>The following types and functions make up the high-level regular expression API.</p>

<h4>Types</h4>
<ul>
<li>@('regex-p') -- internal representation of regular expression patterns</li>
<li>@('matchresult-p') -- result of matching against a string</li>
</ul>

<h4>Functions</h4>
<ul>

<li>@('(parse pattern :legible t) --> (mv err regex)') -- Pattern is a string;
returns either an error or a regex.  If legible is nonnil (the default), then
the pattern string is preprocessed before parsing in a way that allows patterns
to be written more legibly: the preprocessing step removes non-escaped
whitespace and removes comments consisting of the rest of the line after (and
including) any non-escaped @('#') character.</li>

<li>@('(match-regex regex str :case-insens nil) --> matchresult') -- Matches
the given regex against str, using case insensitive matching if case-insens is
set to nonnil.</li>

<li>@('(parse-and-match-regex pattern str :case-insens nil :legible t) --> (mv
err matchresult)') -- Combines @('parse') and @('match-regex').</li>

<li>@('(match pattern str :case-insens nil :legible t) --> matchresult') --
Macro which parses the given pattern into a regex at macroexpansion time,
expanding to a call of @('match-regex') on the resulting regular expression.
Any parse error becomes an error at macroexpansion time.</li>

<li>@('(matchresult->matchedp matchresult) --> boolean') -- returns T if the
regular expression matched the string and NIL otherwise.</li>

<li>@('(matchresult->matched-substr matchresult) --> substr-if-matched') --
returns the matched substring of the input string if there was a match, else
NIL.</li>

<li>@('(matchresult->captured-substr name matchresult) --> substr-if-matched')
-- returns the substring that was captured by the given capture group, or NIL
if the regex didn't match or the capture group was in part of the regex that
didn't match. (As an example of the latter, consider matching the pattern
"(aa)|bb" against the string "bb".)  @('Name') may be a positive number,
which accesses capture groups by position, or a string, which accesses named
capture groups (names are case sensitive).</li>

<li>@('(matchresult->captured-substr! name matchresult) --> substr') -- Same as
the above, but simply returns the empty string if the above would return
NIL.</li>
</ul>

<h4>@('B*') binders for capture groups</h4>

<ul>

<li>@('((captures binding1 binding2 ...) matchresult)') binds variables to
captured substrings from the given matchresult.  A binding may be simply a
variable, in which case a positional capture group is accessed, or @('(var
name)'), in which case @('var') will be bound to the result of looking up the
named capture group @('name').  If a capture group doesn't exist, the variable
is bound to NIL.  The @('captures!')  binding does the same thing but instead
binds the variable to the empty string if the capture group doesn't exist.</li>

<li>@('((named-captures binding1 binding2 ...) matchresult)') is similar to
@('captures'), differing only when the binding is simply a variable.  Instead
of getting a capture group by position, this looks up the downcase of the name
of the variable.  @('Named-captures!') behaves analogously to
@('captures!').</li>

</ul>
"""})

(defxdoc acre-internals
  :parents (acre)
  :short "Umbrella topic for implementation-level documentation of @(see acre).")


(local (xdoc::set-default-parents acre-internals))

(defmacro lstrfix (x)
  `(mbe :logic (acl2::str-fix ,x) :exec ,x))

(defmacro strlen (x)
  `(length (the string (lstrfix ,x))))



  




(deftypes regex
  (deftagsum regex
    :parents (acre-internals)
    :short "Regular expression object"
    (:exact ((str stringp :rule-classes :type-prescription)))
    (:repeat
     ((pat regex)
      (min natp)
      (max acl2::maybe-natp)))
    (:concat ((lst regexlist)))
    (:disjunct ((lst regexlist)))
    (:charset
     ((chars stringp :rule-classes :type-prescription)
      (negp booleanp :rule-classes :type-prescription)))
    (:start ())   ;; matches empty string at beginning
    (:end   ())   ;; matches empty string at end
    (:group
     ((pat regex)
      (index))) ;; allow named groups
    (:backref
     ((index))) ;; allow named backrefs
    (:reverse-pref ((pat regex))) ;; Reverse the preference order of matches.
    (:no-backtrack ((pat regex))) ;; Throws out all but the most-preferred match.
    (:case-sens ;; Make the subpattern match case-sensitively or insensitively.
     ((pat regex)
      (case-insens booleanp :rule-classes :type-prescription)))
    (:zerolength
     ;; Checks that the pattern matches (or does not match, if negp)
     ;; but doesn't change the point in the string where we're matching.
     ((pat regex)
      (lookback natp :rule-classes :type-prescription :default 0)
      (negp booleanp :rule-classes :type-prescription)))
    :layout :list
    :measure (acl2-count x))

  (deflist regexlist :elt-type regex :true-listp t
    :measure (acl2-count x)))

(defines regex-constant-width
  (define regex-constant-width ((x regex-p))
    :returns (width maybe-natp :rule-classes :type-prescription)
    :measure (regex-count x)
    (regex-case x
      :exact (strlen x.str)
      :repeat (b* ((pat-width (regex-constant-width x.pat))
                   ((when (eql pat-width 0)) 0)
                   ((unless pat-width) nil)
                   ((unless (eql x.min x.max)) nil))
                (* pat-width x.min))
      :concat (concat-constant-width x.lst)
      :disjunct (if (consp x.lst)
                    (disjunct-constant-width x.lst)
                  ;; can't match anything, so any constant will work here :)
                  0)
      :charset 1
      :start 0
      :end 0
      :group (regex-constant-width x.pat)
      :backref nil
      :reverse-pref (regex-constant-width x.pat)
      :no-backtrack (regex-constant-width x.pat)
      :case-sens (regex-constant-width x.pat)
      :zerolength 0))

  (define concat-constant-width ((x regexlist-p))
    :returns (width maybe-natp :rule-classes :type-prescription)
    :measure (regexlist-count x)
    (b* (((when (atom x)) 0)
         (width1 (regex-constant-width (car x)))
         ((unless width1) nil)
         (width2 (concat-constant-width (cdr x)))
         ((unless width2) nil))
      (+ width1 width2)))

  (define disjunct-constant-width ((x regexlist-p))
    :guard (consp x)
    :returns (width maybe-natp :rule-classes :type-prescription)
    :measure (if (consp x)
                 (regexlist-count x)
               (+ 1 (regex-count nil)))
    (b* ((width1 (regex-constant-width (car x)))
         ((unless width1) nil)
         ((when (atom (cdr x))) width1)
         (width2 (disjunct-constant-width (cdr x))))
      (and (eql width1 width2)
           width2)))
  ///
  ;; To do: prove this is correct, i.e. if x has constant width and
  ;; match-regex-rec matches on str at position idx, then all states returned
  ;; have new index idx+width.
  (fty::deffixequiv-mutual regex-constant-width))




(define regex-concat2 ((x regex-p) (y regex-p))
  :returns (res regex-p)
  (regex-case x
    :exact
    (regex-case y
      :exact (regex-exact (concatenate 'string x.str y.str))
      :concat (b* (((when (atom y.lst))
                    (regex-fix x))
                   (y1 (car y.lst)))
                (regex-case y1
                  :exact (regex-concat (cons (regex-exact (concatenate 'string x.str y1.str))
                                             (cdr y.lst)))
                  :otherwise (regex-concat (cons x y.lst))))
      :otherwise (regex-concat (list x y)))
    :otherwise
    (regex-case y
      :exact (if (equal y.str "")
                 (regex-fix x)
               (regex-concat (list x y)))
      :concat (regex-concat (cons x y.lst))
      :otherwise (regex-concat (list x y)))))

(define regex-disjunct2 ((x regex-p) (y regex-p))
  :returns (res regex-p)
  (regex-case y
    :disjunct (regex-disjunct (cons x y.lst))
    :otherwise (regex-disjunct (list x y))))
