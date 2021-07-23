; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

; Matt K. mod for July 2021 modification to remove-guard-holders, which was
; causing parse-exact-when-tree-match to fail.
#!acl2
(defattach-system remove-guard-holders-lamp constant-nil-function-arity-0)

(include-book "parser")

(local (include-book "kestrel/utilities/lists/len-const-theorems" :dir :system))
(local (include-book "kestrel/utilities/lists/primitive-theorems" :dir :system))
(local (include-book "std/typed-lists/nat-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-parser-correctness
  :parents (grammar-parser)
  :short "Correctness theorems for the parser of ABNF grammars."
  :long
  (xdoc::topstring
   (xdoc::p
    "The correctness of the parser consists of two parts:")
   (xdoc::ul
    (xdoc::li
     "Soundness:
      if @(tsee parse-grammar) succeeds,
      it returns a parse tree for the input rooted at @('rulelist'):
      @(def parse-treep-of-parse-grammar)
      That is, the parser recognizes only grammars (i.e. lists of rules).")
    (xdoc::li
     "Completeness:
      for every terminated tree rooted at @('rulelist')
      that satisfies the "
     (xdoc::seetopic "grammar-parser-disambiguating-restrictions"
                     "disambiguating restrictions")
     ", @(tsee parse-grammar) succeeds on the string at the leaves of the tree
      and returns that tree:
      @(def parse-grammar-when-tree-match)
      That is, the parser recognizes all grammars (i.e. lists of rules)
      whose trees satisfy the "
     (xdoc::seetopic "grammar-parser-disambiguating-restrictions"
                     "disambiguating restrictions")
     ".")))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-parser-soundness
  :parents (grammar-parser-correctness)
  :short "Soundness theorems for the parser of ABNF grammars."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @(tsee parse-grammar) succeeds,
     it returns a parse tree for the input rooted at @('rulelist'):")
   (xdoc::@def "parse-treep-of-parse-grammar")
   (xdoc::p
    "This is proved via two sets of theorems
     for the parsing functions out of which @(tsee parse-grammar) is built:")
   (xdoc::ul
    (xdoc::li
     "Input decomposition:
      if parsing succeeds,
      the string at the leaves of the returned tree(s)
      consists of the consumed natural numbers in the input.")
    (xdoc::li
     "Tree matching:
      if parsing succeeds,
      the returned tree(s) match(es) the syntactic entity
      that the parsing function is meant to parse.")))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-parser-input-decomposition
  :parents (grammar-parser-soundness)
  :short "Input decomposition theorems for the parser of ABNF grammars."
  :long
  (xdoc::topstring
   (xdoc::p
    "If parsing succeeds,
     the string at the leaves of the returned tree(s)
     consists of the consumed natural numbers in the input.
     That is,
     @(tsee append)ing the string at the leaves with the remaining input
     yields the original input.
     More precisely, it yields the original input
     fixed according to @(tsee nat-list-fix),
     because the parsing functions fix their input;
     an alternative formulation is to avoid @(tsee nat-list-fix)
     but include the hypothesis that the input satisfies @(tsee nat-listp).")
   (xdoc::p
    "The input decomposition theorem of @(tsee parse-any)
     does not involve trees but makes an analogous statement:
     concatenating the returned natural number with the remaining input
     yields the original input.")
   (xdoc::p
    "The input decomposition proof of each parsing function uses,
     as rewrite rules,
     the input decomposition theorems of the parsing functions called by
     the parsing function whose theorem is being proved.
     The proofs also use the definition of @(tsee tree->string),
     which we enable just before these theorems and disable just after."))
  :order-subtopics t)

; disabled just after the input decomposition theorems:
(in-theory (enable tree->string))

(defrule input-decomposition-of-parse-any
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-any)."
  (b* (((mv error? nat? rest-input) (parse-any input)))
    (implies (not error?)
             (equal (cons nat? rest-input)
                    (nat-list-fix input))))
  :enable parse-any)

(defrule input-decomposition-of-parse-exact
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-exact)."
  (b* (((mv error? tree? rest-input) (parse-exact nat input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-exact
  :use input-decomposition-of-parse-any)

(defrule input-decomposition-of-parse-in-range
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-in-range)."
  (b* (((mv error? tree? rest-input) (parse-in-range min max input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-in-range
  :use input-decomposition-of-parse-any)

(defrule input-decomposition-of-parse-in-either-range
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-in-either-range)."
  (b* (((mv error? tree? rest-input) (parse-in-either-range min1 max1
                                                            min2 max2
                                                            input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-in-either-range)

(defrule input-decomposition-of-parse-*-in-either-range
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-*-in-either-range)."
  (b* (((mv & trees rest-input) (parse-*-in-either-range
                                 min1 max1 min2 max2 input)))
    (equal (append (tree-list->string trees)
                   rest-input)
           (nat-list-fix input)))
  :enable parse-*-in-either-range)

(defrule input-decomposition-of-parse-ichar
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-ichar)."
  (b* (((mv error? tree? rest-input) (parse-ichar char input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-ichar)

(defrule input-decomposition-of-parse-ichars
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-ichars)."
  (b* (((mv error? tree? rest-input) (parse-ichars char1 char2 input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-ichars)

(defrule input-decomposition-of-parse-alpha
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-alpha)."
  (b* (((mv error? tree? rest-input) (parse-alpha input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-alpha)

(defrule input-decomposition-of-parse-bit
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-bit)."
  (b* (((mv error? tree? rest-input) (parse-bit input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-bit)

(defrule input-decomposition-of-parse-cr
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-cr)."
  (b* (((mv error? tree? rest-input) (parse-cr input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-cr)

(defrule input-decomposition-of-parse-digit
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-digit)."
  (b* (((mv error? tree? rest-input) (parse-digit input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-digit)

(defrule input-decomposition-of-parse-dquote
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-dquote)."
  (b* (((mv error? tree? rest-input) (parse-dquote input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-dquote)

(defrule input-decomposition-of-parse-htab
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-htab)."
  (b* (((mv error? tree? rest-input) (parse-htab input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-htab)

(defrule input-decomposition-of-parse-lf
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-lf)."
  (b* (((mv error? tree? rest-input) (parse-lf input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-lf)

(defrule input-decomposition-of-parse-sp
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-sp)."
  (b* (((mv error? tree? rest-input) (parse-sp input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-sp)

(defrule input-decomposition-of-parse-vchar
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-vchar)."
  (b* (((mv error? tree? rest-input) (parse-vchar input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-vchar)

(defrule input-decomposition-of-parse-crlf
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-crlf)."
  (b* (((mv error? tree? rest-input) (parse-crlf input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-crlf)

(defrule input-decomposition-of-parse-hexdig
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-hexdig)."
  (b* (((mv error? tree? rest-input) (parse-hexdig input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-hexdig)

(defrule input-decomposition-of-parse-wsp
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-wsp)."
  (b* (((mv error? tree? rest-input) (parse-wsp input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-wsp)

(defrule input-decomposition-of-parse-prose-val
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-prose-val)."
  (b* (((mv error? tree? rest-input) (parse-prose-val input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-prose-val)

(defrule input-decomposition-of-parse-*bit
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-*bit)."
  (b* (((mv & trees rest-input) (parse-*bit input)))
    (equal (append (tree-list->string trees)
                   rest-input)
           (nat-list-fix input)))
  :enable parse-*bit)

(defrule input-decomposition-of-parse-*digit
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-*digit)."
  (b* (((mv & trees rest-input) (parse-*digit input)))
    (equal (append (tree-list->string trees)
                   rest-input)
           (nat-list-fix input)))
  :enable parse-*digit)

(defrule input-decomposition-of-parse-*hexdig
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-*hexdig)."
  (b* (((mv & trees rest-input) (parse-*hexdig input)))
    (equal (append (tree-list->string trees)
                   rest-input)
           (nat-list-fix input)))
  :enable parse-*hexdig)

(defrule input-decomposition-of-parse-1*bit
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-1*bit)."
  (b* (((mv error? trees rest-input) (parse-1*bit input)))
    (implies (not error?)
             (equal (append (tree-list->string trees)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-1*bit)

(defrule input-decomposition-of-parse-1*digit
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-1*digit)."
  (b* (((mv error? trees rest-input) (parse-1*digit input)))
    (implies (not error?)
             (equal (append (tree-list->string trees)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-1*digit)

(defrule input-decomposition-of-parse-1*hexdig
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-1*hexdig)."
  (b* (((mv error? trees rest-input) (parse-1*hexdig input)))
    (implies (not error?)
             (equal (append (tree-list->string trees)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-1*hexdig)

(defrule input-decomposition-of-parse-dot-1*bit
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-dot-1*bit)."
  (b* (((mv error? tree? rest-input) (parse-dot-1*bit input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-dot-1*bit)

(defrule input-decomposition-of-parse-dot-1*digit
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-dot-1*digit)."
  (b* (((mv error? tree? rest-input) (parse-dot-1*digit input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-dot-1*digit)

(defrule input-decomposition-of-parse-dot-1*hexdig
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-dot-1*hexdig)."
  (b* (((mv error? tree? rest-input) (parse-dot-1*hexdig input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-dot-1*hexdig)

(defrule input-decomposition-of-parse-dash-1*bit
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-dash-1*bit)."
  (b* (((mv error? tree? rest-input) (parse-dash-1*bit input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-dash-1*bit)

(defrule input-decomposition-of-parse-dash-1*digit
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-dash-1*digit)."
  (b* (((mv error? tree? rest-input) (parse-dash-1*digit input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-dash-1*digit)

(defrule input-decomposition-of-parse-dash-1*hexdig
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-dash-1*hexdig)."
  (b* (((mv error? tree? rest-input) (parse-dash-1*hexdig input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-dash-1*hexdig)

(defrule input-decomposition-of-parse-*-dot-1*bit
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-*-dot-1*bit)."
  (b* (((mv & trees rest-input) (parse-*-dot-1*bit input)))
    (equal (append (tree-list->string trees)
                   rest-input)
           (nat-list-fix input)))
  :enable parse-*-dot-1*bit)

(defrule input-decomposition-of-parse-*-dot-1*digit
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-*-dot-1*digit)."
  (b* (((mv & trees rest-input) (parse-*-dot-1*digit input)))
    (equal (append (tree-list->string trees)
                   rest-input)
           (nat-list-fix input)))
  :enable parse-*-dot-1*digit)

(defrule input-decomposition-of-parse-*-dot-1*hexdig
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-*-dot-1*hexdig)."
  (b* (((mv & trees rest-input) (parse-*-dot-1*hexdig input)))
    (equal (append (tree-list->string trees)
                   rest-input)
           (nat-list-fix input)))
  :enable parse-*-dot-1*hexdig)

(defrule input-decomposition-of-parse-1*-dot-1*bit
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-1*-dot-1*bit)."
  (b* (((mv error? trees rest-input) (parse-1*-dot-1*bit input)))
    (implies (not error?)
             (equal (append (tree-list->string trees)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-1*-dot-1*bit)

(defrule input-decomposition-of-parse-1*-dot-1*digit
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-1*-dot-1*digit)."
  (b* (((mv error? trees rest-input) (parse-1*-dot-1*digit input)))
    (implies (not error?)
             (equal (append (tree-list->string trees)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-1*-dot-1*digit)

(defrule input-decomposition-of-parse-1*-dot-1*hexdig
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-1*-dot-1*hexdig)."
  (b* (((mv error? trees rest-input) (parse-1*-dot-1*hexdig input)))
    (implies (not error?)
             (equal (append (tree-list->string trees)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-1*-dot-1*hexdig)

(defrule input-decomposition-of-parse-bin-val-rest
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-bin-val-rest)."
  (b* (((mv & tree rest-input) (parse-bin-val-rest input)))
    (equal (append (tree->string tree)
                   rest-input)
           (nat-list-fix input)))
  :enable parse-bin-val-rest)

(defrule input-decomposition-of-parse-dec-val-rest
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-dec-val-rest)."
  (b* (((mv & tree rest-input) (parse-dec-val-rest input)))
    (equal (append (tree->string tree)
                   rest-input)
           (nat-list-fix input)))
  :enable parse-dec-val-rest)

(defrule input-decomposition-of-parse-hex-val-rest
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-hex-val-rest)."
  (b* (((mv & tree rest-input) (parse-hex-val-rest input)))
    (equal (append (tree->string tree)
                   rest-input)
           (nat-list-fix input)))
  :enable parse-hex-val-rest)

(defrule input-decomposition-of-parse-bin-val
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-bin-val)."
  (b* (((mv error? tree? rest-input) (parse-bin-val input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-bin-val)

(defrule input-decomposition-of-parse-dec-val
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-dec-val)."
  (b* (((mv error? tree? rest-input) (parse-dec-val input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-dec-val)

(defrule input-decomposition-of-parse-hex-val
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-hex-val)."
  (b* (((mv error? tree? rest-input) (parse-hex-val input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-hex-val)

(defrule input-decomposition-of-parse-bin/dec/hex-val
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-bin/dec/hex-val)."
  (b* (((mv error? tree? rest-input) (parse-bin/dec/hex-val input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-bin/dec/hex-val)

(defrule input-decomposition-of-parse-num-val
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-num-val)."
  (b* (((mv error? tree? rest-input) (parse-num-val input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-num-val)

(defrule input-decomposition-of-parse-quoted-string
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-quoted-string)."
  (b* (((mv error? tree? rest-input) (parse-quoted-string input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-quoted-string)

(defrule input-decomposition-of-parse-?%i
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-?%i)."
  (b* (((mv & tree rest-input) (parse-?%i input)))
    (equal (append (tree->string tree)
                   rest-input)
           (nat-list-fix input)))
  :enable parse-?%i)

(defrule input-decomposition-of-parse-case-insensitive-string
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for
          @(tsee parse-case-insensitive-string)."
  (b* (((mv error? tree? rest-input) (parse-case-insensitive-string input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-case-insensitive-string)

(defrule input-decomposition-of-parse-case-sensitive-string
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-case-sensitive-string)."
  (b* (((mv error? tree? rest-input) (parse-case-sensitive-string input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-case-sensitive-string)

(defrule input-decomposition-of-parse-char-val
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-char-val)."
  (b* (((mv error? tree? rest-input) (parse-char-val input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-char-val)

(defrule input-decomposition-of-parse-wsp/vchar
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-wsp/vchar)."
  (b* (((mv error? tree? rest-input) (parse-wsp/vchar input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-wsp/vchar)

(defrule input-decomposition-of-parse-*wsp/vchar
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-*wsp/vchar)."
  (b* (((mv & trees rest-input) (parse-*wsp/vchar input)))
    (equal (append (tree-list->string trees)
                   rest-input)
           (nat-list-fix input)))
  :enable parse-*wsp/vchar)

(defrule input-decomposition-of-parse-comment
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-comment)."
  (b* (((mv error? tree? rest-input) (parse-comment input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-comment)

(defrule input-decomposition-of-parse-cnl
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-cnl)."
  (b* (((mv error? tree? rest-input) (parse-cnl input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-cnl)

(defrule input-decomposition-of-parse-cnl-wsp
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-cnl-wsp)."
  (b* (((mv error? tree? rest-input) (parse-cnl-wsp input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-cnl-wsp)

(defrule input-decomposition-of-parse-cwsp
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-cwsp)."
  (b* (((mv error? tree? rest-input) (parse-cwsp input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-cwsp)

(defrule input-decomposition-of-parse-*cwsp
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-*cwsp)."
  (b* (((mv & trees rest-input) (parse-*cwsp input)))
    (equal (append (tree-list->string trees)
                   rest-input)
           (nat-list-fix input)))
  :enable parse-*cwsp)

(defrule input-decomposition-of-parse-1*cwsp
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-1*cwsp)."
  (b* (((mv error? trees rest-input) (parse-1*cwsp input)))
    (implies (not error?)
             (equal (append (tree-list->string trees)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-1*cwsp)

(defrule input-decomposition-of-parse-*digit-star-*digit
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-*digit-star-*digit)."
  (b* (((mv error? tree? rest-input) (parse-*digit-star-*digit input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-*digit-star-*digit)

(defrule input-decomposition-of-parse-repeat
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-repeat)."
  (b* (((mv error? tree? rest-input) (parse-repeat input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-repeat)

(defrule input-decomposition-of-parse-?repeat
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-?repeat)."
  (b* (((mv & tree rest-input) (parse-?repeat input)))
    (equal (append (tree->string tree)
                   rest-input)
           (nat-list-fix input)))
  :enable parse-?repeat)

(defrule input-decomposition-of-parse-alpha/digit/dash
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-alpha/digit/dash)."
  (b* (((mv error? tree? rest-input) (parse-alpha/digit/dash input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-alpha/digit/dash)

(defrule input-decomposition-of-parse-*-alpha/digit/dash
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-*-alpha/digit/dash)."
  (b* (((mv & trees rest-input) (parse-*-alpha/digit/dash input)))
    (equal (append (tree-list->string trees)
                   rest-input)
           (nat-list-fix input)))
  :enable parse-*-alpha/digit/dash)

(defrule input-decomposition-of-parse-rulename
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-rulename)."
  (b* (((mv error? tree? rest-input) (parse-rulename input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-rulename)

(defsection input-decomposition-of-parse-alt/conc/rep/elem/group/option
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorems for
          @(tsee parse-alternation),
          @(tsee parse-concatenation),
          @(tsee parse-repetition),
          @(tsee parse-element),
          @(tsee parse-group),
          @(tsee parse-option),
          @(tsee parse-alt-rest),
          @(tsee parse-alt-rest-comp),
          @(tsee parse-conc-rest), and
          @(tsee parse-conc-rest-comp)."

  (defthm-parse-alt/conc/rep/elem/group/option-flag

    (defthm input-decomposition-of-parse-alternation
      (b* (((mv error? tree? rest-input) (parse-alternation input)))
        (implies (not error?)
                 (equal (append (tree->string tree?)
                                rest-input)
                        (nat-list-fix input))))
      :flag parse-alternation)

    (defthm input-decomposition-of-parse-concatenation
      (b* (((mv error? tree? rest-input) (parse-concatenation input)))
        (implies (not error?)
                 (equal (append (tree->string tree?)
                                rest-input)
                        (nat-list-fix input))))
      :flag parse-concatenation)

    (defthm input-decomposition-of-parse-repetition
      (b* (((mv error? tree? rest-input) (parse-repetition input)))
        (implies (not error?)
                 (equal (append (tree->string tree?)
                                rest-input)
                        (nat-list-fix input))))
      :flag parse-repetition)

    (defthm input-decomposition-of-parse-element
      (b* (((mv error? tree? rest-input) (parse-element input)))
        (implies (not error?)
                 (equal (append (tree->string tree?)
                                rest-input)
                        (nat-list-fix input))))
      :flag parse-element)

    (defthm input-decomposition-of-parse-group
      (b* (((mv error? tree? rest-input) (parse-group input)))
        (implies (not error?)
                 (equal (append (tree->string tree?)
                                rest-input)
                        (nat-list-fix input))))
      :flag parse-group)

    (defthm input-decomposition-of-parse-option
      (b* (((mv error? tree? rest-input) (parse-option input)))
        (implies (not error?)
                 (equal (append (tree->string tree?)
                                rest-input)
                        (nat-list-fix input))))
      :flag parse-option)

    (defthm input-decomposition-of-parse-alt-rest
      (b* (((mv & trees rest-input) (parse-alt-rest input)))
        (equal (append (tree-list->string trees)
                       rest-input)
               (nat-list-fix input)))
      :flag parse-alt-rest)

    (defthm input-decomposition-of-parse-alt-rest-comp
      (b* (((mv error? tree? rest-input) (parse-alt-rest-comp
                                          input)))
        (implies (not error?)
                 (equal (append (tree->string tree?)
                                rest-input)
                        (nat-list-fix input))))
      :flag parse-alt-rest-comp)

    (defthm input-decomposition-of-parse-conc-rest
      (b* (((mv & trees rest-input) (parse-conc-rest input)))
        (equal (append (tree-list->string trees)
                       rest-input)
               (nat-list-fix input)))
      :flag parse-conc-rest)

    (defthm input-decomposition-of-parse-conc-rest-comp
      (b* (((mv error? tree? rest-input) (parse-conc-rest-comp
                                          input)))
        (implies (not error?)
                 (equal (append (tree->string tree?)
                                rest-input)
                        (nat-list-fix input))))
      :flag parse-conc-rest-comp)

    :hints (("Goal" :in-theory (enable tree->string
                                       parse-alternation
                                       parse-concatenation
                                       parse-repetition
                                       parse-element
                                       parse-group
                                       parse-option
                                       parse-alt-rest
                                       parse-alt-rest-comp
                                       parse-conc-rest
                                       parse-conc-rest-comp)))))

(defrule input-decomposition-of-parse-elements
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-elements)."
  (b* (((mv error? tree? rest-input) (parse-elements input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-elements)

(defrule input-decomposition-of-parse-equal-/-equal-slash
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-equal-/-equal-slash)."
  (b* (((mv error? tree? rest-input) (parse-equal-/-equal-slash input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-equal-/-equal-slash)

(defrule input-decomposition-of-parse-defined-as
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-defined-as)."
  (b* (((mv error? tree? rest-input) (parse-defined-as input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-defined-as)

(defrule input-decomposition-of-parse-rule
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-rule)."
  (b* (((mv error? tree? rest-input) (parse-rule input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-rule)

(defrule input-decomposition-of-parse-*cwsp-cnl
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-*cwsp-cnl)."
  (b* (((mv error? tree? rest-input) (parse-*cwsp-cnl input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-*cwsp-cnl)

(defrule input-decomposition-of-parse-rule-/-*cwsp-cnl
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-rule-/-*cwsp-cnl)."
  (b* (((mv error? tree? rest-input) (parse-rule-/-*cwsp-cnl input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-rule-/-*cwsp-cnl)

(defrule input-decomposition-of-parse-*-rule-/-*cwsp-cnl
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-*-rule-/-*cwsp-cnl)."
  (b* (((mv & trees rest-input) (parse-*-rule-/-*cwsp-cnl input)))
    (equal (append (tree-list->string trees)
                   rest-input)
           (nat-list-fix input)))
  :enable parse-*-rule-/-*cwsp-cnl)

(defrule input-decomposition-of-parse-rulelist
  :parents (grammar-parser-input-decomposition)
  :short "Input decomposition theorem for @(tsee parse-rulelist)."
  (b* (((mv error? tree? rest-input) (parse-rulelist input)))
    (implies (not error?)
             (equal (append (tree->string tree?)
                            rest-input)
                    (nat-list-fix input))))
  :enable parse-rulelist)

; enabled just before the input decomposition theorems:
(in-theory (disable tree->string))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-parser-tree-matching

  :parents (grammar-parser-soundness)

  :short "Tree matching theorems for the parser of ABNF grammars."

  :long

  (xdoc::topstring

   (xdoc::p
    "If parsing succeeds,
     the returned tree(s) match(es) the syntactic entities being parsed.
     For instance, if @(tsee parse-alpha) succeeds,
     the returned tree matches @('ALPHA').")

   (xdoc::p
    "The tree matching proof of each parsing function uses, as rewrite rules,
     the tree matching theorems of the parsing functions called by
     the parsing function whose theorem is being proved.")

   (xdoc::p
    "The tree matching theorems use hypotheses of the form
     @('(equal element ...)') or @('(equal repetition ...)'),
     where @('element') and @('repetition') are variables
     that appear in the theorems' conclusions
     as the second arguments of
     @(tsee tree-match-element-p) and @(tsee tree-list-match-repetition-p),
     and where @('...') are constant terms
     that evaluate to certain elements and repetitions.
     The reason for not substituting these hypotheses in the conclusions
     is so that these theorems can be used as rewrite rules
     when proving the tree matching theorems for the calling parsing functions.
     Consider, for example,
     how the tree matching theorem @(tsee tree-match-of-parse-alpha)
     is used in the proof of @(tsee tree-match-of-parse-alpha/digit/dash):
     the goal")

   (xdoc::codeblock
    "(tree-match-element-p"
    "   ... (!_ (/_ *alpha*) (/_ *digit*) (/_ \"-\")) ...)")

   (xdoc::p
    "simplifies (via the executable counterpart rules) to")

   (xdoc::codeblock
    "(tree-match-element-p"
    "   ... '(:group (((:repetition (:repeat 1 (:finite 1))"
    "                  (:rulename (:rulename \"alpha\"))))"
    "                ((:repetition (:repeat 1 (:finite 1))"
    "                  (:rulename (:rulename \"digit\"))))"
    "                 ((:repetition (:repeat 1 (:finite 1))"
    "                  (:char-val (:insensitive \"-\")))))) ...)")

   (xdoc::p
    "and then reduces to, among others, the subgoal")

   (xdoc::codeblock
    "(tree-match-element-p"
    "   ... '(:rulename (:rulename \"alpha\")) ...)")

   (xdoc::p
    "which would not match
     @('(tree-match-element-p ... (element-rulename *alpha*) ...)')
     if that were the conclusion of @(tsee tree-match-of-parse-alpha).
     We could substitute the fully evaluated quoted constants
     into the conclusions of the tree matching theorems
     (e.g. @(''(:rulename (:rulename \"alpha\"))')
     in @(tsee tree-match-of-parse-alpha)),
     but this would be slightly more inconvenient and less readable,
     especially when the elements are not simple rule elements.")

   (xdoc::p
    "In the tree matching theorems for the mutually recursive parsing functions
     (i.e. @(tsee parse-alternation), @(tsee parse-concatenation), etc.),
     the extra variables @('element') and @('repetition')
     in the @('(equal element ...)') and @('(equal repetition ...)') hypotheses
     would lead to an unprovable induction structure
     because the variables @('element') and @('repetition')
     are the same in the induction hypotheses and conclusions,
     but are equated to different constant terms.
     Thus, we first prove by induction versions of the theorems
     with the equalities substituted in the conclusions
     (i.e., the @('tree-match-...-lemma') and @('tree-list-match-...-lemma')
     theorems),
     and then we prove the desired theorems, with the equality hypotheses.
     The latter are used as rewrite rules in the tree matching proofs
     for the parsing functions that call
     the mutually recursive parsing functions.")

   (xdoc::p
    "The tree matching proofs also use the definitions of
     @(tsee tree->string),
     @(tsee tree-match-element-p),
     @(tsee tree-list-match-repetition-p),
     @(tsee tree-list-match-element-p),
     and @(tsee numrep-match-repeat-range-p).
     We enable these definitions just before the tree matching theorems
     and we disable them just after.
     Since in some theorems
     @(tsee tree-match-element-p) does not get expanded
     in places where it should
     (presumably due to ACL2's heuristics for expanding recursive functions),
     we use explicit @(':expand') hints in those theorems;
     the potential looping due to the mutually recursive grammar rules
     (for @('alternation'), @('concatenation'), etc.) does not happen,
     presumably thanks to the firing of the tree matching rewrite rules
     as soon as they apply.
     There is no direct use of the definitions of
     @(tsee tree-list-list-match-alternation-p) and
     @(tsee tree-list-list-match-concatenation-p)
     because the alternations and concatenations in these theorems
     always have an explicit list structure and thus rewrite rules like
     @(tsee tree-list-list-match-alternation-p-of-cons-alternation) suffice.")

   (xdoc::p
    "For some parsing functions that parse repetitions,
     the tree matching theorems say that the returned trees match
     not only the repetitions (via @(tsee tree-list-match-repetition-p)),
     but also the repeated elements (via @(tsee tree-list-match-element-p)).
     This is because subgoals involving @(tsee tree-list-match-element-p)
     arise in the tree matching theorems
     of the callers of such parsing functions."))

  :order-subtopics t)

; disabled just after the tree matching theorems:
(in-theory (enable tree->string
                   tree-match-element-p
                   tree-list-match-repetition-p
                   tree-list-match-element-p
                   numrep-match-repeat-range-p))

(defrule tree-match-of-parse-exact
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-exact)."
  (b* (((mv error? tree? &) (parse-exact nat input)))
    (implies (and (not error?)
                  (equal element (%. nat)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable (parse-exact
           tree-match-num-val-p
           %.-fn))

(defrule tree-match-of-parse-in-range
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-in-range)."
  (b* (((mv error? tree? &) (parse-in-range min max input)))
    (implies (and (not error?)
                  (equal element (%- min max)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable (parse-in-range
           tree-match-num-val-p
           %-))

(defrule tree-match-of-parse-in-either-range
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-in-either-range)."
  (b* (((mv error? tree? &) (parse-in-either-range min1 max1
                                                   min2 max2
                                                   input)))
    (implies (and (not error?)
                  (equal element (!_ (/_ (%- min1 max1))
                                     (/_ (%- min2 max2)))))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable (parse-in-either-range
           !_-fn
           /_-fn))

(defrule tree-list-match-of-parse-*-in-either-range
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-*-in-either-range)."
  (b* (((mv & trees &) (parse-*-in-either-range min1 max1 min2 max2 input)))
    (implies (equal repetition (*_ (!_ (/_ (%- min1 max1))
                                       (/_ (%- min2 max2)))))
             (tree-list-match-repetition-p trees
                                           repetition
                                           *all-concrete-syntax-rules*)))
  :enable (parse-*-in-either-range
           *_
           !_-fn))

(defrule tree-match-of-parse-ichar
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-ichar)."
  (b* (((mv error? tree? &) (parse-ichar char input)))
    (implies (and (not error?)
                  (equal element (element-char-val
                                  (char-val-insensitive
                                   (implode (list char))))))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable (parse-ichar
           tree-match-char-val-p
           nats-match-insensitive-chars-p
           nat-match-insensitive-char-p))

(defrule tree-match-of-parse-ichars
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-ichars)."
  (b* (((mv error? tree? &) (parse-ichars char1 char2 input)))
    (implies (and (not error?)
                  (equal element (element-char-val
                                  (char-val-insensitive
                                   (implode (list char1 char2))))))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable (parse-ichars
           tree-match-char-val-p
           nats-match-insensitive-chars-p
           nat-match-insensitive-char-p))

(defrule tree-match-of-parse-alpha
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-alpha)."
  (b* (((mv error? tree? &) (parse-alpha input)))
    (implies (and (not error?)
                  (equal element (element-rulename *alpha*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-alpha)

(defrule tree-match-of-parse-bit
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-bit)."
  (b* (((mv error? tree? &) (parse-bit input)))
    (implies (and (not error?)
                  (equal element (element-rulename *bit*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-bit)

(defrule tree-match-of-parse-cr
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-cr)."
  (b* (((mv error? tree? &) (parse-cr input)))
    (implies (and (not error?)
                  (equal element (element-rulename *cr*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-cr)

(defrule tree-match-of-parse-digit
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-digit)."
  (b* (((mv error? tree? &) (parse-digit input)))
    (implies (and (not error?)
                  (equal element (element-rulename *digit*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-digit)

(defrule tree-match-of-parse-dquote
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-dquote)."
  (b* (((mv error? tree? &) (parse-dquote input)))
    (implies (and (not error?)
                  (equal element (element-rulename *dquote*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-dquote)

(defrule tree-match-of-parse-htab
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-htab)."
  (b* (((mv error? tree? &) (parse-htab input)))
    (implies (and (not error?)
                  (equal element (element-rulename *htab*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-htab)

(defrule tree-match-of-parse-lf
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-lf)."
  (b* (((mv error? tree? &) (parse-lf input)))
    (implies (and (not error?)
                  (equal element (element-rulename *lf*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-lf)

(defrule tree-match-of-parse-sp
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-sp)."
  (b* (((mv error? tree? &) (parse-sp input)))
    (implies (and (not error?)
                  (equal element (element-rulename *sp*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-sp)

(defrule tree-match-of-parse-vchar
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-vchar)."
  (b* (((mv error? tree? &) (parse-vchar input)))
    (implies (and (not error?)
                  (equal element (element-rulename *vchar*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-vchar)

(defrule tree-match-of-parse-crlf
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-crlf)."
  (b* (((mv error? tree? &) (parse-crlf input)))
    (implies (and (not error?)
                  (equal element (element-rulename *crlf*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-crlf)

(defrule tree-match-of-parse-hexdig
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-hexdig)."
  (b* (((mv error? tree? &) (parse-hexdig input)))
    (implies (and (not error?)
                  (equal element (element-rulename *hexdig*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-hexdig)

(defrule tree-match-of-parse-wsp
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-wsp)."
  (b* (((mv error? tree? &) (parse-wsp input)))
    (implies (and (not error?)
                  (equal element (element-rulename *wsp*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-wsp)

(defrule tree-match-of-parse-prose-val
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-prose-val)."
  (b* (((mv error? tree? &) (parse-prose-val input)))
    (implies (and (not error?)
                  (equal element (element-rulename *prose-val*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-prose-val)

(defrule tree-list-match-of-parse-*bit
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-*bit)."
  (b* (((mv & trees &) (parse-*bit input)))
    (and (implies (equal repetition (*_ *bit*))
                  (tree-list-match-repetition-p trees
                                                repetition
                                                *all-concrete-syntax-rules*))
         (implies (equal element (element-rulename *bit*))
                  (tree-list-match-element-p trees
                                             element
                                             *all-concrete-syntax-rules*))))
  :enable parse-*bit)

(defrule tree-list-match-of-parse-*digit
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-*digit)."
  (b* (((mv & trees &) (parse-*digit input)))
    (and (implies (equal repetition (*_ *digit*))
                  (tree-list-match-repetition-p trees
                                                repetition
                                                *all-concrete-syntax-rules*))
         (implies (equal element (element-rulename *digit*))
                  (tree-list-match-element-p trees
                                             element
                                             *all-concrete-syntax-rules*))))
  :enable parse-*digit)

(defrule tree-list-match-of-parse-*hexdig
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-*hexdig)."
  (b* (((mv & trees &) (parse-*hexdig input)))
    (and (implies (equal repetition (*_ *hexdig*))
                  (tree-list-match-repetition-p trees
                                                repetition
                                                *all-concrete-syntax-rules*))
         (implies (equal element (element-rulename *hexdig*))
                  (tree-list-match-element-p trees
                                             element
                                             *all-concrete-syntax-rules*))))
  :enable parse-*hexdig)

(defrule tree-list-match-of-parse-1*bit
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-1*bit)."
  (b* (((mv error? trees &) (parse-1*bit input)))
    (implies (and (not error?)
                  (equal repetition (1*_ *bit*)))
             (tree-list-match-repetition-p trees
                                           repetition
                                           *all-concrete-syntax-rules*)))
  :enable parse-1*bit)

(defrule tree-list-match-of-parse-1*digit
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-1*digit)."
  (b* (((mv error? trees &) (parse-1*digit input)))
    (implies (and (not error?)
                  (equal repetition (1*_ *digit*)))
             (tree-list-match-repetition-p trees
                                           repetition
                                           *all-concrete-syntax-rules*)))
  :enable parse-1*digit)

(defrule tree-list-match-of-parse-1*hexdig
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-1*hexdig)."
  (b* (((mv error? trees &) (parse-1*hexdig input)))
    (implies (and (not error?)
                  (equal repetition (1*_ *hexdig*)))
             (tree-list-match-repetition-p trees
                                           repetition
                                           *all-concrete-syntax-rules*)))
  :enable parse-1*hexdig)

(defrule tree-match-of-parse-dot-1*bit
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-dot-1*bit)."
  (b* (((mv error? tree? &) (parse-dot-1*bit input)))
    (implies (and (not error?)
                  (equal element (!_ (/_ "."
                                         (1*_ *bit*)))))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable parse-dot-1*bit)

(defrule tree-match-of-parse-dot-1*digit
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-dot-1*digit)."
  (b* (((mv error? tree? &) (parse-dot-1*digit input)))
    (implies (and (not error?)
                  (equal element (!_ (/_ "."
                                         (1*_ *digit*)))))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable parse-dot-1*digit)

(defrule tree-match-of-parse-dot-1*hexdig
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-dot-1*hexdig)."
  (b* (((mv error? tree? &) (parse-dot-1*hexdig input)))
    (implies (and (not error?)
                  (equal element (!_ (/_ "."
                                         (1*_ *hexdig*)))))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable parse-dot-1*hexdig)

(defrule tree-match-of-parse-dash-1*bit
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-dash-1*bit)."
  (b* (((mv error? tree? &) (parse-dash-1*bit input)))
    (implies (and (not error?)
                  (equal element (!_ (/_ "-"
                                         (1*_ *bit*)))))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable parse-dash-1*bit)

(defrule tree-match-of-parse-dash-1*digit
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-dash-1*digit)."
  (b* (((mv error? tree? &) (parse-dash-1*digit input)))
    (implies (and (not error?)
                  (equal element (!_ (/_ "-"
                                         (1*_ *digit*)))))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable parse-dash-1*digit)

(defrule tree-match-of-parse-dash-1*hexdig
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-dash-1*hexdig)."
  (b* (((mv error? tree? &) (parse-dash-1*hexdig input)))
    (implies (and (not error?)
                  (equal element (!_ (/_ "-"
                                         (1*_ *hexdig*)))))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable parse-dash-1*hexdig)

(defrule tree-list-match-of-parse-*-dot-1*bit
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-*-dot-1*bit)."
  (b* (((mv & trees &) (parse-*-dot-1*bit input)))
    (and (implies (equal repetition (*_ (!_ (/_ "."
                                                (1*_ *bit*)))))
                  (tree-list-match-repetition-p trees
                                                repetition
                                                *all-concrete-syntax-rules*))
         (implies (equal element (!_ (/_ "."
                                         (1*_ *bit*))))
                  (tree-list-match-element-p trees
                                             element
                                             *all-concrete-syntax-rules*))))
  :enable parse-*-dot-1*bit)

(defrule tree-list-match-of-parse-*-dot-1*digit
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-*-dot-1*digit)."
  (b* (((mv & trees &) (parse-*-dot-1*digit input)))
    (and (implies (equal repetition (*_ (!_ (/_ "."
                                                (1*_ *digit*)))))
                  (tree-list-match-repetition-p trees
                                                repetition
                                                *all-concrete-syntax-rules*))
         (implies (equal element (!_ (/_ "."
                                         (1*_ *digit*))))
                  (tree-list-match-element-p trees
                                             element
                                             *all-concrete-syntax-rules*))))
  :enable parse-*-dot-1*digit)

(defrule tree-list-match-of-parse-*-dot-1*hexdig
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-*-dot-1*hexdig)."
  (b* (((mv & trees &) (parse-*-dot-1*hexdig input)))
    (and (implies (equal repetition (*_ (!_ (/_ "."
                                                (1*_ *hexdig*)))))
                  (tree-list-match-repetition-p trees
                                                repetition
                                                *all-concrete-syntax-rules*))
         (implies (equal element (!_ (/_ "."
                                         (1*_ *hexdig*))))
                  (tree-list-match-element-p trees
                                             element
                                             *all-concrete-syntax-rules*))))
  :enable parse-*-dot-1*hexdig)

(defrule tree-list-match-of-parse-1*-dot-1*bit
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-1*-dot-1*bit)."
  (b* (((mv error? trees &) (parse-1*-dot-1*bit input)))
    (implies (and (not error?)
                  (equal repetition (1*_ (!_ (/_ "."
                                                 (1*_ *bit*))))))
             (tree-list-match-repetition-p trees
                                           repetition
                                           *all-concrete-syntax-rules*)))
  :enable parse-1*-dot-1*bit)

(defrule tree-list-match-of-parse-1*-dot-1*digit
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-1*-dot-1*digit)."
  (b* (((mv error? trees &) (parse-1*-dot-1*digit input)))
    (implies (and (not error?)
                  (equal repetition (1*_ (!_ (/_ "."
                                                 (1*_ *digit*))))))
             (tree-list-match-repetition-p trees
                                           repetition
                                           *all-concrete-syntax-rules*)))
  :enable parse-1*-dot-1*digit)

(defrule tree-list-match-of-parse-1*-dot-1*hexdig
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-1*-dot-1*hexdig)."
  (b* (((mv error? trees &) (parse-1*-dot-1*hexdig input)))
    (implies (and (not error?)
                  (equal repetition (1*_ (!_ (/_ "."
                                                 (1*_ *hexdig*))))))
             (tree-list-match-repetition-p trees
                                           repetition
                                           *all-concrete-syntax-rules*)))
  :enable parse-1*-dot-1*hexdig)

(defrule tree-match-of-parse-bin-val-rest
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-bin-val-rest)."
  (b* (((mv & tree &) (parse-bin-val-rest input)))
    (implies (equal element (?_ (/_ (1*_ (!_ (/_ "."
                                                 (1*_ *bit*)))))
                                (/_ (!_ (/_ "-"
                                            (1*_ *bit*))))))
             (tree-match-element-p tree element *all-concrete-syntax-rules*)))
  :enable parse-bin-val-rest)

(defrule tree-match-of-parse-dec-val-rest
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-dec-val-rest)."
  (b* (((mv & tree &) (parse-dec-val-rest input)))
    (implies (equal element (?_ (/_ (1*_ (!_ (/_ "."
                                                 (1*_ *digit*)))))
                                (/_ (!_ (/_ "-"
                                            (1*_ *digit*))))))
             (tree-match-element-p tree element *all-concrete-syntax-rules*)))
  :enable parse-dec-val-rest)

(defrule tree-match-of-parse-hex-val-rest
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-hex-val-rest)."
  (b* (((mv & tree &) (parse-hex-val-rest input)))
    (implies (equal element (?_ (/_ (1*_ (!_ (/_ "."
                                                 (1*_ *hexdig*)))))
                                (/_ (!_ (/_ "-"
                                            (1*_ *hexdig*))))))
             (tree-match-element-p tree element *all-concrete-syntax-rules*)))
  :enable parse-hex-val-rest)

(defrule tree-match-of-parse-bin-val
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-bin-val)."
  (b* (((mv error? tree? &) (parse-bin-val input)))
    (implies (and (not error?)
                  (equal element (element-rulename *bin-val*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-bin-val)

(defrule tree-match-of-parse-dec-val
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-dec-val)."
  (b* (((mv error? tree? &) (parse-dec-val input)))
    (implies (and (not error?)
                  (equal element (element-rulename *dec-val*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-dec-val)

(defrule tree-match-of-parse-hex-val
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-hex-val)."
  (b* (((mv error? tree? &) (parse-hex-val input)))
    (implies (and (not error?)
                  (equal element (element-rulename *hex-val*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-hex-val)

(defrule tree-match-of-parse-bin/dec/hex-val
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-bin/dec/hex-val)."
  (b* (((mv error? tree? &) (parse-bin/dec/hex-val input)))
    (implies (and (not error?)
                  (equal element (!_ (/_ *bin-val*)
                                     (/_ *dec-val*)
                                     (/_ *hex-val*))))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable parse-bin/dec/hex-val)

(defrule tree-match-of-parse-num-val
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-num-val)."
  (b* (((mv error? tree? &) (parse-num-val input)))
    (implies (and (not error?)
                  (equal element (element-rulename *num-val*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-num-val)

(defrule tree-match-of-parse-quoted-string
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-quoted-string)."
  (b* (((mv error? tree? &) (parse-quoted-string input)))
    (implies (and (not error?)
                  (equal element (element-rulename *quoted-string*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-quoted-string)

(defrule tree-match-of-parse-?%i
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-?%i)."
  (b* (((mv & tree &) (parse-?%i input)))
    (implies (equal element (?_ (/_ "%i")))
             (tree-match-element-p tree element *all-concrete-syntax-rules*)))
  :enable parse-?%i)

(defrule tree-match-of-parse-case-insensitive-string
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-case-insensitive-string)."
  (b* (((mv error? tree? &) (parse-case-insensitive-string input)))
    (implies (and (not error?)
                  (equal element
                         (element-rulename *case-insensitive-string*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-case-insensitive-string)

(defrule tree-match-of-parse-case-sensitive-string
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-case-sensitive-string)."
  (b* (((mv error? tree? &) (parse-case-sensitive-string input)))
    (implies (and (not error?)
                  (equal element (element-rulename *case-sensitive-string*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-case-sensitive-string)

(defrule tree-match-of-parse-char-val
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-char-val)."
  (b* (((mv error? tree? &) (parse-char-val input)))
    (implies (and (not error?)
                  (equal element (element-rulename *char-val*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-char-val)

(defrule tree-match-of-parse-wsp/vchar
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-wsp/vchar)."
  (b* (((mv error? tree? &) (parse-wsp/vchar input)))
    (implies (and (not error?)
                  (equal element (!_ (/_ *wsp*)
                                     (/_ *vchar*))))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable parse-wsp/vchar)

(defrule tree-list-match-of-parse-*wsp/vchar
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-*wsp/vchar)."
  (b* (((mv & trees &) (parse-*wsp/vchar input)))
    (implies (equal repetition (*_ (!_ (/_ *wsp*)
                                       (/_ *vchar*))))
             (tree-list-match-repetition-p trees
                                           repetition
                                           *all-concrete-syntax-rules*)))
  :enable parse-*wsp/vchar)

(defrule tree-match-of-parse-comment
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-comment)."
  (b* (((mv error? tree? &) (parse-comment input)))
    (implies (and (not error?)
                  (equal element (element-rulename *comment*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-comment)

(defrule tree-match-of-parse-cnl
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-cnl)."
  (b* (((mv error? tree? &) (parse-cnl input)))
    (implies (and (not error?)
                  (equal element (element-rulename *c-nl*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-cnl)

(defrule tree-match-of-parse-cnl-wsp
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-cnl-wsp)."
  (b* (((mv error? tree? &) (parse-cnl-wsp input)))
    (implies (and (not error?)
                  (equal element (!_ (/_ *c-nl* *wsp*))))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable parse-cnl-wsp)

(defrule tree-match-of-parse-cwsp
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-cwsp)."
  (b* (((mv error? tree? &) (parse-cwsp input)))
    (implies (and (not error?)
                  (equal element (element-rulename *c-wsp*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-cwsp)

(defrule tree-list-match-of-parse-*cwsp
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-*cwsp)."
  (b* (((mv & trees &) (parse-*cwsp input)))
    (and (implies (equal repetition (*_ *c-wsp*))
                  (tree-list-match-repetition-p trees
                                                repetition
                                                *all-concrete-syntax-rules*))
         (implies (equal element (element-rulename *c-wsp*))
                  (tree-list-match-element-p trees
                                             element
                                             *all-concrete-syntax-rules*))))
  :enable parse-*cwsp)

(defrule tree-list-match-of-parse-1*cwsp
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-1*cwsp)."
  (b* (((mv error? trees &) (parse-1*cwsp input)))
    (implies (and (not error?)
                  (equal repetition (1*_ *c-wsp*)))
             (tree-list-match-repetition-p trees
                                           repetition
                                           *all-concrete-syntax-rules*)))
  :enable parse-1*cwsp)

(defrule tree-match-of-parse-*digit-star-*digit
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-*digit-star-*digit)."
  (b* (((mv error? tree? &) (parse-*digit-star-*digit input)))
    (implies (and (not error?)
                  (equal element (!_ (/_ (*_ *digit*) "*" (*_ *digit*)))))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable parse-*digit-star-*digit)

(defrule tree-match-of-parse-repeat
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-repeat)."
  (b* (((mv error? tree? &) (parse-repeat input)))
    (implies (and (not error?)
                  (equal element (element-rulename *repeat*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-repeat)

(defrule tree-match-of-parse-?repeat
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-?repeat)."
  (b* (((mv & tree &) (parse-?repeat input)))
    (implies (equal element (?_ (/_ *repeat*)))
             (tree-match-element-p tree element *all-concrete-syntax-rules*)))
  :enable parse-?repeat)

(defrule tree-match-of-parse-alpha/digit/dash
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-alpha/digit/dash)."
  (b* (((mv error? tree? &) (parse-alpha/digit/dash input)))
    (implies (and (not error?)
                  (equal element (!_ (/_ *alpha*)
                                     (/_ *digit*)
                                     (/_ "-"))))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable parse-alpha/digit/dash)

(defrule tree-list-match-of-parse-*-alpha/digit/dash
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-*-alpha/digit/dash)."
  (b* (((mv & trees &) (parse-*-alpha/digit/dash input)))
    (implies (equal repetition (*_ (!_ (/_ *alpha*)
                                       (/_ *digit*)
                                       (/_ "-"))))
             (tree-list-match-repetition-p trees
                                           repetition
                                           *all-concrete-syntax-rules*)))
  :enable parse-*-alpha/digit/dash)

(defrule tree-match-of-parse-rulename
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-rulename)."
  (b* (((mv error? tree? &) (parse-rulename input)))
    (implies (and (not error?)
                  (equal element (element-rulename *rulename*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-rulename)

(defsection tree-match-of-parse-alt/conc/rep/elem/group/option
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorems for
          @(tsee parse-alternation),
          @(tsee parse-concatenation),
          @(tsee parse-repetition),
          @(tsee parse-element),
          @(tsee parse-group),
          @(tsee parse-option),
          @(tsee parse-alt-rest),
          @(tsee parse-alt-rest-comp),
          @(tsee parse-conc-rest), and
          @(tsee parse-conc-rest-comp)."

  (defthm-parse-alt/conc/rep/elem/group/option-flag

    (defthmd tree-match-of-parse-alternation-lemma
      (b* (((mv error? tree? &) (parse-alternation input)))
        (implies (not error?)
                 (tree-match-element-p tree?
                                       (element-rulename *alternation*)
                                       *all-concrete-syntax-rules*)))
      :flag parse-alternation)

    (defthmd tree-match-of-parse-concatenation-lemma
      (b* (((mv error? tree? &) (parse-concatenation input)))
        (implies (not error?)
                 (tree-match-element-p tree?
                                       (element-rulename *concatenation*)
                                       *all-concrete-syntax-rules*)))
      :flag parse-concatenation)

    (defthmd tree-match-of-parse-repetition-lemma
      (b* (((mv error? tree? &) (parse-repetition input)))
        (implies (not error?)
                 (tree-match-element-p tree?
                                       (element-rulename *repetition*)
                                       *all-concrete-syntax-rules*)))
      :flag parse-repetition)

    (defthmd tree-match-of-parse-element-lemma
      (b* (((mv error? tree? &) (parse-element input)))
        (implies (not error?)
                 (tree-match-element-p tree?
                                       (element-rulename *element*)
                                       *all-concrete-syntax-rules*)))
      :flag parse-element)

    (defthmd tree-match-of-parse-group-lemma
      (b* (((mv error? tree? &) (parse-group input)))
        (implies (not error?)
                 (tree-match-element-p tree?
                                       (element-rulename *group*)
                                       *all-concrete-syntax-rules*)))
      :flag parse-group)

    (defthmd tree-match-of-parse-option-lemma
      (b* (((mv error? tree? &) (parse-option input)))
        (implies (not error?)
                 (tree-match-element-p tree?
                                       (element-rulename *option*)
                                       *all-concrete-syntax-rules*)))
      :flag parse-option)

    (defthmd tree-list-match-of-parse-alt-rest-lemma
      (b* (((mv & trees &) (parse-alt-rest input)))
        (tree-list-match-repetition-p trees
                                      (*_ (!_ (/_ (*_ *c-wsp*)
                                                  "/"
                                                  (*_ *c-wsp*)
                                                  *concatenation*)))
                                      *all-concrete-syntax-rules*))
      :flag parse-alt-rest)

    (defthmd tree-match-of-parse-alt-rest-comp-lemma
      (b* (((mv error? tree? &) (parse-alt-rest-comp input)))
        (implies (not error?)
                 (tree-match-element-p tree?
                                       (!_ (/_ (*_ *c-wsp*)
                                               "/"
                                               (*_ *c-wsp*)
                                               *concatenation*))
                                       *all-concrete-syntax-rules*)))
      :flag parse-alt-rest-comp)

    (defthmd tree-list-match-of-parse-conc-rest-lemma
      (b* (((mv & trees &) (parse-conc-rest input)))
        (tree-list-match-repetition-p trees
                                      (*_ (!_ (/_ (1*_ *c-wsp*)
                                                  *repetition*)))
                                      *all-concrete-syntax-rules*))
      :flag parse-conc-rest)

    (defthmd tree-match-of-parse-conc-rest-comp-lemma
      (b* (((mv error? tree? &) (parse-conc-rest-comp input)))
        (implies (not error?)
                 (tree-match-element-p tree?
                                       (!_ (/_ (1*_ *c-wsp*)
                                               *repetition*))
                                       *all-concrete-syntax-rules*)))
      :flag parse-conc-rest-comp)

    :hints (("Goal"
             :expand (:free (tree element rules)
                            (tree-match-element-p tree element rules))
             :in-theory (enable parse-alternation
                                parse-concatenation
                                parse-repetition
                                parse-element
                                parse-group
                                parse-option
                                parse-alt-rest
                                parse-alt-rest-comp
                                parse-conc-rest
                                parse-conc-rest-comp))))

  (defrule tree-match-of-parse-alternation
    (b* (((mv error? tree? &) (parse-alternation input)))
      (implies (and (not error?)
                    (equal element (element-rulename *alternation*)))
               (tree-match-element-p tree?
                                     element
                                     *all-concrete-syntax-rules*)))
    :use tree-match-of-parse-alternation-lemma)

  (defrule tree-match-of-parse-concatenation
    (b* (((mv error? tree? &) (parse-concatenation input)))
      (implies (and (not error?)
                    (equal element (element-rulename *concatenation*)))
               (tree-match-element-p tree?
                                     element
                                     *all-concrete-syntax-rules*)))
    :use tree-match-of-parse-concatenation-lemma)

  (defrule tree-match-of-parse-repetition
    (b* (((mv error? tree? &) (parse-repetition input)))
      (implies (and (not error?)
                    (equal element (element-rulename *repetition*)))
               (tree-match-element-p tree?
                                     element
                                     *all-concrete-syntax-rules*)))
    :use tree-match-of-parse-repetition-lemma)

  (defrule tree-match-of-parse-element
    (b* (((mv error? tree? &) (parse-element input)))
      (implies (and (not error?)
                    (equal element (element-rulename *element*)))
               (tree-match-element-p tree?
                                     element
                                     *all-concrete-syntax-rules*)))
    :use tree-match-of-parse-element-lemma)

  (defrule tree-match-of-parse-group
    (b* (((mv error? tree? &) (parse-group input)))
      (implies (and (not error?)
                    (equal element (element-rulename *group*)))
               (tree-match-element-p tree?
                                     element
                                     *all-concrete-syntax-rules*)))
    :use tree-match-of-parse-group-lemma)

  (defrule tree-match-of-parse-option
    (b* (((mv error? tree? &) (parse-option input)))
      (implies (and (not error?)
                    (equal element (element-rulename *option*)))
               (tree-match-element-p tree?
                                     element
                                     *all-concrete-syntax-rules*)))
    :use tree-match-of-parse-option-lemma)

  (defrule tree-list-match-of-parse-alt-rest
    (b* (((mv & trees &) (parse-alt-rest input)))
      (implies (equal repetition (*_ (!_ (/_ (*_ *c-wsp*)
                                             "/"
                                             (*_ *c-wsp*)
                                             *concatenation*))))
               (tree-list-match-repetition-p trees
                                             repetition
                                             *all-concrete-syntax-rules*)))
    :use tree-list-match-of-parse-alt-rest-lemma)

  (defrule tree-match-of-parse-alt-rest-comp
    (b* (((mv error? tree? &) (parse-alt-rest-comp input)))
      (implies (and (not error?)
                    (equal element (!_ (/_ (*_ *c-wsp*)
                                           "/"
                                           (*_ *c-wsp*)
                                           *concatenation*))))
               (tree-match-element-p tree?
                                     element
                                     *all-concrete-syntax-rules*)))
    :use tree-match-of-parse-alt-rest-comp-lemma)

  (defrule tree-list-match-of-parse-conc-rest
    (b* (((mv & trees &) (parse-conc-rest input)))
      (implies (equal repetition (*_ (!_ (/_ (1*_ *c-wsp*)
                                             *repetition*))))
               (tree-list-match-repetition-p trees
                                             repetition
                                             *all-concrete-syntax-rules*)))
    :use tree-list-match-of-parse-conc-rest-lemma)

  (defrule tree-match-of-parse-conc-rest-comp
    (b* (((mv error? tree? &) (parse-conc-rest-comp input)))
      (implies (and (not error?)
                    (equal element (!_ (/_ (1*_ *c-wsp*)
                                           *repetition*))))
               (tree-match-element-p tree?
                                     element
                                     *all-concrete-syntax-rules*)))
    :use tree-match-of-parse-conc-rest-comp-lemma))

(defrule tree-match-of-parse-elements
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-elements)."
  (b* (((mv error? tree? &) (parse-elements input)))
    (implies (and (not error?)
                  (equal element (element-rulename *elements*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-elements)

(defrule tree-match-of-parse-equal-/-equal-slash
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-equal-/-equal-slash)."
  (b* (((mv error? tree? &) (parse-equal-/-equal-slash input)))
    (implies (and (not error?)
                  (equal element (!_ (/_ "=")
                                     (/_ "=/"))))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable parse-equal-/-equal-slash)

(defrule tree-match-of-parse-defined-as
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-defined-as)."
  (b* (((mv error? tree? &) (parse-defined-as input)))
    (implies (and (not error?)
                  (equal element (element-rulename *defined-as*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-defined-as)

(defrule tree-match-of-parse-rule
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-rule)."
  (b* (((mv error? tree? &) (parse-rule input)))
    (implies (and (not error?)
                  (equal element (element-rulename *rule*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable parse-rule)

(defrule tree-match-of-parse-*cwsp-cnl
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-*cwsp-cnl)."
  (b* (((mv error? tree? &) (parse-*cwsp-cnl input)))
    (implies (and (not error?)
                  (equal element (!_ (/_ (*_ *c-wsp*)
                                         *c-nl*))))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable parse-*cwsp-cnl)

(defrule tree-match-of-parse-rule-/-*cwsp-cnl
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-rule-/-*cwsp-cnl)."
  (b* (((mv error? tree? &) (parse-rule-/-*cwsp-cnl input)))
    (implies (and (not error?)
                  (equal element (!_ (/_ *rule*)
                                     (/_ (!_ (/_ (*_ *c-wsp*)
                                                 *c-nl*))))))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :enable parse-rule-/-*cwsp-cnl)

(defrule tree-list-match-of-parse-*-rule-/-*cwsp-cnl
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-*-rule-/-*cwsp-cnl)."
  (b* (((mv & trees &) (parse-*-rule-/-*cwsp-cnl input)))
    (and (implies (equal repetition (*_ (!_ (/_ *rule*)
                                            (/_ (!_ (/_ (*_ *c-wsp*)
                                                        *c-nl*))))))
                  (tree-list-match-repetition-p trees
                                                repetition
                                                *all-concrete-syntax-rules*))
         (implies (equal element (!_ (/_ *rule*)
                                     (/_ (!_ (/_ (*_ *c-wsp*)
                                                 *c-nl*)))))
                  (tree-list-match-element-p trees
                                             element
                                             *all-concrete-syntax-rules*))))
  :enable parse-*-rule-/-*cwsp-cnl)

(defrule tree-match-of-parse-rulelist
  :parents (grammar-parser-tree-matching)
  :short "Tree matching theorem for @(tsee parse-rulelist)."
  (b* (((mv error? tree? &) (parse-rulelist input)))
    (implies (and (not error?)
                  (equal element (element-rulename *rulelist*)))
             (tree-match-element-p tree? element *all-concrete-syntax-rules*)))
  :expand (:free (tree element rules) (tree-match-element-p tree element rules))
  :enable (parse-rulelist))

; enabled just before the tree matching theorems:
(in-theory (disable tree->string
                    tree-match-element-p
                    tree-list-match-repetition-p
                    tree-list-match-element-p
                    numrep-match-repeat-range-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule parse-treep-of-parse-grammar
  :parents (grammar-parser-soundness)
  :short "Top-level soundness theorem of the parser of ABNF grammars."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @(tsee parse-grammar) succeeds,
     it returns a parse tree for the input rooted at @('rulelist').
     This is proved from
     the input decomposition theorem
     and tree matching theorem for @('rulelist'),
     and the fact that @(tsee parse-grammar) fails if there is extra input.")
   (xdoc::p
    "An alternative formulation is to avoid @(tsee nat-list-fix)
     but include the hypothesis that the input satisfies @(tsee nat-listp)."))
  (let ((tree? (parse-grammar nats)))
    (implies tree?
             (parse-treep tree?
                          (nat-list-fix nats)
                          *rulelist*
                          *all-concrete-syntax-rules*)))
  :enable (parse-grammar parse-treep)
  :use (:instance input-decomposition-of-parse-rulelist
                  (input nats)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-parser-disambiguating-restrictions
  :parents (grammar-parser-completeness)
  :short "Restrictions on parse trees that correspond to
          how the parser of ABNF grammars resolves the @('rulelist') ambiguity."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in the documentation of the "
    (xdoc::seetopic "grammar-parser-implementation"
                    "grammar parser implementation")
    ", the @('rulelist') ambiguity is naturally resolved
     by having @(tsee parse-*cwsp) parse as many @('c-wsp')s as possible,
     like the other @('parse-*...') parsing functions.
     This means that the parser generates only parse trees
     whose @('(*c-wsp c-nl)') subtrees of @('rulelist') trees
     do not start with @('WSP')s,
     because such @('WSP')s always go
     under the immediately preceding @('rule') or @('(*c-wsp c-nl)')
     during parsing;
     except that if the @('rulelist') starts with a @('(*c-wsp c-nl)'),
     that subtree may start with @('WSP'),
     since there is no preceding @('rule') or @('(*c-wsp c-nl)').")
   (xdoc::p
    "The following predicates capture these restrictions.
     They characterize the parse trees generated by the parser.
     The completeness of the parser is, necessarily,
     proved relatively to these restrictions."))
  :order-subtopics t)

(define tree-cwsp-restriction-p ((tree treep))
  :guard (and (tree-match-element-p tree
                                    (element-rulename *c-wsp*)
                                    *all-concrete-syntax-rules*)
              (tree-terminatedp tree))
  :returns (yes/no booleanp)
  :parents (grammar-parser-disambiguating-restrictions)
  :short "Restrictions on the first @('c-wsp') subtrees
          of the (non-starting) @('(*c-wsp c-nl)') trees
          generated by the parser."
  :long
  (xdoc::topstring-p
   "In order for a @('(*c-wsp c-nl)') tree not to start with @('WSP'),
    the first @('c-wsp') subtree (if any) of the @('*c-wsp') repetition
    must not match the @('WSP') alternative of the @('c-wsp') rule.")
  (not (tree-match-element-p (car (car (tree-nonleaf->branches tree)))
                             (element-rulename *wsp*)
                             *all-concrete-syntax-rules*))
  :guard-hints (("Goal"
                 :in-theory (enable tree-terminatedp)
                 :expand (:free (element rules)
                                (tree-match-element-p tree element rules))))
  :no-function t)

(define tree-*cwsp-cnl-restriction-p ((tree treep))
  :guard (and (tree-match-element-p tree
                                    (!_ (/_ (*_ *c-wsp*)
                                            *c-nl*))
                                    *all-concrete-syntax-rules*)
              (tree-terminatedp tree))
  :returns (yes/no booleanp)
  :parents (grammar-parser-disambiguating-restrictions)
  :short "Restrictions on the (non-starting) @('(*c-wsp c-nl)') trees
          generated by the parser."
  :long
  (xdoc::topstring-p
   "In order for a @('(*c-wsp c-nl)') tree not to start with @('WSP'),
    either its @('*c-wsp') repetition must be empty
    or its first @('c-wsp') subtree must satisfy
    the restriction captured by @(tsee tree-cwsp-restriction-p).")
  (or (null (car (tree-nonleaf->branches tree)))
      (tree-cwsp-restriction-p (car (car (tree-nonleaf->branches tree)))))
  :guard-hints (("Goal"
                 :in-theory (enable tree-match-element-p
                                    tree-list-match-repetition-p
                                    tree-terminatedp)))
  :no-function t)

(define tree-rule-/-*cwsp-cnl-restriction-p ((tree treep))
  :guard (and (tree-match-element-p tree
                                    (!_ (/_ *rule*)
                                        (/_ (!_ (/_ (*_ *c-wsp*)
                                                    *c-nl*))))
                                    *all-concrete-syntax-rules*)
              (tree-terminatedp tree))
  :returns (yes/no booleanp)
  :parents (grammar-parser-disambiguating-restrictions)
  :short "Restrictions on the (non-starting) @('( rule / (*c-wsp c-nl) )') trees
          generated by the parser."
  :long
  (xdoc::topstring-p
   "This lifts the restriction captured by @(tsee tree-*cwsp-cnl-restriction-p)
    from @('(*c-wsp c-nl)') to @('( rule / (*c-wsp c-nl) )').
    If the alternative is @('rule'), no restriction applies;
    otherwise, @(tsee tree-*cwsp-cnl-restriction-p) applies.")
  (or (tree-match-element-p (car (car (tree-nonleaf->branches tree)))
                            (element-rulename *rule*)
                            *all-concrete-syntax-rules*)
      (tree-*cwsp-cnl-restriction-p (car (car (tree-nonleaf->branches tree)))))
  :guard-hints (("Goal" :in-theory (enable tree-match-element-p
                                           tree-list-match-repetition-p
                                           tree-terminatedp)))
  :no-function t)

(std::deflist tree-list-*-rule-/-*cwsp-cnl-restriction-p (x)
  (tree-rule-/-*cwsp-cnl-restriction-p x)
  :guard (and (tree-listp x)
              (tree-list-match-repetition-p x
                                            (*_ (!_ (/_ *rule*)
                                                    (/_ (!_ (/_ (*_ *c-wsp*)
                                                                *c-nl*)))))
                                            *all-concrete-syntax-rules*)
              (tree-list-terminatedp x))
  :parents (grammar-parser-disambiguating-restrictions)
  :short "Restrictions on the @('*( rule / (*c-wsp c-nl) )') tree lists
          generated by the parser,
          after the starting @('( rule / (*c-wsp c-nl) )')."
  :long
  (xdoc::topstring-p
   "This lifts the restriction
    captured by @(tsee tree-rule-/-*cwsp-cnl-restriction-p)
    from @('( rule / (*c-wsp c-nl) )') to @('*( rule / (*c-wsp c-nl) )').")
  :elementp-of-nil t
  :guard-hints (("Goal" :in-theory (enable tree-list-match-repetition-p
                                           numrep-match-repeat-range-p))))

(define tree-rulelist-restriction-p ((tree treep))
  :guard (and (tree-match-element-p tree
                                    (element-rulename *rulelist*)
                                    *all-concrete-syntax-rules*)
              (tree-terminatedp tree))
  :returns (yes/no booleanp)
  :parents (grammar-parser-disambiguating-restrictions)
  :short "Restrictions on the @('rulelist') trees generated by the parser."
  :long
  (xdoc::topstring-p
   "This lifts the restriction
    captured by @(tsee tree-list-*-rule-/-*cwsp-cnl-restriction-p)
    from @('*( rule / (*c-wsp c-nl) )') to @('rulelist').
    The restriction only applies to the subtrees after the first one.")
  (b* ((subtrees (car (tree-nonleaf->branches tree))))
    (or (not (consp subtrees))
        (tree-list-*-rule-/-*cwsp-cnl-restriction-p (cdr subtrees))))
  :guard-hints (("Goal"
                 :in-theory (enable tree-list-match-repetition-p
                                    numrep-match-repeat-range-p
                                    tree-terminatedp)
                 :expand ((:free (element rules)
                                 (tree-match-element-p tree element rules)))))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-parser-parsing-failure-propagation
  :parents (grammar-parser-completeness)
  :short "Parsing failure propagation theorems
          for the parser of ABNF grammars."
  :long
  (xdoc::topstring
   (xdoc::p
    "If certain parsing functions fail,
     other parsing functions fail as well,
     because the former parse prefixes of the latter.
     In other words, parsing failures ``propagate''.")
   (xdoc::p
    "The parsing failure propagation theorems below state this kind of facts.
     These theorems are used as rewrite rules in the "
    (xdoc::seetopic "grammar-parser-completeness" "completeness theorems")
    " and in the "
    (xdoc::seetopic "grammar-parser-disambiguation"
                    "disambiguation theorems")
    ". The parsing failure propagation theorems are disabled by default;
     they are enabled in the completeness and disambiguation theorems
     that use them."))
  :order-subtopics t)

(defruled fail-dot-1*bit-when-fail-dot
  :parents (grammar-parser-parsing-failure-propagation)
  :short "Parsing failure propagation
          from @('\".\"') to @('(\".\" 1*BIT)')."
  (implies (mv-nth 0 (parse-ichar #\. input))
           (mv-nth 0 (parse-dot-1*bit input)))
  :enable parse-dot-1*bit)

(defruled fail-dot-1*digit-when-fail-dot
  :parents (grammar-parser-parsing-failure-propagation)
  :short "Parsing failure propagation
          from @('\".\"') to @('(\".\" 1*DIGIT)')."
  (implies (mv-nth 0 (parse-ichar #\. input))
           (mv-nth 0 (parse-dot-1*digit input)))
  :enable parse-dot-1*digit)

(defruled fail-dot-1*hexdig-when-fail-dot
  :parents (grammar-parser-parsing-failure-propagation)
  :short "Parsing failure propagation
          from @('\".\"') to @('(\".\" 1*HEXDIG)')."
  (implies (mv-nth 0 (parse-ichar #\. input))
           (mv-nth 0 (parse-dot-1*hexdig input)))
  :enable parse-dot-1*hexdig)

(defruled fail-dash-1*bit-when-fail-dash
  :parents (grammar-parser-parsing-failure-propagation)
  :short "Parsing failure propagation
          from @('\"-\"') to @('(\"-\" 1*BIT)')."
  (implies (mv-nth 0 (parse-ichar #\- input))
           (mv-nth 0 (parse-dash-1*bit input)))
  :enable parse-dash-1*bit)

(defruled fail-dash-1*digit-when-fail-dash
  :parents (grammar-parser-parsing-failure-propagation)
  :short "Parsing failure propagation
          from @('\"-\"') to @('(\"-\" 1*DIGIT)')."
  (implies (mv-nth 0 (parse-ichar #\- input))
           (mv-nth 0 (parse-dash-1*digit input)))
  :enable parse-dash-1*digit)

(defruled fail-dash-1*hexdig-when-fail-dash
  :parents (grammar-parser-parsing-failure-propagation)
  :short "Parsing failure propagation
          from @('\"-\"') to @('(\"-\" 1*HEXDIG)')."
  (implies (mv-nth 0 (parse-ichar #\- input))
           (mv-nth 0 (parse-dash-1*hexdig input)))
  :enable parse-dash-1*hexdig)

(defruled fail-1*-dot-1*bit-when-fail-dot-1*bit
  :parents (grammar-parser-parsing-failure-propagation)
  :short "Parsing failure propagation
          from @('(\".\" 1*BIT)') to @('1*(\".\" 1*BIT)')."
  (implies (mv-nth 0 (parse-dot-1*bit input))
           (mv-nth 0 (parse-1*-dot-1*bit input)))
  :enable parse-1*-dot-1*bit)

(defruled fail-1*-dot-1*digit-when-fail-dot-1*digit
  :parents (grammar-parser-parsing-failure-propagation)
  :short "Parsing failure propagation
          from @('(\".\" 1*DIGIT)') to @('1*(\".\" 1*DIGIT)')."
  (implies (mv-nth 0 (parse-dot-1*digit input))
           (mv-nth 0 (parse-1*-dot-1*digit input)))
  :enable parse-1*-dot-1*digit)

(defruled fail-1*-dot-1*hexdig-when-fail-dot-1*hexdig
  :parents (grammar-parser-parsing-failure-propagation)
  :short "Parsing failure propagation
          from @('(\".\" 1*HEXDIG)') to @('1*(\".\" 1*HEXDIG)')."
  (implies (mv-nth 0 (parse-dot-1*hexdig input))
           (mv-nth 0 (parse-1*-dot-1*hexdig input)))
  :enable parse-1*-dot-1*hexdig)

(defruled fail-repeat-when-fail-digit-and-fail-star
  :parents (grammar-parser-parsing-failure-propagation)
  :short "Parsing failure propagation
          from @('DIGIT') and @('\"*\"') to @('repeat')."
  (implies (and (mv-nth 0 (parse-digit input))
                (mv-nth 0 (parse-ichar #\* input)))
           (mv-nth 0 (parse-repeat input)))
  :enable (parse-repeat
           parse-1*digit
           parse-*digit-star-*digit
           parse-*digit))

(defruled fail-conc-rest-comp-when-fail-cwsp
  :parents (grammar-parser-parsing-failure-propagation)
  :short "Parsing failure propagation
          from @('c-wsp') to @('(1*c-wsp repetition)')."
  (implies (mv-nth 0 (parse-cwsp input))
           (mv-nth 0 (parse-conc-rest-comp input)))
  :enable (parse-conc-rest-comp
           parse-1*cwsp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-parser-constraints-from-parsing

  :parents (grammar-parser-completeness grammar-parser-disambiguation)

  :short "Parsing constraint theorems for the parser of ABNF grammars."

  :long

  (xdoc::topstring

   (xdoc::p
    "If a parsing function succeeds,
     the parsed input must satisfy certain constraints.
     For example, if @(tsee parse-alpha) succeeds,
     the input must be non-empty and start with (the ASCII code of) a letter.
     As another example, if @(tsee parse-comment) succeeds,
     the input must be non-empty
     and start with (the ASCII code of) a semicolon.")

   (xdoc::p
    "The parsing constraint theorems below capture constraints of this kind.")

   (xdoc::h3 "Usage")

   (xdoc::p
    "These theorems are used, together with the "
    (xdoc::seetopic "grammar-parser-constraints-from-tree-matching"
                    "tree matching constraint theorems")
    ", to prove the "
    (xdoc::seetopic "grammar-parser-disambiguation"
                    "disambiguation theorems")
    ",  which in turn are used to prove the "
    (xdoc::seetopic "grammar-parser-completeness"
                    "completeness theorems")
    ".")

   (xdoc::p
    "The parsing constraint theorems have no rule classes.
     They are used in the proofs of the disambiguation theorems
     via @(':use') hints.")

   (xdoc::h3 "Scope")

   (xdoc::p
    "There are parsing constraint theorems
     only for some of the parsing functions:
     just the ones used to prove the disambiguation theorems.
     Furthermore, each parsing constraint theorem only states necessary,
     but generally not sufficient,
     conditions for the success of the corresponding parsing function:
     it states only the constraints used to prove the disambiguation theorems.")

   (xdoc::p
    "Most parsing constraint theorems state constraints
     just on the first natural number of the input (the @(tsee car)),
     because most of the grammar is LL(1);
     these constraints correspond to `first sets'
     in LL(1) parsing theory.
     A few parsing constraint theorems state additional constraints
     on the second natural number of the input (the @(tsee cadr)),
     as needed for the LL(2) portions of the grammar.")

   (xdoc::h3 "Proof Methods")

   (xdoc::p
    "The proof of each parsing constraint theorem
     uses the definition of the corresponding parsing function,
     e.g. @(tsee constraints-from-parse-alpha) uses
     the definition of @(tsee parse-alpha).
     In @(tsee constraints-from-parse-repetition),
     @(tsee parse-repetition) does not get expanded even if it is enabled
     (presumably due to ACL2's heuristics for expanding recursive functions);
     thus, we use an explcit @(':expand') hint in that theorem.")

   (xdoc::p
    "When a parsing function calls another parsing function
     that has a parsing constraint theorem,
     this theorem is used (via a @(':use') hint)
     in the proof of the caller's parsing constraint theorem,
     e.g. @(tsee constraints-from-parse-in-range) is used
     in the proof of @(tsee constraints-from-parse-alpha)
     twice, once for each call of @(tsee parse-in-range) in @(tsee parse-alpha).
     If instead the called parsing function
     does not have a parsing constraint theorem,
     the definition of the called parsing function is enabled
     in the proof of the parsing constraint theorem of the caller,
     e.g. the proof of @(tsee constraints-from-parse-wsp/vchar)
     enables the definition of @(tsee parse-vchar).")

   (xdoc::p
    "Since @(tsee constraints-from-parse-ichar)
     and @(tsee constraints-from-parse-ichars)
     state constraints with @(tsee nat-match-insensitive-char-p),
     and since those two theorems are used in the proofs
     of many other parsing constraint theorems,
     the proofs of the latter theorems
     use the definition @(tsee nat-match-insensitive-char-p).
     To avoid enabling it explicitly in many theorems,
     we enable @(tsee nat-match-insensitive-char-p)
     just before the parsing constraint theorems
     and we disable it just after."))

  :order-subtopics t)

; disabled just after the parsing constraint theorems:
(in-theory (enable nat-match-insensitive-char-p))

(defrule constraints-from-parse-in-range
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-in-range)."
  (implies (not (mv-nth 0 (parse-in-range min max input)))
           (and (<= (nfix min) (nfix (car input)))
                (<= (nfix (car input)) (nfix max))))
  :rule-classes nil
  :enable (parse-in-range
           parse-any))

(defrule constraints-from-parse-in-either-range
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-in-either-range)."
  (implies (not (mv-nth 0 (parse-in-either-range min1 max1 min2 max2 input)))
           (or (and (<= (nfix min1) (nfix (car input)))
                    (<= (nfix (car input)) (nfix max1)))
               (and (<= (nfix min2) (nfix (car input)))
                    (<= (nfix (car input)) (nfix max2)))))
  :rule-classes nil
  :enable parse-in-either-range
  :use ((:instance constraints-from-parse-in-range (min min1) (max max1))
        (:instance constraints-from-parse-in-range (min min2) (max max2))))

(defrule constraints-from-parse-ichar
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-ichar)."
  (implies (not (mv-nth 0 (parse-ichar char input)))
           (nat-match-insensitive-char-p (nfix (car input)) char))
  :rule-classes nil
  :enable (parse-ichar
           parse-any))

(defrule constraints-from-parse-ichars
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-ichars)."
  (implies (not (mv-nth 0 (parse-ichars char1 char2 input)))
           (and (nat-match-insensitive-char-p (nfix (car input)) char1)
                (nat-match-insensitive-char-p (nfix (cadr input)) char2)))
  :rule-classes nil
  :enable (parse-ichars
           parse-any))

(defrule constraints-from-parse-alpha
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-alpha)."
  (implies (not (mv-nth 0 (parse-alpha input)))
           (or (and (<= (char-code #\A) (car input))
                    (<= (car input) (char-code #\Z)))
               (and (<= (char-code #\a) (car input))
                    (<= (car input) (char-code #\z)))))
  :rule-classes nil
  :enable parse-alpha
  :use ((:instance constraints-from-parse-in-range
                   (min (char-code #\A))
                   (max (char-code #\Z)))
        (:instance constraints-from-parse-in-range
                   (min (char-code #\a))
                   (max (char-code #\z)))))

(defrule constraints-from-parse-bit
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-bit)."
  (implies (not (mv-nth 0 (parse-bit input)))
           (member-equal (car input) (chars=>nats '(#\0 #\1))))
  :rule-classes nil
  :enable parse-bit
  :use ((:instance constraints-from-parse-ichar (char #\0))
        (:instance constraints-from-parse-ichar (char #\1))))

(defrule constraints-from-parse-digit
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-digit)."
  (implies (not (mv-nth 0 (parse-digit input)))
           (and (<= (char-code #\0) (nfix (car input)))
                (<= (nfix (car input)) (char-code #\9))))
  :rule-classes nil
  :enable parse-digit
  :use (:instance constraints-from-parse-in-range
                  (min (char-code #\0))
                  (max (char-code #\9))))

(defrule constraints-from-parse-htab
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-htab)."
  (implies (not (mv-nth 0 (parse-htab input)))
           (equal (car input) (char-code #\Tab)))
  :rule-classes nil
  :enable (parse-htab
           parse-exact
           parse-any))

(defrule constraints-from-parse-sp
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-sp)."
  (implies (not (mv-nth 0 (parse-sp input)))
           (equal (car input) (char-code #\Space)))
  :rule-classes nil
  :enable (parse-sp
           parse-exact
           parse-any))

(defrule constraints-from-parse-hexdig
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-hexdig)."
  (implies (not (mv-nth 0 (parse-hexdig input)))
           (or (and (<= (char-code #\0) (car input))
                    (<= (car input) (char-code #\9)))
               (and (<= (char-code #\A) (car input))
                    (<= (car input) (char-code #\F)))
               (and (<= (char-code #\a) (car input))
                    (<= (car input) (char-code #\z)))))
  :rule-classes nil
  :enable parse-hexdig
  :use (constraints-from-parse-digit
        (:instance constraints-from-parse-ichar (char #\A))
        (:instance constraints-from-parse-ichar (char #\B))
        (:instance constraints-from-parse-ichar (char #\C))
        (:instance constraints-from-parse-ichar (char #\D))
        (:instance constraints-from-parse-ichar (char #\E))
        (:instance constraints-from-parse-ichar (char #\F))))

(defrule constraints-from-parse-wsp
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-wsp)."
  (implies (not (mv-nth 0 (parse-wsp input)))
           (member-equal (car input) (chars=>nats '(#\Tab #\Space))))
  :rule-classes nil
  :enable parse-wsp
  :use (constraints-from-parse-sp
        constraints-from-parse-htab))

(defrule constraints-from-parse-bin-val
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-bin-val)."
  (implies (not (mv-nth 0 (parse-bin-val input)))
           (member-equal (car input) (chars=>nats '(#\B #\b))))
  :enable parse-bin-val
  :use (:instance constraints-from-parse-ichar (char #\b)))

(defrule constraints-from-parse-dec-val
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-dec-val)."
  (implies (not (mv-nth 0 (parse-dec-val input)))
           (member-equal (car input) (chars=>nats '(#\D #\d))))
  :enable parse-dec-val
  :use (:instance constraints-from-parse-ichar (char #\d)))

(defrule constraints-from-parse-num-val
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-num-val)."
  (implies (not (mv-nth 0 (parse-num-val input)))
           (equal (car input) (char-code #\%)))
  :rule-classes nil
  :enable parse-num-val
  :use (:instance constraints-from-parse-ichar (char #\%)))

(defrule constraints-from-parse-case-insensitive-string
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-case-insensitive-string)."
  (implies (not (mv-nth 0 (parse-case-insensitive-string input)))
           (or (and (equal (car input) (char-code #\%))
                    (member-equal (cadr input) (chars=>nats '(#\I #\i))))
               (equal (car input) (char-code #\"))))
  :rule-classes nil
  :enable (parse-case-insensitive-string
           parse-?%i
           parse-quoted-string
           parse-dquote
           parse-exact
           parse-any)
  :use (:instance constraints-from-parse-ichars (char1 #\%) (char2 #\i)))

(defrule constraints-from-parse-char-val
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-char-val)."
  (implies (not (mv-nth 0 (parse-char-val input)))
           (or (and (equal (car input) (char-code #\%))
                    (member-equal (cadr input)
                                  (chars=>nats '(#\I #\S #\i #\s))))
               (equal (car input) (char-code #\"))))
  :rule-classes nil
  :enable (parse-char-val
           parse-case-sensitive-string
           parse-quoted-string
           parse-dquote
           parse-exact
           parse-any)
  :use (constraints-from-parse-case-insensitive-string
        (:instance constraints-from-parse-ichars (char1 #\%) (char2 #\s))))

(defrule constraints-from-parse-wsp/vchar
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-wsp/vchar)."
  (implies (not (mv-nth 0 (parse-wsp/vchar input)))
           (or (equal (car input) (char-code #\Tab))
               (and (<= (char-code #\Space) (car input))
                    (<= (car input) (char-code #\~)))))
  :enable (parse-wsp/vchar
           parse-vchar)
  :use (constraints-from-parse-wsp
        (:instance constraints-from-parse-in-range
                   (min (char-code #\!))
                   (max (char-code #\~)))))

(defrule constraints-from-parse-comment
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-comment)."
  (implies (not (mv-nth 0 (parse-comment input)))
           (equal (car input) (char-code #\;)))
  :rule-classes nil
  :enable parse-comment
  :use (:instance constraints-from-parse-ichar (char #\;)))

(defrule constraints-from-parse-cwsp
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-cwsp)."
  (implies (not (mv-nth 0 (parse-cwsp input)))
           (member-equal (car input)
                         (chars=>nats '(#\Tab #\Return #\Space #\;))))
  :rule-classes nil
  :enable (parse-cwsp
           parse-cnl-wsp
           parse-cnl
           parse-crlf
           parse-cr
           parse-exact
           parse-any)
  :use (constraints-from-parse-comment
        constraints-from-parse-wsp))

(defrule constraints-from-parse-1*cwsp
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-1*cwsp)."
  (implies (not (mv-nth 0 (parse-1*cwsp input)))
           (member-equal (car input)
                         (chars=>nats '(#\Tab #\Return #\Space #\;))))
  :rule-classes nil
  :enable parse-1*cwsp
  :use constraints-from-parse-cwsp)

(defrule constraints-from-parse-alpha/digit/dash
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-alpha/digit/dash)."
  (implies (not (mv-nth 0 (parse-alpha/digit/dash input)))
           (or (and (<= (char-code #\A) (car input))
                    (<= (car input) (char-code #\Z)))
               (and (<= (char-code #\a) (car input))
                    (<= (car input) (char-code #\z)))
               (and (<= (char-code #\0) (car input))
                    (<= (car input) (char-code #\9)))
               (equal (car input) (char-code #\-))))
  :rule-classes nil
  :enable parse-alpha/digit/dash
  :use (constraints-from-parse-alpha
        constraints-from-parse-digit
        (:instance constraints-from-parse-ichar (char #\-))))

(defrule constraints-from-parse-rulename
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-rulename)."
  (implies (not (mv-nth 0 (parse-rulename input)))
           (or (and (<= (char-code #\A) (car input))
                    (<= (car input) (char-code #\Z)))
               (and (<= (char-code #\a) (car input))
                    (<= (car input) (char-code #\z)))))
  :rule-classes nil
  :enable parse-rulename
  :use constraints-from-parse-alpha)

(defrule constraints-from-parse-group
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-group)."
  (implies (not (mv-nth 0 (parse-group input)))
           (equal (car input) (char-code #\()))
  :rule-classes nil
  :enable parse-group
  :use (:instance constraints-from-parse-ichar (char #\()))

(defrule constraints-from-parse-option
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-option)."
  (implies (not (mv-nth 0 (parse-option input)))
           (equal (car input) (char-code #\[)))
  :rule-classes nil
  :enable parse-option
  :use (:instance constraints-from-parse-ichar (char #\[)))

(defrule constraints-from-parse-repetition
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-repetition)."
  (implies (not (mv-nth 0 (parse-repetition input)))
           (or (and (<= (char-code #\A) (car input))
                    (<= (car input) (char-code #\Z)))
               (and (<= (char-code #\a) (car input))
                    (<= (car input) (char-code #\z)))
               (and (<= (char-code #\0) (car input))
                    (<= (car input) (char-code #\9)))
               (member-equal (car input)
                             (chars=>nats '(#\" #\% #\( #\* #\< #\[)))))
  :rule-classes nil
  :expand (parse-repetition input)
  :enable (parse-element
           parse-prose-val
           parse-?repeat
           parse-repeat
           parse-1*digit
           parse-*digit-star-*digit
           parse-*digit)
  :use (constraints-from-parse-rulename
        constraints-from-parse-group
        constraints-from-parse-option
        constraints-from-parse-char-val
        constraints-from-parse-num-val
        constraints-from-parse-digit
        (:instance constraints-from-parse-ichar (char #\<))
        (:instance constraints-from-parse-ichar (char #\*))))

(defrule constraints-from-parse-rule
  :parents (grammar-parser-constraints-from-parsing)
  :short "Constraints induced by @(tsee parse-rule)."
  (implies (not (mv-nth 0 (parse-rule input)))
           (or (and (<= (char-code #\A) (car input))
                    (<= (car input) (char-code #\Z)))
               (and (<= (char-code #\a) (car input))
                    (<= (car input) (char-code #\z)))))
  :rule-classes nil
  :enable parse-rule
  :use constraints-from-parse-rulename)

; enabled just before the parsing constraint theorems:
(in-theory (disable nat-match-insensitive-char-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-parser-constraints-from-tree-matching

  :parents (grammar-parser-completeness grammar-parser-disambiguation)

  :short "Tree maching constraint theorems for the parser of ABNF grammars."

  :long

  (xdoc::topstring

   (xdoc::p
    "If a (list of) terminated tree(s) matches a syntactic entity,
     the string at the leaves of the tree(s) must satisfy certain constraints.
     For example, if a terminated tree matches @('CRLF'),
     the string at the leaves of the tree
     must be non-empty and start with a carriage return.")

   (xdoc::p
    "The tree matching constraint theorems below
     capture constraints of this kind.
     While these theorems are not directly related to the parser,
     they are motivated by the parser (see below).")

   (xdoc::h3 "Usage")

   (xdoc::p
    "These theorems are used, together with the "
    (xdoc::seetopic "grammar-parser-constraints-from-parsing"
                    "parsing constraint theorems")
    ", to prove the "
    (xdoc::seetopic "grammar-parser-disambiguation"
                    "disambiguation theorems")
    ", which in turn are used to prove the "
    (xdoc::seetopic "grammar-parser-completeness"
                    "completeness theorems")
    ".")

   (xdoc::p
    "The tree matching constraint theorems have no rule classes.
     They are used in the proofs of the disambiguation theorems
     via @(':use') hints.")

   (xdoc::p
    "Some tree matching constraint theorems are used
     to incrementally prove other tree matching constraint theorems (see below),
     also via @(':use') hints.")

   (xdoc::h3 "Scope")

   (xdoc::p
    "There are tree matching constraint theorems
     only for some syntactic entities:
     just the ones used to prove the disambiguation theorems,
     and to incrementally prove other tree matching constraint theorems.
     Furthermore, each tree matching constraint theorem only states necessary,
     but generally not sufficient,
     conditions for the matching of the corresponding syntactic entity:
     it states only the constraints used to prove the disambiguation theorems
     (and, incrementally, other tree matching constraint theorems).")

   (xdoc::p
    "Most tree matching constraint theorems state constraints
     just on the first natural number of the string at the leaves of the tree(s)
     (the @(tsee car)),
     because most of the grammar is LL(1).
     A few tree matching constraint theorems state additional constraints
     on the second natural number of the string at the leaves of the tree(s)
     (the @(tsee cadr)),
     as needed for the LL(2) portions of the grammar.
     Since the tree matching constraint theorem
     @(tsee constraints-from-tree-match-ichars)
     would have to state constraints
     either on the first natural number
     or on the first and second natural numbers
     depending on the instantiation of @('charstring'),
     for simplicity this theorem states constraints
     on the whole string at the leaves of the tree.")

   (xdoc::h3 "Hypotheses on the Tree(s)")

   (xdoc::p
    "Most tree matching constraint theorems include
     hypotheses saying that the trees are terminated.
     This ensures that the strings at the leaves of the trees
     consist of natural numbers and not rule names,
     since the constraints are stated on natural numbers.")

   (xdoc::p
    "A few tree matching constraint theorems do not need these hypotheses
     because the corresponding syntactic entities can only be matched
     by trees whose (starting) leaves are natural numbers.
     For instance, in @(tsee constraints-from-tree-match-dot-etc.),
     the group @('(\".\" ...)') can only be matched
     by a tree whose first leaf is a natural number,
     upon which the theorem states the constraint.")

   (xdoc::h3 "Hypotheses on the String at the Leaves of the Tree(s)")

   (xdoc::p
    "The tree matching constraint theorems
     whose names end with @('-when-nonempty')
     include hypotheses saying that the string at the leaves is not empty.
     This is because the corresponding syntactic entities may be matched
     by a tree with an empty string at the leaves
     or by an empty list of trees.
     For example,
     in @(tsee constraints-from-tree-match-bin-val-rest-when-nonempty),
     the matching tree may have no subtrees,
     since the syntactic entity in question
     is an option @('[ 1*(\".\" 1*BIT) / (\"-\" 1*BIT) ]').
     As another example,
     in @(tsee constraints-from-tree-list-match-*digit-when-nonempty),
     the matching list of trees may be empty.")

   (xdoc::h3 "Proof Methods")

   (xdoc::p
    "The proof of each tree matching constraint theorem
     expands @(tsee tree-match-element-p)
     or @(tsee tree-list-match-repetition-p)
     (depending on whether the theorem applies to
     a single tree or to a list of trees).
     But most theorems need explicit @(':expand') hints for that:
     just enabling the functions does not suffice
     (presumably due to ACL2's heuristics for expanding recursive functions).")

   (xdoc::p
    "Since many repetitions consist of one element,
     the rewrite rule @(tsee tree-list-match-repetition-p-of-1-repetition)
     is used in many proofs.
     It is enabled just before the tree matching constraint theorems
     and disabled just after.")

   (xdoc::p
    "Except for
     @(tsee constraints-from-tree-match-dot-etc.) and
     @(tsee constraints-from-tree-match-dash-etc.),
     the alternations and concatenations of the syntactic entities being matched
     have an explicit list structure,
     and so the proof automatically uses rewrite rules like
     @(tsee tree-list-list-match-alternation-p-of-cons-alternation).
     In contrast,
     for @(tsee constraints-from-tree-match-dot-etc.) and
     for @(tsee constraints-from-tree-match-dash-etc.),
     we expand
     @(tsee tree-list-list-match-alternation-p) and
     @(tsee tree-list-list-match-concatenation-p)
     via explicit @(':expand') hints,
     because just enabling these two functions does not suffice
     (presumably due to ACL2's heuristics for expanding recursive functions).")

   (xdoc::p
    "The expansions described above reduce
     the matching of the (list of) tree(s) with syntactic entities
     in the hypothesis,
     to the matching of subtrees with syntactic sub-entities.
     Tree matching constraint theorems for these subtrees
     are used in the proofs for the containing trees, via @(':use') hints.
     For example, the proof of @(tsee constraints-from-tree-match-alpha)
     uses @(tsee constraints-from-tree-match-ichars) twice,
     once for each alternative of @('ALPHA') that the subtree may match.")

   (xdoc::p
    "As the matching of the tree(s) in the hypotheses of the theorems
     is reduced, in the proofs, to the matching of subtrees as just explained,
     we also need
     to reduce the tree strings to subtree strings and
     to reduce the terminated tree hypotheses to terminated subtree hypotheses,
     so that the tree matching constraint theorems for the subtrees apply.
     We accomplish the latter reductions by expanding the definitions of
     @(tsee tree->string),
     @(tsee tree-list->string),
     @(tsee tree-list-list->string), and
     @(tsee tree-terminatedp).
     We enable them just before the tree matching constraint theorems
     and we disable them just after.
     Enabled rules for
     @(tsee tree-list-terminatedp) and @(tsee tree-list-list-terminatedp)
     suffice, so we do not need to enable these two functions.")

   (xdoc::p
    "Since @(tsee constraints-from-tree-match-ichars)
     states constraints with @(tsee nats-match-insensitive-chars-p),
     and since that theorem is used in the proofs
     of several other tree matching constraint theorems,
     the proofs of the latter theorems
     use the definition of @(tsee nat-match-insensitive-char-p),
     which we enable just before the tree matching constraint theorems
     and we disable just after.
     The rewrite rules
     @('nats-match-sensitive-chars-p-when-atom-chars') and
     @('nats-match-sensitive-chars-p-when-cons-chars')
     reduce @(tsee nats-match-insensitive-chars-p)
     to @(tsee nat-match-insensitive-char-p)
     because the @('chars') argument is constant."))

  :order-subtopics t)

; disabled just after the tree matching constraint theorems:
(in-theory (enable tree->string
                   tree-list->string
                   tree-list-list->string
                   tree-terminatedp
                   tree-list-match-repetition-p-of-1-repetition
                   nat-match-insensitive-char-p))

(defrule constraints-from-tree-match-exact
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a tree that matches
          a direct numeric value notation."
  (implies (tree-match-element-p tree
                                 (element-num-val (num-val-direct nats))
                                 *all-concrete-syntax-rules*)
           (equal (car (tree->string tree))
                  (car (nat-list-fix nats))))
  :rule-classes nil
  :enable (tree-match-element-p
           tree-match-num-val-p))

(defrule constraints-from-tree-match-in-range
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a tree that matches
          a range numeric value notation."
  (implies (tree-match-element-p tree
                                 (element-num-val (num-val-range min max))
                                 *all-concrete-syntax-rules*)
           (and (<= (nfix min)
                    (car (tree->string tree)))
                (<= (car (tree->string tree))
                    (nfix max))))
  :rule-classes nil
  :enable (tree-match-element-p
           tree-match-num-val-p))

(defrule constraints-from-tree-match-ichars
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a tree that matches
          a case-insensitive character value notation."
  (implies (tree-match-element-p tree
                                 (element-char-val
                                  (char-val-insensitive charstring))
                                 *all-concrete-syntax-rules*)
           (nats-match-insensitive-chars-p (tree->string tree)
                                           (explode charstring)))
  :rule-classes nil
  :enable (tree-match-element-p
           tree-match-char-val-p))

(defrule constraints-from-tree-match-alpha
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('ALPHA')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *alpha*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (or (and (<= (char-code #\A)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\Z)))
               (and (<= (char-code #\a)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\z)))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use ((:instance constraints-from-tree-match-in-range
                   (tree (car (car (tree-nonleaf->branches tree))))
                   (min #x41)
                   (max #x5a))
        (:instance constraints-from-tree-match-in-range
                   (tree (car (car (tree-nonleaf->branches tree))))
                   (min #x61)
                   (max #x7a))))

(defrule constraints-from-tree-match-cr
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('CR')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *cr*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (car (tree->string tree))
                  (char-code #\Return)))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-exact
                  (tree (car (car (tree-nonleaf->branches tree))))
                  (nats (list #x0d))))

(defrule constraints-from-tree-match-digit
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('DIGIT')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *digit*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (and (<= (char-code #\0)
                    (car (tree->string tree)))
                (<= (car (tree->string tree))
                    (char-code #\9))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-in-range
                  (tree (car (car (tree-nonleaf->branches tree))))
                  (min #x30)
                  (max #x39)))

(defrule constraints-from-tree-match-dquote
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('DQUOTE')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *dquote*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (car (tree->string tree))
                  (char-code #\")))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-exact
                  (tree (car (car (tree-nonleaf->branches tree))))
                  (nats (list #x22))))

(defrule constraints-from-tree-match-htab
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('HTAB')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *htab*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (car (tree->string tree))
                  (char-code #\Tab)))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-exact
                  (tree (car (car (tree-nonleaf->branches tree))))
                  (nats (list #x09))))

(defrule constraints-from-tree-match-sp
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('SP')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *sp*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (car (tree->string tree))
                  (char-code #\Space)))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-exact
                  (tree (car (car (tree-nonleaf->branches tree))))
                  (nats (list #x20))))

(defrule constraints-from-tree-match-vchar
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('VCHAR')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *vchar*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (and (<= (char-code #\!)
                    (car (tree->string tree)))
                (<= (car (tree->string tree))
                    (char-code #\~))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-in-range
                  (tree (car (car (tree-nonleaf->branches tree))))
                  (min #x21)
                  (max #x7e)))

(defrule constraints-from-tree-match-crlf
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('CRLF')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *crlf*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (car (tree->string tree))
                  (char-code #\Return)))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-cr
                  (tree (car (car (tree-nonleaf->branches tree))))))

(defrule constraints-from-tree-match-wsp
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('WSP')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *wsp*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (member-equal (car (tree->string tree))
                         (chars=>nats '(#\Tab #\Space))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use ((:instance constraints-from-tree-match-htab
                   (tree (car (car (tree-nonleaf->branches tree)))))
        (:instance constraints-from-tree-match-sp
                   (tree (car (car (tree-nonleaf->branches tree)))))))

(defrule constraints-from-tree-match-prose-val
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('prose-val')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *prose-val*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (car (tree->string tree))
                  (char-code #\<)))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-ichars
                  (tree (car (car (tree-nonleaf->branches tree))))
                  (charstring "<")))

(defrule constraints-from-tree-list-match-*digit-when-nonempty
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a non-empty list of terminated trees
          that matches @('*DIGIT')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *digit*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (consp (tree-list->string trees)))
           (and (<= (char-code #\0)
                    (car (tree-list->string trees)))
                (<= (car (tree-list->string trees))
                    (char-code #\9))))
  :rule-classes nil
  :enable tree-list-match-repetition-p
  :use (:instance constraints-from-tree-match-digit
                  (tree (car trees))))

(defrule constraints-from-tree-list-match-1*digit
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a list of terminated trees that matches
          @('1*DIGIT')."
  (implies (and (tree-list-match-repetition-p trees
                                              (1*_ *digit*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees))
           (and (<= (char-code #\0)
                    (car (tree-list->string trees)))
                (<= (car (tree-list->string trees))
                    (char-code #\9))))
  :rule-classes nil
  :enable tree-list-match-repetition-p
  :use (:instance constraints-from-tree-match-digit
                  (tree (car trees))))

(defrule constraints-from-tree-match-dot-etc.
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a tree that matches a group @('(\".\" ...)')."
  (implies (and (tree-match-element-p tree
                                      element
                                      *all-concrete-syntax-rules*)
                (equal (element-kind element) :group)
                (consp (element-group->get element))
                (not (consp (cdr (element-group->get element))))
                (consp (car (element-group->get element)))
                (equal (car (car (element-group->get element)))
                       (repetition (repeat-range 1 (nati-finite 1))
                                   (element-char-val
                                    (char-val-insensitive ".")))))
           (equal (car (tree->string tree))
                  (char-code #\.)))
  :rule-classes nil
  :expand ((:free (rules) (tree-match-element-p tree element rules))
           (:free (alternation rules)
                  (tree-list-list-match-alternation-p
                   (tree-nonleaf->branches tree) alternation rules))
           (:free (concatenation rules)
                  (tree-list-list-match-concatenation-p
                   (tree-nonleaf->branches tree) concatenation rules)))
  :use (:instance constraints-from-tree-match-ichars
                  (tree (car (car (tree-nonleaf->branches tree))))
                  (charstring ".")))

(defrule constraints-from-tree-match-dash-etc.
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a tree that matches a group @('(\"-\" ...)')."
  (implies (and (tree-match-element-p tree
                                      element
                                      *all-concrete-syntax-rules*)
                (equal (element-kind element) :group)
                (consp (element-group->get element))
                (not (consp (cdr (element-group->get element))))
                (consp (car (element-group->get element)))
                (equal (car (car (element-group->get element)))
                       (repetition (repeat-range 1 (nati-finite 1))
                                   (element-char-val
                                    (char-val-insensitive "-")))))
           (equal (car (tree->string tree)) (char-code #\-)))
  :rule-classes nil
  :expand ((:free (rules) (tree-match-element-p tree element rules))
           (:free (alternation rules)
                  (tree-list-list-match-alternation-p
                   (tree-nonleaf->branches tree) alternation rules))
           (:free (concatenation rules)
                  (tree-list-list-match-concatenation-p
                   (tree-nonleaf->branches tree) concatenation rules)))
  :use (:instance constraints-from-tree-match-ichars
                  (tree (car (car (tree-nonleaf->branches tree))))
                  (charstring "-")))

(defrule constraints-from-tree-match-bin-val-rest-when-nonempty
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a tree
          that matches @('[ 1*(\".\" 1*BIT) / (\"-\" 1*BIT) ]')
          and that has a non-empty string at the leaves."
  (implies (and (tree-match-element-p tree
                                      (?_ (/_ (1*_ (!_ (/_ "."
                                                           (1*_ *bit*)))))
                                          (/_ (!_ (/_ "-"
                                                      (1*_ *bit*)))))
                                      *all-concrete-syntax-rules*)
                (consp (tree->string tree)))
           (member-equal (car (tree->string tree))
                         (chars=>nats '(#\- #\.))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable tree-list-match-repetition-p-of-1+-repetitions
  :use ((:instance constraints-from-tree-match-dot-etc.
                   (tree (car (car (tree-nonleaf->branches tree))))
                   (element (!_ (/_ "."
                                    (1*_ *bit*)))))
        (:instance constraints-from-tree-match-dash-etc.
                   (tree (car (car (tree-nonleaf->branches tree))))
                   (element (!_ (/_ "-"
                                    (1*_ *bit*)))))))

(defrule constraints-from-tree-match-dec-val-rest-when-nonempty
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a tree
          that matches @('[ 1*(\".\" 1*DIGIT) / (\"-\" 1*DIGIT) ]')
          and that has a non-empty string at the leaves."
  (implies (and (tree-match-element-p tree
                                      (?_ (/_ (1*_ (!_ (/_ "."
                                                           (1*_ *digit*)))))
                                          (/_ (!_ (/_ "-"
                                                      (1*_ *digit*)))))
                                      *all-concrete-syntax-rules*)
                (consp (tree->string tree)))
           (member-equal (car (tree->string tree))
                         (chars=>nats '(#\- #\.))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable tree-list-match-repetition-p-of-1+-repetitions
  :use ((:instance constraints-from-tree-match-dot-etc.
                   (tree (car (car (tree-nonleaf->branches tree))))
                   (element (!_ (/_ "."
                                    (1*_ *digit*)))))
        (:instance constraints-from-tree-match-dash-etc.
                   (tree (car (car (tree-nonleaf->branches tree))))
                   (element (!_ (/_ "-"
                                    (1*_ *digit*)))))))

(defrule constraints-from-tree-match-hex-val-rest-when-nonempty
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a tree
          that matches @('[ 1*(\".\" 1*HEXDIG) / (\"-\" 1*HEXDIG) ]')
          and that has a non-empty string at the leaves."
  (implies (and (tree-match-element-p tree
                                      (?_ (/_ (1*_ (!_ (/_ "."
                                                           (1*_ *hexdig*)))))
                                          (/_ (!_ (/_ "-"
                                                      (1*_ *hexdig*)))))
                                      *all-concrete-syntax-rules*)
                (consp (tree->string tree)))
           (member-equal (car (tree->string tree))
                         (chars=>nats '(#\- #\.))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable tree-list-match-repetition-p-of-1+-repetitions
  :use ((:instance constraints-from-tree-match-dot-etc.
                   (tree (car (car (tree-nonleaf->branches tree))))
                   (element (!_ (/_ "."
                                    (1*_ *hexdig*)))))
        (:instance constraints-from-tree-match-dash-etc.
                   (tree (car (car (tree-nonleaf->branches tree))))
                   (element (!_ (/_ "-"
                                    (1*_ *hexdig*)))))))

(defrule constraints-from-tree-match-bin-val
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('bin-val')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *bin-val*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (member-equal (car (tree->string tree))
                         (chars=>nats '(#\B #\b))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-ichars
                  (tree (car (car (tree-nonleaf->branches tree))))
                  (charstring "b")))

(defrule constraints-from-tree-match-dec-val
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('dec-val')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *dec-val*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (member-equal (car (tree->string tree))
                         (chars=>nats '(#\D #\d))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-ichars
                  (tree (car (car (tree-nonleaf->branches tree))))
                  (charstring "d")))

(defrule constraints-from-tree-match-hex-val
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('hex-val')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *hex-val*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (member-equal (car (tree->string tree))
                         (chars=>nats '(#\X #\x))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-ichars
                  (tree (car (car (tree-nonleaf->branches tree))))
                  (charstring "x")))

(defrule constraints-from-tree-match-bin/dec/hex-val
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches
          @('(bin-val / dec-val / hex-val)')."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ *bin-val*)
                                          (/_ *dec-val*)
                                          (/_ *hex-val*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (member-equal (car (tree->string tree))
                         (chars=>nats '(#\B #\D #\X #\b #\d #\x))))
  :rule-classes nil
  :enable tree-match-element-p
  :use ((:instance constraints-from-tree-match-bin-val
                   (tree (car (car (tree-nonleaf->branches tree)))))
        (:instance constraints-from-tree-match-dec-val
                   (tree (car (car (tree-nonleaf->branches tree)))))
        (:instance constraints-from-tree-match-hex-val
                   (tree (car (car (tree-nonleaf->branches tree)))))))

(defrule constraints-from-tree-match-num-val
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('num-val')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *num-val*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (and (equal (car (tree->string tree))
                       (char-code #\%))
                (member-equal (cadr (tree->string tree))
                              (chars=>nats '(#\B #\D #\X #\b #\d #\x)))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use ((:instance constraints-from-tree-match-ichars
                   (tree (car (car (tree-nonleaf->branches tree))))
                   (charstring "%"))
        (:instance constraints-from-tree-match-bin/dec/hex-val
                   (tree (car (cadr (tree-nonleaf->branches tree)))))))

(defrule constraints-from-tree-match-quoted-string
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches
          @('quoted-string')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *quoted-string*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (car (tree->string tree))
                  (char-code #\")))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-dquote
                  (tree (car (car (tree-nonleaf->branches tree))))))

(defrule constraints-from-tree-match-case-sensitive-string
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches
          @('case-sensitive-string')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *case-sensitive-string*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (and (equal (car (tree->string tree))
                       (char-code #\%))
                (member-equal (cadr (tree->string tree))
                              (chars=>nats '(#\S #\s)))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-ichars
                  (tree (car (car (tree-nonleaf->branches tree))))
                  (charstring "%s")))

(defrule constraints-from-tree-match-?-%i-when-nonempty
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a tree
          that matches @('[ \"%i\" ]')
          and that has a non-empty string at the leaves."
  (implies (and (tree-match-element-p tree
                                      (?_ (/_ "%i"))
                                      *all-concrete-syntax-rules*)
                (consp (tree->string tree)))
           (and (equal (car (tree->string tree))
                       (char-code #\%))
                (member-equal (cadr (tree->string tree))
                              (chars=>nats '(#\I #\i)))))
  :rule-classes nil
  :enable tree-match-element-p
  :use (:instance constraints-from-tree-match-ichars
                  (tree (car (car (tree-nonleaf->branches tree))))
                  (charstring "%i")))

(defrule constraints-from-tree-match-case-insensitive-string
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches
          @('case-insensitive-string')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename
                                       *case-insensitive-string*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (or (equal (car (tree->string tree))
                      (char-code #\"))
               (and (equal (car (tree->string tree))
                           (char-code #\%))
                    (member-equal (cadr (tree->string tree))
                                  (chars=>nats '(#\I #\i))))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use ((:instance constraints-from-tree-match-?-%i-when-nonempty
                   (tree (car (car (tree-nonleaf->branches tree)))))
        (:instance constraints-from-tree-match-quoted-string
                   (tree (car (cadr (tree-nonleaf->branches tree)))))))

(defrule constraints-from-tree-match-char-val
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('char-val')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *char-val*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (member-equal (car (tree->string tree))
                         (chars=>nats '(#\" #\%))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use ((:instance constraints-from-tree-match-case-insensitive-string
                   (tree (car (car (tree-nonleaf->branches tree)))))
        (:instance constraints-from-tree-match-case-sensitive-string
                   (tree (car (car (tree-nonleaf->branches tree)))))))

(defrule constraints-from-tree-match-comment
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('comment')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *comment*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (car (tree->string tree))
                  (char-code #\;)))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-ichars
                  (tree (car (car (tree-nonleaf->branches tree))))
                  (charstring ";")))

(defrule constraints-from-tree-match-cnl
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('c-nl')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *c-nl*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (member-equal (car (tree->string tree))
                         (chars=>nats '(#\Return #\;))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use ((:instance constraints-from-tree-match-comment
                   (tree (car (car (tree-nonleaf->branches tree)))))
        (:instance constraints-from-tree-match-crlf
                   (tree (car (car (tree-nonleaf->branches tree)))))))

(defrule constraints-from-tree-match-cnl-wsp
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches
          @('(c-nl WSP)')."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ *c-nl* *wsp*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (member-equal (car (tree->string tree))
                         (chars=>nats '(#\Return #\;))))
  :rule-classes nil
  :enable tree-match-element-p
  :use (:instance constraints-from-tree-match-cnl
                  (tree (car (car (tree-nonleaf->branches tree))))))

(defrule constraints-from-tree-match-cwsp
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('c-wsp')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *c-wsp*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (member-equal (car (tree->string tree))
                         (chars=>nats '(#\Tab #\Return #\Space #\;))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use ((:instance constraints-from-tree-match-cnl-wsp
                   (tree (car (car (tree-nonleaf->branches tree)))))
        (:instance constraints-from-tree-match-wsp
                   (tree (car (car (tree-nonleaf->branches tree)))))))

(defrule constraints-from-tree-list-match-*cwsp-when-nonempty
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a non-empty list of terminated trees
          that matches @('*c-wsp')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *c-wsp*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (consp (tree-list->string trees)))
           (member-equal (car (tree-list->string trees))
                         (chars=>nats '(#\Tab #\Return #\Space #\;))))
  :rule-classes nil
  :enable tree-list-match-repetition-p
  :use (:instance constraints-from-tree-match-cwsp
                  (tree (car trees))))

(defrule constraints-from-tree-match-*digit-star-*digit
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches
          @('(*DIGIT \"*\" *DIGIT)')."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ (*_ *digit*) "*" (*_ *digit*)))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (or (and (<= (char-code #\0)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\9)))
               (equal (car (tree->string tree))
                      (char-code #\*))))
  :rule-classes nil
  :enable tree-match-element-p
  :use ((:instance constraints-from-tree-match-ichars
                   (tree (car (cadr (tree-nonleaf->branches tree))))
                   (charstring "*"))
        (:instance constraints-from-tree-list-match-*digit-when-nonempty
                   (trees (car (tree-nonleaf->branches tree))))))

(defrule constraints-from-tree-match-repeat
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('repeat')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *repeat*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (or (and (<= (char-code #\0)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\9)))
               (equal (car (tree->string tree))
                      (char-code #\*))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use ((:instance constraints-from-tree-list-match-1*digit
                   (trees (car (tree-nonleaf->branches tree))))
        (:instance constraints-from-tree-match-*digit-star-*digit
                   (tree (car (car (tree-nonleaf->branches tree)))))))

(defrule constraints-from-tree-match-?repeat-when-nonempty
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree
          that matches @('[repeat]')
          and that has a non-empty string at the leaves."
  (implies (and (tree-match-element-p tree
                                      (?_ (/_ *repeat*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (consp (tree->string tree)))
           (or (and (<= (char-code #\0)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\9)))
               (equal (car (tree->string tree))
                      (char-code #\*))))
  :rule-classes nil
  :enable tree-match-element-p
  :use (:instance constraints-from-tree-match-repeat
                  (tree (car (car (tree-nonleaf->branches tree))))))

(defrule constraints-from-tree-match-rulename
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('rulename')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *rulename*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (or (and (<= (char-code #\A)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\Z)))
               (and (<= (char-code #\a)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\z)))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-alpha
                  (tree (car (car (tree-nonleaf->branches tree))))))

(defrule constraints-from-tree-match-group
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('group')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *group*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (car (tree->string tree))
                  (char-code #\()))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-ichars
                  (tree (car (car (tree-nonleaf->branches tree))))
                  (charstring "(")))

(defrule constraints-from-tree-match-option
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('option')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *option*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (car (tree->string tree))
                  (char-code #\[)))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-ichars
                  (tree (car (car (tree-nonleaf->branches tree))))
                  (charstring "[")))

(defrule constraints-from-tree-match-element
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('element')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *element*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (or (and (<= (char-code #\A)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\Z)))
               (and (<= (char-code #\a)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\z)))
               (member-equal (car (tree->string tree))
                             (chars=>nats '(#\" #\% #\( #\< #\[)))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use ((:instance constraints-from-tree-match-rulename
                   (tree (car (car (tree-nonleaf->branches tree)))))
        (:instance constraints-from-tree-match-group
                   (tree (car (car (tree-nonleaf->branches tree)))))
        (:instance constraints-from-tree-match-option
                   (tree (car (car (tree-nonleaf->branches tree)))))
        (:instance constraints-from-tree-match-char-val
                   (tree (car (car (tree-nonleaf->branches tree)))))
        (:instance constraints-from-tree-match-num-val
                   (tree (car (car (tree-nonleaf->branches tree)))))
        (:instance constraints-from-tree-match-prose-val
                   (tree (car (car (tree-nonleaf->branches tree)))))))

(defrule constraints-from-tree-match-repetition
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches
          @('repetition')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *repetition*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (or (and (<= (char-code #\A)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\Z)))
               (and (<= (char-code #\a)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\z)))
               (and (<= (char-code #\0)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\9)))
               (member-equal (car (tree->string tree))
                             (chars=>nats '(#\" #\% #\( #\* #\< #\[)))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use ((:instance constraints-from-tree-match-?repeat-when-nonempty
                   (tree (car (car (tree-nonleaf->branches tree)))))
        (:instance constraints-from-tree-match-element
                   (tree (car (cadr (tree-nonleaf->branches tree)))))))

(defrule constraints-from-tree-match-concatenation
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches
          @('concatenation')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *concatenation*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (or (and (<= (char-code #\A)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\Z)))
               (and (<= (char-code #\a)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\z)))
               (and (<= (char-code #\0)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\9)))
               (member-equal (car (tree->string tree))
                             (chars=>nats '(#\" #\% #\( #\* #\< #\[)))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use ((:instance constraints-from-tree-match-repetition
                   (tree (car (car (tree-nonleaf->branches tree)))))))

(defrule constraints-from-tree-match-alternation
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches
          @('alternation')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *alternation*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (or (and (<= (char-code #\A)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\Z)))
               (and (<= (char-code #\a)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\z)))
               (and (<= (char-code #\0)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\9)))
               (member-equal (car (tree->string tree))
                             (chars=>nats '(#\" #\% #\( #\* #\< #\[)))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use ((:instance constraints-from-tree-match-concatenation
                   (tree (car (car (tree-nonleaf->branches tree)))))))

(defrule constraints-from-tree-match-elements
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('elements')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *elements*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (or (and (<= (char-code #\A)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\Z)))
               (and (<= (char-code #\a)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\z)))
               (and (<= (char-code #\0)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\9)))
               (member-equal (car (tree->string tree))
                             (chars=>nats '(#\" #\% #\( #\* #\< #\[)))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-alternation
                  (tree (car (car (tree-nonleaf->branches tree))))))

(defrule constraints-from-tree-match-equal-/-equal-slash
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches
          @('(\"=\" / \"=/\")')."
  (implies (tree-match-element-p tree
                                 (!_ (/_ "=")
                                     (/_ "=/"))
                                 *all-concrete-syntax-rules*)
           (equal (car (tree->string tree))
                  (char-code #\=)))
  :rule-classes nil
  :enable tree-match-element-p
  :use ((:instance constraints-from-tree-match-ichars
                   (tree (car (car (tree-nonleaf->branches tree))))
                   (charstring "="))
        (:instance constraints-from-tree-match-ichars
                   (tree (car (car (tree-nonleaf->branches tree))))
                   (charstring "=/"))))

(defrule constraints-from-tree-match-defined-as
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches
          @('defined-as')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *defined-as*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (member-equal (car (tree->string tree))
                         (chars=>nats '(#\Tab #\Return #\Space #\; #\=))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use ((:instance constraints-from-tree-match-equal-/-equal-slash
                   (tree (car (cadr (tree-nonleaf->branches tree)))))
        (:instance constraints-from-tree-list-match-*cwsp-when-nonempty
                   (trees (car (tree-nonleaf->branches tree))))))

(defrule constraints-from-tree-match-rule
  :parents (grammar-parser-constraints-from-tree-matching)
  :short "Constraints induced by a terminated tree that matches @('rule')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *rule*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (or (and (<= (char-code #\A)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\Z)))
               (and (<= (char-code #\a)
                        (car (tree->string tree)))
                    (<= (car (tree->string tree))
                        (char-code #\z)))))
  :rule-classes nil
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :use (:instance constraints-from-tree-match-rulename
                  (tree (car (car (tree-nonleaf->branches tree))))))

; enabled just before the tree matching constraint theorems:
(in-theory (disable tree->string
                    tree-list->string
                    tree-list-list->string
                    tree-terminatedp
                    tree-list-match-repetition-p-of-1-repetition))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-parser-disambiguation
  :parents (grammar-parser-completeness)

  :short "Disambiguation theorems for the parser of ABNF grammars."

  :long

  (xdoc::topstring

   (xdoc::p
    "If a (list of) terminated tree(s) matches a syntactic entity,
     attempting to parse the string at the leaves of the tree(s)
     with a parsing function for a different syntactic entity fails, in general.
     For example, if a terminated tree matches @('HTAB'),
     @(tsee parse-sp) fails on the string at the leaves of the tree:
     this is stated by the disambiguation theorem
     @(tsee fail-sp-when-match-htab).")

   (xdoc::p
    "The disambiguation theorems below state this kind of facts.
     Essentially, these theorems say that certain syntactic entities
     are incompatible with certain parsing functions;
     they are used to show that the parser can disambiguate its input
     (hence the name of these theorems).")

   (xdoc::h3 "Usage")

   (xdoc::p
    "The disambiguation theorems are used to prove the "
    (xdoc::seetopic "grammar-parser-completeness"
                    "completeness theorems")
    ".")

   (xdoc::p
    "The disambiguation theorems are rewrite rules that are disabled by default.
     They are explicitly enabled in the individual completeness theorems.")

   (xdoc::p
    "Some disambiguation theorems are used
     to incrementally prove other disambiguation theorems (see below),
     also via explicit enabling.")

   (xdoc::h3 "Scope")

   (xdoc::p
    "There are disambiguation theorems
     only for some combinations of syntactic entities and parsing functions:
     just the ones used to prove the completeness theorems,
     and to incrementally prove other disambiguation theorems.")

   (xdoc::p
    "Given the potentially ``quadratic'' number
     of disambiguation theorems
     (i.e. for all syntactic entities combined with all parsing functions),
     some disambiguation theorems group together
     multiple tree matching hypotheses or multiple parsing failure conclusions.
     For example, @(tsee fail-bit/digit/hexdig/dot/dash-when-match-slash)
     asserts the failure of multiple parsing functions
     for the given tree matching hypothesis:
     this theorem replaces five potential theorems
     (one for each parsing function mentioned there).
     As another example, @(tsee fail-cwsp-when-match-alt/conc/rep)
     asserts the failure of a given parsing function
     for multiple syntactic entities matched by the tree:
     this theorem replaces three potential theorems
     (one for each syntactic entity mentioned there).
     More grouping (and thus reduction in the number of disambiguation theorems)
     is possible,
     but we also try to keep the disambiguation theorems' names
     sufficiently descriptive while not excessively long.")

   (xdoc::h3 "Formulation")

   (xdoc::p
    "The formulation of the disambiguation theorems is derived from
     the subgoals that arise in the completeness proofs
     (and in the incrementally proved disambiguation proofs):
     the disambiguation theorems serve to prove those subgoals.
     The disambiguation theorems were developed
     in the process of proving the completeness theorems,
     based on failed subgoals in the latter.")

   (xdoc::p
    "In particular,
     the ``asymmetric'' use of trees and parsing functions
     to show incompatibility
     (as opposed to showing incompatibility
     between parsing functions or between trees)
     reflects the structure of the subgoals in the completeness theorems;
     see the documentation of the completeness theorems for details.")

   (xdoc::p
    "The formulation of each disambiguation theorem also involves
     some remaining input
     that is @(tsee append)ed after the string at the leaves of the tree(s).
     That is, each disambiguation theorem says something of this form:
     if a (list of) terminated tree(s) matches certain syntactic entities
     and possibly satisfies certain "
    (xdoc::seetopic "grammar-parser-disambiguating-restrictions"
                    "disambiguating restrictions")
    ", then running certain parsing functions on the @(tsee append) of
     (i) the string at the leaves of the tree and
     (ii) some remaining input
     possibly satisfing certain hypotheses explained below,
     fails.
     This is similar to the way in which
     the completeness theorems are formulated.")

   (xdoc::p
    "Most disambiguation theorems involve a single (list of) tree(s).
     Four of them (i.e.
     @(tsee fail-alpha/digit/dash-when-match-*cwsp-close-round/square),
     @(tsee fail-bit/digit/hexdig/dot/dash-when-match-*cwsp-close-round/square),
     @(tsee fail-alt-rest-comp-when-match-*cwsp-close-round/square), and
     @(tsee fail-conc-rest-comp-when-match-*cwsp-close-round/square))
     involve a list of trees matching @('*c-wsp')
     and a tree matching @('\")\"') or @('\"]\"');
     the parsing function in their conclusion
     is applied to the @(tsee append) of
     (i) the string at the leaves of the list of trees,
     (ii) the string at the leaves of the tree, and
     (iii) some remaining input.
     These four theorems are used
     in the completeness proofs of the mutually recursive parsing functions,
     precisely in the induction step lemmas
     for @(tsee parse-group) and @(tsee parse-option).
     In those lemmas, the tree matching hypothesis reduces to, among others,
     the fact that a list of subtrees matches @('*c-wsp')
     and that the subtree just after that list matches @('\")\"') or @('\"]\"'):
     the four disambiguation theorems apply to that (list of) subtree(s).
     Note that @('*c-wsp \")\"') and @('*c-wsp \"]\"') are the ending parts
     of the definientia of @('group') and @('option').")

   (xdoc::h3 "Hypotheses on the Remaining Input")

   (xdoc::p
    "In all the disambiguation theorems,
     the remaining input (following the string at the leaves of the tree(s))
     is denoted by the variable @('rest-input').
     The hypotheses on the remaining input, when present,
     are that certain parsing functions fail on the remaining input.")

   (xdoc::p
    "In most cases, the hypotheses on the remaining input are present
     when the (list of) tree(s) may have an empty string at the leaves.
     When that string is empty,
     the incompatibility between the tree(s) and the parsing functions
     does not apply.
     Thus, each of these theorems includes the hypothesis
     that the parsing function fails on the remaining input,
     to ensure that the conclusion holds in this case.
     For example, in @(tsee fail-bit-when-match-*cwsp),
     if the list of trees is empty,
     the incompatibility
     between (the first tree of the list matching) @('c-wsp')
     and the parsing function @(tsee parse-bit) does not apply;
     but the hypothesis that @(tsee parse-bit) fails on @('rest-input')
     maintains the truth of the theorem in case the list of trees is empty.
     In general, for each of these disambiguation theorems,
     the hypothesis asserts the failure on the remaining input
     of the same parsing function that the theorem shows to be
     incompatible with the syntactic entity matched by the tree(s).")

   (xdoc::p
    "The hypotheses just mentioned could be weakened
     to require the parsing failure on the remaining input
     only if the string at the leaves of the tree(s) is in fact empty;
     however, the stronger hypotheses keep the theorems simpler
     without precluding the eventual proof of
    the top-level completeness theorem.
     Another possibility is to have, instead, hypotheses stating that
     the string at the leaves of the tree(s) are not empty;
     however, the current formulation seems more readily usable
     in the proofs of completeness,
     obviating a case split based on whether the string is empty or not.")

   (xdoc::p
    "The disambiguation theorem
     @(tsee fail-equal-slash-when-match-equal-and-rest-fail-slash)
     has the hypothesis that @(tsee parse-ichar) with argument @('#\\/')
     fails on the remaining input.
     Without this hypothesis,
     @(tsee parse-ichars) with arguments @('#\\=') and @('#\\/') could succeed:
     after parsing the @('\"=\"') in the string at the leaves of the tree,
     it could parse a @('\"/\"') in the remaining input,
     obtaining a @('\"=/\"').")

   (xdoc::p
    "The disambiguation theorem
     @(tsee fail-*digit-star-*digit-when-match-1*digit)
     has the hypotheses that
     both @(tsee parse-ichar) with argument @('#\\*')
     and @(tsee parse-digit)
     fail on the remaining input.
     Without the first hypothesis,
     @(tsee parse-*digit-star-*digit) could succeed:
     after parsing the @('DIGIT')s from the string at the leaves of the trees,
     it could parse a @('\"*\"') from the remaining input,
     and then zero or more @('DIGIT')s,
     obtaining a @('(*DIGIT \"*\" *DIGIT)').
     Without the second hypothesis,
     @(tsee parse-*digit-star-*digit) could also succeed:
     after parsing the @('DIGIT')s from the string at the leaves of the trees,
     it could parse additional @('DIGIT')s from the remaining input,
     then a @('\"*\"'),
     and then zero or more @('DIGIT')s,
     obtaining a @('(*DIGIT \"*\" *DIGIT)').
     The second hypothesis is stronger than needed,
     because the presence of a @('DIGIT') at the start of the remaining input
     does not imply the success of @(tsee parse-*digit-star-*digit);
     however, the stronger hypothesis keeps the theorems simpler
     without precluding the eventual proof of
     the top-level completeness theorem.")

   (xdoc::p
    "The disambiguation theorem @(tsee fail-cwsp-when-match-cnl)
     has the hypothesis that @(tsee parse-wsp) fails on the remaining input.
     Without this hypothesis, @(tsee parse-cwsp) could succeed:
     after parsing the @('c-nl') from the string at the leaves of the tree,
     it could parse a @('WSP') from the remaining input,
     obtaining a @('c-wsp').")

   (xdoc::p
    "The disambiguation theorems
     @(tsee fail-alt-rest-comp-when-match-cnl) and
     @(tsee fail-conc-rest-comp-when-match-cnl)
     also have the hypothesis that @(tsee parse-wsp) fails
     on the remaining input.
     Without this hypothesis,
     @(tsee parse-alt-rest-comp) or
     @(tsee parse-conc-rest-comp)
     could succeed:
     after parsing the @('c-nl') from the string at the leaves of the tree,
     it could parse a @('WSP') from the remaining input,
     forming the first @('c-wsp')
     of a @('(*c-wsp \"/\" *c-wsp concatenation)')
     or of a @('*(1*c-wsp repetition)'),
     and then proceed to parse more, eventually obtaining
     a @('(*c-wsp \"/\" *c-wsp concatenation)') or @('*(1*c-wsp repetition)').
     The hypothesis is stronger than needed,
     because the presence of a @('WSP') at the start of the remaining input
     does not imply the success of
     @(tsee parse-alt-rest-comp) or
     @(tsee parse-conc-rest-comp);
     however, the stronger hypothesis keeps the theorems simpler
     without precluding the eventual proof of
     the top-level completeness theorem.")

   (xdoc::p
    "The disambiguation theorem @(tsee fail-conc-rest-comp-when-match-*cwsp)
     has the hypotheses that
     both @(tsee parse-repetition) and @(tsee parse-cwsp)
     fail on the remaining input.
     Without the first hypothesis,
     @(tsee parse-conc-rest-comp) could succeed:
     after parsing the @('*c-wsp') from the string at the leaves of the trees,
     assuming that there is at least one tree,
     it could parse a @('repetition') from the remaining input,
     obtaining a @('(1*c-wsp repetition)').
     Without the second hypothesis,
     @(tsee parse-conc-rest-comp) could also succeed:
     after parsing the @('*c-wsp') from the string at the leaves of the trees,
     it could parse a @('c-wsp') from the remaining input,
     and then a @('repetition'),
     obtaining a @('(1*c-wsp repetition)').")

   (xdoc::h3 "Hypotheses on the Tree(s)")

   (xdoc::p
    "Many disambiguation theorems include
     hypotheses saying that the trees are terminated.
     This ensures that the strings at the leaves of the trees
     consist of natural numbers and not rule names,
     since the incompatibilities with the parsing functions
     are in terms of natural numbers.
     Some disambiguation theorems do not need these hypotheses
     because the syntactic entities can only be matched
     by trees whose (starting) leaves are natural numbers.
     For instance, in @(tsee fail-dot-when-match-dash-etc.),
     the group @('(\"-\" ...)') can only be matched by a tree
     whose first leaf is a natural number,
     upon which the incompatibility with the parsing function applies.")

   (xdoc::p
    "A few disambiguation theorems include hypotheses
     that the tree(s) satisfy the "
    (xdoc::seetopic "grammar-parser-disambiguating-restrictions"
                    "disambiguating restrictions")
    ". These theorems say that @(tsee parse-wsp) fails
     on the strings at the leaves of trees
     that satisfy the disambiguating restrictions.
     Since the restrictions say that these trees cannot start with @('WSP'),
     as the syntactic entities matched by the trees
     would otherwise allow that,
     these hypotheses are essential to the truth of these theorems.")

   (xdoc::h3 "Proof Methods")

   (xdoc::p
    "Most disambiguation theorems are proved by using, via @(':use') hints,
     parsing constraint theorems and tree matching constraint theorems
     that explicate incompatible constraints
     between the parsing functions
     and the syntactic entities matched by the trees.
     For example, in @(tsee fail-sp-when-match-htab),
     the fact that the tree matches @('HTAB') induces the constraint that
     the first natural number of the string at the leaves of the tree is 9,
     but the fact that @(tsee parse-sp) succeeds induces the constraint that
     the first natural number of the string at the leaves of the tree is 32.")

   (xdoc::p
    "The disambiguation theorems
     @(tsee fail-case-insensitive-string-when-match-case-sensitive-string) and
     @(tsee fail-char-val-when-match-num/prose-val)
     have a @(':cases') hint on whether
     the string at the leaves of the tree has a second natural number or not.
     Without this hint, the proof fails.
     Perhaps this case split is related to the fact that
     these disambiguation theorems are proved via constraints that involve
     not only the first but also the second natural number in the string,
     for LL(2) parts of the grammar.")

   (xdoc::p
    "The proofs of some disambiguation theorems
     use other disambiguation theorems.
     The former enable the latter explcitly, to use them as rewrite rules.
     As explained earlier, some disambiguation theorems group together
     multiple tree matching hypotheses or multiple parsing conclusions,
     to reduce the potentially quadratic number of theorems.
     This means that,
     when some of these disambiguation theorems
     are used in the proofs of others,
     only ``parts'' of the former are actually used.")

   (xdoc::p
    "A disambiguation theorem about a list of trees matching a repetition,
     such that another disambiguation theorem exists
     about a tree matching the element of that repetition
     and about the same parsing function,
     is proved just by enabling the latter disambiguation theorem
     and @(tsee tree-list-match-repetition-p),
     without any parsing constraint theorems
     and tree matching constraint theorems.
     For example, @(tsee fail-bit-when-match-*cwsp) is proved just by enabling
     @(tsee fail-bit/digit/hexdig/dot/dash-when-match-cwsp)
     (of which only the @(tsee parse-bit) failure is used here) and
     @(tsee tree-list-match-repetition-p).")

   (xdoc::p
    "Some disambiguation theorems are proved by
     expanding the tree matching hypotheses
     and the parsing function calls in the conclusions,
     and enabling disambiguation theorems so that they apply to
     the resulting subtree matching facts and called parsing functions;
     we also enable
     predicates like @(tsee tree-terminatedp) and recursive companions and
     functions like @(tsee tree->string) and recursive companions,
     so that they apply to the subtrees resulting from the matching expansion.
     For example,
     @(tsee fail-alpha/digit/dash-when-match-alt-rest-comp) is proved by
     reducing the tree matching hypothesis to
     a list of subtrees matching @('*c-wsp') and a tree matching @('\"/\"').
     Then @(tsee fail-alpha/digit/dash-when-match-cwsp)
     is used for the case in which the list of subtrees is not empty,
     while @(tsee fail-alpha/digit/dash-when-match-slash-/-close-round/square)
     (the @('slash') part)
     is used for the case in which the list of subtree is empty.")

   (xdoc::p
    "The proofs of some disambiguation theorems
     use certain completeness theorems.
     In some cases, this is related to LL(*) parts of the grammar:
     the completeness theorems serve to go ``past''
     the unbounded look-ahead,
     before reaching the point where the constraints
     from (sub)tree matching and (called) parsing functions are incompatible.
     For example, @(tsee fail-conc-rest-comp-when-match-alt-rest-comp)
     shows the incompatibility
     between @('(*c-wsp \"/\" *c-wsp concatenation)')
     and @('(1*c-wsp repetition)'):
     the completeness theorem @(tsee parse-1*cwsp-when-tree-list-match)
     is used to go past the unbounded @('1*c-wsp')
     that could start @('(*c-wsp \"/\" *c-wsp concatenation)')
     to show that @('repetition') is incompatible with @('\"/\"').
     As another example, @(tsee fail-*digit-star-*digit-when-match-1*digit)
     shows the incompatibility
     between @('(*DIGIT \"*\" *DIGIT)') and @('1*DIGIT'):
     the completeness theorem @(tsee parse-*digit-when-tree-list-match)
     is used to go past the unbounded @('*DIGIT')
     that could start @('1*DIGIT')
     to show that @('\"*\"') is incompatible with
     the assumptions on the remaining input.")

   (xdoc::p
    "In other disambiguation theorems,
     the use of completeness theorems
     is not related to LL(*) parts of the grammar,
     but is suggested by subgoals involving trees
     and parsing functions called by the ones in the theorems' conclusions.
     For example, in @(tsee fail-cwsp-when-match-cnl),
     the expansion of @(tsee parse-cwsp) and @(tsee parse-cnl-wsp)
     produces a call to @(tsee parse-cnl)
     on the string at the leaves of the tree
     that the theorem hypothesizes to match @('c-nl'):
     thus, @(tsee parse-cnl-when-tree-match) applies here.")

   (xdoc::p
    "When a disambiguation theorem uses a completeness theorem,
     the former appears in the file just after the latter,
     with a comment referring to the completeness theorem used.
     However, the disambiguation theorem is
     under the manual topic about disambiguation theorems,
     not under the manual topic about completeness theorems.")

   (xdoc::p
    "The disambiguation theorem @(tsee fail-conc-rest-comp-when-match-*cwsp)
     uses, as a rewrite rule, the "
    (xdoc::seetopic "grammar-parser-parsing-failure-propagation"
                    "parsing failure propagation theorem")
    " @(tsee fail-conc-rest-comp-when-fail-cwsp).")

   (xdoc::p
    "In some theorems, just enabling some functions does not suffice
     to expand them in all the places where they need to be expanded
     (presumably due to ACL2's heuristics for expanding recursive functions).
     Thus, we use @(':expand') hints in those cases.")

   (xdoc::p
    "Some of the disambiguation theorem proofs
     do not seem as systematic as desired.
     Two of them use @(':cases') hints
     (different from the ones discussed earlier,
     which are related to LL(2) parts of the grammar),
     one of them uses an @(':induct') hint,
     one of them uses a local lemma,
     some use various rules about @(tsee tree-list-match-repetition-p),
     and some expand many definitions.
     It may be possible to make these proofs more systematic,
     by introducing and using
     some additional ``intermediate '' disambiguation theorems
     and some additional rules about the ABNF semantics."))

  :order-subtopics t)

; disabled just after the disambiguation theorems:
(in-theory (enable nat-match-insensitive-char-p))

(defruled fail-1st-range-when-match-2nd-range
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between two disjoint numeric ranges."
  (implies (and (tree-match-element-p tree
                                      (%- min2 max2)
                                      *all-concrete-syntax-rules*)
                (< (nfix max1) (nfix min2)))
           (mv-nth 0 (parse-in-range min1 max1 (append (tree->string tree)
                                                       rest-input))))
  :use ((:instance constraints-from-tree-match-in-range
                   (min min2)
                   (max max2))
        (:instance constraints-from-parse-in-range
                   (min min1)
                   (max max1)
                   (input (append (tree->string tree) rest-input))))
  :enable %-)

(defruled fail-0-when-match-1
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('\"0\"') and @('\"1\"')."
  (implies (tree-match-element-p tree
                                 (element-char-val (char-val-insensitive "1"))
                                 *all-concrete-syntax-rules*)
           (mv-nth 0 (parse-ichar #\0 (append (tree->string tree)
                                              rest-input))))
  :use ((:instance constraints-from-tree-match-ichars
                   (charstring "1"))
        (:instance constraints-from-parse-ichar
                   (char #\0)
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-digit-when-match-a/b/c/d/e/f
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('DIGIT') and
          any of
          @('\"A\"'),
          @('\"B\"'),
          @('\"C\"'),
          @('\"D\"'),
          @('\"E\"'), and
          @('\"F\"')."
  (implies (and (tree-match-element-p tree element *all-concrete-syntax-rules*)
                (elementp element)
                (equal (element-kind element)
                       :char-val)
                (equal (char-val-kind (element-char-val->get element))
                       :insensitive)
                (member-equal (char-val-insensitive->get
                               (element-char-val->get element))
                              '("A" "B" "C" "D" "E" "F")))
           (mv-nth 0 (parse-digit (append (tree->string tree) rest-input))))
  :use ((:instance constraints-from-tree-match-ichars
                   (charstring (char-val-insensitive->get
                                (element-char-val->get element))))
        (:instance constraints-from-parse-digit
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-a/b/c/d/e/f-when-match-other-a/b/c/d/e/f
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between any two distinct elements among
          @('\"A\"'),
          @('\"B\"'),
          @('\"C\"'),
          @('\"D\"'),
          @('\"E\"'), and
          @('\"F\"')."
  (implies (and (tree-match-element-p tree element *all-concrete-syntax-rules*)
                (elementp element)
                (equal (element-kind element)
                       :char-val)
                (equal (char-val-kind (element-char-val->get element))
                       :insensitive)
                (member-equal (char-val-insensitive->get
                               (element-char-val->get element))
                              '("A" "B" "C" "D" "E" "F"))
                (member-equal char '(#\A #\B #\C #\D #\E #\F))
                (not (equal (explode (char-val-insensitive->get
                                      (element-char-val->get element)))
                            (list char))))
           (mv-nth 0 (parse-ichar char (append (tree->string tree)
                                               rest-input))))
  :use ((:instance constraints-from-tree-match-ichars
                   (charstring (char-val-insensitive->get
                                (element-char-val->get element))))
        (:instance constraints-from-parse-ichar
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-sp-when-match-htab
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('SP') and @('HTAB')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *htab*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (mv-nth 0 (parse-sp (append (tree->string tree) rest-input))))
  :use (constraints-from-tree-match-htab
        (:instance constraints-from-parse-sp
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-either-range-when-match-close-angle
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(%x20-3D / %x3F-7E)') and @('\">\"')."
  (implies (tree-match-element-p tree
                                 (element-char-val (char-val-insensitive ">"))
                                 *all-concrete-syntax-rules*)
           (mv-nth 0 (parse-in-either-range #x20 #x3d #x3f #x7e
                                            (append (tree->string tree)
                                                    rest-input))))
  :use ((:instance constraints-from-tree-match-ichars
                   (charstring ">"))
        (:instance constraints-from-parse-in-either-range
                   (min1 #x20)
                   (max1 #x3d)
                   (min2 #x3f)
                   (max2 #x7e)
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-bit-when-match-*-dot-1*bit
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('BIT') and
          @('*(\".\" 1*BIT)') not followed by @('BIT')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ "."
                                                          (1*_ *bit*))))
                                              *all-concrete-syntax-rules*)
                (mv-nth 0 (parse-bit rest-input)))
           (mv-nth 0 (parse-bit (append (tree-list->string trees)
                                        rest-input))))
  :use ((:instance constraints-from-tree-match-dot-etc.
                   (tree (car trees))
                   (element (!_ (/_ "."
                                    (1*_ *bit*)))))
        (:instance constraints-from-parse-bit
                   (input (append (tree-list->string trees) rest-input))))
  :enable tree-list-match-repetition-p-of-0+-reps-when-consp)

(defruled fail-digit-when-match-*-dot-1*digit
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('DIGIT') and
          @('*(\".\" 1*DIGIT)') not followed by @('DIGIT')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ "."
                                                          (1*_ *digit*))))
                                              *all-concrete-syntax-rules*)
                (mv-nth 0 (parse-digit rest-input)))
           (mv-nth 0 (parse-digit (append (tree-list->string trees)
                                          rest-input))))
  :use ((:instance constraints-from-tree-match-dot-etc.
                   (tree (car trees))
                   (element (!_ (/_ "."
                                    (1*_ *digit*)))))
        (:instance constraints-from-parse-digit
                   (input (append (tree-list->string trees) rest-input))))
  :enable tree-list-match-repetition-p-of-0+-reps-when-consp)

(defruled fail-hexdig-when-match-*-dot-1*hexdig
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('HEXDIG') and
          @('*(\".\" 1*HEXDIG)') not followed by @('HEXDIG')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ "."
                                                          (1*_ *hexdig*))))
                                              *all-concrete-syntax-rules*)
                (mv-nth 0 (parse-hexdig rest-input)))
           (mv-nth 0 (parse-hexdig (append (tree-list->string trees)
                                           rest-input))))
  :use ((:instance constraints-from-tree-match-dot-etc.
                   (tree (car trees))
                   (element (!_ (/_ "."
                                    (1*_ *hexdig*)))))
        (:instance constraints-from-parse-hexdig
                   (input (append (tree-list->string trees) rest-input))))
  :enable tree-list-match-repetition-p-of-0+-reps-when-consp)

(defruled fail-dot-when-match-dash-etc.
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('\".\"') and @('(\"-\" ...)')."
  (implies (and (tree-match-element-p tree
                                      element
                                      *all-concrete-syntax-rules*)
                (equal (element-kind element) :group)
                (consp (element-group->get element))
                (not (consp (cdr (element-group->get element))))
                (consp (car (element-group->get element)))
                (equal (car (car (element-group->get element)))
                       (repetition (repeat-range 1 (nati-finite 1))
                                   (element-char-val
                                    (char-val-insensitive "-")))))
           (mv-nth 0 (parse-ichar #\. (append (tree->string tree) rest-input))))
  :use (constraints-from-tree-match-dash-etc.
        (:instance constraints-from-parse-ichar
                   (char #\.)
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-bit-when-match-bin-val-rest
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('BIT') and
          @('[ 1*(\".\" 1*BIT) / (\"-\" 1*BIT) ]')
          not followed by @('BIT')."
  (implies (and (tree-match-element-p tree
                                      (?_ (/_ (1*_ (!_ (/_ "."
                                                           (1*_ *bit*)))))
                                          (/_ (!_ (/_ "-"
                                                      (1*_ *bit*)))))
                                      *all-concrete-syntax-rules*)
                (mv-nth 0 (parse-bit rest-input)))
           (mv-nth 0 (parse-bit (append (tree->string tree) rest-input))))
  :use (constraints-from-tree-match-bin-val-rest-when-nonempty
        (:instance constraints-from-parse-bit
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-digit-when-match-dec-val-rest
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('DIGIT') and
          @('[ 1*(\".\" 1*DIGIT) / (\"-\" 1*DIGIT) ]')
          not followed by @('DIGIT')."
  (implies (and (tree-match-element-p tree
                                      (?_ (/_ (1*_ (!_ (/_ "."
                                                           (1*_ *digit*)))))
                                          (/_ (!_ (/_ "-"
                                                      (1*_ *digit*)))))
                                      *all-concrete-syntax-rules*)
                (mv-nth 0 (parse-digit rest-input)))
           (mv-nth 0 (parse-digit (append (tree->string tree) rest-input))))
  :use (constraints-from-tree-match-dec-val-rest-when-nonempty
        (:instance constraints-from-parse-digit
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-hexdig-when-match-hex-val-rest
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('HEXDIG') and
          @('[ 1*(\".\" 1*HEXDIG) / (\"-\" 1*HEXDIG) ]')
          not followed by @('HEXDIG')."
  (implies (and (tree-match-element-p tree
                                      (?_ (/_ (1*_ (!_ (/_ "."
                                                           (1*_ *hexdig*)))))
                                          (/_ (!_ (/_ "-"
                                                      (1*_ *hexdig*)))))
                                      *all-concrete-syntax-rules*)
                (mv-nth 0 (parse-hexdig rest-input)))
           (mv-nth 0 (parse-hexdig (append (tree->string tree)
                                           rest-input))))
  :use (constraints-from-tree-match-hex-val-rest-when-nonempty
        (:instance constraints-from-parse-hexdig
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-bin-val-when-match-dec/hex-val
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('bin-val') and
          any of @('dec-val') and @('hex-val')."
  (implies (and (tree-match-element-p tree element *all-concrete-syntax-rules*)
                (member-equal element (list (element-rulename *dec-val*)
                                            (element-rulename *hex-val*)))
                (tree-terminatedp tree))
           (mv-nth 0 (parse-bin-val (append (tree->string tree)
                                            rest-input))))
  :use (constraints-from-tree-match-dec-val
        constraints-from-tree-match-hex-val
        (:instance constraints-from-parse-bin-val
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-dec-val-when-match-hex-val
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('dec-val') and @('hex-val')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *hex-val*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (mv-nth 0 (parse-dec-val (append (tree->string tree)
                                            rest-input))))
  :use (constraints-from-tree-match-hex-val
        (:instance constraints-from-parse-dec-val
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-either-range-when-match-dquote
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(%x20-21 / %x23-7E)') and @('DQUOTE')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *dquote*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (mv-nth 0 (parse-in-either-range #x20 #x21 #x23 #x7e
                                            (append (tree->string tree)
                                                    rest-input))))
  :use (constraints-from-tree-match-dquote
        (:instance constraints-from-parse-in-either-range
                   (min1 #x20)
                   (max1 #x21)
                   (min2 #x23)
                   (max2 #x7e)
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-%i-when-match-quoted-string
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('\"%i\"') and @('quoted-string')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *quoted-string*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (mv-nth 0 (parse-ichars #\% #\i (append (tree->string tree)
                                                   rest-input))))
  :use (constraints-from-tree-match-quoted-string
        (:instance constraints-from-parse-ichars
                   (char1 #\%)
                   (char2 #\i)
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-case-insensitive-string-when-match-case-sensitive-string
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('case-insensitive-string') and
          @('case-sensitive-string')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *case-sensitive-string*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (mv-nth 0 (parse-case-insensitive-string (append (tree->string tree)
                                                            rest-input))))
  :cases ((consp (cdr (tree->string tree))))
  :use (constraints-from-tree-match-case-sensitive-string
        (:instance constraints-from-parse-case-insensitive-string
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-wsp-when-match-vchar-/-rule-/-cnl-wsp
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('WSP') and
          any of @('VCHAR'), @('rule'), and @('(c-nl WSP)')."
  (implies (and (tree-match-element-p tree element *all-concrete-syntax-rules*)
                (member-equal element (list (element-rulename *vchar*)
                                            (element-rulename *rule*)
                                            (!_ (/_ *c-nl* *wsp*))))
                (tree-terminatedp tree))
           (mv-nth 0 (parse-wsp (append (tree->string tree) rest-input))))
  :use (constraints-from-tree-match-vchar
        constraints-from-tree-match-rule
        constraints-from-tree-match-cnl-wsp
        (:instance constraints-from-parse-wsp
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-wsp/vchar-when-match-crlf
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(WSP / VCHAR)') and @('CRLF')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *crlf*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (mv-nth 0 (parse-wsp/vchar (append (tree->string tree)
                                              rest-input))))
  :use (constraints-from-tree-match-crlf
        (:instance constraints-from-parse-wsp/vchar
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-comment-when-match-crlf
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('comment') and @('CRLF')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *crlf*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (mv-nth 0 (parse-comment (append (tree->string tree) rest-input))))
  :use (constraints-from-tree-match-crlf
        (:instance constraints-from-parse-comment
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-digit-when-match-star/dash
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('DIGIT') and
          any of @('\"*\"') and @('\"-\"')."
  (implies (and (tree-match-element-p tree element *all-concrete-syntax-rules*)
                (member-equal element (list (element-char-val
                                             (char-val-insensitive "*"))
                                            (element-char-val
                                             (char-val-insensitive "-")))))
           (mv-nth 0 (parse-digit (append (tree->string tree) rest-input))))
  :use ((:instance constraints-from-tree-match-ichars
                   (charstring "*"))
        (:instance constraints-from-tree-match-ichars
                   (charstring "-"))
        (:instance constraints-from-parse-digit
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-alpha-when-match-digit/dash
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('ALPHA') and
          any of @('DIGIT') and @('\"-\"')."
  (implies (and (tree-match-element-p tree
                                      element
                                      *all-concrete-syntax-rules*)
                (member-equal element (list (element-rulename *digit*)
                                            (element-char-val
                                             (char-val-insensitive "-"))))
                (tree-terminatedp tree))
           (mv-nth 0 (parse-alpha (append (tree->string tree) rest-input))))
  :use (constraints-from-tree-match-digit
        (:instance constraints-from-tree-match-ichars
                   (charstring "-"))
        (:instance constraints-from-parse-alpha
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-cwsp-when-match-slash-/-close-round/square
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('c-wsp') and
          any of @('\"/\"'), @('\")\"'), and @('\"]\"')."
  (implies (and (tree-match-element-p tree element *all-concrete-syntax-rules*)
                (member-equal element (list (element-char-val
                                             (char-val-insensitive "/"))
                                            (element-char-val
                                             (char-val-insensitive ")"))
                                            (element-char-val
                                             (char-val-insensitive "]")))))
           (mv-nth 0 (parse-cwsp (append (tree->string tree) rest-input))))
  :use ((:instance constraints-from-tree-match-ichars
                   (charstring "/"))
        (:instance constraints-from-tree-match-ichars
                   (charstring ")"))
        (:instance constraints-from-tree-match-ichars
                   (charstring "]"))
        (:instance constraints-from-parse-cwsp
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-cwsp-when-match-equal-/-equal-slash
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('c-wsp') and
          any of @('\"=\"') and @('\"=/\"')."
  (implies (tree-match-element-p tree
                                 (!_ (/_ "=")
                                     (/_ "=/"))
                                 *all-concrete-syntax-rules*)
           (mv-nth 0 (parse-cwsp (append (tree->string tree) rest-input))))
  :use (constraints-from-tree-match-equal-/-equal-slash
        (:instance constraints-from-parse-cwsp
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-cwsp-when-match-elements
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('c-wsp') and @('elements')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *elements*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (mv-nth 0 (parse-cwsp (append (tree->string tree) rest-input))))
  :use (constraints-from-tree-match-elements
        (:instance constraints-from-parse-cwsp
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-cwsp-when-match-alt/conc/rep
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('c-wsp') and
          any of @('alternation'), @('concatenation'), and @('repetition')."
  (implies (and (tree-match-element-p tree element *all-concrete-syntax-rules*)
                (member-equal element (list (element-rulename *alternation*)
                                            (element-rulename *concatenation*)
                                            (element-rulename *repetition*)))
                (tree-terminatedp tree))
           (mv-nth 0 (parse-cwsp (append (tree->string tree) rest-input))))
  :use (constraints-from-tree-match-alternation
        constraints-from-tree-match-concatenation
        constraints-from-tree-match-repetition
        (:instance constraints-from-parse-cwsp
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-1*cwsp-when-match-slash-/-close-round/square
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('1*c-wsp') and
          any of @('\"/\"'), @('\")\"'), and @('\"]\"')."
  (implies (and (tree-match-element-p tree element *all-concrete-syntax-rules*)
                (member-equal element (list (element-char-val
                                             (char-val-insensitive "/"))
                                            (element-char-val
                                             (char-val-insensitive ")"))
                                            (element-char-val
                                             (char-val-insensitive "]")))))
           (mv-nth 0 (parse-1*cwsp (append (tree->string tree) rest-input))))
  :use ((:instance constraints-from-tree-match-ichars
                   (charstring "/"))
        (:instance constraints-from-tree-match-ichars
                   (charstring ")"))
        (:instance constraints-from-tree-match-ichars
                   (charstring "]"))
        (:instance constraints-from-parse-1*cwsp
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-repetition-when-match-slash-/-close-round/square
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('repetition') and
          any of @('\"/\"'), @('\")\"'), and @('\"]\"')."
  (implies (and (tree-match-element-p tree element *all-concrete-syntax-rules*)
                (member-equal element (list (element-char-val
                                             (char-val-insensitive "/"))
                                            (element-char-val
                                             (char-val-insensitive ")"))
                                            (element-char-val
                                             (char-val-insensitive "]")))))
           (mv-nth 0 (parse-repetition (append (tree->string tree)
                                               rest-input))))
  :use ((:instance constraints-from-tree-match-ichars
                   (charstring "/"))
        (:instance constraints-from-tree-match-ichars
                   (charstring ")"))
        (:instance constraints-from-tree-match-ichars
                   (charstring "]"))
        (:instance constraints-from-parse-repetition
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-alpha/digit/dash-when-match-slash-/-close-round/square
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(ALPHA / DIGIT / \"-\")') and
          any of @('\"/\"'), @('\")\"'), and @('\"]\"')."
  (implies (and (tree-match-element-p tree element *all-concrete-syntax-rules*)
                (member-equal element (list (element-char-val
                                             (char-val-insensitive "/"))
                                            (element-char-val
                                             (char-val-insensitive ")"))
                                            (element-char-val
                                             (char-val-insensitive "]")))))
           (mv-nth 0 (parse-alpha/digit/dash (append (tree->string tree)
                                                     rest-input))))
  :use ((:instance constraints-from-tree-match-ichars
                   (charstring "/"))
        (:instance constraints-from-tree-match-ichars
                   (charstring ")"))
        (:instance constraints-from-tree-match-ichars
                   (charstring "]"))
        (:instance constraints-from-parse-alpha/digit/dash
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-alpha/digit/dash-when-match-cnl
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(ALPHA / DIGIT / \"-\")') and @('c-nl')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *c-nl*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (mv-nth 0 (parse-alpha/digit/dash (append (tree->string tree)
                                                     rest-input))))
  :use (constraints-from-tree-match-cnl
        (:instance constraints-from-parse-alpha/digit/dash
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-alpha/digit/dash-when-match-cwsp
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(ALPHA / DIGIT / \"-\")') and @('c-wsp')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *c-wsp*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (mv-nth 0 (parse-alpha/digit/dash (append (tree->string tree)
                                                     rest-input))))
  :use (constraints-from-tree-match-cwsp
        (:instance constraints-from-parse-alpha/digit/dash
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-alpha/digit/dash-when-match-*cwsp
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(ALPHA / DIGIT / \"-\")') and
          @('*c-wsp') not followed by @('(ALPHA / DIGIT / \"-\")')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *c-wsp*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-alpha/digit/dash rest-input)))
           (mv-nth 0 (parse-alpha/digit/dash (append (tree-list->string trees)
                                                     rest-input))))
  :enable (tree-list-match-repetition-p
           fail-alpha/digit/dash-when-match-cwsp))

(defruled fail-alpha/digit/dash-when-match-alt-rest-comp
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(ALPHA / DIGIT / \"-\")') and
          @('(*c-wsp \"/\" *c-wsp concatenation)')."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ (*_ *c-wsp*)
                                              "/"
                                              (*_ *c-wsp*)
                                              *concatenation*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (mv-nth 0 (parse-alpha/digit/dash (append (tree->string tree)
                                                     rest-input))))
  :expand ((:free (element rules) (tree-match-element-p tree element rules))
           (tree->string tree)
           (tree-list->string (car (tree-nonleaf->branches tree)))
           (tree-list-list->string (tree-nonleaf->branches tree)))
  :enable (tree-list-match-repetition-p
           tree-list-match-repetition-p-of-1-repetition
           tree-list->string
           tree-list-list->string
           tree-terminatedp
           fail-alpha/digit/dash-when-match-slash-/-close-round/square
           fail-alpha/digit/dash-when-match-cwsp))

(defruled fail-alpha/digit/dash-when-match-alt-rest
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(ALPHA / DIGIT / \"-\")') and
          @('*(*c-wsp \"/\" *c-wsp concatenation)')
          not followed by @('(ALPHA / DIGIT / \"-\")')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ (*_ *c-wsp*)
                                                          "/"
                                                          (*_ *c-wsp*)
                                                          *concatenation*)))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-alpha/digit/dash rest-input)))
           (mv-nth 0 (parse-alpha/digit/dash (append (tree-list->string trees)
                                                     rest-input))))
  :enable (tree-list-match-repetition-p
           fail-alpha/digit/dash-when-match-alt-rest-comp))

(defruled fail-alpha/digit/dash-when-match-conc-rest-comp
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(ALPHA / DIGIT / \"-\")') and
          @('(1*c-wsp repetition)')."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ (1*_ *c-wsp*)
                                              *repetition*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (mv-nth 0 (parse-alpha/digit/dash (append (tree->string tree)
                                                     rest-input))))
  :enable (tree-match-element-p
           tree-list-match-repetition-p-of-1+-repetitions
           tree->string
           tree-list->string
           tree-list-list->string
           tree-terminatedp
           fail-alpha/digit/dash-when-match-cwsp))

(defruled fail-alpha/digit/dash-when-match-conc-rest
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(ALPHA / DIGIT / \"-\")') and
          @('*(1*c-wsp repetition)')
          not followed by @('(ALPHA / DIGIT / \"-\")')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ (1*_ *c-wsp*)
                                                          *repetition*)))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-alpha/digit/dash rest-input)))
           (mv-nth 0 (parse-alpha/digit/dash (append (tree-list->string trees)
                                                     rest-input))))
  :enable (tree-list-match-repetition-p
           fail-alpha/digit/dash-when-match-conc-rest-comp))

(defruled fail-alpha/digit/dash-when-match-*cwsp-close-round/square
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(ALPHA / DIGIT / \"-\")') and
          @('*c-wsp') followed by @('\")\"') or @('\"]\"')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *c-wsp*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (tree-match-element-p tree element *all-concrete-syntax-rules*)
                (member-equal element (list (element-char-val
                                             (char-val-insensitive ")"))
                                            (element-char-val
                                             (char-val-insensitive "]")))))
           (mv-nth 0 (parse-alpha/digit/dash
                      (append (tree-list->string trees)
                              (tree->string tree)
                              rest-input))))
  :expand (tree-list->string trees)
  :enable (tree-list-match-repetition-p
           fail-alpha/digit/dash-when-match-slash-/-close-round/square
           fail-alpha/digit/dash-when-match-cwsp))

(defruled fail-alpha/digit/dash-when-match-defined-as
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(ALPHA / DIGIT / \"-\")') and
          @('defined-as')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *defined-as*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (mv-nth 0 (parse-alpha/digit/dash (append (tree->string tree)
                                                     rest-input))))
  :use (constraints-from-tree-match-defined-as
        (:instance constraints-from-parse-alpha/digit/dash
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-bit/digit/hexdig/dot/dash-when-match-slash
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between (i) any of
          @('BIT'), @('DIGIT'), @('HEXDIG'), @('\".\"'), and @('\"-\"') and
          (ii) @('\"/\"')."
  (implies (tree-match-element-p tree
                                 (element-char-val (char-val-insensitive "/"))
                                 *all-concrete-syntax-rules*)
           (and (mv-nth 0 (parse-bit (append (tree->string tree)
                                             rest-input)))
                (mv-nth 0 (parse-digit (append (tree->string tree)
                                               rest-input)))
                (mv-nth 0 (parse-hexdig (append (tree->string tree)
                                                rest-input)))
                (mv-nth 0 (parse-ichar #\. (append (tree->string tree)
                                                   rest-input)))
                (mv-nth 0 (parse-ichar #\- (append (tree->string tree)
                                                   rest-input)))))
  :use ((:instance constraints-from-tree-match-ichars
                   (charstring "/"))
        (:instance constraints-from-parse-bit
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-digit
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-hexdig
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-ichar
                   (char #\.)
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-ichar
                   (char #\-)
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-bit/digit/hexdig/dot/dash-when-match-cnl
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between (i) any of
          @('BIT'), @('DIGIT'), @('HEXDIG'), @('\".\"'), and @('\"-\"') and
          (ii) @('c-nl')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *c-nl*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (and (mv-nth 0 (parse-bit (append (tree->string tree)
                                             rest-input)))
                (mv-nth 0 (parse-digit (append (tree->string tree)
                                               rest-input)))
                (mv-nth 0 (parse-hexdig (append (tree->string tree)
                                                rest-input)))
                (mv-nth 0 (parse-ichar #\. (append (tree->string tree)
                                                   rest-input)))
                (mv-nth 0 (parse-ichar #\- (append (tree->string tree)
                                                   rest-input)))))
  :use (constraints-from-tree-match-cnl
        (:instance constraints-from-parse-bit
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-digit
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-hexdig
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-ichar
                   (char #\.)
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-ichar
                   (char #\-)
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-bit/digit/hexdig/dot/dash-when-match-cwsp
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between (i) any of
          @('BIT'), @('DIGIT'), @('HEXDIG'), @('\".\"'), and @('\"-\"') and
          (ii) @('c-wsp')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *c-wsp*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (and (mv-nth 0 (parse-bit (append (tree->string tree)
                                             rest-input)))
                (mv-nth 0 (parse-digit (append (tree->string tree)
                                               rest-input)))
                (mv-nth 0 (parse-hexdig (append (tree->string tree)
                                                rest-input)))
                (mv-nth 0 (parse-ichar #\. (append (tree->string tree)
                                                   rest-input)))
                (mv-nth 0 (parse-ichar #\- (append (tree->string tree)
                                                   rest-input)))))
  :use (constraints-from-tree-match-cwsp
        (:instance constraints-from-parse-bit
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-digit
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-hexdig
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-ichar
                   (char #\.)
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-ichar
                   (char #\-)
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-bit/digit/hexdig/dot/dash-when-match-alt-rest-comp
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between (i) any of
          @('BIT'), @('DIGIT'), @('HEXDIG'), @('\".\"'), and @('\"-\"') and
          (ii) @('(*c-wsp \"/\" *c-wsp concatenation)')."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ (*_ *c-wsp*)
                                              "/"
                                              (*_ *c-wsp*)
                                              *concatenation*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (and (mv-nth 0 (parse-bit (append (tree->string tree)
                                             rest-input)))
                (mv-nth 0 (parse-digit (append (tree->string tree)
                                               rest-input)))
                (mv-nth 0 (parse-hexdig (append (tree->string tree)
                                                rest-input)))
                (mv-nth 0 (parse-ichar #\. (append (tree->string tree)
                                                   rest-input)))
                (mv-nth 0 (parse-ichar #\- (append (tree->string tree)
                                                   rest-input)))))
  :expand ((tree->string tree)
           (tree-list->string (car (tree-nonleaf->branches tree)))
           (tree-list-list->string (tree-nonleaf->branches tree)))
  :enable (tree-match-element-p
           tree-list-match-repetition-p
           tree-list->string
           tree-list-list->string
           tree-terminatedp
           tree-list-match-repetition-p-of-1-repetition
           fail-bit/digit/hexdig/dot/dash-when-match-slash
           fail-bit/digit/hexdig/dot/dash-when-match-cwsp))

(defruled fail-bit/digit/hexdig/dot/dash-when-match-conc-rest-comp
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between (i) any of
          @('BIT'), @('DIGIT'), @('HEXDIG'), @('\".\"'), and @('\"-\"') and
          (ii) @('(1*c-wsp repetition)')."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ (1*_ *c-wsp*)
                                              *repetition*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (and (mv-nth 0 (parse-bit (append (tree->string tree)
                                             rest-input)))
                (mv-nth 0 (parse-digit (append (tree->string tree)
                                               rest-input)))
                (mv-nth 0 (parse-hexdig (append (tree->string tree)
                                                rest-input)))
                (mv-nth 0 (parse-ichar #\. (append (tree->string tree)
                                                   rest-input)))
                (mv-nth 0 (parse-ichar #\- (append (tree->string tree)
                                                   rest-input)))))
  :enable (tree-match-element-p
           tree-list-match-repetition-p-of-1+-repetitions
           tree->string
           tree-list->string
           tree-list-list->string
           tree-terminatedp
           fail-bit/digit/hexdig/dot/dash-when-match-cwsp))

(defruled fail-bit/digit/hexdig/dot/dash-when-match-close-round/square
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between (i) any of
          @('BIT'), @('DIGIT'), @('HEXDIG'), @('\".\"'), and @('\"-\"') and
          (ii) any of @('\")\"') and @('\"]\"')."
  (implies (and (tree-match-element-p tree element *all-concrete-syntax-rules*)
                (member-equal element (list (element-char-val
                                             (char-val-insensitive ")"))
                                            (element-char-val
                                             (char-val-insensitive "]")))))
           (and (mv-nth 0 (parse-bit (append (tree->string tree)
                                             rest-input)))
                (mv-nth 0 (parse-digit (append (tree->string tree)
                                               rest-input)))
                (mv-nth 0 (parse-hexdig (append (tree->string tree)
                                                rest-input)))
                (mv-nth 0 (parse-ichar #\. (append (tree->string tree)
                                                   rest-input)))
                (mv-nth 0 (parse-ichar #\- (append (tree->string tree)
                                                   rest-input)))))
  :use ((:instance constraints-from-tree-match-ichars
                   (charstring ")"))
        (:instance constraints-from-tree-match-ichars
                   (charstring "]"))
        (:instance constraints-from-parse-bit
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-digit
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-hexdig
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-ichar
                   (char #\.)
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-ichar
                   (char #\-)
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-bit/digit/hexdig/dot/dash-when-match-*cwsp-close-round/square
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between (i) any of
          @('BIT'), @('DIGIT'), @('HEXDIG'), @('\".\"'), and @('\"-\"') and
          (ii) @('*c-wsp') followed by @('\")\"') or @('\"]\"')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *c-wsp*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (tree-match-element-p tree element *all-concrete-syntax-rules*)
                (member-equal element (list (element-char-val
                                             (char-val-insensitive ")"))
                                            (element-char-val
                                             (char-val-insensitive "]")))))
           (and (mv-nth 0 (parse-bit (append (tree-list->string trees)
                                             (tree->string tree)
                                             rest-input)))
                (mv-nth 0 (parse-digit (append (tree-list->string trees)
                                               (tree->string tree)
                                               rest-input)))
                (mv-nth 0 (parse-hexdig (append (tree-list->string trees)
                                                (tree->string tree)
                                                rest-input)))
                (mv-nth 0 (parse-ichar #\. (append (tree-list->string trees)
                                                   (tree->string tree)
                                                   rest-input)))
                (mv-nth 0 (parse-ichar #\- (append (tree-list->string trees)
                                                   (tree->string tree)
                                                   rest-input)))))
  :expand (tree-list->string trees)
  :enable (tree-list-match-repetition-p
           fail-bit/digit/hexdig/dot/dash-when-match-close-round/square
           fail-bit/digit/hexdig/dot/dash-when-match-cwsp))

(defruled fail-bit-when-match-alt-rest
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('BIT') and
          @('*(*c-wsp \"/\" *c-wsp concatenation)')
          not followed by @('BIT')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ (*_ *c-wsp*)
                                                          "/"
                                                          (*_ *c-wsp*)
                                                          *concatenation*)))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-bit rest-input)))
           (mv-nth 0 (parse-bit (append (tree-list->string trees)
                                        rest-input))))
  :enable (tree-list-match-repetition-p
           fail-bit/digit/hexdig/dot/dash-when-match-alt-rest-comp))

(defruled fail-digit-when-match-alt-rest
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('DIGIT') and
          @('*(*c-wsp \"/\" *c-wsp concatenation)')
          not followed by @('DIGIT')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ (*_ *c-wsp*)
                                                          "/"
                                                          (*_ *c-wsp*)
                                                          *concatenation*)))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-digit rest-input)))
           (mv-nth 0 (parse-digit (append (tree-list->string trees)
                                          rest-input))))
  :enable (tree-list-match-repetition-p
           fail-bit/digit/hexdig/dot/dash-when-match-alt-rest-comp))

(defruled fail-hexdig-when-match-alt-rest
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('HEXDIG') and
          @('*(*c-wsp \"/\" *c-wsp concatenation)')
          not followed by @('HEXDIG')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ (*_ *c-wsp*)
                                                          "/"
                                                          (*_ *c-wsp*)
                                                          *concatenation*)))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-hexdig rest-input)))
           (mv-nth 0 (parse-hexdig (append (tree-list->string trees)
                                           rest-input))))
  :enable (tree-list-match-repetition-p
           fail-bit/digit/hexdig/dot/dash-when-match-alt-rest-comp))

(defruled fail-dot-when-match-alt-rest
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('\".\"') and
          @('*(*c-wsp \"/\" *c-wsp concatenation)')
          not followed by @('\".\"')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ (*_ *c-wsp*)
                                                          "/"
                                                          (*_ *c-wsp*)
                                                          *concatenation*)))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-ichar #\. rest-input)))
           (mv-nth 0 (parse-ichar #\. (append (tree-list->string trees)
                                              rest-input))))
  :enable (tree-list-match-repetition-p
           fail-bit/digit/hexdig/dot/dash-when-match-alt-rest-comp))

(defruled fail-dash-when-match-alt-rest
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('\"-\"') and
          @('*(*c-wsp \"/\" *c-wsp concatenation)')
          not followed by @('\"-\"')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ (*_ *c-wsp*)
                                                          "/"
                                                          (*_ *c-wsp*)
                                                          *concatenation*)))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (mv-nth 0 (parse-ichar #\- (append (tree-list->string trees)
                                              rest-input))))
  :enable (tree-list-match-repetition-p
           fail-bit/digit/hexdig/dot/dash-when-match-alt-rest-comp))

(defruled fail-bit-when-match-conc-rest
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('BIT') and
          @('*(1*c-wsp repetition)')
          not followed by @('BIT')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ (1*_ *c-wsp*)
                                                          *repetition*)))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-bit rest-input)))
           (mv-nth 0 (parse-bit (append (tree-list->string trees)
                                        rest-input))))
  :enable (tree-list-match-repetition-p
           fail-bit/digit/hexdig/dot/dash-when-match-conc-rest-comp))

(defruled fail-digit-when-match-conc-rest
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('DIGIT') and
          @('*(1*c-wsp repetition)')
          not followed by @('DIGIT')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ (1*_ *c-wsp*)
                                                          *repetition*)))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-digit rest-input)))
           (mv-nth 0 (parse-digit (append (tree-list->string trees)
                                          rest-input))))
  :enable (tree-list-match-repetition-p
           fail-bit/digit/hexdig/dot/dash-when-match-conc-rest-comp))

(defruled fail-hexdig-when-match-conc-rest
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('HEXDIG') and
          @('*(1*c-wsp repetition)')
          not followed by @('HEXDIG')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ (1*_ *c-wsp*)
                                                          *repetition*)))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-hexdig rest-input)))
           (mv-nth 0 (parse-hexdig (append (tree-list->string trees)
                                           rest-input))))
  :enable (tree-list-match-repetition-p
           fail-bit/digit/hexdig/dot/dash-when-match-conc-rest-comp))

(defruled fail-dot-when-match-conc-rest
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('\".\"') and
          @('*(1*c-wsp repetition)')
          not followed by @('\".\"')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ (1*_ *c-wsp*)
                                                          *repetition*)))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-ichar #\. rest-input)))
           (mv-nth 0 (parse-ichar #\. (append (tree-list->string trees)
                                              rest-input))))
  :enable (tree-list-match-repetition-p
           fail-bit/digit/hexdig/dot/dash-when-match-conc-rest-comp))

(defruled fail-dash-when-match-conc-rest
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('\"-\"') and
          @('*(1*c-wsp repetition)')
          not followed by @('\"-\"')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ (1*_ *c-wsp*)
                                                          *repetition*)))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (mv-nth 0 (parse-ichar #\- (append (tree-list->string trees)
                                              rest-input))))
  :enable (tree-list-match-repetition-p
           fail-bit/digit/hexdig/dot/dash-when-match-conc-rest-comp))

(defruled fail-bit-when-match-*cwsp
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('BIT') and
          @('*c-wsp') not followed by @('BIT')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *c-wsp*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-bit rest-input)))
           (mv-nth 0 (parse-bit (append (tree-list->string trees)
                                        rest-input))))
  :enable (tree-list-match-repetition-p
           fail-bit/digit/hexdig/dot/dash-when-match-cwsp))

(defruled fail-digit-when-match-*cwsp
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('DIGIT') and
          @('*c-wsp') not followed by @('DIGIT')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *c-wsp*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-digit rest-input)))
           (mv-nth 0 (parse-digit (append (tree-list->string trees)
                                          rest-input))))
  :enable (tree-list-match-repetition-p
           fail-bit/digit/hexdig/dot/dash-when-match-cwsp))

(defruled fail-hexdig-when-match-*cwsp
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('HEXDIG') and
          @('*c-wsp') not followed by @('HEXDIG')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *c-wsp*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-hexdig rest-input)))
           (mv-nth 0 (parse-hexdig (append (tree-list->string trees)
                                           rest-input))))
  :enable (tree-list-match-repetition-p
           fail-bit/digit/hexdig/dot/dash-when-match-cwsp))

(defruled fail-dot-when-match-*cwsp
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('\".\"') and
          @('*c-wsp') not followed by @('\".\"')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *c-wsp*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-ichar #\. rest-input)))
           (mv-nth 0 (parse-ichar #\. (append (tree-list->string trees)
                                              rest-input))))
  :enable (tree-list-match-repetition-p
           fail-bit/digit/hexdig/dot/dash-when-match-cwsp))

(defruled fail-dash-when-match-*cwsp
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('\"-\"') and
          @('*c-wsp') not followed by @('\"=\"')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *c-wsp*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (mv-nth 0 (parse-ichar #\- (append (tree-list->string trees)
                                              rest-input))))
  :enable (tree-list-match-repetition-p
           fail-bit/digit/hexdig/dot/dash-when-match-cwsp))

(defruled fail-slash-when-match-*cwsp
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('\"/\"') and
          @('*c-wsp') not followed by @('\"/\"')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *c-wsp*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-ichar #\/ rest-input)))
           (mv-nth 0 (parse-ichar #\/ (append (tree-list->string trees)
                                              rest-input))))
  :use ((:instance constraints-from-tree-match-cwsp
                   (tree (car trees)))
        (:instance constraints-from-parse-ichar
                   (char #\/)
                   (input (append (tree-list->string trees) rest-input))))
  :enable tree-list-match-repetition-p-of-0+-reps-when-consp)

(defruled fail-slash-when-match-elements
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('\"/\"') and @('elements')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *elements*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (mv-nth 0 (parse-ichar #\/ (append (tree->string tree) rest-input))))
  :use (constraints-from-tree-match-elements
        (:instance constraints-from-parse-ichar
                   (char #\/)
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-digit/star-when-match-element
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between (i) any of @('DIGIT') and @('\"*\"') and
          (ii) @('element')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *element*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (and (mv-nth 0 (parse-digit (append (tree->string tree)
                                               rest-input)))
                (mv-nth 0 (parse-ichar #\* (append (tree->string tree)
                                                   rest-input)))))
  :use (constraints-from-tree-match-element
        (:instance constraints-from-parse-digit
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-ichar
                   (char #\*)
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-num-val-when-match-prose-val
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('num-val') and @('prose-val')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *prose-val*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (mv-nth 0 (parse-num-val (append (tree->string tree) rest-input))))
  :use (constraints-from-tree-match-prose-val
        (:instance constraints-from-parse-num-val
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-char-val-when-match-num/prose-val
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('char-val') and
          any of @('num-val') and @('prose-val')."
  (implies (and (tree-match-element-p tree
                                      element
                                      *all-concrete-syntax-rules*)
                (member-equal element (list (element-rulename *num-val*)
                                            (element-rulename *prose-val*)))
                (tree-terminatedp tree))
           (mv-nth 0 (parse-char-val (append (tree->string tree) rest-input))))
  :cases ((consp (cdr (tree->string tree))))
  :use (constraints-from-tree-match-num-val
        constraints-from-tree-match-prose-val
        (:instance constraints-from-parse-char-val
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-option-when-match-char/num/prose-val
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('option') and
          any of @('char-val'), @('num-val'), and @('prose-val')."
  (implies (and (tree-match-element-p tree
                                      element
                                      *all-concrete-syntax-rules*)
                (member-equal element (list (element-rulename *char-val*)
                                            (element-rulename *num-val*)
                                            (element-rulename *prose-val*)))
                (tree-terminatedp tree))
           (mv-nth 0 (parse-option (append (tree->string tree) rest-input))))
  :use (constraints-from-tree-match-char-val
        constraints-from-tree-match-num-val
        constraints-from-tree-match-prose-val
        (:instance constraints-from-parse-option
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-group-when-match-option-/-char/num/prose-val
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('group') and
          any of @('option'), @('char-val'), @('num-val'), and @('prose-val')."
  (implies (and (tree-match-element-p tree
                                      element
                                      *all-concrete-syntax-rules*)
                (member-equal element (list (element-rulename *option*)
                                            (element-rulename *char-val*)
                                            (element-rulename *num-val*)
                                            (element-rulename *prose-val*)))
                (tree-terminatedp tree))
           (mv-nth 0 (parse-group (append (tree->string tree) rest-input))))
  :use (constraints-from-tree-match-option
        constraints-from-tree-match-char-val
        constraints-from-tree-match-num-val
        constraints-from-tree-match-prose-val
        (:instance constraints-from-parse-group
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-rulename-when-match-group/option-/-char/num/prose-val
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('rulename') and
          any of
          @('group'),
          @('option'),
          @('char-val'),
          @('num-val'), and
          @('prose-val')."
  (implies (and (tree-match-element-p tree
                                      element
                                      *all-concrete-syntax-rules*)
                (member-equal element (list (element-rulename *group*)
                                            (element-rulename *option*)
                                            (element-rulename *char-val*)
                                            (element-rulename *num-val*)
                                            (element-rulename *prose-val*)))
                (tree-terminatedp tree))
           (mv-nth 0 (parse-rulename (append (tree->string tree) rest-input))))
  :use (constraints-from-tree-match-group
        constraints-from-tree-match-option
        constraints-from-tree-match-char-val
        constraints-from-tree-match-num-val
        constraints-from-tree-match-prose-val
        (:instance constraints-from-parse-rulename
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-slash-when-match-close-round/square
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('\"/\"') and
          any of @('\")\"') and @('\"]\"')."
  (implies (and (tree-match-element-p tree element *all-concrete-syntax-rules*)
                (member-equal element (list (element-char-val
                                             (char-val-insensitive ")"))
                                            (element-char-val
                                             (char-val-insensitive "]")))))
           (mv-nth 0 (parse-ichar #\/ (append (tree->string tree) rest-input))))
  :use ((:instance constraints-from-tree-match-ichars
                   (charstring ")"))
        (:instance constraints-from-tree-match-ichars
                   (charstring "]"))
        (:instance constraints-from-parse-ichar
                   (char #\/)
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-equal-slash-when-match-equal-and-rest-fail-slash
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('\"=/\"') and
          @('\"=\"') not followed by @('\"/\"')."
  (implies (and (tree-match-element-p tree
                                      (element-char-val
                                       (char-val-insensitive "="))
                                      *all-concrete-syntax-rules*)
                (mv-nth 0 (parse-ichar #\/ rest-input)))
           (mv-nth 0 (parse-ichars #\= #\/ (append (tree->string tree)
                                                   rest-input))))
  :enable (tree-match-element-p
           tree-match-char-val-p
           parse-ichars
           parse-ichar
           parse-any
           tree->string))

(defruled fail-slash/htab/sp/wsp/rep-when-match-cnl
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between
          (i) any of
          @('\"/\"'),
          @('HTAB'),
          @('SP'),
          @('WSP'), and
          @('repetition') and
          (ii) @('c-nl')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *c-nl*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (and (mv-nth 0 (parse-ichar #\/ (append (tree->string tree)
                                                   rest-input)))
                (mv-nth 0 (parse-htab (append (tree->string tree)
                                              rest-input)))
                (mv-nth 0 (parse-sp (append (tree->string tree)
                                            rest-input)))
                (mv-nth 0 (parse-wsp (append (tree->string tree)
                                             rest-input)))
                (mv-nth 0 (parse-repetition (append (tree->string tree)
                                                    rest-input)))))
  :use (constraints-from-tree-match-cnl
        (:instance constraints-from-parse-ichar
                   (char #\/)
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-htab
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-sp
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-wsp
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-parse-repetition
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-rule-when-match-*cwsp-cnl
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('rule') and @('(*c-wsp c-nl)')."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ (*_ *c-wsp*)
                                              *c-nl*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (mv-nth 0 (parse-rule (append (tree->string tree) rest-input))))
  :cases ((consp (car (tree-nonleaf->branches tree))))
  :enable (tree-match-element-p
           tree-list-match-repetition-p-of-1-repetition
           tree-list-match-repetition-p-of-0+-reps-when-consp
           tree-terminatedp
           tree->string
           tree-list->string
           tree-list-list->string)
  :use ((:instance constraints-from-tree-match-cnl
                   (tree (caadr (tree-nonleaf->branches tree))))
        (:instance constraints-from-tree-match-cwsp
                   (tree (car (car (tree-nonleaf->branches tree)))))
        (:instance constraints-from-parse-rule
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-wsp-when-match-cwsp-and-restriction
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('WSP') and @('c-wsp'),
          when the tree satisfies the disambiguating restrictions."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *c-wsp*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (tree-cwsp-restriction-p tree))
           (mv-nth 0 (parse-wsp (append (tree->string tree) rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (tree-cwsp-restriction-p
           tree->string
           tree-list->string
           tree-list-list->string
           tree-terminatedp
           tree-list-match-repetition-p-of-1-repetition)
  :use ((:instance constraints-from-parse-wsp
                   (input (append (tree->string tree) rest-input)))
        (:instance constraints-from-tree-match-cnl-wsp
                   (tree (car (car (tree-nonleaf->branches tree)))))))

(defruled fail-wsp-when-match-*cwsp-cnl-and-restriction
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('WSP') and @('(*c-wsp c-nl)')
          when the tree satisfies the disambiguating restrictions."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ (*_ *c-wsp*)
                                              *c-nl*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (tree-*cwsp-cnl-restriction-p tree))
           (mv-nth 0 (parse-wsp (append (tree->string tree) rest-input))))
  :cases ((consp (car (tree-nonleaf->branches tree))))
  :enable (tree-match-element-p
           tree-list-match-repetition-p-of-1-repetition
           tree-list-match-repetition-p-of-0+-reps-when-consp
           tree-terminatedp
           tree->string
           tree-list->string
           tree-list-list->string
           tree-*cwsp-cnl-restriction-p
           fail-wsp-when-match-cwsp-and-restriction)
  :use ((:instance constraints-from-tree-match-cnl
                   (tree (car (cadr (tree-nonleaf->branches tree)))))
        (:instance constraints-from-tree-match-cwsp
                   (tree (car (car (tree-nonleaf->branches tree)))))
        (:instance constraints-from-parse-wsp
                   (input (append (tree->string tree) rest-input)))))

(defruled fail-wsp-when-match-rule-/-*cwsp-cnl-and-restriction
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('WSP') and
          any of @('rule') and @('(*c-wsp c-nl)'),
          when the tree satisfies the disambiguating restrictions."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ *rule*)
                                          (/_ (!_ (/_ (*_ *c-wsp*)
                                                      *c-nl*))))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (tree-rule-/-*cwsp-cnl-restriction-p tree))
           (mv-nth 0 (parse-wsp (append (tree->string tree) rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (tree-list-match-repetition-p-of-1-repetition
           tree-terminatedp
           tree->string
           tree-list->string
           tree-list-list->string
           tree-rule-/-*cwsp-cnl-restriction-p
           fail-wsp-when-match-vchar-/-rule-/-cnl-wsp
           fail-wsp-when-match-*cwsp-cnl-and-restriction))

(defruled fail-wsp-when-match-*-rule-/-*cwsp-cnl-and-restriction
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('WSP') and
          @('*( rule / (*c-wsp c-nl) )') not followed by @('WSP'),
          when the list of trees satisfies the disambiguating restrictions."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ *rule*)
                                                      (/_ (!_ (/_ (*_ *c-wsp*)
                                                                  *c-nl*)))))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (tree-list-*-rule-/-*cwsp-cnl-restriction-p trees)
                (mv-nth 0 (parse-wsp rest-input)))
           (mv-nth 0 (parse-wsp (append (tree-list->string trees) rest-input))))
  :enable (tree-list-*-rule-/-*cwsp-cnl-restriction-p
           tree-list-match-repetition-p
           fail-wsp-when-match-rule-/-*cwsp-cnl-and-restriction))

; enabled just before the disambiguation theorems:
(in-theory (disable nat-match-insensitive-char-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-parser-completeness

  :parents (grammar-parser-correctness)

  :short "Completeness theorems for the parser of ABNF grammars."

  :long

  (xdoc::topstring

   (xdoc::p
    "For every terminated tree rooted at @('rulelist')
     that satisfies the "
    (xdoc::seetopic "grammar-parser-disambiguating-restrictions"
                    "disambiguating restrictions")
    ", @(tsee parse-grammar) succeeds on the string at the leaves of the tree
     and returns that tree:
     @(def parse-grammar-when-tree-match)")

   (xdoc::p
    "This is proved by proving the following,
     for each parsing function out of which @(tsee parse-grammar) is built:
     if a (list of) terminated tree(s) matches a certain syntactic entity
     and possibly satisfies certain "
    (xdoc::seetopic "grammar-parser-disambiguating-restrictions"
                    "disambiguating restrictions")
    ", then running the parsing function on the @(tsee append) of
     (i) the string at the leaves of the tree(s) and
     (ii) some remaining input
     possibly satisfying certain hypotheses explained below,
     succeeds and yields that (list of) tree(s) and that remaining input.
     More precisely, the parsing function yields
     the (list of) tree(s) fixed with @(tsee tree-fix) or @(tsee tree-list-fix)
     and the remaining input fixed with @(tsee nat-list-fix);
     an alternative formulation is to avoid these fixing functions
     but include the hypotheses
     that the (list of) tree(s) satisfies @(tsee treep) or @(tsee tree-listp)
     and that the remaining input satisfies @(tsee nat-listp).")

   (xdoc::p
    "For example, the completeness theorem @(tsee parse-alpha-when-tree-match)
     says that running @(tsee parse-alpha) on the @(tsee append) of
     (i) the leaves of a terminated tree that matches @('ALPHA'), and
     (ii) some remaining input,
     succeeds and yields
     (the fixing of) that tree and (the fixing of) that remaining input.
     Since @('ALPHA') is not involved in the "
    (xdoc::seetopic "grammar-parser-disambiguating-restrictions"
                    "disambiguating restrictions")
    ", @(tsee parse-alpha-when-tree-match) has no hypothesis
     related to those disambiguating restrictions.
     This theorem also has no hypothesis on the remaining input,
     as explained below.")

   (xdoc::p
    "The completeness theorem of @(tsee parse-any)
     does not involve trees but makes an analogous statement:
     running @(tsee parse-any) on
     the @(tsee cons) of a natural number and some remaining natural numbers,
     returns (the fixing of) that natural number and
     (the fixing of) the remaining natural numbers.")

   (xdoc::h3 "Hypotheses on the Remaining Input")

   (xdoc::p
    "In all the completeness theorems,
     the remaining input (following the string at the leaves of the tree(s))
     is denoted by the variable @('rest-input').
     The hypotheses on the remaining input, when present,
     are that certain parsing functions fail on the remaining input.")

   (xdoc::p
    "If a parsing function ignores the remaining input,
     the corresponding completeness theorem
     has no hypotheses on the remaining input.
     This is the case for parsing functions that,
     like @(tsee parse-alpha) mentioned above,
     parse a fixed number of natural numbers from the input.
     This is also the case for
     parsing functions that parse a fixed number of natural numbers
     after parsing a variable number of natural numbers:
     for example,
     @(tsee parse-prose-val) always parses the closing angle bracket
     (which is a single character)
     after parsing a variable number of characters
     after parsing the opening angle bracket.")

   (xdoc::p
    "In contrast,
     if a parsing function ``examines'' (part of) the remaining input,
     the corresponding completeness theorem
     has hypotheses on the remaining input.
     If a parsing function examines part of the remaining input,
     but that part of the remaining input is absent from the returned tree(s)
     (by hypothesis of the function's completeness theorem),
     it means that the function attempts but fails
     to parse further into the remaining input,
     backtracking and returning a (list of) tree(s)
     only for the input that precedes the remaining input.
     Thus, the completeness theorem for the function
     must include hypotheses stating or implying such parsing failures.
     Without these hypotheses,
     parsing further into the remaining input might succeed,
     extending the tree(s) and rendering the theorem untrue.
     Some concrete examples are given below.")

   (xdoc::p
    "A parsing function for
     a repetition of zero or more instances of some syntactic entity
     always examines the remaining input to decide when to stop.
     The function's completeness theorem has a hypothesis on the remaining input
     stating or implying that
     parsing another instance of the syntactic entity fails.
     For example, @(tsee parse-*bit) stops when @(tsee parse-bit) fails;
     this parsing failure occurs in the remaining input.
     The completeness theorem @(tsee parse-*bit-when-tree-list-match)
     has the hypothesis that @(tsee parse-bit) fails on the remaining input.
     Without this hypothesis, the theorem would not hold because,
     if another @('BIT') could be parsed from the remaining input,
     then @(tsee parse-*bit) would return (at least) an additional tree
     beyond the list of trees hypothesized in the theorem.")

   (xdoc::p
    "A parsing function for an optional occurrence of some syntactic entity
     may examine the remaining input.
     This happens when parsing the syntactic entity fails,
     in which case the function returns a tree without leaves,
     because the optional entity is absent.
     The function's completeness theorem has a hypothesis on the remaining input
     stating or implying that parsing the syntactic entity fails.
     For example, @(tsee parse-?%i) may fail to parse @('\"%i\"');
     this parsing failure occurs in the remaining input,
     because the function returns a tree without leaves,
     reflecting the absence of the syntactic entity.
     The completeness theorem @(tsee parse-?%i-when-tree-match)
     has the hypothesis that @(tsee parse-ichars)
     (with arguments @('#\\%') and @('#\\i'))
     fails on the remaining input.
     Without this hypothesis, the theorem would not hold because,
     if @('\"%i\"') could be parsed from the remaining input
     but the tree hypothesized by the theorem had no leaves,
     then @(tsee parse-?%i) would return a tree with leaves instead.")

   (xdoc::p
    "The kind of hypothesis on the remaining input
     described in the previous paragraph,
     for the completeness theorems of parsing functions
     that parse optional entities,
     is stronger than needed.
     If the parsing function succeeds in parsing the optional entity,
     then it does not examine the remaining input, returning a tree with leaves.
     So the hypothesis on the remaining input could be weakened
     to require the parsing failure to happen only if the tree has no leaves.
     However, in syntactically valid ABNF grammars,
     the stronger hypothesis is always satisfied
     (e.g. @('[ \"%i\" ]') cannot be followed by @('\"%i\"')),
     so there is no loss in using the stronger hypothesis;
     the stronger hypothesis keeps the completeness theorems simpler
     without precluding the eventual proof
     of the top-level completeness theorem.")

   (xdoc::p
    "If a parsing function calls, or may call, another parsing function
     as its last action,
     the former's completeness theorem ``inherits''
     the hypotheses on the remaining input
     from the latter's completeness theorem.
     If the hypotheses were not inherited,
     the called function may successfully parse some of the remaining input,
     returning more or different subtrees
     than hypothesized by the calling function's completeness theorem,
     rendering the theorem untrue.
     For example,
     since @(tsee parse-1*bit) calls @(tsee parse-*bit) as its last action,
     @(tsee parse-1*bit-when-tree-list-match) inherits from
     @(tsee parse-*bit-when-tree-list-match)
     the hypothesis that @(tsee parse-bit) fails on the remaining input;
     otherwise, @(tsee parse-*bit) could return additional @('BIT') trees
     and so @(tsee parse-1*bit) could return additional @('BIT') trees as well.
     As another example,
     since @(tsee parse-dot-1*bit) calls @(tsee parse-1*bit) as its last action,
     @(tsee parse-dot-1*bit-when-tree-match) inherits from
     @(tsee parse-*bit-when-tree-list-match)
     the hypothesis that @(tsee parse-bit) fails on the remaining input;
     otherwise, @(tsee parse-1*bit) could return additional @('BIT') trees
     and so @(tsee parse-dot-1*bit) could return a tree
     with additional @('BIT') subtrees.
     As a third example,
     since @(tsee parse-bin/dec/hex-val) may call @(tsee parse-bin-val)
     (and @(tsee parse-dec-val) and @(tsee parse-hex-val))
     as its last action,
     @(tsee parse-bin/dec/hex-val-when-tree-match) inherits from
     @(tsee parse-bin-val-when-tree-match)
     (and @(tsee parse-dec-val-when-tree-match)
     and @(tsee parse-hex-val-when-tree-match))
     various parsing failure hypotheses on the remaining input.")

   (xdoc::p
    "As a slight generalization of the situation
     described in the previous paragraph,
     a parsing function may call, as its last action,
     another parsing function that may return a tree without leaves.
     In this case, the calling parsing function's completeness theorem inherits
     the hypotheses on the remaining input
     also from the completeness theorem of
     the parsing function that it calls just before the last one.
     For example,
     @(tsee parse-elements) calls @(tsee parse-*cwsp) as its last action,
     and thus @(tsee parse-elements-when-tree-match) inherits
     from @(tsee parse-*cwsp-when-tree-list-match)
     the hypothesis that @(tsee parse-cwsp) fails on the remaining input,
     as explained earlier.
     But since @(tsee parse-*cwsp) may return a tree with no leaves
     (if no instances of @('c-wsp') follow the @('alternation')),
     @(tsee parse-elements-when-tree-match) also inherits
     the hypotheses on the remaining input
     from @(tsee parse-alternation-when-tree-match).")

   (xdoc::p
    "As illustrated by
     the @(tsee parse-bin/dec/hex-val-when-tree-match) example above,
     when a parsing function may call a set of different parsing functions
     as its last action,
     the calling function's completeness theorem inherits
     from the called functions' completeness theorems
     all the hypotheses on the remaining input.
     The resulting hypotheses, in the calling function's completeness theorem,
     are stronger than needed:
     they could be weakened to require an inherited parsing failure hypothesis
     only if the subtree(s) correspond(s) to the called function.
     For example, in @(tsee parse-bin/dec/hex-val-when-tree-match),
     the failure of @(tsee parse-bit) could be required only if
     the @('(bin-val / dec-val / hex-val)') tree has a @('bin-val') subtree.
     However, in syntactically valid ABNF grammars,
     the stronger hypotheses are always satisfied
     (e.g. @('dec-val') cannot be followed by @('BIT')),
     so there is no loss in using the stronger hypotheses;
     the stronger hypotheses keep the completeness theorems simpler
     without precluding the eventual proof
     of the top-level completeness theorem.")

   (xdoc::p
    "In the rules in [RFC:4], certain repeated and optional syntactic entities
     ``nest to the right'',
     e.g. @('1*BIT') nests to the right inside @('1*(\".\" 1*BIT)').
     When this kind of nesting occurs,
     the completeness theorem
     of the parsing function for the outer repetition or option
     has not only the parsing failure hypotheses on the remaining input
     relative to the outer repetition or option,
     but also the parsing failure hypotheses on the remaining input
     relative to the inner repetition or option.
     For example, @(tsee parse-1*-dot-1*bit-when-tree-list-match)
     (and @(tsee parse-*-dot-1*bit-when-tree-list-match))
     includes not only the failure of @(tsee parse-dot-1*bit)
     (actually, a stronger hypothesis, as explained below),
     but also the failure of @(tsee parse-bit).
     As another example, @(tsee parse-bin-val-rest-when-tree-match)
     includes the failure of @(tsee parse-bit) for the @('1*BIT') repetition
     as well as (stronger hypotheses, as explained below, implying)
     the failure of (both alternatives inside)
     the @('[ 1*(\".\" 1*BIT) \"/\" (\"-\" 1*BIT) ]') option.")

   (xdoc::p
    "Besides the cases already mentioned
     of stronger hypotheses on the remaining input
     (that keep the theorems simpler while not precluding the top-level proof),
     there are other cases in which completeness theorems have
     stronger parsing failure hypotheses than needed.
     An example, as hinted above,
     is @(tsee parse-1*-dot-1*bit-when-tree-list-match):
     instead of having a hypothesis
     requiring the failure of @(tsee parse-1*-dot-1*bit),
     the theorem has the stronger hypothesis that
     @(tsee parse-ichar) with argument @('#\\.') fails.
     However, in syntactically valid ABNF grammars,
     the stronger hypotheses are always satisfied
     (e.g. @('1*(\".\" 1*BIT)') cannot be followed by @('\".\"')
     unless that is followed by @('BIT')),
     so there is no loss in using the stronger hypotheses;
     the stronger hypotheses keep the completeness theorems simpler
     without precluding the eventual proof
     of the top-level completeness theorem.")

   (xdoc::p
    "The two alternatives parsed by @(tsee parse-equal-/-equal-slash)
     are one a prefix of the other.
     Therefore, @(tsee parse-equal-/-equal-slash-when-tree-match)
     has the hypothesis that @(tsee parse-ichar) with argument @('#\\/')
     fails on the remaining input.
     Without this hypothesis, the tree hypothesized in the theorem
     could match just @('\"=\"'),
     but the remaining input could start with @('\"/\"'),
     in which case @(tsee parse-equal-/-equal-slash)
     would return a tree matching @('\"=/\"') instead,
     rendering the theorem untrue.
     This hypothesis on the remaining input is stronger than needed:
     it could be weakened to requiring the parsing failure
     only if the tree matches @('\"=\"').
     However, in syntactically valid ABNF grammars,
     the stronger hypothesis is always satisfied
     (i.e. @('\"=/\"') cannot be followed by @('\"/\"')),
     so there is no loss in using the stronger hypothesis;
     the stronger hypothesis keeps this completeness theorem simpler
     without precluding the eventual proof
     of the top-level completeness theorem.")

   (xdoc::p
    "Since
     (i) @(tsee parse-rule) calls @(tsee parse-cnl) as its last action,
     (ii) @(tsee parse-cnl) always returns a tree with leaves, and
     (iii) @(tsee parse-cnl-when-tree-match) has
     no hypotheses on the remaining input,
     it may seem that @(tsee parse-rule-when-tree-match)
     needs no hypotheses on the remaining input.
     However, before calling @(tsee parse-cnl),
     @(tsee parse-rule) calls @(tsee parse-elements),
     which may parse the ending @('c-nl')
     and then attempt and fail to parse @('WSP') after @('c-nl')
     (this is how the "
    (xdoc::seetopic "grammar-parser-implementation"
                    "grammar parser implementation")
    " resolves the @('rulelist') ambiguity).
     Thus, @(tsee parse-rule) may actually examine part of the remaining input.
     The needed hypothesis is that @(tsee parse-wsp)
     fails on the remaining input:
     if @('WSP') could be parsed from the remaining input,
     @(tsee parse-rule) would put that with the @('c-nl')
     under an additional @('c-wsp') instance
     under @('elements') and under @('rule'),
     thus returning a different tree than hypothesized in the theorem.")

   (xdoc::p
    "An analogous discussion to the one in the previous paragraph
     applies to @(tsee parse-*cwsp-cnl).
     Thus, @(tsee parse-*cwsp-cnl-when-tree-match) has the hypothesis that
     @(tsee parse-wsp) fails on the remaining input.")

   (xdoc::h3 "Hypotheses on the Tree(s)")

   (xdoc::p
    "Most completeness theorems include
     hypotheses saying that the trees are terminated.
     This ensures that the strings at the leaves of the trees
     consist of natural numbers and not rule names,
     since the parsing functions operate on natural numbers.
     A few completeness theorems do not need those hypotheses
     because the corresponding syntactic entities can only be matched
     by trees whose leaves are natural numbers, e.g.
     @(tsee parse-exact-when-tree-match),
     @(tsee parse-ichar-when-tree-match), and
     @(tsee parse-?%i-when-tree-match).")

   (xdoc::p
    "The completeness theorems
     @(tsee parse-*-rule-/-*cwsp-cnl-when-tree-list-match-and-restriction) and
     @(tsee parse-rulelist-when-tree-match-and-restriction),
     as suggested by the ending of their names,
     have hypotheses saying that the (list of) tree(s) satisfies "
    (xdoc::seetopic "grammar-parser-disambiguating-restrictions"
                    "the disambiguating restrictions")
    ". Without these hypotheses, the theorems would not hold
     because there would be multiple choices of trees for certain inputs,
     but the parser only produces one choice for each input.")

   (xdoc::h3 "Proof Methods")

   (xdoc::p
    "The completeness theorems of the more ``basic'' parsing functions
     @(tsee parse-any),
     @(tsee parse-exact),
     @(tsee parse-in-range),
     @(tsee parse-ichar), and
     @(tsee parse-ichars)
     are proved by expanding the necessary definitions.
     The proofs for @(tsee parse-exact) and @(tsee parse-in-range)
     use @(tsee parse-any-of-cons) as a rewrite rule,
     obviating the need to expand @(tsee parse-any).
     The proofs for @(tsee parse-exact) and @(tsee parse-in-range)
     also expand some tree-related functions, which seems odd
     because it should be possible to treat trees as abstract data types;
     there may be ways to avoid that, perhaps by adding some tree lemmas.")

   (xdoc::p
    "Each of the other completeness theorems is proved, generally speaking,
     by reducing the tree matching hypothesis
     to one or more subtree matching facts,
     reducing the call to the parsing function on the (list of) tree(s)
     to calls to other parsing functions on (lists of) subtrees,
     and using the already proved theorems for the called parsing functions
     to show that the calling parsing function returns the right results.
     The completeness theorems are used as rewrite rules
     (implicitly, since they are enabled).
     The subtree matching facts to which the tree matching hypothesis reduces
     are used to relieve the hypotheses of these rewrite rules.")

   (xdoc::p
    "For example, @(tsee parse-cr-when-tree-match) is proved as follows.
     The hypothesis that the tree matches @('CR') is reduced
     to the fact that its (only) subtree matches @('%x0D').
     The call to @(tsee parse-cr) in the conclusion is reduced
     to a call to @(tsee parse-exact) with argument @('#x0d')
     on the @(tsee append) of
     (i) the string at the leaves of the subtree and
     (ii) the remaining input.
     The rewrite rule @(tsee parse-exact-when-tree-match) then applies
     (whose hypothesis is relieved
     via the aforementioned fact that the subtree matches @('%0D')),
     rewriting the call to @(tsee parse-exact) to the triple consisting of
     @('nil') (i.e. success), the subtree, and the remaining input.
     Therefore, @(tsee parse-cr), by its definition,
     returns the triple consisting of
     @('nil') (i.e. success),
     the @('CR') tree with the @('%x0D') subtree,
     and the remaining input.
     Thus, @(tsee parse-cr-when-tree-match) is proved.")

   (xdoc::p
    "This reduction approach works also when there are multiple subtrees.
     For example, @(tsee parse-crlf-when-tree-match) is proved as follows.
     The hypothesis that the tree matches @('CRLF') is reduced
     to the first subtree matching @('CR')
     and the second subtree matching @('LF').
     The call to @(tsee parse-crlf) is reduced to
     a call to @(tsee parse-cr)
     on the string at the leaves of the first subtree
     and a call to @(tsee parse-lf)
     on the string at the leaves of the second subtree.
     Then @(tsee parse-cr-when-tree-match) and @(tsee parse-lf-when-tree-match)
     apply.")

   (xdoc::p
    "Since completeness theorems generally have hypotheses
     about the trees being terminated,
     in order to apply completeness theorems as rewrite rules to subtrees
     (in the reduction approach outlined above),
     the hypothesis that the trees are terminated
     must be reduced to facts that subtrees are terminated
     to relieve the hypotheses of the rewrite rules.
     Thus,
     we enable @(tsee tree-terminatedp) just before the completeness theorems
     and we disable it just after.
     The existing enabled rewrite rules take care of
     @(tsee tree-list-terminatedp) and @(tsee tree-list-list-terminatedp).")

   (xdoc::p
    "Similarly, when calls to parsing functions on trees
     are reduced to calls to parsing functions on subtrees,
     the strings at the leaves of the trees must be reduced to
     strings at the leaves of the subtrees.
     Thus, we enable
     @(tsee tree->string),
     @(tsee tree-list->string), and
     @(tsee tree-list-list->string)
     just before the completeness theorems
     and we disable them just after.
     The existing enabled rules about
     @(tsee tree-list->string) and
     @(tsee tree-list-list->string)
     do not suffice:
     if these two functions are not enabled,
     the proofs of some completeness theorems fails.")

   (xdoc::p
    "The @(tsee tree-match-element-p) hypotheses of the completeness theorems
     are expanded via explicit @(':expand') hints;
     just enabling @(tsee tree-match-element-p) does not perform the expansion
     (presumably due to ACL2's heuristics for expanding recursive functions).
     Since many repetitions consist of one element,
     the rewrite rule @(tsee tree-list-match-repetition-p-of-1-repetition)
     is used in many completeness proofs:
     we enable it just before the completeness theorems
     and disabled it just after.
     There is no direct use of the definitions of
     @(tsee tree-list-list-match-alternation-p) and
     @(tsee tree-list-list-match-concatenation-p)
     because the alternations and concatenations in the completeness theorems
     always have an explicit list structure and thus rewrite rules like
     @(tsee tree-list-list-match-alternation-p-of-cons-alternation) suffice.
     Repetition are handled via the rules
     @(tsee tree-list-match-repetition-p-of-0+-reps-when-consp) and
     @(tsee tree-list-match-repetition-p-of-1+-repetitions)
     where needed, as explained below.")

   (xdoc::p
    "If a parsing function may backtrack,
     its completeness theorem uses a disambiguation theorem as a rewrite rule,
     by explicitly enabling it
     (with just one exception:
     @(tsee parse-alpha-when-tree-match) uses
     @(tsee fail-1st-range-when-match-2nd-range) with a @(':use') hint,
     because the latter does not quite apply as a rewrite rule there).
     For example,
     in the proof of the completeness theorem @(tsee parse-wsp-when-tree-match),
     the hypothesis that the tree matches @('WSP')
     reduces to two cases for the subtree:
     either the subtree matches @('SP') or the subtree matches @('HTAB').
     In the first case,
     the completeness theorem @(tsee parse-sp-when-tree-match)
     implies that @(tsee parse-sp) succeeds, so @(tsee parse-wsp) succeeds
     and @(tsee parse-wsp-when-tree-match) is proved.
     In the second case, in order to use, in a similar way,
     the completeness theorem @(tsee parse-htab-when-tree-match),
     we need to show that @(tsee parse-sp) fails,
     so that @(tsee parse-wsp) reduces to @(tsee parse-htab) by backtracking
     and then @(tsee parse-wsp-when-tree-match) is proved
     using @(tsee parse-htab-when-tree-match).
     The disambiguation theorem @(tsee fail-sp-when-match-htab)
     serves to show that, in the second case above, @(tsee parse-sp) fails.")

   (xdoc::p
    "All the completeness theorems for parsing functions that may backtrack
     follow this proof pattern,
     which motivates the formulation of the disambiguation theorems.
     In particular,
     it motivates the ``asymmetric'' use of trees and parsing functions
     to show incompatibility
     (as opposed to showing incompatibility
     between parsing functions or between trees).")

   (xdoc::p
    "Some completeness theorems use some disambiguation theorems
     not to show that the parsing function must backtrack,
     but to relieve hypotheses of other completeness theorems.
     For example,
     in the completeness theorem
     @(tsee parse-1*-dot-1*bit-when-tree-list-match),
     the disambiguation theorem @(tsee fail-bit-when-match-*-dot-1*bit)
     serves to relieve the @(tsee parse-bit) failure hypothesis
     of the @(tsee parse-dot-1*bit-when-tree-match) completeness theorem.")

   (xdoc::p
    "If a parsing function parses a repetition of one or more elements
     (e.g. @(tsee parse-1*bit)),
     its completeness theorem
     (e.g. @(tsee parse-1*bit-when-tree-list-match))
     is proved by
     using @(tsee tree-list-match-repetition-p-of-1+-repetitions)
     to reduce the matching to
     a single element and to a repetition of zero or more elements,
     and then using the completeness theorems
     for the element
     (e.g. @(tsee parse-bit-when-tree-match))
     and for the repetition of zero or more elements
     (e.g. @(tsee parse-*bit-when-tree-list-match)).")

   (xdoc::p
    "If a parsing function is singly recursive (e.g. @(tsee parse-*bit)),
     i.e. it parses a repetition of zero or more elements,
     its completeness theorem is proved by induction
     on the length of the list of trees that matches the repetition;
     induction on the parsing function does not work,
     because the argument of the parsing function is not a variable
     (it is @('(append (tree-list->string trees) rest-input)')).
     We enable @(tsee tree-list-match-repetition-p-of-0+-reps-when-consp)
     to handle the induction step of the proof.
     We also disable the rewrite rule @('acl2::nat-list-fix-of-append')
     because it interferes with the proof
     by preventing @(tsee nat-list-fix) from being eliminated
     via the rewrite rule that shows that the parsing function fixes the input
     (e.g. the theorem "
    (xdoc::seetopic "parse-*bit" "@('parse-*bit-of-nat-list-fix-input')")
    ").")

   (xdoc::p
    "The proof of the mutually recursive parsing functions
     (i.e. @(tsee parse-alternation), @(tsee parse-concatenation), etc.)
     is more complex.
     As with the singly recursive parsing functions,
     a straightforward induction on the mutually recursive parsing functions
     does not work because their arguments are not variables
     (they are
     @('(append (tree->string tree) rest-input)') and
     @('(append (tree-list->string trees) rest-input)')).
     In analogy with
     the completeness theorems for the singly recursive parsing functions,
     we could try an induction on the sizes of the trees
     (variables @('tree') and @('trees')),
     but the formulation seems somewhat complicated,
     due to the presence of multiple parsing functions.")

   (xdoc::p
    "Instead, we take the desired formulation of each completeness theorem
     of the mutually recursive parsing functions,
     we add a hypothesis that a new variable @('input') is equal to
     @('(append (tree->string tree) rest-input)') or
     @('(append (tree-list->string trees) rest-input)'),
     we universally quantify
     the @('tree') or @('trees') variable and the @('rest-input') variable
     into a @(tsee define-sk) predicate with argument @('input'),
     and we prove all these predicates by induction on
     the mutually recursive functions.
     That is, we prove that the parsing functions
     satisfy their ``completeness properties'' for every way
     in which their input can be ``split''
     into (the string at the leaves of) a (list of) tree(s)
     and some remaining input.
     The predicates capture these completeness properties.")

   (xdoc::p
    "The predicates are @(tsee pred-alternation),
     @(tsee pred-concatenation), etc.
     They are not guard-verified because they only serve
     to prove the completeness of the mutually recursive parsing functions.
     The consequents of the implications in their bodies
     call the parsing functions on
     @('(append (tree->string tree) rest-input)') or
     @('(append (tree-list->string trees) rest-input)'),
     and not on the shorter @('input') that the antecedents assert to be equal,
     for a practical reason:
     if we used @('input') in the consequents,
     the rewrite rules generated by @(tsee define-sk)
     (e.g. @('pred-alternation-necc'))
     would have @('tree'), @('trees'), and @('rest-input') as free variables,
     making their use harder.
     The predicates also include
     the fact that the remaining input satisfies @(tsee nat-listp),
     instead of using @(tsee nat-list-fix) in the consequent:
     this is because the @(tsee nat-list-fix) approach causes the proofs to fail
     (perhaps due to some interaction with the equality with @('input')),
     so we use @(tsee nat-listp) instead in the predicates.")

   (xdoc::p
    "We prove by induction on the mutually recursive parsing functions that
     all the predicates hold for every @('input') argument:
     see
     @(tsee
       parse-alt/conc/rep/elem/group/option-when-tree-/-tree-list-match-lemmas).
     These are completeness lemmas,
     from which the completeness theorems are proved with ease.
     The completeness theorem have the same formulation as the ones
     for the other, non-recursive or singly recursive parsing functions;
     in particular, they use @(tsee nat-list-fix) instead of @(tsee nat-listp)
     on the remaining input.")

   (xdoc::p
    "The induction proof of the conpleteness lemmas generates
     5 base cases and 26 induction steps.
     We prove each of them separately
     (these are the theorems whose names end with
     @('-base-case') and @('-induction-step-N') where @('N') is a number,
     e.g. @(tsee parse-element-when-tree-match-base-case)
     and @(tsee parse-alternation-when-tree-match-induction-step-2).
     Attempting to prove the completeness lemmas by induction in one shot fails,
     perhaps due to interference between the different hints
     used for the base cases and induction steps;
     however,
     it may be possible to find a way to prove the lemmas in one shot.")

   (xdoc::p
    "The formulation of each base case and induction step
     is derived directly from the output
     generated by
     the @('defthm-parse-alt/conc/rep/elem/group/option-flag') form.
     Attempting to prove each base case and induction step in one shot fails,
     perhaps because of the equality between @('input') and
     @('(append (tree->string tree) rest-input)') or
     @('(append (tree-list->string trees) rest-input)').
     So, we prove each base case and induction step via a local lemma
     where the predicate in the conclusion of the base case or induction step
     is replaced with its definition;
     the base case or induction step is then proved just by
     expanding the predicate definition
     and using the local lemma as a rewrite rule.")

   (xdoc::p
    "The proof of each local lemma for base cases and induction steps
     is similar to the proofs of the completeness theorems
     of the non-recursive and singly recursive parsing functions.
     In addition, these local lemmas use (implicitly)
     the rewrite rules generated by @(tsee define-sk)
     (e.g. @('pred-alternation-necc'));
     some disambiguation theorems are sometimes enabled
     to relieve the hypotheses of these @(tsee define-sk) rewrite rules.
     The induction steps that involve lists of trees
     (as opposed to single trees)
     use a @(':cases') hint to split on whether the lists are empty or not.")

   (xdoc::p
    "Earlier we explained that some completeness theorems have
     stronger parsing failure hypotheses on the remaining input
     than needed, in order to keep the theorems simpler.
     These theorems enable certain "
    (xdoc::seetopic "grammar-parser-parsing-failure-propagation"
                    "parsing failure propagation theorems")
    " to turn the stronger hypotheses into
     the facts needed to show the weaker parsing failures
     within the parsing functions.
     For example,
     in the completeness theorem @(tsee parse-*-dot-1*bit-when-tree-list-match),
     the parsing failure propagation theorem
     @(tsee fail-dot-1*bit-when-fail-dot)
     is used to turn the hypothesis that
     @(tsee parse-ichar) with argument @('#\\.') fails
     into the fact that @(tsee parse-dot-1*bit) fails,
     needed to show that @(tsee parse-*-dot-1*bit) stops
     before the remaining input."))

  :order-subtopics t)

; disabled just after the completeness theorems:
(in-theory (enable tree->string
                   tree-list->string
                   tree-list-list->string
                   tree-terminatedp
                   tree-list-match-repetition-p-of-1-repetition))

(defrule parse-any-of-cons
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-any)."
  (equal (parse-any (cons nat nats))
         (mv nil (nfix nat) (nat-list-fix nats)))
  :enable parse-any)

(defrule parse-exact-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-exact)."
  (implies (tree-match-element-p tree (%. nat) *all-concrete-syntax-rules*)
           (equal (parse-exact nat (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :enable (parse-exact
           tree-match-element-p
           tree-match-num-val-p
           %.-fn
           treep
           tree-fix
           tree-kind
           tree-leafterm->get))

(defrule parse-in-range-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-in-range)."
  (implies (tree-match-element-p tree (%- min max) *all-concrete-syntax-rules*)
           (equal (parse-in-range min max (append (tree->string tree)
                                                  rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :enable (parse-in-range
           tree-match-element-p
           tree-match-num-val-p
           %-
           acl2::equal-len-const
           treep
           tree-fix
           tree-kind
           tree-leafterm->get))

(defrule parse-in-either-range-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-in-either-range)."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ (%- min1 max1))
                                          (/_ (%- min2 max2)))
                                      *all-concrete-syntax-rules*)
                (< (nfix max1)
                   (nfix min2)))
           (equal (parse-in-either-range min1 max1 min2 max2
                                         (append (tree->string tree)
                                                 rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-in-either-range
           !_-fn
           /_-fn
           fail-1st-range-when-match-2nd-range))

(defrule parse-*-in-either-range-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-*-in-either-range)."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ (%- min1 max1))
                                                      (/_ (%- min2 max2))))
                                              *all-concrete-syntax-rules*)
                (< (nfix max1)
                   (nfix min2))
                (mv-nth 0 (parse-in-either-range min1 max1 min2 max2
                                                 rest-input)))
           (equal (parse-*-in-either-range min1 max1 min2 max2
                                           (append (tree-list->string trees)
                                                   rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :induct (len trees)
  :enable (parse-*-in-either-range
           tree-list-match-repetition-p-of-0+-reps-when-consp
           *_)
  :disable acl2::nat-list-fix-of-append)

(defrule parse-ichar-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-ichar)."
  (implies (tree-match-element-p tree
                                 (element-char-val (char-val-insensitive
                                                    (implode (list char))))
                                 *all-concrete-syntax-rules*)
           (equal (parse-ichar char (append (tree->string tree)
                                            rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :enable (parse-ichar
           tree-match-element-p
           tree-match-char-val-p
           parse-any))

(defrule parse-ichars-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-ichars)."
  (implies (tree-match-element-p tree
                                 (element-char-val (char-val-insensitive
                                                    (implode (list char1
                                                                   char2))))
                                 *all-concrete-syntax-rules*)
           (equal (parse-ichars char1 char2 (append (tree->string tree)
                                                    rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :enable (parse-ichars
           tree-match-element-p
           tree-match-char-val-p
           parse-any))

(defrule parse-alpha-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-alpha)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *alpha*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-alpha (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-alpha
  :use (:instance fail-1st-range-when-match-2nd-range
                  (tree (car (car (tree-nonleaf->branches tree))))
                  (min1 #x41)
                  (max1 #x5a)
                  (min2 #x61)
                  (max2 #x7a)))

(defrule parse-bit-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-bit)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *bit*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-bit (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-bit
           fail-0-when-match-1))

(defrule parse-cr-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-cr)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *cr*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-cr (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-cr)

(defrule parse-digit-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-digit)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *digit*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-digit (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-digit)

(defrule parse-dquote-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-dquote)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *dquote*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-dquote (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-dquote)

(defrule parse-htab-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-htab)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *htab*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-htab (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-htab)

(defrule parse-lf-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-lf)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *lf*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-lf (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-lf)

(defrule parse-sp-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-sp)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *sp*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-sp (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-sp)

(defrule parse-vchar-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-vchar)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *vchar*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-vchar (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-vchar)

(defrule parse-crlf-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-crlf)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *crlf*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-crlf (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-crlf)

(defrule parse-hexdig-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-hexdig)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *hexdig*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-hexdig (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-hexdig
           fail-digit-when-match-a/b/c/d/e/f
           fail-a/b/c/d/e/f-when-match-other-a/b/c/d/e/f))

(defrule parse-wsp-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-wsp)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *wsp*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-wsp (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-wsp
           fail-sp-when-match-htab))

(defrule parse-prose-val-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-prose-val)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *prose-val*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-prose-val (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-prose-val
           fail-either-range-when-match-close-angle))

(defrule parse-*bit-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-*bit)."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *bit*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-bit rest-input)))
           (equal (parse-*bit (append (tree-list->string trees) rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :induct (len trees)
  :enable (parse-*bit
           tree-list-match-repetition-p-of-0+-reps-when-consp)
  :disable acl2::nat-list-fix-of-append)

(defrule parse-*digit-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-*digit)."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *digit*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-digit rest-input)))
           (equal (parse-*digit (append (tree-list->string trees) rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :induct (len trees)
  :enable (parse-*digit
           tree-list-match-repetition-p-of-0+-reps-when-consp)
  :disable acl2::nat-list-fix-of-append)

; rewrites with PARSE-*DIGIT-WHEN-TREE-LIST-MATCH:
(defruled fail-*digit-star-*digit-when-match-1*digit
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(*DIGIT \"*\" *DIGIT)')
          and @('1*DIGIT') not followed by @('DIGIT') or @('\"*\"')."
  (implies (and (tree-list-match-repetition-p trees
                                              (1*_ *digit*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-ichar #\* rest-input)))
           (mv-nth 0 (parse-*digit-star-*digit (append (tree-list->string trees)
                                                       rest-input))))
  :enable parse-*digit-star-*digit
  :use (:instance tree-list-match-repetition-p-of-0+-reps-when-1+-reps
                  (element (element-rulename *digit*))
                  (rules *all-concrete-syntax-rules*)))

(defrule parse-*hexdig-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-*hexdig)."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *hexdig*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-hexdig rest-input)))
           (equal (parse-*hexdig (append (tree-list->string trees) rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :induct (len trees)
  :enable (parse-*hexdig
           tree-list-match-repetition-p-of-0+-reps-when-consp)
  :disable acl2::nat-list-fix-of-append)

(defrule parse-1*bit-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-1*bit)."
  (implies (and (tree-list-match-repetition-p trees
                                              (1*_ *bit*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-bit rest-input)))
           (equal (parse-1*bit (append (tree-list->string trees) rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :enable (parse-1*bit
           tree-list-match-repetition-p-of-1+-repetitions))

(defrule parse-1*digit-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-1*digit)."
  (implies (and (tree-list-match-repetition-p trees
                                              (1*_ *digit*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-digit rest-input)))
           (equal (parse-1*digit (append (tree-list->string trees) rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :enable (parse-1*digit
           tree-list-match-repetition-p-of-1+-repetitions))

(defrule parse-1*hexdig-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-1*hexdig)."
  (implies (and (tree-list-match-repetition-p trees
                                              (1*_ *hexdig*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-hexdig rest-input)))
           (equal (parse-1*hexdig (append (tree-list->string trees) rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :enable (parse-1*hexdig
           tree-list-match-repetition-p-of-1+-repetitions))

(defrule parse-dot-1*bit-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-dot-1*bit)."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ "."
                                              (1*_ *bit*)))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-bit rest-input)))
           (equal (parse-dot-1*bit (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-dot-1*bit)

(defrule parse-dot-1*digit-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-dot-1*digit)."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ "."
                                              (1*_ *digit*)))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-digit rest-input)))
           (equal (parse-dot-1*digit (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-dot-1*digit)

(defrule parse-dot-1*hexdig-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-dot-1*hexdig)."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ "."
                                              (1*_ *hexdig*)))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-hexdig rest-input)))
           (equal (parse-dot-1*hexdig (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-dot-1*hexdig)

(defrule parse-dash-1*bit-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-dash-1*bit)."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ "-"
                                              (1*_ *bit*)))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-bit rest-input)))
           (equal (parse-dash-1*bit (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-dash-1*bit)

(defrule parse-dash-1*digit-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-dash-1*digit)."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ "-"
                                              (1*_ *digit*)))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-digit rest-input)))
           (equal (parse-dash-1*digit (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-dash-1*digit)

(defrule parse-dash-1*hexdig-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-dash-1*hexdig)."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ "-"
                                              (1*_ *hexdig*)))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-hexdig rest-input)))
           (equal (parse-dash-1*hexdig (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-dash-1*hexdig)

(defrule parse-*-dot-1*bit-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-*-dot-1*bit)."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ "."
                                                          (1*_ *bit*))))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input)))
           (equal (parse-*-dot-1*bit (append (tree-list->string trees)
                                             rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :induct (len trees)
  :enable (parse-*-dot-1*bit
           tree-list-match-repetition-p-of-0+-reps-when-consp
           fail-bit-when-match-*-dot-1*bit
           fail-dot-1*bit-when-fail-dot)
  :disable acl2::nat-list-fix-of-append)

(defrule parse-*-dot-1*digit-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-*-dot-1*digit)."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ "."
                                                          (1*_ *digit*))))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input)))
           (equal (parse-*-dot-1*digit (append (tree-list->string trees)
                                               rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :induct (len trees)
  :enable (parse-*-dot-1*digit
           tree-list-match-repetition-p-of-0+-reps-when-consp
           fail-digit-when-match-*-dot-1*digit
           fail-dot-1*digit-when-fail-dot)
  :disable acl2::nat-list-fix-of-append)

(defrule parse-*-dot-1*hexdig-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-*-dot-1*hexdig)."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ "."
                                                          (1*_ *hexdig*))))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input)))
           (equal (parse-*-dot-1*hexdig (append (tree-list->string trees)
                                                rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :induct (len trees)
  :enable (parse-*-dot-1*hexdig
           tree-list-match-repetition-p-of-0+-reps-when-consp
           fail-hexdig-when-match-*-dot-1*hexdig
           fail-dot-1*hexdig-when-fail-dot)
  :disable acl2::nat-list-fix-of-append)

(defrule parse-1*-dot-1*bit-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-1*-dot-1*bit)."
  (implies (and (tree-list-match-repetition-p trees
                                              (1*_ (!_ (/_ "."
                                                           (1*_ *bit*))))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input)))
           (equal (parse-1*-dot-1*bit (append (tree-list->string trees)
                                              rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :enable (parse-1*-dot-1*bit
           tree-list-match-repetition-p-of-1+-repetitions
           fail-bit-when-match-*-dot-1*bit))

(defrule parse-1*-dot-1*digit-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-1*-dot-1*digit)."
  (implies (and (tree-list-match-repetition-p trees
                                              (1*_ (!_ (/_ "."
                                                           (1*_ *digit*))))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input)))
           (equal (parse-1*-dot-1*digit (append (tree-list->string trees)
                                                rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :enable (parse-1*-dot-1*digit
           tree-list-match-repetition-p-of-1+-repetitions
           fail-digit-when-match-*-dot-1*digit))

(defrule parse-1*-dot-1*hexdig-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-1*-dot-1*hexdig)."
  (implies (and (tree-list-match-repetition-p trees
                                              (1*_ (!_ (/_ "."
                                                           (1*_ *hexdig*))))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input)))
           (equal (parse-1*-dot-1*hexdig (append (tree-list->string trees)
                                                 rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :enable (parse-1*-dot-1*hexdig
           tree-list-match-repetition-p-of-1+-repetitions
           fail-hexdig-when-match-*-dot-1*hexdig))

(defrule parse-bin-val-rest-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-bin-val-rest)."
  (implies (and (tree-match-element-p tree
                                      (?_ (/_ (1*_ (!_ (/_ "."
                                                           (1*_ *bit*)))))
                                          (/_ (!_ (/_ "-"
                                                      (1*_ *bit*)))))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (equal (parse-bin-val-rest (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-bin-val-rest
           fail-dot-when-match-dash-etc.
           fail-dash-1*bit-when-fail-dash
           fail-dot-1*bit-when-fail-dot
           fail-1*-dot-1*bit-when-fail-dot-1*bit))

(defrule parse-dec-val-rest-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-dec-val-rest)."
  (implies (and (tree-match-element-p tree
                                      (?_ (/_ (1*_ (!_ (/_ "."
                                                           (1*_ *digit*)))))
                                          (/_ (!_ (/_ "-"
                                                      (1*_ *digit*)))))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (equal (parse-dec-val-rest (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-dec-val-rest
           fail-dot-when-match-dash-etc.
           fail-dash-1*digit-when-fail-dash
           fail-dot-1*digit-when-fail-dot
           fail-1*-dot-1*digit-when-fail-dot-1*digit))

(defrule parse-hex-val-rest-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-hex-val-rest)."
  (implies (and (tree-match-element-p tree
                                      (?_ (/_ (1*_ (!_ (/_ "."
                                                           (1*_ *hexdig*)))))
                                          (/_ (!_ (/_ "-"
                                                      (1*_ *hexdig*)))))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (equal (parse-hex-val-rest (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-hex-val-rest
           fail-dot-when-match-dash-etc.
           fail-dash-1*hexdig-when-fail-dash
           fail-dot-1*hexdig-when-fail-dot
           fail-1*-dot-1*hexdig-when-fail-dot-1*hexdig))

(defrule parse-bin-val-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-bin-val)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *bin-val*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (equal (parse-bin-val (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-bin-val
           fail-bit-when-match-bin-val-rest))

(defrule parse-dec-val-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-dec-val)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *dec-val*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (equal (parse-dec-val (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-dec-val
           fail-digit-when-match-dec-val-rest))

(defrule parse-hex-val-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-hex-val)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *hex-val*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (equal (parse-hex-val (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-hex-val
           fail-hexdig-when-match-hex-val-rest))

(defrule parse-bin/dec/hex-val-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-bin/dec/hex-val)."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ *bin-val*)
                                          (/_ *dec-val*)
                                          (/_ *hex-val*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (equal (parse-bin/dec/hex-val (append (tree->string tree)
                                                 rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-bin/dec/hex-val
           fail-bin-val-when-match-dec/hex-val
           fail-dec-val-when-match-hex-val))

(defrule parse-num-val-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-num-val)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *num-val*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (equal (parse-num-val (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-num-val)

(defrule parse-quoted-string-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-quoted-string)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *quoted-string*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-quoted-string (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-quoted-string
           fail-either-range-when-match-dquote))

(defrule parse-case-sensitive-string-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-case-sensitive-string)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *case-sensitive-string*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-case-sensitive-string (append (tree->string tree)
                                                       rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-case-sensitive-string)

(defrule parse-?%i-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-?%i)."
  (implies (and (tree-match-element-p tree
                                      (?_ (/_ "%i"))
                                      *all-concrete-syntax-rules*)
                (mv-nth 0 (parse-ichars #\% #\i rest-input)))
           (equal (parse-?%i (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-?%i)

(defrule parse-case-insensitive-string-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-case-insensitive-string)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename
                                       *case-insensitive-string*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-case-insensitive-string (append (tree->string tree)
                                                         rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-case-insensitive-string
           fail-%i-when-match-quoted-string))

(defrule parse-char-val-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-char-val)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *char-val*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-char-val (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-char-val
           fail-case-insensitive-string-when-match-case-sensitive-string))

(defrule parse-wsp/vchar-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-wsp/vchar)."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ *wsp*)
                                          (/_ *vchar*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-wsp/vchar (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-wsp/vchar
           fail-wsp-when-match-vchar-/-rule-/-cnl-wsp))

(defrule parse-*wsp/vchar-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-*wsp/vchar)."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ *wsp*)
                                                      (/_ *vchar*)))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-wsp/vchar rest-input)))
           (equal (parse-*wsp/vchar (append (tree-list->string trees)
                                            rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :induct (len trees)
  :enable (parse-*wsp/vchar
           tree-list-match-repetition-p-of-0+-reps-when-consp)
  :disable acl2::nat-list-fix-of-append)

(defrule parse-comment-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-comment)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *comment*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-comment (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-comment
           fail-wsp/vchar-when-match-crlf))

(defrule parse-cnl-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-cnl)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *c-nl*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-cnl (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-cnl
           fail-comment-when-match-crlf))

; rewrites with PARSE-CNL-WHEN-TREE-MATCH:
(defruled fail-alt-rest-comp-when-match-cnl
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(*c-wsp \"/\" *c-wsp concatenation)')
          and @('c-nl') not followed by @('WSP')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *c-nl*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-wsp rest-input)))
           (mv-nth 0 (parse-alt-rest-comp
                      (append (tree->string tree) rest-input))))
  :expand ((:free (input) (parse-alt-rest-comp input))
           (:free (input) (parse-*cwsp input)))
  :enable (fail-slash/htab/sp/wsp/rep-when-match-cnl
           parse-cwsp
           parse-cnl-wsp
           parse-wsp))

; rewrites with PARSE-CNL-WHEN-TREE-MATCH:
(defruled fail-conc-rest-comp-when-match-cnl
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(1*c-wsp repetition)')
          and @('c-nl') not followed by @('WSP')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *c-nl*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-wsp rest-input)))
           (mv-nth 0 (parse-conc-rest-comp
                      (append (tree->string tree) rest-input))))
  :expand (:free (input) (parse-conc-rest-comp input))
  :enable (fail-slash/htab/sp/wsp/rep-when-match-cnl
           parse-1*cwsp
           parse-cwsp
           parse-cnl-wsp
           parse-wsp))

; rewrites with PARSE-CNL-WHEN-TREE-MATCH:
(defruled fail-cwsp-when-match-cnl
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between between @('c-wsp')
          and @('c-nl') not followed by @('WSP')."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *c-nl*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-wsp rest-input)))
           (mv-nth 0 (parse-cwsp (append (tree->string tree) rest-input))))
  :enable (fail-slash/htab/sp/wsp/rep-when-match-cnl
           parse-cwsp
           parse-cnl-wsp
           parse-wsp))

(defrule parse-cnl-wsp-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-cnl-wsp)."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ *c-nl* *wsp*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-cnl-wsp (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-cnl-wsp)

(defrule parse-cwsp-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-cwsp)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *c-wsp*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-cwsp (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-cwsp
           fail-wsp-when-match-vchar-/-rule-/-cnl-wsp))

; rewrites with PARSE-CWSP-WHEN-TREE-MATCH (in LEMMA):
(defruled fail-alt-rest-comp-when-match-*cwsp
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(*c-wsp \"/\" *c-wsp concatenation)')
          and @('*c-wsp')
          not followed by @('(*c-wsp \"/\" *c-wsp concatenation)')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *c-wsp*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-alt-rest-comp rest-input)))
           (mv-nth 0 (parse-alt-rest-comp
                      (append (tree-list->string trees) rest-input))))
  :induct (len trees)
  :expand (:free (input) (parse-alt-rest-comp input))
  :enable tree-list-match-repetition-p-of-0+-reps-when-consp

  :prep-lemmas
  ((defrule lemma
     (implies (and (tree-match-element-p tree
                                         (element-rulename *c-wsp*)
                                         *all-concrete-syntax-rules*)
                   (tree-terminatedp tree))
              (equal (mv-nth 2 (parse-*cwsp
                                (append (tree->string tree) rest-input)))
                     (mv-nth 2 (parse-*cwsp rest-input))))
     :enable parse-*cwsp)))

(defrule parse-*cwsp-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-*cwsp)."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *c-wsp*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-cwsp rest-input)))
           (equal (parse-*cwsp (append (tree-list->string trees) rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :induct (len trees)
  :enable (parse-*cwsp
           tree-list-match-repetition-p-of-0+-reps-when-consp)
  :disable acl2::nat-list-fix-of-append)

; rewrites with PARSE-*CWSP-WHEN-TREE-LIST-MATCH:
(defruled fail-alt-rest-comp-when-match-*cwsp-close-round/square
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(*c-wsp \"/\" *c-wsp concatenation)')
          and @('*c-wsp') followed by @('\")\"') or @('\"]\"')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *c-wsp*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (tree-match-element-p tree element *all-concrete-syntax-rules*)
                (member-equal element (list (element-char-val
                                             (char-val-insensitive ")"))
                                            (element-char-val
                                             (char-val-insensitive "]")))))
           (mv-nth 0 (parse-alt-rest-comp
                      (append (tree-list->string trees)
                              (tree->string tree)
                              rest-input))))
  :expand (:free (input) (parse-alt-rest-comp input))
  :enable (fail-cwsp-when-match-slash-/-close-round/square
           fail-slash-when-match-close-round/square))

(defrule parse-1*cwsp-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-1*cwsp)."
  (implies (and (tree-list-match-repetition-p trees
                                              (1*_ *c-wsp*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-cwsp rest-input)))
           (equal (parse-1*cwsp (append (tree-list->string trees)
                                          rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :enable (parse-1*cwsp
           tree-list-match-repetition-p-of-1+-repetitions))

; rewrites with PARSE-1*CWSP-WHEN-TREE-LIST-MATCH:
(defruled fail-conc-rest-comp-when-match-*cwsp
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(1*c-wsp repetition)')
          and @('*c-wsp') not followed by @('repetition') or @('c-wsp')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *c-wsp*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-repetition rest-input))
                (mv-nth 0 (parse-cwsp rest-input)))
           (mv-nth 0 (parse-conc-rest-comp
                      (append (tree-list->string trees) rest-input))))
  :enable (fail-conc-rest-comp-when-fail-cwsp
           parse-conc-rest-comp)
  :use (:instance tree-list-match-repetition-p-of-1+-reps-when-0+-reps
                  (element (element-rulename *c-wsp*))
                  (rules *all-concrete-syntax-rules*)))

; rewrites with PARSE-1*CWSP-WHEN-TREE-LIST-MATCH:
(defruled fail-conc-rest-comp-when-match-*cwsp-close-round/square
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(1*c-wsp repetition)')
          and @('*c-wsp') followed by @('\")\"') or @('\"]\"')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ *c-wsp*)
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (tree-match-element-p tree element *all-concrete-syntax-rules*)
                (member-equal element (list (element-char-val
                                             (char-val-insensitive ")"))
                                            (element-char-val
                                             (char-val-insensitive "]")))))
           (mv-nth 0 (parse-conc-rest-comp
                      (append (tree-list->string trees)
                              (tree->string tree)
                              rest-input))))
  :expand (:free (input) (parse-conc-rest-comp input))
  :enable (fail-1*cwsp-when-match-slash-/-close-round/square
           fail-cwsp-when-match-slash-/-close-round/square
           fail-repetition-when-match-slash-/-close-round/square)
  :use (:instance tree-list-match-repetition-p-of-1+-reps-when-0+-reps
                  (element (element-rulename *c-wsp*))
                  (rules *all-concrete-syntax-rules*)))

; rewrites with PARSE-1*CWSP-WHEN-TREE-LIST-MATCH:
(defruled fail-conc-rest-comp-when-match-alt-rest-comp
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(1*c-wsp repetition)')
          and @('(*c-wsp \"/\" *c-wsp concatenation)')."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ (*_ *c-wsp*)
                                              "/"
                                              (*_ *c-wsp*)
                                              *concatenation*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (mv-nth 0 (parse-conc-rest-comp
                      (append (tree->string tree) rest-input))))
  :expand ((:free (element rules) (tree-match-element-p tree element rules))
           (:free (input) (parse-conc-rest-comp input)))
  :enable (fail-1*cwsp-when-match-slash-/-close-round/square
           fail-cwsp-when-match-slash-/-close-round/square
           fail-repetition-when-match-slash-/-close-round/square)
  :use (:instance tree-list-match-repetition-p-of-1+-reps-when-0+-reps
                  (trees (car (tree-nonleaf->branches tree)))
                  (element (element-rulename *c-wsp*))
                  (rules *all-concrete-syntax-rules*)))

(defruled fail-conc-rest-comp-when-match-alt-rest
  :parents (grammar-parser-disambiguation)
  :short "Disambiguation between @('(1*c-wsp repetition)')
          and @('*(*c-wsp \"/\" *c-wsp concatenation)')
          not followed by @('(1*c-wsp repetition)')."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ (*_ *c-wsp*)
                                                          "/"
                                                          (*_ *c-wsp*)
                                                          *concatenation*)))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-conc-rest-comp rest-input)))
           (mv-nth 0 (parse-conc-rest-comp
                      (append (tree-list->string trees) rest-input))))
  :enable (tree-list-match-repetition-p
           fail-conc-rest-comp-when-match-alt-rest-comp))

(defrule parse-*digit-star-*digit-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-*digit-star-*digit)."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ (*_ *digit*) "*" (*_ *digit*)))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-digit rest-input)))
           (equal (parse-*digit-star-*digit (append (tree->string tree)
                                                    rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-*digit-star-*digit
           fail-digit-when-match-star/dash))

(defrule parse-repeat-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-repeat)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *repeat*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-ichar #\* rest-input)))
           (equal (parse-repeat (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-repeat
           fail-*digit-star-*digit-when-match-1*digit))

(defrule parse-?repeat-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-?repeat)."
  (implies (and (tree-match-element-p tree
                                      (?_ (/_ *repeat*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-ichar #\* rest-input)))
           (equal (parse-?repeat (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-?repeat
           fail-repeat-when-fail-digit-and-fail-star))

(defrule parse-alpha/digit/dash-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-alpha/digit/dash)."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ *alpha*)
                                          (/_ *digit*)
                                          (/_ "-"))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-alpha/digit/dash (append (tree->string tree)
                                                  rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-alpha/digit/dash
           fail-alpha-when-match-digit/dash
           fail-digit-when-match-star/dash))

(defrule parse-*-alpha/digit/dash-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-*-alpha/digit/dash)."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ *alpha*)
                                                      (/_ *digit*)
                                                      (/_ "-")))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-alpha/digit/dash rest-input)))
           (equal (parse-*-alpha/digit/dash (append (tree-list->string trees)
                                                    rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :induct (len trees)
  :enable (parse-*-alpha/digit/dash
           tree-list-match-repetition-p-of-0+-reps-when-consp)
  :disable acl2::nat-list-fix-of-append)

(defrule parse-rulename-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-rulename)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *rulename*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-alpha/digit/dash rest-input)))
           (equal (parse-rulename (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable parse-rulename)

(define-sk pred-alternation (input)
  :parents (grammar-parser-completeness)
  :short "Completeness property for @(tsee parse-alternation)."
  (forall (tree rest-input)
          (implies
           (and (tree-match-element-p tree
                                      (element-rulename *alternation*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (nat-listp rest-input)
                (mv-nth 0 (parse-alt-rest-comp rest-input))
                (mv-nth 0 (parse-conc-rest-comp rest-input))
                (mv-nth 0 (parse-alpha/digit/dash rest-input))
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input))
                (equal input (append (tree->string tree) rest-input)))
           (equal (parse-alternation (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) rest-input))))
  :enabled :thm
  :non-executable t
  :verify-guards nil)

(define-sk pred-concatenation (input)
  :parents (grammar-parser-completeness)
  :short "Completeness property for @(tsee parse-concatenation)."
  (forall (tree rest-input)
          (implies
           (and (tree-match-element-p tree
                                      (element-rulename *concatenation*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (nat-listp rest-input)
                (mv-nth 0 (parse-conc-rest-comp rest-input))
                (mv-nth 0 (parse-alpha/digit/dash rest-input))
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input))
                (equal input (append (tree->string tree) rest-input)))
           (equal (parse-concatenation (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) rest-input))))
  :enabled :thm
  :non-executable t
  :verify-guards nil)

(define-sk pred-repetition (input)
  :parents (grammar-parser-completeness)
  :short "Completeness property for @(tsee parse-repetition)."
  (forall (tree rest-input)
          (implies
           (and (tree-match-element-p tree
                                      (element-rulename *repetition*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (nat-listp rest-input)
                (mv-nth 0 (parse-alpha/digit/dash rest-input))
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input))
                (equal input (append (tree->string tree) rest-input)))
           (equal (parse-repetition (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) rest-input))))
  :enabled :thm
  :non-executable t
  :verify-guards nil)

(define-sk pred-element (input)
  :parents (grammar-parser-completeness)
  :short "Completeness property for @(tsee parse-element)."
  (forall (tree rest-input)
          (implies
           (and (tree-match-element-p tree
                                      (element-rulename *element*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (nat-listp rest-input)
                (mv-nth 0 (parse-alpha/digit/dash rest-input))
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input))
                (equal input (append (tree->string tree) rest-input)))
           (equal (parse-element (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) rest-input))))
  :enabled :thm
  :non-executable t
  :verify-guards nil)

(define-sk pred-group (input)
  :parents (grammar-parser-completeness)
  :short "Completeness property for @(tsee parse-group)."
  (forall (tree rest-input)
          (implies (and (tree-match-element-p tree
                                              (element-rulename *group*)
                                              *all-concrete-syntax-rules*)
                        (tree-terminatedp tree)
                        (nat-listp rest-input)
                        (equal input (append (tree->string tree) rest-input)))
                   (equal (parse-group (append (tree->string tree) rest-input))
                          (mv nil (tree-fix tree) rest-input))))
  :enabled :thm
  :non-executable t
  :verify-guards nil)

(define-sk pred-option (input)
  :parents (grammar-parser-completeness)
  :short "Completeness property for @(tsee parse-option)."
  (forall (tree rest-input)
          (implies (and (tree-match-element-p tree
                                              (element-rulename *option*)
                                              *all-concrete-syntax-rules*)
                        (tree-terminatedp tree)
                        (nat-listp rest-input)
                        (equal input (append (tree->string tree) rest-input)))
                   (equal (parse-option (append (tree->string tree) rest-input))
                          (mv nil (tree-fix tree) rest-input))))
  :enabled :thm
  :non-executable t
  :verify-guards nil)

(define-sk pred-alt-rest (input)
  :parents (grammar-parser-completeness)
  :short "Completeness property for @(tsee parse-alt-rest)."
  (forall (trees rest-input)
          (implies
           (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ (*_ *c-wsp*)
                                                          "/"
                                                          (*_ *c-wsp*)
                                                          *concatenation*)))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (nat-listp rest-input)
                (mv-nth 0 (parse-alt-rest-comp rest-input))
                (mv-nth 0 (parse-conc-rest-comp rest-input))
                (mv-nth 0 (parse-alpha/digit/dash rest-input))
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input))
                (equal input (append (tree-list->string trees) rest-input)))
           (equal (parse-alt-rest (append (tree-list->string trees)
                                                  rest-input))
                  (mv nil (tree-list-fix trees) rest-input))))
  :enabled :thm
  :non-executable t
  :verify-guards nil)

(define-sk pred-alt-rest-comp (input)
  :short "Completeness property for @(tsee parse-alt-rest-comp)."
  :parents (grammar-parser-completeness)
  (forall (tree rest-input)
          (implies
           (and (tree-match-element-p tree
                                      (!_ (/_ (*_ *c-wsp*)
                                              "/"
                                              (*_ *c-wsp*)
                                              *concatenation*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (nat-listp rest-input)
                (mv-nth 0 (parse-conc-rest-comp rest-input))
                (mv-nth 0 (parse-alpha/digit/dash rest-input))
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input))
                (equal input (append (tree->string tree) rest-input)))
           (equal (parse-alt-rest-comp (append (tree->string tree)
                                                            rest-input))
                  (mv nil (tree-fix tree) rest-input))))
  :enabled :thm
  :non-executable t
  :verify-guards nil)

(define-sk pred-conc-rest (input)
  :parents (grammar-parser-completeness)
  :short "Completeness property for @(tsee parse-conc-rest)."
  (forall (trees rest-input)
          (implies
           (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ (1*_ *c-wsp*)
                                                          *repetition*)))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (nat-listp rest-input)
                (mv-nth 0 (parse-conc-rest-comp rest-input))
                (mv-nth 0 (parse-alpha/digit/dash rest-input))
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input))
                (equal input (append (tree-list->string trees) rest-input)))
           (equal (parse-conc-rest (append (tree-list->string trees)
                                                    rest-input))
                  (mv nil (tree-list-fix trees) rest-input))))
  :enabled :thm
  :non-executable t
  :verify-guards nil)

(define-sk pred-conc-rest-comp (input)
  :parents (grammar-parser-completeness)
  :short "Completeness property for @(tsee parse-conc-rest-comp)."
  (forall (tree rest-input)
          (implies
           (and (tree-match-element-p tree
                                      (!_ (/_ (1*_ *c-wsp*)
                                              *repetition*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (nat-listp rest-input)
                (mv-nth 0 (parse-alpha/digit/dash rest-input))
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input))
                (equal input (append (tree->string tree) rest-input)))
           (equal (parse-conc-rest-comp (append (tree->string
                                                               tree)
                                                              rest-input))
                  (mv nil (tree-fix tree) rest-input))))
  :enabled :thm
  :non-executable t
  :verify-guards nil)

(defruled parse-alternation-when-tree-match-induction-step-1
  :parents (grammar-parser-completeness)
  :short "First induction step of
          the completeness lemma for @(tsee parse-alternation)."
  (implies (and (mv-nth 0 (parse-concatenation input))
                (pred-concatenation input))
           (pred-alternation input))
  :enable pred-alternation

  :prep-lemmas
  ((defrule lemma
     (implies (and (mv-nth 0 (parse-concatenation input))
                   (pred-concatenation input)
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (element-rulename *alternation*))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-alt-rest-comp rest-input))
                   (mv-nth 0 (parse-conc-rest-comp rest-input))
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-alternation input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable (fail-conc-rest-comp-when-match-alt-rest
              fail-alpha/digit/dash-when-match-alt-rest
              fail-bit-when-match-alt-rest
              fail-digit-when-match-alt-rest
              fail-hexdig-when-match-alt-rest
              fail-dot-when-match-alt-rest
              fail-dash-when-match-alt-rest))))

(defruled parse-alternation-when-tree-match-induction-step-2
  :parents (grammar-parser-completeness)
  :short "Second induction step of
          the completeness lemma for @(tsee parse-alternation)."
  (implies (and (not (mv-nth 0 (parse-concatenation input)))
                (< (len (mv-nth 2 (parse-concatenation input)))
                   (len input))
                (pred-concatenation input)
                (pred-alt-rest (mv-nth 2 (parse-concatenation input))))
           (pred-alternation input))
  :enable pred-alternation

  :prep-lemmas
  ((defrule lemma
     (implies (and (not (mv-nth 0 (parse-concatenation input)))
                   (< (len (mv-nth 2 (parse-concatenation input)))
                      (len input))
                   (pred-concatenation input)
                   (pred-alt-rest
                    (mv-nth 2 (parse-concatenation input)))
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (element-rulename *alternation*))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-alt-rest-comp rest-input))
                   (mv-nth 0 (parse-conc-rest-comp rest-input))
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-alternation input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable (parse-alternation
              fail-conc-rest-comp-when-match-alt-rest
              fail-alpha/digit/dash-when-match-alt-rest
              fail-bit-when-match-alt-rest
              fail-digit-when-match-alt-rest
              fail-hexdig-when-match-alt-rest
              fail-dot-when-match-alt-rest
              fail-dash-when-match-alt-rest))))

(defruled parse-concatenation-when-tree-match-induction-step-1
  :parents (grammar-parser-completeness)
  :short "First induction step of
          the completeness lemma for @(tsee parse-concatenation)."
  (implies (and (mv-nth 0 (parse-repetition input))
                (pred-repetition input))
           (pred-concatenation input))
  :enable pred-concatenation

  :prep-lemmas
  ((defrule lemma
     (implies (and (mv-nth 0 (parse-repetition input))
                   (pred-repetition input)
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (element-rulename *concatenation*))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-conc-rest-comp rest-input))
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-concatenation input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable (fail-alpha/digit/dash-when-match-conc-rest
              fail-bit-when-match-conc-rest
              fail-digit-when-match-conc-rest
              fail-hexdig-when-match-conc-rest
              fail-dot-when-match-conc-rest
              fail-dash-when-match-conc-rest))))

(defruled parse-concatenation-when-tree-match-induction-step-2
  :parents (grammar-parser-completeness)
  :short "Second induction step of
          the completeness lemma for @(tsee parse-concatenation)."
  (implies (and (not (mv-nth 0 (parse-repetition input)))
                (< (len (mv-nth 2 (parse-repetition input)))
                   (len input))
                (pred-repetition input)
                (pred-conc-rest (mv-nth 2 (parse-repetition input))))
           (pred-concatenation input))
  :enable pred-concatenation

  :prep-lemmas
  ((defrule lemma
     (implies (and (not (mv-nth 0 (parse-repetition input)))
                   (< (len (mv-nth 2 (parse-repetition input)))
                      (len input))
                   (pred-repetition input)
                   (pred-conc-rest (mv-nth 2 (parse-repetition input)))
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (element-rulename *concatenation*))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-conc-rest-comp rest-input))
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-concatenation input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable (parse-concatenation
              fail-alpha/digit/dash-when-match-conc-rest
              fail-bit-when-match-conc-rest
              fail-digit-when-match-conc-rest
              fail-hexdig-when-match-conc-rest
              fail-dot-when-match-conc-rest
              fail-dash-when-match-conc-rest))))

(defruled parse-repetition-when-tree-match-induction-step-1
  :parents (grammar-parser-completeness)
  :short "First induction step of
          the completeness lemma for @(tsee parse-repetition)."
  (implies (and (mv-nth 0 (parse-element (mv-nth 2 (parse-?repeat input))))
                (pred-element (mv-nth 2 (parse-?repeat input))))
           (pred-repetition input))
  :enable pred-repetition

  :prep-lemmas
  ((defrule lemma
     (implies (and (mv-nth 0 (parse-element (mv-nth 2 (parse-?repeat input))))
                   (pred-element (mv-nth 2 (parse-?repeat input)))
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (element-rulename *repetition*))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-repetition input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable (parse-repetition
              fail-digit/star-when-match-element
              fail-digit/star-when-match-element))))

(defruled parse-repetition-when-tree-match-induction-step-2
  :parents (grammar-parser-completeness)
  :short "Second induction step of
          the completeness lemma for @(tsee parse-repetition)."
  (implies (and (not (mv-nth 0 (parse-element
                                (mv-nth 2 (parse-?repeat input)))))
                (pred-element (mv-nth 2 (parse-?repeat input))))
           (pred-repetition input))
  :enable pred-repetition

  :prep-lemmas
  ((defrule lemma
     (implies (and (not (mv-nth 0 (parse-element
                                   (mv-nth 2 (parse-?repeat input)))))
                   (pred-element (mv-nth 2 (parse-?repeat input)))
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (element-rulename *repetition*))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-repetition input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable (parse-repetition
              fail-digit/star-when-match-element
              fail-digit/star-when-match-element))))

(defruled parse-element-when-tree-match-induction-step-1
  :parents (grammar-parser-completeness)
  :short "First induction step of
          the completeness lemma for @(tsee parse-element)."
  (implies (and (mv-nth 0 (parse-rulename input))
                (mv-nth 0 (parse-group input))
                (mv-nth 0 (parse-option input))
                (mv-nth 0 (parse-char-val input))
                (mv-nth 0 (parse-num-val input))
                (mv-nth 0 (parse-prose-val input))
                (pred-group input)
                (pred-option input))
           (pred-element input))
  :enable pred-element

  :prep-lemmas
  ((defrule lemma
     (implies (and (mv-nth 0 (parse-rulename input))
                   (mv-nth 0 (parse-group input))
                   (mv-nth 0 (parse-option input))
                   (mv-nth 0 (parse-char-val input))
                   (mv-nth 0 (parse-num-val input))
                   (mv-nth 0 (parse-prose-val input))
                   (pred-group input)
                   (pred-option input)
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (element-rulename *element*))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-element input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable parse-element)))

(defruled parse-element-when-tree-match-induction-step-2
  :parents (grammar-parser-completeness)
  :short "Second induction step of
          the completeness lemma for @(tsee parse-element)."
  (implies (and (mv-nth 0 (parse-rulename input))
                (mv-nth 0 (parse-group input))
                (mv-nth 0 (parse-option input))
                (mv-nth 0 (parse-char-val input))
                (mv-nth 0 (parse-num-val input))
                (not (mv-nth 0 (parse-prose-val input)))
                (pred-group input)
                (pred-option input))
           (pred-element input))
  :enable pred-element

  :prep-lemmas
  ((defrule lemma
     (implies (and (mv-nth 0 (parse-rulename input))
                   (mv-nth 0 (parse-group input))
                   (mv-nth 0 (parse-option input))
                   (mv-nth 0 (parse-char-val input))
                   (mv-nth 0 (parse-num-val input))
                   (not (mv-nth 0 (parse-prose-val input)))
                   (pred-group input)
                   (pred-option input)
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (element-rulename *element*))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-element input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable parse-element)))

(defruled parse-element-when-tree-match-induction-step-3
  :parents (grammar-parser-completeness)
  :short "Third induction step of
          the completeness lemma for @(tsee parse-element)."
  (implies (and (mv-nth 0 (parse-rulename input))
                (mv-nth 0 (parse-group input))
                (mv-nth 0 (parse-option input))
                (mv-nth 0 (parse-char-val input))
                (not (mv-nth 0 (parse-num-val input)))
                (pred-group input)
                (pred-option input))
           (pred-element input))
  :enable pred-element

  :prep-lemmas
  ((defrule lemma
     (implies (and (mv-nth 0 (parse-rulename input))
                   (mv-nth 0 (parse-group input))
                   (mv-nth 0 (parse-option input))
                   (mv-nth 0 (parse-char-val input))
                   (not (mv-nth 0 (parse-num-val input)))
                   (pred-group input)
                   (pred-option input)
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (element-rulename *element*))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-element input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable (parse-element
              fail-num-val-when-match-prose-val))))

(defruled parse-element-when-tree-match-induction-step-4
  :parents (grammar-parser-completeness)
  :short "Fourth induction step of
          the completeness lemma for @(tsee parse-element)."
  (implies (and (mv-nth 0 (parse-rulename input))
                (mv-nth 0 (parse-group input))
                (mv-nth 0 (parse-option input))
                (not (mv-nth 0 (parse-char-val input)))
                (pred-group input)
                (pred-option input))
           (pred-element input))
  :enable pred-element

  :prep-lemmas
  ((defrule lemma
     (implies (and (mv-nth 0 (parse-rulename input))
                   (mv-nth 0 (parse-group input))
                   (mv-nth 0 (parse-option input))
                   (not (mv-nth 0 (parse-char-val input)))
                   (pred-group input)
                   (pred-option input)
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (element-rulename *element*))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-element input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable (parse-element
              fail-char-val-when-match-num/prose-val))))

(defruled parse-element-when-tree-match-induction-step-5
  :parents (grammar-parser-completeness)
  :short "Fifth induction step of
          the completeness lemma for @(tsee parse-element)."
  (implies (and (mv-nth 0 (parse-rulename input))
                (mv-nth 0 (parse-group input))
                (not (mv-nth 0 (parse-option input)))
                (pred-group input)
                (pred-option input))
           (pred-element input))
  :enable pred-element

  :prep-lemmas
  ((defrule lemma
     (implies (and (mv-nth 0 (parse-rulename input))
                   (mv-nth 0 (parse-group input))
                   (not (mv-nth 0 (parse-option input)))
                   (pred-group input)
                   (pred-option input)
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (element-rulename *element*))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-element input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable (parse-element
              fail-option-when-match-char/num/prose-val))))

(defruled parse-element-when-tree-match-induction-step-6
  :parents (grammar-parser-completeness)
  :short "Sixth induction step of
          the completeness lemma for @(tsee parse-element)."
  (implies (and (mv-nth 0 (parse-rulename input))
                (not (mv-nth 0 (parse-group input)))
                (pred-group input))
           (pred-element input))
  :enable pred-element

  :prep-lemmas
  ((defrule lemma
     (implies (and (mv-nth 0 (parse-rulename input))
                   (not (mv-nth 0 (parse-group input)))
                   (pred-group input)
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (element-rulename *element*))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-element input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable (parse-element
              fail-group-when-match-option-/-char/num/prose-val))))

(defruled parse-element-when-tree-match-base-case
  :parents (grammar-parser-completeness)
  :short "Base case of
          the completeness lemma for @(tsee parse-element)."
  (implies (not (mv-nth 0 (parse-rulename input)))
           (pred-element input))
  :enable pred-element

  :prep-lemmas
  ((defrule lemma
     (implies (and (not (mv-nth 0 (parse-rulename input)))
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (element-rulename *element*))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-element input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable (parse-element
              fail-rulename-when-match-group/option-/-char/num/prose-val))))

(defruled parse-group-when-tree-match-base-case
  :parents (grammar-parser-completeness)
  :short "Base case of
          the completeness lemma for @(tsee parse-group)."
  (implies (mv-nth 0 (parse-ichar #\( input))
           (pred-group input))
  :enable pred-group

  :prep-lemmas
  ((defrule lemma
     (implies (and (mv-nth 0 (parse-ichar #\( input))
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (element-rulename *group*))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-group input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules)
                    (tree-match-element-p tree element rules)))))

(defruled parse-group-when-tree-match-induction-step-1
  :parents (grammar-parser-completeness)
  :short "First induction step of
          the completeness lemma for @(tsee parse-group)."
  (implies (and (not (mv-nth 0 (parse-ichar #\( input)))
                (mv-nth 0 (parse-alternation
                           (mv-nth 2 (parse-*cwsp
                                      (mv-nth 2 (parse-ichar #\( input))))))
                (pred-alternation
                 (mv-nth 2 (parse-*cwsp
                            (mv-nth 2 (parse-ichar #\( input))))))
           (pred-group input))
  :enable pred-group

  :prep-lemmas
  ((defrule lemma
     (implies (and (not (mv-nth 0 (parse-ichar #\( input)))
                   (mv-nth 0 (parse-alternation
                              (mv-nth 2 (parse-*cwsp
                                         (mv-nth 2 (parse-ichar #\( input))))))
                   (pred-alternation
                    (mv-nth 2 (parse-*cwsp
                               (mv-nth 2 (parse-ichar #\( input)))))
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (element-rulename *group*))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-group input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable
     (tree-terminatedp
      fail-cwsp-when-match-alt/conc/rep
      fail-alt-rest-comp-when-match-*cwsp-close-round/square
      fail-conc-rest-comp-when-match-*cwsp-close-round/square
      fail-alpha/digit/dash-when-match-*cwsp-close-round/square
      fail-bit/digit/hexdig/dot/dash-when-match-*cwsp-close-round/square))))

(defruled parse-group-when-tree-match-induction-step-2
  :parents (grammar-parser-completeness)
  :short "Second induction step of
          the completeness lemma for @(tsee parse-group)."
  (implies
   (and (not (mv-nth 0 (parse-ichar #\( input)))
        (not (mv-nth 0 (parse-alternation
                        (mv-nth 2 (parse-*cwsp
                                   (mv-nth 2 (parse-ichar #\( input)))))))
        (mv-nth 0 (parse-ichar
                   #\)
                   (mv-nth 2 (parse-*cwsp
                              (mv-nth 2 (parse-alternation
                                         (mv-nth 2 (parse-*cwsp
                                                    (mv-nth 2 (parse-ichar
                                                               #\(
                                                               input))))))))))
        (pred-alternation
         (mv-nth 2 (parse-*cwsp (mv-nth 2 (parse-ichar #\( input))))))
   (pred-group input))
  :enable pred-group

  :prep-lemmas
  ((defrule lemma
     (implies
      (and (not (mv-nth 0 (parse-ichar #\( input)))
           (not (mv-nth 0 (parse-alternation
                           (mv-nth 2 (parse-*cwsp
                                      (mv-nth 2 (parse-ichar #\( input)))))))
           (mv-nth 0 (parse-ichar
                      #\)
                      (mv-nth 2 (parse-*cwsp
                                 (mv-nth 2 (parse-alternation
                                            (mv-nth 2 (parse-*cwsp
                                                       (mv-nth 2
                                                               (parse-ichar
                                                                #\(
                                                                input))))))))))
           (pred-alternation
            (mv-nth 2 (parse-*cwsp (mv-nth 2 (parse-ichar #\( input)))))
           (tree-match-element-p tree
                                 element
                                 *all-concrete-syntax-rules*)
           (equal element (element-rulename *group*))
           (tree-terminatedp tree)
           (nat-listp rest-input)
           (equal input (append (tree->string tree) rest-input)))
      (equal (parse-group input)
             (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable
     (fail-cwsp-when-match-alt/conc/rep
      fail-alt-rest-comp-when-match-*cwsp-close-round/square
      fail-conc-rest-comp-when-match-*cwsp-close-round/square
      fail-alpha/digit/dash-when-match-*cwsp-close-round/square
      fail-bit/digit/hexdig/dot/dash-when-match-*cwsp-close-round/square
      fail-cwsp-when-match-slash-/-close-round/square))))

(defruled parse-group-when-tree-match-induction-step-3
  :parents (grammar-parser-completeness)
  :short "Third induction step of
          the completeness lemma for @(tsee parse-group)."
  (implies
   (and (not (mv-nth 0 (parse-ichar #\( input)))
        (not (mv-nth 0 (parse-alternation
                        (mv-nth 2 (parse-*cwsp
                                   (mv-nth 2 (parse-ichar #\( input)))))))
        (not (mv-nth 0 (parse-ichar
                        #\)
                        (mv-nth 2 (parse-*cwsp
                                   (mv-nth 2 (parse-alternation
                                              (mv-nth 2 (parse-*cwsp
                                                         (mv-nth
                                                          2
                                                          (parse-ichar
                                                           #\(
                                                           input)))))))))))
        (pred-alternation
         (mv-nth 2 (parse-*cwsp (mv-nth 2 (parse-ichar #\( input))))))
   (pred-group input))
  :enable pred-group

  :prep-lemmas
  ((defrule lemma
     (implies
      (and (not (mv-nth 0 (parse-ichar #\( input)))
           (not (mv-nth 0 (parse-alternation
                           (mv-nth 2 (parse-*cwsp
                                      (mv-nth 2 (parse-ichar #\( input)))))))
           (not (mv-nth 0 (parse-ichar
                           #\)
                           (mv-nth 2 (parse-*cwsp
                                      (mv-nth 2 (parse-alternation
                                                 (mv-nth 2 (parse-*cwsp
                                                            (mv-nth
                                                             2
                                                             (parse-ichar
                                                              #\(
                                                              input)))))))))))
           (pred-alternation
            (mv-nth 2 (parse-*cwsp (mv-nth 2 (parse-ichar #\( input)))))
           (tree-match-element-p tree
                                 element
                                 *all-concrete-syntax-rules*)
           (equal element (element-rulename *group*))
           (tree-terminatedp tree)
           (nat-listp rest-input)
           (equal input (append (tree->string tree) rest-input)))
      (equal (parse-group input)
             (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable
     (parse-group
      fail-cwsp-when-match-alt/conc/rep
      fail-alt-rest-comp-when-match-*cwsp-close-round/square
      fail-conc-rest-comp-when-match-*cwsp-close-round/square
      fail-alpha/digit/dash-when-match-*cwsp-close-round/square
      fail-bit/digit/hexdig/dot/dash-when-match-*cwsp-close-round/square
      fail-cwsp-when-match-slash-/-close-round/square))))

(defruled parse-option-when-tree-match-base-case
  :parents (grammar-parser-completeness)
  :short "Base case of
          the completeness lemma for @(tsee parse-option)."
  (implies (mv-nth 0 (parse-ichar #\[ input))
           (pred-option input))
  :enable pred-option

  :prep-lemmas
  ((defrule lemma
     (implies (and (mv-nth 0 (parse-ichar #\[ input))
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (element-rulename *option*))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-option input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules)
                    (tree-match-element-p tree element rules)))))

(defruled parse-option-when-tree-match-induction-step-1
  :parents (grammar-parser-completeness)
  :short "First induction step of
          the completeness lemma for @(tsee parse-option)."
  (implies (and (not (mv-nth 0 (parse-ichar #\[ input)))
                (mv-nth 0 (parse-alternation
                           (mv-nth 2 (parse-*cwsp
                                      (mv-nth 2 (parse-ichar #\[ input))))))
                (pred-alternation
                 (mv-nth 2 (parse-*cwsp
                            (mv-nth 2 (parse-ichar #\[ input))))))
           (pred-option input))
  :enable pred-option

  :prep-lemmas
  ((defrule lemma
     (implies (and (not (mv-nth 0 (parse-ichar #\[ input)))
                   (mv-nth 0 (parse-alternation
                              (mv-nth 2 (parse-*cwsp
                                         (mv-nth 2 (parse-ichar #\[ input))))))
                   (pred-alternation
                    (mv-nth 2 (parse-*cwsp
                               (mv-nth 2 (parse-ichar #\[ input)))))
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (element-rulename *option*))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-option input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable
     (fail-cwsp-when-match-alt/conc/rep
      fail-alt-rest-comp-when-match-*cwsp-close-round/square
      fail-conc-rest-comp-when-match-*cwsp-close-round/square
      fail-alpha/digit/dash-when-match-*cwsp-close-round/square
      fail-bit/digit/hexdig/dot/dash-when-match-*cwsp-close-round/square))))

(defruled parse-option-when-tree-match-induction-step-2
  :parents (grammar-parser-completeness)
  :short "Second induction step of
          the completeness lemma for @(tsee parse-option)."
  (implies
   (and (not (mv-nth 0 (parse-ichar #\[ input)))
        (not (mv-nth 0 (parse-alternation
                        (mv-nth 2 (parse-*cwsp
                                   (mv-nth 2 (parse-ichar #\[ input)))))))
        (mv-nth 0 (parse-ichar
                   #\]
                   (mv-nth 2 (parse-*cwsp
                              (mv-nth 2 (parse-alternation
                                         (mv-nth 2 (parse-*cwsp
                                                    (mv-nth 2 (parse-ichar
                                                               #\[
                                                               input))))))))))
        (pred-alternation
         (mv-nth 2 (parse-*cwsp (mv-nth 2 (parse-ichar #\[ input))))))
   (pred-option input))
  :enable pred-option

  :prep-lemmas
  ((defrule lemma
     (implies
      (and (not (mv-nth 0 (parse-ichar #\[ input)))
           (not (mv-nth 0 (parse-alternation
                           (mv-nth 2 (parse-*cwsp
                                      (mv-nth 2 (parse-ichar #\[ input)))))))
           (mv-nth 0 (parse-ichar
                      #\]
                      (mv-nth 2 (parse-*cwsp
                                 (mv-nth 2 (parse-alternation
                                            (mv-nth 2 (parse-*cwsp
                                                       (mv-nth 2
                                                               (parse-ichar
                                                                #\[
                                                                input))))))))))
           (pred-alternation
            (mv-nth 2 (parse-*cwsp (mv-nth 2 (parse-ichar #\[ input)))))
           (tree-match-element-p tree element *all-concrete-syntax-rules*)
           (equal element (element-rulename *option*))
           (tree-terminatedp tree)
           (nat-listp rest-input)
           (equal input (append (tree->string tree) rest-input)))
      (equal (parse-option input)
             (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable
     (fail-cwsp-when-match-alt/conc/rep
      fail-alt-rest-comp-when-match-*cwsp-close-round/square
      fail-conc-rest-comp-when-match-*cwsp-close-round/square
      fail-alpha/digit/dash-when-match-*cwsp-close-round/square
      fail-bit/digit/hexdig/dot/dash-when-match-*cwsp-close-round/square
      fail-cwsp-when-match-slash-/-close-round/square))))

(defruled parse-option-when-tree-match-induction-step-3
  :parents (grammar-parser-completeness)
  :short "Third induction step of
          the completeness lemma for @(tsee parse-option)."
  (implies
   (and (not (mv-nth 0 (parse-ichar #\[ input)))
        (not (mv-nth 0 (parse-alternation
                        (mv-nth 2 (parse-*cwsp
                                   (mv-nth 2 (parse-ichar #\[ input)))))))
        (not (mv-nth 0 (parse-ichar
                        #\]
                        (mv-nth 2 (parse-*cwsp
                                   (mv-nth 2 (parse-alternation
                                              (mv-nth 2 (parse-*cwsp
                                                         (mv-nth
                                                          2
                                                          (parse-ichar
                                                           #\[
                                                           input)))))))))))
        (pred-alternation
         (mv-nth 2 (parse-*cwsp (mv-nth 2 (parse-ichar #\[ input))))))
   (pred-option input))
  :enable pred-option

  :prep-lemmas
  ((defrule lemma
     (implies
      (and (not (mv-nth 0 (parse-ichar #\[ input)))
           (not (mv-nth 0 (parse-alternation
                           (mv-nth 2 (parse-*cwsp
                                      (mv-nth 2 (parse-ichar #\[ input)))))))
           (not (mv-nth 0 (parse-ichar
                           #\]
                           (mv-nth 2 (parse-*cwsp
                                      (mv-nth 2 (parse-alternation
                                                 (mv-nth 2 (parse-*cwsp
                                                            (mv-nth
                                                             2
                                                             (parse-ichar
                                                              #\[
                                                              input)))))))))))
           (pred-alternation
            (mv-nth 2 (parse-*cwsp (mv-nth 2 (parse-ichar #\[ input)))))
           (tree-match-element-p tree element *all-concrete-syntax-rules*)
           (equal element (element-rulename *option*))
           (tree-terminatedp tree)
           (nat-listp rest-input)
           (equal input (append (tree->string tree) rest-input)))
      (equal (parse-option input)
             (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable
     (parse-option
      fail-cwsp-when-match-alt/conc/rep
      fail-alt-rest-comp-when-match-*cwsp-close-round/square
      fail-conc-rest-comp-when-match-*cwsp-close-round/square
      fail-alpha/digit/dash-when-match-*cwsp-close-round/square
      fail-bit/digit/hexdig/dot/dash-when-match-*cwsp-close-round/square
      fail-cwsp-when-match-slash-/-close-round/square))))

(defruled parse-alt-rest-when-tree-list-match-induction-step-1
  :parents (grammar-parser-completeness)
  :short "First induction step of
          the completeness lemma for @(tsee parse-alt-rest)."
  (implies (and (mv-nth 0 (parse-alt-rest-comp input))
                (pred-alt-rest-comp input))
           (pred-alt-rest input))
  :enable pred-alt-rest

  :prep-lemmas
  ((defrule lemma
     (implies (and (mv-nth 0 (parse-alt-rest-comp input))
                   (pred-alt-rest-comp input)
                   (tree-list-match-repetition-p trees
                                                 repetition
                                                 *all-concrete-syntax-rules*)
                   (equal repetition (*_ (!_ (/_ (*_ *c-wsp*)
                                                 "/"
                                                 (*_ *c-wsp*)
                                                 *concatenation*))))
                   (tree-list-terminatedp trees)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-alt-rest-comp rest-input))
                   (mv-nth 0 (parse-conc-rest-comp rest-input))
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree-list->string trees) rest-input)))
              (equal (parse-alt-rest input)
                     (mv nil (tree-list-fix trees) rest-input)))
     :cases ((consp trees))
     :enable (parse-alt-rest
              tree-list-match-repetition-p-of-0+-reps-when-consp
              fail-conc-rest-comp-when-match-alt-rest
              fail-alpha/digit/dash-when-match-alt-rest
              fail-bit-when-match-alt-rest
              fail-digit-when-match-alt-rest
              fail-hexdig-when-match-alt-rest
              fail-dot-when-match-alt-rest
              fail-dash-when-match-alt-rest))))

(defruled parse-alt-rest-when-tree-list-match-induction-step-2
  :parents (grammar-parser-completeness)
  :short "Second induction step of
          the completeness lemma for @(tsee parse-alt-rest)."
  (implies (and (not (mv-nth 0 (parse-alt-rest-comp input)))
                (< (len (mv-nth 2 (parse-alt-rest-comp input)))
                   (len input))
                (pred-alt-rest-comp input)
                (pred-alt-rest
                 (mv-nth 2 (parse-alt-rest-comp input))))
           (pred-alt-rest input))
  :enable pred-alt-rest

  :prep-lemmas
  ((defrule lemma
     (implies (and (not (mv-nth 0 (parse-alt-rest-comp input)))
                   (< (len (mv-nth 2 (parse-alt-rest-comp input)))
                      (len input))
                   (pred-alt-rest-comp input)
                   (pred-alt-rest
                    (mv-nth 2 (parse-alt-rest-comp input)))
                   (tree-list-match-repetition-p trees
                                                 repetition
                                                 *all-concrete-syntax-rules*)
                   (equal repetition (*_ (!_ (/_ (*_ *c-wsp*)
                                                 "/"
                                                 (*_ *c-wsp*)
                                                 *concatenation*))))
                   (tree-list-terminatedp trees)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-alt-rest-comp rest-input))
                   (mv-nth 0 (parse-conc-rest-comp rest-input))
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree-list->string trees) rest-input)))
              (equal (parse-alt-rest input)
                     (mv nil (tree-list-fix trees) rest-input)))
     :cases ((consp trees))
     :enable (parse-alt-rest
              tree-list-match-repetition-p-of-0+-reps-when-consp
              fail-conc-rest-comp-when-match-alt-rest
              fail-alpha/digit/dash-when-match-alt-rest
              fail-bit-when-match-alt-rest
              fail-digit-when-match-alt-rest
              fail-hexdig-when-match-alt-rest
              fail-dot-when-match-alt-rest
              fail-dash-when-match-alt-rest))))

(defruled parse-alt-rest-comp-when-tree-match-base-case
  :parents (grammar-parser-completeness)
  :short "Base case of
          the completeness lemma for @(tsee parse-alt-rest-comp)."
  (implies (mv-nth 0 (parse-ichar #\/ (mv-nth 2 (parse-*cwsp input))))
           (pred-alt-rest-comp input))
  :enable pred-alt-rest-comp

  :prep-lemmas
  ((defrule lemma
     (implies (and (mv-nth 0 (parse-ichar #\/ (mv-nth 2 (parse-*cwsp input))))
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (!_ (/_ (*_ *c-wsp*)
                                          "/"
                                          (*_ *c-wsp*)
                                          *concatenation*)))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-conc-rest-comp rest-input))
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-alt-rest-comp input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable fail-cwsp-when-match-slash-/-close-round/square)))

(defruled parse-alt-rest-comp-when-tree-match-induction-step-1
  :parents (grammar-parser-completeness)
  :short "First induction step of
          the completeness lemma for @(tsee parse-alt-rest-comp)."
  (implies
   (and (not (mv-nth 0 (parse-ichar #\/ (mv-nth 2 (parse-*cwsp input)))))
        (mv-nth 0 (parse-concatenation
                   (mv-nth 2 (parse-*cwsp
                              (mv-nth 2 (parse-ichar
                                         #\/
                                         (mv-nth 2 (parse-*cwsp input))))))))
        (pred-concatenation
         (mv-nth 2 (parse-*cwsp
                    (mv-nth 2 (parse-ichar
                               #\/
                               (mv-nth 2 (parse-*cwsp input))))))))
   (pred-alt-rest-comp input))
  :enable pred-alt-rest-comp

  :prep-lemmas
  ((defrule lemma
     (implies
      (and (not (mv-nth 0 (parse-ichar #\/ (mv-nth 2 (parse-*cwsp input)))))
           (mv-nth 0 (parse-concatenation
                      (mv-nth 2 (parse-*cwsp
                                 (mv-nth 2 (parse-ichar
                                            #\/
                                            (mv-nth 2 (parse-*cwsp
                                                       input))))))))
           (pred-concatenation
            (mv-nth 2 (parse-*cwsp
                       (mv-nth 2 (parse-ichar
                                  #\/
                                  (mv-nth 2 (parse-*cwsp input)))))))
           (tree-match-element-p tree
                                 element
                                 *all-concrete-syntax-rules*)
           (equal element (!_ (/_ (*_ *c-wsp*)
                                  "/"
                                  (*_ *c-wsp*)
                                  *concatenation*)))
           (tree-terminatedp tree)
           (nat-listp rest-input)
           (mv-nth 0 (parse-conc-rest-comp rest-input))
           (mv-nth 0 (parse-alpha/digit/dash rest-input))
           (mv-nth 0 (parse-bit rest-input))
           (mv-nth 0 (parse-digit rest-input))
           (mv-nth 0 (parse-hexdig rest-input))
           (mv-nth 0 (parse-ichar #\. rest-input))
           (mv-nth 0 (parse-ichar #\- rest-input))
           (equal input (append (tree->string tree) rest-input)))
      (equal (parse-alt-rest-comp input)
             (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable (fail-cwsp-when-match-slash-/-close-round/square
              fail-cwsp-when-match-alt/conc/rep))))

(defruled parse-alt-rest-comp-when-tree-match-induction-step-2
  :parents (grammar-parser-completeness)
  :short "Second induction step of
          the completeness lemma for @(tsee parse-alt-rest-comp)."
  (implies
   (and (not (mv-nth 0 (parse-ichar #\/ (mv-nth 2 (parse-*cwsp input)))))
        (not (mv-nth 0 (parse-concatenation
                        (mv-nth 2 (parse-*cwsp
                                   (mv-nth 2 (parse-ichar
                                              #\/
                                              (mv-nth 2 (parse-*cwsp
                                                         input)))))))))
        (pred-concatenation
         (mv-nth 2 (parse-*cwsp
                    (mv-nth 2 (parse-ichar
                               #\/
                               (mv-nth 2 (parse-*cwsp input))))))))
   (pred-alt-rest-comp input))
  :enable pred-alt-rest-comp

  :prep-lemmas
  ((defrule lemma
     (implies
      (and (not (mv-nth 0 (parse-ichar #\/ (mv-nth 2 (parse-*cwsp input)))))
           (not (mv-nth 0 (parse-concatenation
                           (mv-nth 2 (parse-*cwsp
                                      (mv-nth 2 (parse-ichar
                                                 #\/
                                                 (mv-nth 2 (parse-*cwsp
                                                            input)))))))))
           (pred-concatenation
            (mv-nth 2 (parse-*cwsp
                       (mv-nth 2 (parse-ichar
                                  #\/
                                  (mv-nth 2 (parse-*cwsp input)))))))
           (tree-match-element-p tree
                                 element
                                 *all-concrete-syntax-rules*)
           (equal element (!_ (/_ (*_ *c-wsp*)
                                  "/"
                                  (*_ *c-wsp*)
                                  *concatenation*)))
           (tree-terminatedp tree)
           (nat-listp rest-input)
           (mv-nth 0 (parse-conc-rest-comp rest-input))
           (mv-nth 0 (parse-alpha/digit/dash rest-input))
           (mv-nth 0 (parse-bit rest-input))
           (mv-nth 0 (parse-digit rest-input))
           (mv-nth 0 (parse-hexdig rest-input))
           (mv-nth 0 (parse-ichar #\. rest-input))
           (mv-nth 0 (parse-ichar #\- rest-input))
           (equal input (append (tree->string tree) rest-input)))
      (equal (parse-alt-rest-comp input)
             (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable (parse-alt-rest-comp
              fail-cwsp-when-match-slash-/-close-round/square
              fail-cwsp-when-match-alt/conc/rep))))

(defruled parse-conc-rest-when-tree-list-match-induction-step-1
  :parents (grammar-parser-completeness)
  :short "First induction step of
          the completeness lemma for @(tsee parse-conc-rest)."
  (implies (and (mv-nth 0 (parse-conc-rest-comp input))
                (pred-conc-rest-comp input))
           (pred-conc-rest input))
  :enable pred-conc-rest

  :prep-lemmas
  ((defrule lemma
     (implies (and (mv-nth 0 (parse-conc-rest-comp input))
                   (pred-conc-rest-comp input)
                   (tree-list-match-repetition-p trees
                                                 repetition
                                                 *all-concrete-syntax-rules*)
                   (equal repetition (*_ (!_ (/_ (1*_ *c-wsp*)
                                                 *repetition*))))
                   (tree-list-terminatedp trees)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-conc-rest-comp rest-input))
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree-list->string trees) rest-input)))
              (equal (parse-conc-rest input)
                     (mv nil (tree-list-fix trees) rest-input)))
     :cases ((consp trees))
     :enable (parse-conc-rest
              tree-list-match-repetition-p-of-0+-reps-when-consp
              fail-alpha/digit/dash-when-match-conc-rest
              fail-bit-when-match-conc-rest
              fail-digit-when-match-conc-rest
              fail-hexdig-when-match-conc-rest
              fail-dot-when-match-conc-rest
              fail-dash-when-match-conc-rest))))

(defruled parse-conc-rest-when-tree-list-match-induction-step-2
  :parents (grammar-parser-completeness)
  :short "Second induction step of
          the completeness lemma for @(tsee parse-conc-rest)."
  (implies (and (not (mv-nth 0 (parse-conc-rest-comp input)))
                (< (len (mv-nth 2 (parse-conc-rest-comp input)))
                   (len input))
                (pred-conc-rest-comp input)
                (pred-conc-rest
                 (mv-nth 2 (parse-conc-rest-comp input))))
           (pred-conc-rest input))
  :enable pred-conc-rest

  :prep-lemmas
  ((defrule lemma
     (implies (and (not (mv-nth 0 (parse-conc-rest-comp input)))
                   (< (len (mv-nth 2 (parse-conc-rest-comp
                                      input)))
                      (len input))
                   (pred-conc-rest-comp input)
                   (pred-conc-rest
                    (mv-nth 2 (parse-conc-rest-comp input)))
                   (tree-list-match-repetition-p trees
                                                 repetition
                                                 *all-concrete-syntax-rules*)
                   (equal repetition (*_ (!_ (/_ (1*_ *c-wsp*)
                                                 *repetition*))))
                   (tree-list-terminatedp trees)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-conc-rest-comp rest-input))
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree-list->string trees) rest-input)))
              (equal (parse-conc-rest input)
                     (mv nil (tree-list-fix trees) rest-input)))
     :cases ((consp trees))
     :enable (parse-conc-rest
              tree-list-match-repetition-p-of-0+-reps-when-consp
              fail-alpha/digit/dash-when-match-conc-rest
              fail-bit-when-match-conc-rest
              fail-digit-when-match-conc-rest
              fail-hexdig-when-match-conc-rest
              fail-dot-when-match-conc-rest
              fail-dash-when-match-conc-rest))))

(defruled parse-conc-rest-comp-when-tree-match-base-case
  :parents (grammar-parser-completeness)
  :short "Base case of
          the completeness lemma for
          @(tsee parse-conc-rest-comp)."
  (implies (mv-nth 0 (parse-1*cwsp input))
           (pred-conc-rest-comp input))
  :enable pred-conc-rest-comp

  :prep-lemmas
  ((defrule lemma
     (implies (and (mv-nth 0 (parse-1*cwsp input))
                   (tree-match-element-p tree
                                         element
                                         *all-concrete-syntax-rules*)
                   (equal element (!_ (/_ (1*_ *c-wsp*)
                                          *repetition*)))
                   (tree-terminatedp tree)
                   (nat-listp rest-input)
                   (mv-nth 0 (parse-alpha/digit/dash rest-input))
                   (mv-nth 0 (parse-bit rest-input))
                   (mv-nth 0 (parse-digit rest-input))
                   (mv-nth 0 (parse-hexdig rest-input))
                   (mv-nth 0 (parse-ichar #\. rest-input))
                   (mv-nth 0 (parse-ichar #\- rest-input))
                   (equal input (append (tree->string tree) rest-input)))
              (equal (parse-conc-rest-comp input)
                     (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable fail-cwsp-when-match-alt/conc/rep)))

(defruled parse-conc-rest-comp-when-tree-match-induction-step-1
  :parents (grammar-parser-completeness)
  :short "First induction step of
          the completeness lemma for
          @(tsee parse-conc-rest-comp)."
  (implies
   (and (not (mv-nth 0 (parse-1*cwsp input)))
        (mv-nth 0 (parse-repetition (mv-nth 2 (parse-1*cwsp input))))
        (pred-repetition (mv-nth 2 (parse-1*cwsp input))))
   (pred-conc-rest-comp input))
  :enable pred-conc-rest-comp

  :prep-lemmas
  ((defrule lemma
     (implies
      (and (not (mv-nth 0 (parse-1*cwsp input)))
           (mv-nth 0 (parse-repetition (mv-nth 2 (parse-1*cwsp input))))
           (pred-repetition (mv-nth 2 (parse-1*cwsp input)))
           (tree-match-element-p tree
                                 element
                                 *all-concrete-syntax-rules*)
           (equal element (!_ (/_ (1*_ *c-wsp*)
                                  *repetition*)))
           (tree-terminatedp tree)
           (nat-listp rest-input)
           (mv-nth 0 (parse-alpha/digit/dash rest-input))
           (mv-nth 0 (parse-bit rest-input))
           (mv-nth 0 (parse-digit rest-input))
           (mv-nth 0 (parse-hexdig rest-input))
           (mv-nth 0 (parse-ichar #\. rest-input))
           (mv-nth 0 (parse-ichar #\- rest-input))
           (equal input (append (tree->string tree) rest-input)))
      (equal (parse-conc-rest-comp input)
             (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable fail-cwsp-when-match-alt/conc/rep)))

(defruled parse-conc-rest-comp-when-tree-match-induction-step-2
  :parents (grammar-parser-completeness)
  :short "Second induction step of
          the completeness lemma for
          @(tsee parse-conc-rest-comp)."
  (implies
   (and (not (mv-nth 0 (parse-1*cwsp input)))
        (not (mv-nth 0 (parse-repetition (mv-nth 2 (parse-1*cwsp input)))))
        (pred-repetition (mv-nth 2 (parse-1*cwsp input))))
   (pred-conc-rest-comp input))
  :enable pred-conc-rest-comp

  :prep-lemmas
  ((defrule lemma
     (implies
      (and (not (mv-nth 0 (parse-1*cwsp input)))
           (not (mv-nth 0 (parse-repetition (mv-nth 2 (parse-1*cwsp input)))))
           (pred-repetition (mv-nth 2 (parse-1*cwsp input)))
           (tree-match-element-p tree
                                 element
                                 *all-concrete-syntax-rules*)
           (equal element (!_ (/_ (1*_ *c-wsp*)
                                  *repetition*)))
           (tree-terminatedp tree)
           (nat-listp rest-input)
           (mv-nth 0 (parse-alpha/digit/dash rest-input))
           (mv-nth 0 (parse-bit rest-input))
           (mv-nth 0 (parse-digit rest-input))
           (mv-nth 0 (parse-hexdig rest-input))
           (mv-nth 0 (parse-ichar #\. rest-input))
           (mv-nth 0 (parse-ichar #\- rest-input))
           (equal input (append (tree->string tree) rest-input)))
      (equal (parse-conc-rest-comp input)
             (mv nil (tree-fix tree) rest-input)))
     :expand (:free (element rules) (tree-match-element-p tree element rules))
     :enable (parse-conc-rest-comp
              fail-cwsp-when-match-alt/conc/rep))))

(defsection
  parse-alt/conc/rep/elem/group/option-when-tree-/-tree-list-match-lemmas
  :parents (grammar-parser-completeness)
  :short "Completeness lemmas for the mutually recursive parsing functions."

  (defthm-parse-alt/conc/rep/elem/group/option-flag

    (defthmd parse-alternation-when-tree-match-lemma
      (pred-alternation input)
      :flag parse-alternation)

    (defthmd parse-concatenation-when-tree-match-lemma
      (pred-concatenation input)
      :flag parse-concatenation)

    (defthmd parse-repetition-when-tree-match-lemma
      (pred-repetition input)
      :flag parse-repetition)

    (defthmd parse-element-when-tree-match-lemma
      (pred-element input)
      :flag parse-element)

    (defthmd parse-group-when-tree-match-lemma
      (pred-group input)
      :flag parse-group)

    (defthmd parse-option-when-tree-match-lemma
      (pred-option input)
      :flag parse-option)

    (defthmd parse-alt-rest-when-tree-list-match-lemma
      (pred-alt-rest input)
      :flag parse-alt-rest)

    (defthmd parse-alt-rest-comp-when-tree-match-lemma
      (pred-alt-rest-comp input)
      :flag parse-alt-rest-comp)

    (defthmd parse-conc-rest-when-tree-list-match-lemma
      (pred-conc-rest input)
      :flag parse-conc-rest)

    (defthmd parse-conc-rest-comp-when-tree-match-lemma
      (pred-conc-rest-comp input)
      :flag parse-conc-rest-comp)

    :hints
    (("Goal"
      :in-theory
      (enable
       parse-alternation-when-tree-match-induction-step-1
       parse-alternation-when-tree-match-induction-step-2
       parse-concatenation-when-tree-match-induction-step-1
       parse-concatenation-when-tree-match-induction-step-2
       parse-repetition-when-tree-match-induction-step-1
       parse-repetition-when-tree-match-induction-step-2
       parse-element-when-tree-match-induction-step-1
       parse-element-when-tree-match-induction-step-2
       parse-element-when-tree-match-induction-step-3
       parse-element-when-tree-match-induction-step-4
       parse-element-when-tree-match-induction-step-5
       parse-element-when-tree-match-induction-step-6
       parse-element-when-tree-match-base-case
       parse-group-when-tree-match-base-case
       parse-group-when-tree-match-induction-step-1
       parse-group-when-tree-match-induction-step-2
       parse-group-when-tree-match-induction-step-3
       parse-option-when-tree-match-base-case
       parse-option-when-tree-match-induction-step-1
       parse-option-when-tree-match-induction-step-2
       parse-option-when-tree-match-induction-step-3
       parse-alt-rest-when-tree-list-match-induction-step-1
       parse-alt-rest-when-tree-list-match-induction-step-2
       parse-alt-rest-comp-when-tree-match-base-case
       parse-alt-rest-comp-when-tree-match-induction-step-1
       parse-alt-rest-comp-when-tree-match-induction-step-2
       parse-conc-rest-when-tree-list-match-induction-step-1
       parse-conc-rest-when-tree-list-match-induction-step-2
       parse-conc-rest-comp-when-tree-match-base-case
       parse-conc-rest-comp-when-tree-match-induction-step-1
       parse-conc-rest-comp-when-tree-match-induction-step-2)))))

(defrule parse-alternation-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-alternation)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *alternation*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-alt-rest-comp rest-input))
                (mv-nth 0 (parse-conc-rest-comp rest-input))
                (mv-nth 0 (parse-alpha/digit/dash rest-input))
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (equal (parse-alternation (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :use ((:instance parse-alternation-when-tree-match-lemma
                   (input (nat-list-fix
                           (append (tree->string tree) rest-input))))
        (:instance parse-alternation-of-nat-list-fix-input
                   (input (append (tree->string tree) rest-input))))
  :disable ((:congruence parse-alternation-nat-list-equiv-congruence-on-input)))

(defrule parse-concatenation-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-concatenation)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *concatenation*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-conc-rest-comp rest-input))
                (mv-nth 0 (parse-alpha/digit/dash rest-input))
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (equal (parse-concatenation (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :use ((:instance parse-concatenation-when-tree-match-lemma
                   (input (nat-list-fix
                           (append (tree->string tree) rest-input))))
        (:instance parse-concatenation-of-nat-list-fix-input
                   (input (append (tree->string tree) rest-input))))
  :disable ((:congruence parse-concatenation-nat-list-equiv-congruence-on-input)))

(defrule parse-repetition-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-repetition)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *repetition*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-alpha/digit/dash rest-input))
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (equal (parse-repetition (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :use ((:instance parse-repetition-when-tree-match-lemma
                   (input (nat-list-fix
                           (append (tree->string tree) rest-input))))
        (:instance parse-repetition-of-nat-list-fix-input
                   (input (append (tree->string tree) rest-input))))
  :disable ((:congruence parse-repetition-nat-list-equiv-congruence-on-input)))

(defrule parse-element-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-element)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *element*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-alpha/digit/dash rest-input))
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (equal (parse-element (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :use ((:instance parse-element-when-tree-match-lemma
                   (input (nat-list-fix
                           (append (tree->string tree) rest-input))))
        (:instance parse-element-of-nat-list-fix-input
                   (input (append (tree->string tree) rest-input))))
  :disable ((:congruence parse-element-nat-list-equiv-congruence-on-input)))

(defrule parse-group-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-group)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *group*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-group (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :use ((:instance parse-group-when-tree-match-lemma
                   (input (nat-list-fix
                           (append (tree->string tree) rest-input))))
        (:instance parse-group-of-nat-list-fix-input
                   (input (append (tree->string tree) rest-input))))
  :disable ((:congruence parse-group-nat-list-equiv-congruence-on-input)))

(defrule parse-option-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-option)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *option*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree))
           (equal (parse-option (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :use ((:instance parse-option-when-tree-match-lemma
                   (input (nat-list-fix
                           (append (tree->string tree) rest-input))))
        (:instance parse-option-of-nat-list-fix-input
                   (input (append (tree->string tree) rest-input))))
  :disable ((:congruence parse-option-nat-list-equiv-congruence-on-input)))

(defrule parse-alt-rest-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-alt-rest)."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ (*_ *c-wsp*)
                                                          "/"
                                                          (*_ *c-wsp*)
                                                          *concatenation*)))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-alt-rest-comp rest-input))
                (mv-nth 0 (parse-conc-rest-comp rest-input))
                (mv-nth 0 (parse-alpha/digit/dash rest-input))
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (equal (parse-alt-rest (append (tree-list->string trees)
                                                  rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :use ((:instance parse-alt-rest-when-tree-list-match-lemma
                   (input (nat-list-fix
                           (append (tree-list->string trees) rest-input))))
        (:instance parse-alt-rest-of-nat-list-fix-input
                   (input (append (tree-list->string trees) rest-input))))
  :disable ((:congruence parse-alt-rest-nat-list-equiv-congruence-on-input)))

(defrule parse-alt-rest-comp-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-alt-rest-comp)."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ (*_ *c-wsp*)
                                              "/"
                                              (*_ *c-wsp*)
                                              *concatenation*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-conc-rest-comp rest-input))
                (mv-nth 0 (parse-alpha/digit/dash rest-input))
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (equal (parse-alt-rest-comp
                   (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :use ((:instance parse-alt-rest-comp-when-tree-match-lemma
                   (input (nat-list-fix
                           (append (tree->string tree) rest-input))))
        (:instance parse-alt-rest-comp-of-nat-list-fix-input
                   (input (append (tree->string tree) rest-input))))
  :disable ((:congruence parse-alt-rest-comp-nat-list-equiv-congruence-on-input)))

(defrule parse-conc-rest-when-tree-list-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-conc-rest)."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ (1*_ *c-wsp*)
                                                          *repetition*)))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (mv-nth 0 (parse-conc-rest-comp rest-input))
                (mv-nth 0 (parse-alpha/digit/dash rest-input))
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (equal (parse-conc-rest (append (tree-list->string trees)
                                                    rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :use ((:instance parse-conc-rest-when-tree-list-match-lemma
                   (input (nat-list-fix
                           (append (tree-list->string trees) rest-input))))
        (:instance parse-conc-rest-of-nat-list-fix-input
                   (input (append (tree-list->string trees) rest-input))))
  :disable ((:congruence parse-conc-rest-nat-list-equiv-congruence-on-input)))

(defrule parse-conc-rest-comp-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-conc-rest-comp)."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ (1*_ *c-wsp*)
                                              *repetition*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-alpha/digit/dash rest-input))
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input)))
           (equal (parse-conc-rest-comp
                   (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :use ((:instance parse-conc-rest-comp-when-tree-match-lemma
                   (input (nat-list-fix
                           (append (tree->string tree) rest-input))))
        (:instance parse-conc-rest-comp-of-nat-list-fix-input
                   (input (append (tree->string tree) rest-input))))
  :disable ((:congruence parse-conc-rest-comp-nat-list-equiv-congruence-on-input)))

(defrule parse-elements-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-elements)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *elements*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-alt-rest-comp rest-input))
                (mv-nth 0 (parse-conc-rest-comp rest-input))
                (mv-nth 0 (parse-repetition rest-input))
                (mv-nth 0 (parse-alpha/digit/dash rest-input))
                (mv-nth 0 (parse-bit rest-input))
                (mv-nth 0 (parse-digit rest-input))
                (mv-nth 0 (parse-hexdig rest-input))
                (mv-nth 0 (parse-ichar #\. rest-input))
                (mv-nth 0 (parse-ichar #\- rest-input))
                (mv-nth 0 (parse-cwsp rest-input)))
           (equal (parse-elements (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-elements
           fail-alt-rest-comp-when-match-*cwsp
           fail-conc-rest-comp-when-match-*cwsp
           fail-alpha/digit/dash-when-match-*cwsp
           fail-bit-when-match-*cwsp
           fail-digit-when-match-*cwsp
           fail-hexdig-when-match-*cwsp
           fail-dot-when-match-*cwsp
           fail-dash-when-match-*cwsp))

(defrule parse-equal-/-equal-slash-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-equal-/-equal-slash)."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ "=")
                                          (/_ "=/"))
                                      *all-concrete-syntax-rules*)
                (mv-nth 0 (parse-ichar #\/ rest-input)))
           (equal (parse-equal-/-equal-slash (append (tree->string tree)
                                                     rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-equal-/-equal-slash
           fail-equal-slash-when-match-equal-and-rest-fail-slash))

(defrule parse-defined-as-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-defined-as)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *defined-as*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-cwsp rest-input))
                (mv-nth 0 (parse-ichar #\/ rest-input)))
           (equal (parse-defined-as (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-defined-as
           fail-cwsp-when-match-equal-/-equal-slash
           fail-slash-when-match-*cwsp))

(defrule parse-rule-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-rule)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *rule*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-wsp rest-input)))
           (equal (parse-rule (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-rule
           fail-alpha/digit/dash-when-match-defined-as
           fail-cwsp-when-match-elements
           fail-slash-when-match-elements
           fail-alpha/digit/dash-when-match-cnl
           fail-bit/digit/hexdig/dot/dash-when-match-cnl
           fail-slash/htab/sp/wsp/rep-when-match-cnl
           fail-alt-rest-comp-when-match-cnl
           fail-conc-rest-comp-when-match-cnl
           fail-cwsp-when-match-cnl))

(defrule parse-*cwsp-cnl-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-*cwsp-cnl)."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ (*_ *c-wsp*)
                                              *c-nl*))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-wsp rest-input)))
           (equal (parse-*cwsp-cnl (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-*cwsp-cnl
           fail-cwsp-when-match-cnl))

(defrule parse-rule-/-*cwsp-cnl-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-rule-/-*cwsp-cnl)."
  (implies (and (tree-match-element-p tree
                                      (!_ (/_ *rule*)
                                          (/_ (!_ (/_ (*_ *c-wsp*)
                                                      *c-nl*))))
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (mv-nth 0 (parse-wsp rest-input)))
           (equal (parse-rule-/-*cwsp-cnl (append (tree->string tree)
                                                  rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-rule-/-*cwsp-cnl
           fail-rule-when-match-*cwsp-cnl))

(defrule parse-*-rule-/-*cwsp-cnl-when-tree-list-match-and-restriction
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-*-rule-/-*cwsp-cnl)."
  (implies (and (tree-list-match-repetition-p trees
                                              (*_ (!_ (/_ *rule*)
                                                      (/_ (!_ (/_ (*_ *c-wsp*)
                                                                  *c-nl*)))))
                                              *all-concrete-syntax-rules*)
                (tree-list-terminatedp trees)
                (tree-list-*-rule-/-*cwsp-cnl-restriction-p trees)
                (mv-nth 0 (parse-rule-/-*cwsp-cnl rest-input))
                (mv-nth 0 (parse-wsp rest-input)))
           (equal (parse-*-rule-/-*cwsp-cnl (append (tree-list->string trees)
                                                    rest-input))
                  (mv nil (tree-list-fix trees) (nat-list-fix rest-input))))
  :induct (len trees)
  :enable (parse-*-rule-/-*cwsp-cnl
           tree-list-match-repetition-p-of-0+-reps-when-consp
           tree-list-*-rule-/-*cwsp-cnl-restriction-p
           fail-wsp-when-match-*-rule-/-*cwsp-cnl-and-restriction)
  :disable acl2::nat-list-fix-of-append)

(defrule parse-rulelist-when-tree-match-and-restriction
  :parents (grammar-parser-completeness)
  :short "Completeness theorem for @(tsee parse-rulelist)."
  (implies (and (tree-match-element-p tree
                                      (element-rulename *rulelist*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (tree-rulelist-restriction-p tree)
                (mv-nth 0 (parse-rule-/-*cwsp-cnl rest-input))
                (mv-nth 0 (parse-wsp rest-input)))
           (equal (parse-rulelist (append (tree->string tree) rest-input))
                  (mv nil (tree-fix tree) (nat-list-fix rest-input))))
  :expand (:free (element rules) (tree-match-element-p tree element rules))
  :enable (parse-rulelist
           tree-list-match-repetition-p-of-1+-repetitions
           tree-rulelist-restriction-p
           fail-wsp-when-match-*-rule-/-*cwsp-cnl-and-restriction))

(defrule parse-grammar-when-tree-match
  :parents (grammar-parser-completeness)
  :short "Top-level completeness theorem of the parser of ABNF grammars."
  :long
  (xdoc::topstring
   (xdoc::p
    "For every terminated tree rooted at @('rulelist')
     that satisfies the "
    (xdoc::seetopic "grammar-parser-disambiguating-restrictions"
                    "disambiguating restrictions")
    ", @(tsee parse-grammar) succeeds on the string at the leaves of the tree
     and returns that tree.")
   (xdoc::p
    "This is proved from @(tsee parse-rulelist-when-tree-match-and-restriction)
     and the fact that its two parsing failure hypotheses are satisfied
     because there is no extra input
     beyond the string at the leaves of the tree.")
   (xdoc::p
    "An alternative formulation is to avoid @(tsee tree-fix)
     but include the hypothesis that the tree satisfies @(tsee treep)."))
  (implies (and (tree-match-element-p tree
                                      (element-rulename *rulelist*)
                                      *all-concrete-syntax-rules*)
                (tree-terminatedp tree)
                (tree-rulelist-restriction-p tree))
           (equal (parse-grammar (tree->string tree))
                  (tree-fix tree)))
  :enable parse-grammar
  :disable parse-rulelist-when-tree-match-and-restriction
  :use (:instance parse-rulelist-when-tree-match-and-restriction
                  (rest-input nil)))

; enabled just before the completeness theorems:
(in-theory (disable tree->string
                    tree-list->string
                    tree-list-list->string
                    tree-terminatedp
                    tree-list-match-repetition-p-of-1-repetition))
