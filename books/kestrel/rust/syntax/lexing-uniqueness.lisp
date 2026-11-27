; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "extra-grammatical-restrictions")

(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lexing-uniqueness
  :parents (extra-grammatical-restrictions)
  :short "Theorem that an input has at most one correct lexing,
          as to the strings of the lexemes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The specification of lexing is @(tsee lexing-okp):
     a relation between a list of lexeme CSTs and an input.
     We prove that it determines
     where each lexeme starts and ends:
     two lists of CSTs that are both correct lexings of the same input
     have the same strings, in the same order
     (see @(tsee lexeme-cst-list->strings)).
     In particular, they have the same number of lexemes.")
   (xdoc::p
    "The theorem is about the strings of the CSTs, not the CSTs themselves,
     because the grammar gives some strings more than one CST.
     For example, the exponent of the float literal @('1e1_2')
     matches the rule")
   (xdoc::codeblock
    "float-exponent = ( %s\"e\" / %s\"E\" ) [ \"+\" / \"-\" ]"
    "                 *( dec-digit / \"_\" ) dec-digit *( dec-digit / \"_\" )")
   (xdoc::p
    "in two ways:
     the digit that the rule requires can be the @('1') or the @('2').
     The specification accepts both CSTs.")
   (xdoc::p
    "The theorem follows from maximal munch alone
     (see @(tsee lexeme-cst-maximal-p)).
     The first lexemes of two correct lexings of an input
     both start the input,
     so the string of one is a prefix of the string of the other.
     Then the second, with the input that follows it,
     is a candidate for extending the first,
     which is maximal;
     so the two strings are equal,
     the two lexings continue from the same remaining input,
     and the argument repeats.")
   (xdoc::p
    "This is a property of the specification:
     the lexer has no part in it."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lexeme-cst-list->strings ((trees abnf::tree-listp))
  :returns (strings true-listp)
  :short "The strings of a list of lexeme CSTs, one string for each CST."
  :long
  (xdoc::topstring
   (xdoc::p
    "This differs from @(tsee abnf::tree-list->string),
     which appends the strings of the trees into one:
     here the result keeps the boundaries between the lexemes."))
  (b* (((when (endp trees)) nil))
    (cons (abnf::tree->string (car trees))
          (lexeme-cst-list->strings (cdr trees))))
  :hooks (:fix)

  ///

  (defrule lexeme-cst-list->strings-when-not-consp
    (implies (not (consp trees))
             (equal (lexeme-cst-list->strings trees)
                    nil)))

  (defret len-of-lexeme-cst-list->strings
    (equal (len strings)
           (len trees))
    :hints (("Goal" :induct t :in-theory (enable fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; One lexeme.

; If two valid lexeme CSTs both start the same input,
; the string of the first is a prefix of the string of the second,
; and the first is maximal, then the two strings are equal:
; the second, with the input that follows it,
; is a candidate in the definition of lexeme-cst-maximal-p.

(defruledl tree->string-when-maximal-and-prefixp
  (implies (and (abnf::treep tree2)
                (nat-listp input)
                (prefixp (abnf::tree->string tree1) input)
                (prefixp (abnf::tree->string tree2) input)
                (lexeme-cst-maximal-p
                 tree1
                 (nthcdr (len (abnf::tree->string tree1)) input))
                (lexeme-cst-okp tree2)
                (lexeme-cst-float-period-okp
                 tree2
                 (nthcdr (len (abnf::tree->string tree2)) input))
                (prefixp (abnf::tree->string tree1)
                         (abnf::tree->string tree2)))
           (equal (abnf::tree->string tree2)
                  (abnf::tree->string tree1)))
  :use (:instance lexeme-cst-maximal-p-necc
                  (tree tree1)
                  (rest-input (nthcdr (len (abnf::tree->string tree1)) input))
                  (rest-input2 (nthcdr (len (abnf::tree->string tree2))
                                       input))))

; Two maximal valid lexeme CSTs that start the same input
; have the same string,
; since one of the two strings is a prefix of the other.

(defrulel tree->string-when-both-maximal
  (implies (and (abnf::treep tree1)
                (abnf::treep tree2)
                (nat-listp input)
                (prefixp (abnf::tree->string tree1) input)
                (prefixp (abnf::tree->string tree2) input)
                (lexeme-cst-okp tree1)
                (lexeme-cst-okp tree2)
                (lexeme-cst-maximal-p
                 tree1
                 (nthcdr (len (abnf::tree->string tree1)) input))
                (lexeme-cst-maximal-p
                 tree2
                 (nthcdr (len (abnf::tree->string tree2)) input))
                (lexeme-cst-float-period-okp
                 tree1
                 (nthcdr (len (abnf::tree->string tree1)) input))
                (lexeme-cst-float-period-okp
                 tree2
                 (nthcdr (len (abnf::tree->string tree2)) input)))
           (equal (abnf::tree->string tree1)
                  (abnf::tree->string tree2)))
  :rule-classes nil
  :use (tree->string-when-maximal-and-prefixp
        (:instance tree->string-when-maximal-and-prefixp
                   (tree1 tree2)
                   (tree2 tree1))
        (:instance acl2::prefixp-one-way-or-another
                   (x (abnf::tree->string tree1))
                   (y (abnf::tree->string tree2))
                   (z input))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; All the lexemes.

; The first lexemes of two correct lexings of an input have the same string.

(defruledl tree->string-of-car-when-lexing-okp
  (implies (and (lexing-okp trees1 input)
                (lexing-okp trees2 input)
                (abnf::tree-listp trees1)
                (abnf::tree-listp trees2)
                (nat-listp input)
                (consp trees1)
                (consp trees2))
           (equal (equal (abnf::tree->string (car trees1))
                         (abnf::tree->string (car trees2)))
                  t))
  :expand ((lexing-okp trees1 input)
           (lexing-okp trees2 input))
  :use (:instance tree->string-when-both-maximal
                  (tree1 (car trees1))
                  (tree2 (car trees2))))

; The other lexemes of a correct lexing
; are a correct lexing of the input after the first lexeme.

(defruledl lexing-okp-of-cdr-when-lexing-okp
  (implies (and (abnf::tree-listp trees)
                (nat-listp input)
                (consp trees)
                (lexing-okp trees input))
           (lexing-okp (cdr trees)
                       (nthcdr (len (abnf::tree->string (car trees)))
                               input)))
  :expand (lexing-okp trees input))

; So the other lexemes of the second lexing are a correct lexing
; of the input after the first lexeme of the first lexing.

(defruledl lexing-okp-of-cdr-when-lexing-okp-of-other
  (implies (and (abnf::tree-listp trees1)
                (abnf::tree-listp trees2)
                (nat-listp input)
                (consp trees1)
                (consp trees2)
                (lexing-okp trees1 input)
                (lexing-okp trees2 input))
           (lexing-okp (cdr trees2)
                       (nthcdr (len (abnf::tree->string (car trees1)))
                               input)))
  :use (tree->string-of-car-when-lexing-okp
        (:instance lexing-okp-of-cdr-when-lexing-okp (trees trees2))))

; A correct lexing of an input has no lexemes exactly when the input is empty.

(defruledl consp-when-lexing-okp
  (implies (and (lexing-okp trees input)
                (nat-listp input))
           (equal (consp trees)
                  (consp input)))
  :expand (lexing-okp trees input)
  :enable prefixp)

; The two lexings advance together:
; after the first lexeme of each, the same input remains.

(local
 (defun lexing-uniqueness-induction (trees1 trees2 input)
   (if (or (endp trees1) (endp trees2))
       (list trees1 trees2 input)
     (lexing-uniqueness-induction
      (cdr trees1)
      (cdr trees2)
      (nthcdr (len (abnf::tree->string (car trees1))) input)))))

(defruledl equal-of-lexeme-cst-list->strings-when-lexing-okp-lemma
  (implies (and (abnf::tree-listp trees1)
                (abnf::tree-listp trees2)
                (nat-listp input)
                (lexing-okp trees1 input)
                (lexing-okp trees2 input))
           (equal (lexeme-cst-list->strings trees1)
                  (lexeme-cst-list->strings trees2)))
  :induct (lexing-uniqueness-induction trees1 trees2 input)
  :enable (lexeme-cst-list->strings
           tree->string-of-car-when-lexing-okp
           lexing-okp-of-cdr-when-lexing-okp
           lexing-okp-of-cdr-when-lexing-okp-of-other
           consp-when-lexing-okp))

(defrule equal-of-lexeme-cst-list->strings-when-lexing-okp
  :short "Two correct lexings of an input have the same strings."
  :long
  (xdoc::topstring
   (xdoc::p
    "If two lists of lexeme CSTs both satisfy @(tsee lexing-okp)
     for the same input,
     then their lexemes have the same strings, in the same order.
     So the specification determines the lexemes of an input
     as to where each starts and ends;
     it does not determine the CSTs
     (see @(see lexing-uniqueness))."))
  (implies (and (lexing-okp trees1 input)
                (lexing-okp trees2 input))
           (equal (lexeme-cst-list->strings trees1)
                  (lexeme-cst-list->strings trees2)))
  :rule-classes nil
  :use (:instance equal-of-lexeme-cst-list->strings-when-lexing-okp-lemma
                  (trees1 (abnf::tree-list-fix trees1))
                  (trees2 (abnf::tree-list-fix trees2))
                  (input (nat-list-fix input))))

(defrule equal-of-len-when-lexing-okp
  :short "Two correct lexings of an input have the same number of lexemes."
  (implies (and (lexing-okp trees1 input)
                (lexing-okp trees2 input))
           (equal (len trees1)
                  (len trees2)))
  :rule-classes nil
  :use (equal-of-lexeme-cst-list->strings-when-lexing-okp
        (:instance len-of-lexeme-cst-list->strings (trees trees1))
        (:instance len-of-lexeme-cst-list->strings (trees trees2)))
  :disable len-of-lexeme-cst-list->strings)
