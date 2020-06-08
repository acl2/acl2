; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "null-literal")
(include-book "grammar")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ null-literal-grammar-validation
  :parents (null-literal)
  :short "Validation of the definition of @(tsee null-literalp)
          with respect to the ABNF grammar of Java."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate @(tsee null-literalp) defines the null literal
     `directly', i.e. without reference to the grammar.
     Here we introduce an alternative predicate based on the grammar,
     and we show it equivalent to @(tsee null-literalp)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk grammar-null-literalp (x)
  :returns (yes/no booleanp)
  :short "Definition of the null literal based on the grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This defines a null literal as a string at the leaves of
     a terminated tree rooted at the @('null-literal') nonterminal."))
  (exists (tree)
          (and (abnf-tree-with-root-p tree "null-literal")
               (equal (abnf::tree->string tree)
                      x)))
  :guard-hints (("Goal" :in-theory (enable abnf-tree-with-root-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define null-literal-tree ()
  :returns (tree (abnf-tree-with-root-p tree "null-literal"))
  :short "Tree for the null literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in @(tsee grammar-null-literalp-when-null-literalp)."))
  (abnf::tree-nonleaf (abnf::rulename "null-literal")
                      (list (list (abnf::tree-leafterm
                                   (string=>unicode *null-literal*))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled grammar-null-literalp-when-null-literalp
  :short "Proof of @(tsee grammar-null-literalp) from @(tsee null-literalp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved using @(tsee null-literal-tree)
     as witness for the existential quantification:
     if @('x') is the null literal,
     then we can use the tree as witness,
     since its leaves are the null literal @('x') as well."))
  (implies (null-literalp x)
           (grammar-null-literalp x))
  :enable (null-literalp
           equal-of-ascii=>string-to-equal-of-string=>unicode)
  :use (:instance grammar-null-literalp-suff
        (tree (null-literal-tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled null-literalp-when-grammar-null-literalp
  :short "Proof of @(tsee null-literalp) from @(tsee grammar-null-literalp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved via a lemma asserting that
     a terminated tree rooted at @('null-literal')
     has leaves that satisfy @(tsee null-literalp).
     The lemma is proved by exhaustively opening @(tsee abnf-tree-with-root-p),
     thus prescribing the exact form of the tree,
     and in particular its leaves.
     The theorem is then proved by instantiating the lemma
     to the witness tree of @(tsee grammar-null-literalp)."))
  (implies (grammar-null-literalp x)
           (null-literalp x))
  :enable (grammar-null-literalp)
  :use (:instance lemma (tree (grammar-null-literalp-witness x)))

  :prep-lemmas
  ((defrule lemma
     (implies (abnf-tree-with-root-p tree "null-literal")
              (null-literalp (abnf::tree->string tree)))
     :rule-classes nil
     :expand ((:free (element)
               (abnf::tree-match-element-p tree element *grammar*)))
     :enable (abnf-tree-with-root-p
              abnf::tree-match-element-p
              abnf::tree-list-match-repetition-p-of-1-repetition
              abnf::tree-match-char-val-p
              abnf::nat-match-sensitive-char-p
              abnf::treep
              abnf::tree-listp
              abnf::tree-list-listp
              abnf::tree-terminatedp
              abnf::tree-kind
              abnf::tree-nonleaf->rulename?
              abnf::tree-nonleaf->branches
              abnf::tree-leafterm->get
              acl2::equal-len-const)
     :prep-books
     ((include-book "kestrel/utilities/lists/len-const-theorems" :dir :system)
      (include-book "std/lists/top" :dir :system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled null-literalp-is-grammar-null-literalp
  :short "Equivalence of @(tsee null-literalp)
          and @(tsee grammar-null-literalp)."
  (equal (null-literalp x)
         (grammar-null-literalp x))
  :use (grammar-null-literalp-when-null-literalp
        null-literalp-when-grammar-null-literalp))
