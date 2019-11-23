; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
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
  :short "Validation of the definition of @(tsee null-literal-p)
          with respect to the ABNF grammar of Java."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate @(tsee null-literal-p) defines the null literal
     `directly', i.e. without reference to the grammar.
     Here we introduce an alternative predicate based on the grammar,
     and we show it equivalent to @(tsee null-literal-p)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk grammar-null-literal-p (x)
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
    "This is used in @(tsee grammar-null-literal-p-when-null-literal-p)."))
  (abnf::tree-nonleaf (abnf::rulename "null-literal")
                      (list (list (abnf::tree-leafterm
                                   (string=>unicode *null-literal*))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled grammar-null-literal-p-when-null-literal-p
  :short "Proof of @(tsee grammar-null-literal-p) from @(tsee null-literal-p)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved using @(tsee null-literal-tree)
     as witness for the existential quantification:
     if @('x') is the null literal,
     then we can use the tree as witness,
     since its leaves are the null literal @('x') as well."))
  (implies (null-literal-p x)
           (grammar-null-literal-p x))
  :enable (null-literal-p
           equal-of-ascii=>string-to-equal-of-string=>unicode)
  :use (:instance grammar-null-literal-p-suff
        (tree (null-literal-tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled null-literal-p-when-grammar-null-literal-p
  :short "Proof of @(tsee null-literal-p) from @(tsee grammar-null-literal-p)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved via a lemma asserting that
     a terminated tree rooted at @('null-literal')
     has leaves that satisfy @(tsee null-literal-p).
     The lemma is proved by exhaustively opening @(tsee abnf-tree-with-root-p),
     thus prescribing the exact form of the tree,
     and in particular its leaves.
     The theorem is then proved by instantiating the lemma
     to the witness tree of @(tsee grammar-null-literal-p)."))
  (implies (grammar-null-literal-p x)
           (null-literal-p x))
  :enable (grammar-null-literal-p)
  :use (:instance lemma (tree (grammar-null-literal-p-witness x)))

  :prep-lemmas
  ((defrule lemma
     (implies (abnf-tree-with-root-p tree "null-literal")
              (null-literal-p (abnf::tree->string tree)))
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

(defruled null-literal-p-is-grammar-null-literal-p
  :short "Equivalence of @(tsee null-literal-p)
          and @(tsee grammar-null-literal-p)."
  (equal (null-literal-p x)
         (grammar-null-literal-p x))
  :use (grammar-null-literal-p-when-null-literal-p
        null-literal-p-when-grammar-null-literal-p))
