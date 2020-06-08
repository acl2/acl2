; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "boolean-literals")
(include-book "grammar")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ boolean-literals-grammar-validation
  :parents (boolean-literals)
  :short "Validation of the definition of @(tsee boolean-literalp)
          with respect to the ABNF grammar of Java."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate @(tsee boolean-literalp) defines boolean literals
     `directly', i.e. without reference to the grammar.
     Here we introduce an alternative predicate based on the grammar,
     and we show it equivalent to @(tsee boolean-literalp)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk grammar-boolean-literalp (x)
  :returns (yes/no booleanp)
  :short "Definition of boolean literals based on the grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This defines a boolean literal as a string at the leaves of
     a terminated tree rooted at the @('boolean-literal') nonterminal."))
  (exists (tree)
          (and (abnf-tree-with-root-p tree "boolean-literal")
               (equal (abnf::tree->string tree)
                      x)))
  :guard-hints (("Goal" :in-theory (enable abnf-tree-with-root-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-literal-tree ((literal boolean-literalp))
  :returns
  (tree (abnf-tree-with-root-p tree "boolean-literal")
        :hints (("Goal"
                 :in-theory
                 (enable boolean-literalp
                         equal-of-ascii=>string-to-equal-of-string=>unicode))))
  :short "Tree for a boolean literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in
     @(tsee grammar-boolean-literalp-when-boolean-literalp)."))
  (b* ((literal (mbe :logic (if (boolean-literalp literal)
                                literal
                              (string=>unicode "true"))
                     :exec literal)))
    (abnf::tree-nonleaf (abnf::rulename "boolean-literal")
                        (list (list (abnf::tree-leafterm literal)))))
  :guard-hints (("Goal" :in-theory (enable boolean-literalp)))
  :hooks (:fix)
  ///

  (defrule tree->string-of-boolean-literal-tree
    (equal (abnf::tree->string (boolean-literal-tree literal))
           (if (boolean-literalp literal)
               literal
             (string=>unicode "true")))
    :enable (abnf::tree->string boolean-literalp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled grammar-boolean-literalp-when-boolean-literalp
  :short "Proof of @(tsee grammar-boolean-literalp)
          from @(tsee boolean-literalp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved using @(tsee boolean-literal-tree)
     as witness for the existential quantification:
     if @('x') is a boolean literal,
     then we can use its tree as witness,
     since its leaves are the boolean literal @('x') as well."))
  (implies (boolean-literalp x)
           (grammar-boolean-literalp x))
  :use (:instance grammar-boolean-literalp-suff
        (tree (boolean-literal-tree x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled boolean-literalp-when-grammar-boolean-literalp
  :short "Proof of @(tsee boolean-literalp)
          from @(tsee grammar-boolean-literalp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved via a lemma asserting that
     a terminated tree rooted at @('boolean-literal')
     has leaves that satisfy @(tsee boolean-literalp).
     The lemma is proved by exhaustively opening @(tsee abnf-tree-with-root-p),
     which splits into two cases corresponding to
     the two alternatives of the @('boolean-literal') rule,
     thus prescribing the exact form of the tree in each case,
     and in particular its leaves.
     The theorem is then proved by instantiating the lemma
     to the witness tree of @(tsee grammar-boolean-literalp)."))
  (implies (grammar-boolean-literalp x)
           (boolean-literalp x))
  :enable (grammar-boolean-literalp)
  :use (:instance lemma (tree (grammar-boolean-literalp-witness x)))

  :prep-lemmas
  ((defrule lemma
     (implies (abnf-tree-with-root-p tree "boolean-literal")
              (boolean-literalp (abnf::tree->string tree)))
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

(defruled boolean-literalp-is-grammar-boolean-literalp
  :short "Equivalence of @(tsee boolean-literalp)
          and @(tsee grammar-boolean-literalp)."
  (equal (boolean-literalp x)
         (grammar-boolean-literalp x))
  :use (grammar-boolean-literalp-when-boolean-literalp
        boolean-literalp-when-grammar-boolean-literalp))
