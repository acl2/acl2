; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "keywords")
(include-book "grammar")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ keywords-grammar-validation
  :parents (keywords)
  :short "Validation of the definition of @(tsee jkeywordp)
          with respect to the ABNF grammar of Java."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate @(tsee jkeywordp) defines (non-restricted) keywords
     `directly', i.e. without reference to the grammar.
     Here we introduce an alternative predicate based on the grammar,
     and we show it equivalent to @(tsee jkeywordp).")
   (xdoc::p
    "We only perform this validation for non-restricted keywords,
     and not for restricted keywords (see @(tsee restricted-jkeywordp),
     because the latter do not have a grammar rule."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk grammar-jkeywordp (x)
  :returns (yes/no booleanp)
  :short "Definition of (non-restricted) keywords based on the grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This defines a (non-restricted) keyword as a string at the leaves of
     a terminated tree rooted at the @('keyword') nonterminal."))
  (exists (tree)
          (and (abnf-tree-with-root-p tree "keyword")
               (equal (abnf::tree->string tree)
                      x)))
  :guard-hints (("Goal" :in-theory (enable abnf-tree-with-root-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jkeyword-tree ((keyword jkeywordp))
  :returns
  (tree (abnf-tree-with-root-p tree "keyword")
        :hints (("Goal"
                 :in-theory
                 (enable jkeywordp
                         equal-of-ascii=>string-to-equal-of-string=>unicode))))
  :short "Tree for a (non-restricted) keyword."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in @(tsee grammar-jkeywordp-when-jkeywordp)."))
  (let ((keyword (mbe :logic (if (jkeywordp keyword)
                                 keyword
                               (string=>unicode "_"))
                      :exec keyword)))
    (abnf::tree-nonleaf (abnf::rulename "keyword")
                        (list (list (abnf::tree-leafterm keyword)))))
  :guard-hints (("Goal" :in-theory (enable jkeywordp)))
  :hooks (:fix)
  ///

  (defrule tree->string-of-keyword-tree
    (equal (abnf::tree->string (jkeyword-tree keyword))
           (if (jkeywordp keyword)
               keyword
             (string=>unicode "_")))
    :enable (abnf::tree->string jkeywordp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled grammar-jkeywordp-when-jkeywordp
  :short "Proof of @(tsee grammar-jkeywordp) from @(tsee jkeywordp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved using @(tsee jkeyword-tree)
     as witness for the existential quantification:
     if @('x') is a (non-restricted) keyword,
     then we can use its tree as witness,
     since its leaves are the keyword @('x') as well."))
  (implies (jkeywordp x)
           (grammar-jkeywordp x))
  :use (:instance grammar-jkeywordp-suff
        (tree (jkeyword-tree x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled jkeywordp-when-grammar-jkeywordp
  :short "Proof of @(tsee jkeywordp) from @(tsee grammar-jkeywordp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved via a lemma asserting that
     a terminated tree rooted at @('keyword')
     has leaves that satisfy @(tsee jkeywordp).
     The lemma is proved by exhaustively opening @(tsee abnf-tree-with-root-p),
     which splits into many cases corresponding to
     the many alternatives of the @('keyword') rule,
     thus prescribing the exact form of the tree in each case,
     and in particular its leaves.
     The theorem is then proved by instantiating the lemma
     to the witness tree of @(tsee grammar-jkeywordp)."))
  (implies (grammar-jkeywordp x)
           (jkeywordp x))
  :enable (grammar-jkeywordp)
  :use (:instance lemma (tree (grammar-jkeywordp-witness x)))

  :prep-lemmas
  ((defrule lemma
     (implies (abnf-tree-with-root-p tree "keyword")
              (jkeywordp (abnf::tree->string tree)))
     :rule-classes nil
     :expand ((:free (element)
               (abnf::tree-match-element-p tree element *grammar*)))
     :enable (abnf-tree-with-root-p
              abnf::tree-match-element-p
              abnf::tree-list-match-repetition-p-of-1-repetition
              abnf::tree-match-char-val-p
              abnf::nat-match-sensitive-char-p
              abnf::nat-match-insensitive-char-p
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

(defruled jkeywordp-is-grammar-jkeywordp
  :short "Equivalence of @(tsee jkeywordp) and @(tsee grammar-jkeywordp)."
  (equal (jkeywordp x)
         (grammar-jkeywordp x))
  :use (grammar-jkeywordp-when-jkeywordp
        jkeywordp-when-grammar-jkeywordp))
