; Java Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "keywords")
(include-book "grammar")

(local (include-book "kestrel/utilities/lists/len-const-theorems" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ keywords-grammar-validation
  :parents (keywords)
  :short "Validation of the definition of
          @(tsee reserved-keywordp) and @(tsee contextual-keywordp)
          with respect to the ABNF grammar of Java."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicates @(tsee reserved-keywordp) and @(tsee contextual-keywordp)
     define reserved and contextual keywords
     `directly', i.e. without reference to the grammar.
     Here we introduce alternative predicates based on the grammar,
     and we show the equivalent to
     @(tsee reserved-keywordp) and @(tsee contextual-keywordp)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk grammar-reserved-keywordp (x)
  :returns (yes/no booleanp)
  :short "Definition of reserved keywords based on the grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This defines a reserved keyword as a string at the leaves of
     a terminated tree rooted at the @('reserved-keyword') nonterminal."))
  (exists (tree)
          (and (abnf-tree-with-root-p tree "reserved-keyword")
               (equal (abnf::tree->string tree)
                      x)))
  :guard-hints (("Goal" :in-theory (enable abnf-tree-with-root-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk grammar-contextual-keywordp (x)
  :returns (yes/no booleanp)
  :short "Definition of contextual keywords based on the grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This defines a contextual keyword as a string at the leaves of
     a terminated tree rooted at the @('contextual-keyword') nonterminal."))
  (exists (tree)
          (and (abnf-tree-with-root-p tree "contextual-keyword")
               (equal (abnf::tree->string tree)
                      x)))
  :guard-hints (("Goal" :in-theory (enable abnf-tree-with-root-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define reserved-keyword-tree ((keyword reserved-keywordp))
  :returns
  (tree (abnf-tree-with-root-p tree "reserved-keyword")
        :hints (("Goal"
                 :in-theory
                 (enable reserved-keywordp
                         equal-of-ascii=>string-to-equal-of-string=>unicode))))
  :short "Tree for a reserved keyword."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in @(tsee grammar-reserved-keywordp-when-reserved-keywordp)."))
  (let ((keyword (mbe :logic (if (reserved-keywordp keyword)
                                 keyword
                               (string=>unicode "_"))
                      :exec keyword)))
    (abnf::tree-nonleaf (abnf::rulename "reserved-keyword")
                        (list (list (abnf::tree-leafterm keyword)))))
  :guard-hints (("Goal" :in-theory (enable reserved-keywordp)))

  ///

  (defrule tree->string-of-reserved-keyword-tree
    (equal (abnf::tree->string (reserved-keyword-tree keyword))
           (if (reserved-keywordp keyword)
               keyword
             (string=>unicode "_")))
    :enable (abnf::tree->string reserved-keywordp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define contextual-keyword-tree ((keyword contextual-keywordp))
  :returns
  (tree (abnf-tree-with-root-p tree "contextual-keyword")
        :hints (("Goal"
                 :in-theory
                 (enable contextual-keywordp
                         equal-of-ascii=>string-to-equal-of-string=>unicode))))
  :short "Tree for a contextual keyword."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in @(tsee grammar-contextual-keywordp-when-contextual-keywordp)."))
  (let ((keyword (mbe :logic (if (contextual-keywordp keyword)
                                 keyword
                               (string=>unicode "yield"))
                      :exec keyword)))
    (abnf::tree-nonleaf (abnf::rulename "contextual-keyword")
                        (list (list (abnf::tree-leafterm keyword)))))
  :guard-hints (("Goal" :in-theory (enable contextual-keywordp)))

  ///

  (defrule tree->string-of-contextual-keyword-tree
    (equal (abnf::tree->string (contextual-keyword-tree keyword))
           (if (contextual-keywordp keyword)
               keyword
             (string=>unicode "yield")))
    :enable (abnf::tree->string contextual-keywordp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled grammar-reserved-keywordp-when-reserved-keywordp
  :short "Proof of @(tsee grammar-reserved-keywordp)
          from @(tsee reserved-keywordp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved using @(tsee reserved-keyword-tree)
     as witness for the existential quantification:
     if @('x') is a reserved keyword,
     then we can use its tree as witness,
     since its leaves are the keyword @('x') as well."))
  (implies (reserved-keywordp x)
           (grammar-reserved-keywordp x))
  :use (:instance grammar-reserved-keywordp-suff
        (tree (reserved-keyword-tree x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled grammar-contextual-keywordp-when-contextual-keywordp
  :short "Proof of @(tsee grammar-contextual-keywordp)
          from @(tsee contextual-keywordp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved using @(tsee contextual-keyword-tree)
     as witness for the existential quantification:
     if @('x') is a contextual keyword,
     then we can use its tree as witness,
     since its leaves are the keyword @('x') as well."))
  (implies (contextual-keywordp x)
           (grammar-contextual-keywordp x))
  :use (:instance grammar-contextual-keywordp-suff
        (tree (contextual-keyword-tree x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled reserved-keywordp-when-grammar-reserved-keywordp
  :short "Proof of @(tsee reserved-keywordp)
          from @(tsee grammar-reserved-keywordp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved via a lemma asserting that
     a terminated tree rooted at @('reserved-keyword')
     has leaves that satisfy @(tsee reserved-keywordp).
     The lemma is proved by exhaustively opening @(tsee abnf-tree-with-root-p),
     which splits into many cases corresponding to
     the many alternatives of the @('reserved-keyword') rule,
     thus prescribing the exact form of the tree in each case,
     and in particular its leaves.
     The theorem is then proved by instantiating the lemma
     to the witness tree of @(tsee grammar-reserved-keywordp)."))
  (implies (grammar-reserved-keywordp x)
           (reserved-keywordp x))
  :enable (grammar-reserved-keywordp)
  :use (:instance lemma (tree (grammar-reserved-keywordp-witness x)))

  :prep-lemmas
  ((defrule lemma
     (implies (abnf-tree-with-root-p tree "reserved-keyword")
              (reserved-keywordp (abnf::tree->string tree)))
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
              acl2::equal-len-const))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled contextual-keywordp-when-grammar-contextual-keywordp
  :short "Proof of @(tsee contextual-keywordp)
          from @(tsee grammar-contextual-keywordp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved via a lemma asserting that
     a terminated tree rooted at @('contextual-keyword')
     has leaves that satisfy @(tsee contextual-keywordp).
     The lemma is proved by exhaustively opening @(tsee abnf-tree-with-root-p),
     which splits into many cases corresponding to
     the many alternatives of the @('contextual-keyword') rule,
     thus prescribing the exact form of the tree in each case,
     and in particular its leaves.
     The theorem is then proved by instantiating the lemma
     to the witness tree of @(tsee grammar-contextual-keywordp)."))
  (implies (grammar-contextual-keywordp x)
           (contextual-keywordp x))
  :enable (grammar-contextual-keywordp)
  :use (:instance lemma (tree (grammar-contextual-keywordp-witness x)))

  :prep-lemmas
  ((defrule lemma
     (implies (abnf-tree-with-root-p tree "contextual-keyword")
              (contextual-keywordp (abnf::tree->string tree)))
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
              acl2::equal-len-const))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled reserved-keywordp-is-grammar-reserved-keywordp
  :short "Equivalence of @(tsee reserved-keywordp)
          and @(tsee grammar-reserved-keywordp)."
  (equal (reserved-keywordp x)
         (grammar-reserved-keywordp x))
  :use (grammar-reserved-keywordp-when-reserved-keywordp
        reserved-keywordp-when-grammar-reserved-keywordp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled contextual-keywordp-is-grammar-contextual-keywordp
  :short "Equivalence of @(tsee contextual-keywordp)
          and @(tsee grammar-contextual-keywordp)."
  (equal (contextual-keywordp x)
         (grammar-contextual-keywordp x))
  :use (grammar-contextual-keywordp-when-contextual-keywordp
        contextual-keywordp-when-grammar-contextual-keywordp))
