; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

;TODO:
;; (include-book "decimal-digits")
(include-book "kestrel/java/language/decimal-digits" :dir :system)

;TODO:
;; (include-book "grammar")
(include-book "kestrel/java/language/grammar" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ decimal-digits-grammar-validation
  :parents (decimal-digits)
  :short "Validation of the definition of @(tsee digitp)
          with respect to the ABNF grammar of Java."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate @(tsee digitp) defines decimal digits
     `directly', i.e. without reference to the grammar.
     Here we introduce an alternative predicate based on the grammar,
     and we show it equivalent to @(tsee digitp)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk grammar-digitp (x)
  :returns (yes/no booleanp)
  :short "Definition of decimal digits based on the grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This defines a decimal digit as a string at the leaves of
     a terminated tree rooted at the @('digit') nonterminal.
     The string is always a singleton.")
   (xdoc::p
    "This characterizes a (singleton) list of Unicode characters,
     while @(tsee digitp) characterizes a single Unicode character.
     Thus, the equivalence theorem has to take this into account."))
  (exists (tree)
          (and (abnf-tree-with-root-p tree "digit")
               (equal (abnf::tree->string tree)
                      x)))
  :guard-hints (("Goal" :in-theory (enable abnf-tree-with-root-p)))
  ///

  (defruled singleton-when-grammar-digitp
    (implies (grammar-digitp x)
             (equal (len x) 1))
    :enable (grammar-digitp
             abnf-tree-with-root-p
             abnf::tree-terminatedp
             abnf::tree-list-terminatedp
             abnf::tree-list-list-terminatedp
             abnf::tree-match-element-p
             abnf::tree-list-match-repetition-p-of-1-repetition
             abnf::tree-match-char-val-p
             abnf::tree->string
             abnf::tree-list->string
             abnf::tree-list-list->string
             acl2::equal-len-const)
    :expand ((:free (tree element)
              (abnf::tree-match-element-p tree element *grammar*)))
    :prep-books
    ((include-book "kestrel/utilities/lists/len-const-theorems" :dir :system)
     (include-book "std/lists/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit-tree ((digit digitp))
  :returns
  (tree (abnf-tree-with-root-p tree "digit")
        :hints (("Goal"
                 :in-theory
                 (enable digitp
                         digit-fix
                         abnf-tree-with-root-p
                         abnf::tree-terminatedp
                         abnf::tree-match-element-p
                         abnf::tree-list-match-repetition-p-of-1-repetition
                         abnf::tree-match-char-val-p
                         abnf::nat-match-insensitive-char-p)
                 :expand ((:free (tree$ element)
                           (abnf::tree-match-element-p
                            tree$ element *grammar*))))))
  :short "Tree for a decimal digit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in @(tsee grammar-digitp-when-digitp).")
   (xdoc::p
    "If the digit is @('0'), the resulting tree has just a leaf subtree.
     Otherwise, it has a @('non-zero-digit') subtree with a leaf subtree."))
  (b* ((digit (digit-fix digit)))
    (if (equal digit (char-code #\0))
        (abnf::tree-nonleaf (abnf::rulename "digit")
                            (list (list (abnf::tree-leafterm (list digit)))))
      (abnf::tree-nonleaf
       (abnf::rulename "digit")
       (list
        (list
         (abnf::tree-nonleaf (abnf::rulename "non-zero-digit")
                             (list
                              (list
                               (abnf::tree-leafterm (list digit))))))))))
  :guard-hints (("Goal" :in-theory (enable digitp)))
  ///

  (defrule tree->string-of-digit-tree
    (equal (abnf::tree->string (digit-tree digit))
           (list (digit-fix digit)))
    :enable (abnf::tree->string digitp digit-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled grammar-digitp-when-digitp
  :short "Proof of @(tsee grammar-digitp) from @(tsee digitp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved using @(tsee digit-tree)
     as witness for the existential quantification:
     if @('x') is a digit
     then we can use its tree as witness,
     since its leaves are the digit @('x') as well."))
  (implies (digitp x)
           (grammar-digitp (list x)))
  :use (:instance grammar-digitp-suff
        (tree (digit-tree x))
        (x (list x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled digitp-when-grammar-digitp
  :short "Proof of @(tsee digitp) from @(tsee grammar-digitp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved via a lemma asserting that
     a terminated tree rooted at @('digit')
     has a string at the leaves whose only element satisfies @(tsee digitp)
     (that this string is a singleton is proved in @(tsee grammar-digitp)).
     The lemma is proved by exhaustively opening @(tsee abnf-tree-with-root-p),
     which splits into cases corresponding to
     the alternatives of the @('digit') and @('non-zero-digit') rules,
     thus prescribing the exact form of the tree in each case,
     and in particular its leaves.
     The theorem is then proved by instantiating the lemma
     to the witness tree of @(tsee grammar-digitp)."))
  (implies (grammar-digitp x)
           (digitp (car x)))
  :enable grammar-digitp
  :use (:instance lemma (tree (grammar-digitp-witness x)))

  :prep-lemmas
  ((defrule lemma
     (implies (abnf-tree-with-root-p tree "digit")
              (digitp (car (abnf::tree->string tree))))
     :rule-classes nil
     :expand ((:free (tree element)
               (abnf::tree-match-element-p tree element *grammar*)))
     :enable (abnf-tree-with-root-p
              abnf::tree-match-element-p
              abnf::tree-list-match-repetition-p-of-1-repetition
              abnf::tree-match-char-val-p
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

(defruled digitp-is-grammar-digitp
  :short "Equivalence of @(tsee digitp) and @(tsee grammar-digitp)."
  (equal (digitp x)
         (grammar-digitp (list x)))
  :use (grammar-digitp-when-digitp
        (:instance digitp-when-grammar-digitp (x (list x)))))
