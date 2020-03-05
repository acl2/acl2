; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "decimal-digits")
(include-book "grammar")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ decimal-digits-grammar-validation
  :parents (decimal-digits)
  :short "Validation of the definition of @(tsee dec-digitp)
          with respect to the ABNF grammar of Java."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate @(tsee dec-digitp) defines decimal digits
     `directly', i.e. without reference to the grammar.
     Here we introduce an alternative predicate based on the grammar,
     and we show it equivalent to @(tsee dec-digitp)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk grammar-dec-digitp (x)
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
     while @(tsee dec-digitp) characterizes a single Unicode character.
     Thus, the equivalence theorem has to take this into account."))
  (exists (tree)
          (and (abnf-tree-with-root-p tree "digit")
               (equal (abnf::tree->string tree)
                      x)))
  :guard-hints (("Goal" :in-theory (enable abnf-tree-with-root-p)))
  ///

  (defruled singleton-when-grammar-dec-digitp
    (implies (grammar-dec-digitp x)
             (equal (len x) 1))
    :enable (grammar-dec-digitp
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

(define dec-digit-tree ((digit dec-digitp))
  :returns
  (tree (abnf-tree-with-root-p tree "digit")
        :hints (("Goal"
                 :in-theory
                 (enable dec-digitp
                         dec-digit-fix
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
    "This is used in @(tsee grammar-dec-digitp-when-dec-digitp).")
   (xdoc::p
    "If the digit is @('0'), the resulting tree has just a leaf subtree.
     Otherwise, it has a @('non-zero-digit') subtree with a leaf subtree."))
  (b* ((digit (dec-digit-fix digit)))
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
  :guard-hints (("Goal" :in-theory (enable dec-digitp)))
  :hooks (:fix)
  ///

  (defrule tree->string-of-dec-digit-tree
    (equal (abnf::tree->string (dec-digit-tree digit))
           (list (dec-digit-fix digit)))
    :enable (abnf::tree->string dec-digitp dec-digit-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled grammar-dec-digitp-when-dec-digitp
  :short "Proof of @(tsee grammar-dec-digitp) from @(tsee dec-digitp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved using @(tsee dec-digit-tree)
     as witness for the existential quantification:
     if @('x') is a digit
     then we can use its tree as witness,
     since its leaves are the digit @('x') as well."))
  (implies (dec-digitp x)
           (grammar-dec-digitp (list x)))
  :use (:instance grammar-dec-digitp-suff
        (tree (dec-digit-tree x))
        (x (list x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dec-digitp-when-grammar-dec-digitp
  :short "Proof of @(tsee dec-digitp) from @(tsee grammar-dec-digitp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved via a lemma asserting that
     a terminated tree rooted at @('digit')
     has a string at the leaves whose only element satisfies @(tsee dec-digitp)
     (that this string is a singleton is proved in @(tsee grammar-dec-digitp)).
     The lemma is proved by exhaustively opening @(tsee abnf-tree-with-root-p),
     which splits into cases corresponding to
     the alternatives of the @('digit') and @('non-zero-digit') rules,
     thus prescribing the exact form of the tree in each case,
     and in particular its leaves.
     The theorem is then proved by instantiating the lemma
     to the witness tree of @(tsee grammar-dec-digitp)."))
  (implies (grammar-dec-digitp x)
           (dec-digitp (car x)))
  :enable grammar-dec-digitp
  :use (:instance lemma (tree (grammar-dec-digitp-witness x)))

  :prep-lemmas
  ((defrule lemma
     (implies (abnf-tree-with-root-p tree "digit")
              (dec-digitp (car (abnf::tree->string tree))))
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

(defruled dec-digitp-is-grammar-dec-digitp
  :short "Equivalence of @(tsee dec-digitp) and @(tsee grammar-dec-digitp)."
  (equal (dec-digitp x)
         (grammar-dec-digitp (list x)))
  :use (grammar-dec-digitp-when-dec-digitp
        (:instance dec-digitp-when-grammar-dec-digitp (x (list x)))))
