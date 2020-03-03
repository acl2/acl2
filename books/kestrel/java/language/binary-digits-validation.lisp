; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "binary-digits")
(include-book "grammar")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ binary-digits-grammar-validation
  :parents (binary-digits)
  :short "Validation of the definition of @(tsee bin-digitp)
          with respect to the ABNF grammar of Java."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate @(tsee bin-digitp) defines binary digits
     `directly', i.e. without reference to the grammar.
     Here we introduce an alternative predicate based on the grammar,
     and we show it equivalent to @(tsee bin-digitp)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk grammar-bin-digitp (x)
  :returns (yes/no booleanp)
  :short "Definition of binary digits based on the grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This defines a binary digit as a string at the leaves of
     a terminated tree rooted at the @('binary-digit') nonterminal.
     The string is always a singleton.")
   (xdoc::p
    "This characterizes a (singleton) list of Unicode characters,
     while @(tsee bin-digitp) characterizes a single Unicode character.
     Thus, the equivalence theorem has to take this into account."))
  (exists (tree)
          (and (abnf-tree-with-root-p tree "binary-digit")
               (equal (abnf::tree->string tree)
                      x)))
  :guard-hints (("Goal" :in-theory (enable abnf-tree-with-root-p)))
  ///

  (defruled singleton-when-grammar-bin-digitp
    (implies (grammar-bin-digitp x)
             (equal (len x) 1))
    :enable (grammar-bin-digitp
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

(define bin-digit-tree ((digit bin-digitp))
  :returns
  (tree (abnf-tree-with-root-p tree "binary-digit")
        :hints (("Goal"
                 :in-theory
                 (enable bin-digitp
                         bin-digit-fix
                         abnf-tree-with-root-p
                         abnf::tree-terminatedp
                         abnf::tree-match-element-p
                         abnf::tree-list-match-repetition-p-of-1-repetition
                         abnf::tree-match-char-val-p
                         abnf::nat-match-insensitive-char-p)
                 :expand ((:free (tree$ element)
                           (abnf::tree-match-element-p
                            tree$ element *grammar*))))))
  :short "Tree for a binary digit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in @(tsee grammar-bin-digitp-when-bin-digitp)."))
  (abnf::tree-nonleaf (abnf::rulename "binary-digit")
                      (list
                       (list
                        (abnf::tree-leafterm (list (bin-digit-fix digit))))))
  :guard-hints (("Goal" :in-theory (enable bin-digitp)))
  :hooks (:fix)
  ///

  (defrule tree->string-of-bin-digit-tree
    (equal (abnf::tree->string (bin-digit-tree digit))
           (list (bin-digit-fix digit)))
    :enable (abnf::tree->string bin-digitp bin-digit-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled grammar-bin-digitp-when-bin-digitp
  :short "Proof of @(tsee grammar-bin-digitp) from @(tsee bin-digitp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved using @(tsee bin-digit-tree)
     as witness for the existential quantification:
     if @('x') is a binary digit
     then we can use its tree as witness,
     since its leaves are the binary digit @('x') as well."))
  (implies (bin-digitp x)
           (grammar-bin-digitp (list x)))
  :use (:instance grammar-bin-digitp-suff
        (tree (bin-digit-tree x))
        (x (list x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bin-digitp-when-grammar-bin-digitp
  :short "Proof of @(tsee bin-digitp) from @(tsee grammar-bin-digitp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved via a lemma asserting that
     a terminated tree rooted at @('binary-digit')
     has a string at the leaves
     whose only element satisfies @(tsee bin-digitp)
     (that this string is a singleton
     is proved in @(tsee grammar-bin-digitp)).
     The lemma is proved by exhaustively opening @(tsee abnf-tree-with-root-p),
     which splits into cases corresponding to
     the alternatives of the @('binary-digit') rule,
     thus prescribing the exact form of the tree in each case,
     and in particular its leaves.
     The theorem is then proved by instantiating the lemma
     to the witness tree of @(tsee grammar-bin-digitp)."))
  (implies (grammar-bin-digitp x)
           (bin-digitp (car x)))
  :enable grammar-bin-digitp
  :use (:instance lemma (tree (grammar-bin-digitp-witness x)))

  :prep-lemmas
  ((defrule lemma
     (implies (abnf-tree-with-root-p tree "binary-digit")
              (bin-digitp (car (abnf::tree->string tree))))
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

(defruled bin-digitp-is-grammar-bin-digitp
  :short "Equivalence of
          @(tsee bin-digitp) and @(tsee grammar-bin-digitp)."
  (equal (bin-digitp x)
         (grammar-bin-digitp (list x)))
  :use (grammar-bin-digitp-when-bin-digitp
        (:instance bin-digitp-when-grammar-bin-digitp (x (list x)))))
