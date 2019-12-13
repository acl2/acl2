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
;; (include-book "binary-digits")
(include-book "kestrel/java/language/binary-digits" :dir :system)

;TODO:
;; (include-book "grammar")
(include-book "kestrel/java/language/grammar" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ binary-digits-grammar-validation
  :parents (binary-digits)
  :short "Validation of the definition of @(tsee binary-digitp)
          with respect to the ABNF grammar of Java."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate @(tsee binary-digitp) defines binary digits
     `directly', i.e. without reference to the grammar.
     Here we introduce an alternative predicate based on the grammar,
     and we show it equivalent to @(tsee binary-digitp)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk grammar-binary-digitp (x)
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
     while @(tsee binary-digitp) characterizes a single Unicode character.
     Thus, the equivalence theorem has to take this into account."))
  (exists (tree)
          (and (abnf-tree-with-root-p tree "binary-digit")
               (equal (abnf::tree->string tree)
                      x)))
  :guard-hints (("Goal" :in-theory (enable abnf-tree-with-root-p)))
  ///

  (defruled singleton-when-grammar-binary-digitp
    (implies (grammar-binary-digitp x)
             (equal (len x) 1))
    :enable (grammar-binary-digitp
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

(define binary-digit-tree ((digit binary-digitp))
  :returns
  (tree (abnf-tree-with-root-p tree "binary-digit")
        :hints (("Goal"
                 :in-theory
                 (enable binary-digitp
                         binary-digit-fix
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
    "This is used in @(tsee grammar-binary-digitp-when-binary-digitp)."))
  (abnf::tree-nonleaf (abnf::rulename "binary-digit")
                      (list
                       (list
                        (abnf::tree-leafterm (list (binary-digit-fix digit))))))
  :guard-hints (("Goal" :in-theory (enable binary-digitp)))
  ///

  (defrule tree->string-of-binary-digit-tree
    (equal (abnf::tree->string (binary-digit-tree digit))
           (list (binary-digit-fix digit)))
    :enable (abnf::tree->string binary-digitp binary-digit-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled grammar-binary-digitp-when-binary-digitp
  :short "Proof of @(tsee grammar-binary-digitp) from @(tsee binary-digitp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved using @(tsee binary-digit-tree)
     as witness for the existential quantification:
     if @('x') is a binary digit
     then we can use its tree as witness,
     since its leaves are the binary digit @('x') as well."))
  (implies (binary-digitp x)
           (grammar-binary-digitp (list x)))
  :use (:instance grammar-binary-digitp-suff
        (tree (binary-digit-tree x))
        (x (list x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled binary-digitp-when-grammar-binary-digitp
  :short "Proof of @(tsee binary-digitp) from @(tsee grammar-binary-digitp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved via a lemma asserting that
     a terminated tree rooted at @('binary-digit')
     has a string at the leaves
     whose only element satisfies @(tsee binary-digitp)
     (that this string is a singleton
     is proved in @(tsee grammar-binary-digitp)).
     The lemma is proved by exhaustively opening @(tsee abnf-tree-with-root-p),
     which splits into cases corresponding to
     the alternatives of the @('binary-digit') rule,
     thus prescribing the exact form of the tree in each case,
     and in particular its leaves.
     The theorem is then proved by instantiating the lemma
     to the witness tree of @(tsee grammar-binary-digitp)."))
  (implies (grammar-binary-digitp x)
           (binary-digitp (car x)))
  :enable grammar-binary-digitp
  :use (:instance lemma (tree (grammar-binary-digitp-witness x)))

  :prep-lemmas
  ((defrule lemma
     (implies (abnf-tree-with-root-p tree "binary-digit")
              (binary-digitp (car (abnf::tree->string tree))))
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

(defruled binary-digitp-is-grammar-binary-digitp
  :short "Equivalence of
          @(tsee binary-digitp) and @(tsee grammar-binary-digitp)."
  (equal (binary-digitp x)
         (grammar-binary-digitp (list x)))
  :use (grammar-binary-digitp-when-binary-digitp
        (:instance binary-digitp-when-grammar-binary-digitp (x (list x)))))
