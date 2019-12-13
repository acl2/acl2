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
;; (include-book "octal-digits")
(include-book "kestrel/java/language/octal-digits" :dir :system)

;TODO:
;; (include-book "grammar")
(include-book "kestrel/java/language/grammar" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ octal-digits-grammar-validation
  :parents (octal-digits)
  :short "Validation of the definition of @(tsee octal-digitp)
          with respect to the ABNF grammar of Java."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate @(tsee octal-digitp) defines octal digits
     `directly', i.e. without reference to the grammar.
     Here we introduce an alternative predicate based on the grammar,
     and we show it equivalent to @(tsee octal-digitp)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk grammar-octal-digitp (x)
  :returns (yes/no booleanp)
  :short "Definition of octal digits based on the grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This defines an octal digit as a string at the leaves of
     a terminated tree rooted at the @('octal-digit') nonterminal.
     The string is always a singleton.")
   (xdoc::p
    "This characterizes a (singleton) list of Unicode characters,
     while @(tsee octal-digitp) characterizes a single Unicode character.
     Thus, the equivalence theorem has to take this into account."))
  (exists (tree)
          (and (abnf-tree-with-root-p tree "octal-digit")
               (equal (abnf::tree->string tree)
                      x)))
  :guard-hints (("Goal" :in-theory (enable abnf-tree-with-root-p)))
  ///

  (defruled singleton-when-grammar-octal-digitp
    (implies (grammar-octal-digitp x)
             (equal (len x) 1))
    :enable (grammar-octal-digitp
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

(define octal-digit-tree ((digit octal-digitp))
  :returns
  (tree (abnf-tree-with-root-p tree "octal-digit")
        :hints (("Goal"
                 :in-theory
                 (enable octal-digitp
                         octal-digit-fix
                         abnf-tree-with-root-p
                         abnf::tree-terminatedp
                         abnf::tree-match-element-p
                         abnf::tree-list-match-repetition-p-of-1-repetition
                         abnf::tree-match-char-val-p
                         abnf::nat-match-insensitive-char-p)
                 :expand ((:free (tree$ element)
                           (abnf::tree-match-element-p
                            tree$ element *grammar*))))))
  :short "Tree for an octal digit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in @(tsee grammar-octal-digitp-when-octal-digitp)."))
  (abnf::tree-nonleaf (abnf::rulename "octal-digit")
                      (list
                       (list
                        (abnf::tree-leafterm (list (octal-digit-fix digit))))))
  :guard-hints (("Goal" :in-theory (enable octal-digitp)))
  ///

  (defrule tree->string-of-octal-digit-tree
    (equal (abnf::tree->string (octal-digit-tree digit))
           (list (octal-digit-fix digit)))
    :enable (abnf::tree->string octal-digitp octal-digit-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled grammar-octal-digitp-when-octal-digitp
  :short "Proof of @(tsee grammar-octal-digitp) from @(tsee octal-digitp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved using @(tsee octal-digit-tree)
     as witness for the existential quantification:
     if @('x') is an octal digit
     then we can use its tree as witness,
     since its leaves are the octal digit @('x') as well."))
  (implies (octal-digitp x)
           (grammar-octal-digitp (list x)))
  :use (:instance grammar-octal-digitp-suff
        (tree (octal-digit-tree x))
        (x (list x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled octal-digitp-when-grammar-octal-digitp
  :short "Proof of @(tsee octal-digitp) from @(tsee grammar-octal-digitp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved via a lemma asserting that
     a terminated tree rooted at @('octal-digit')
     has a string at the leaves
     whose only element satisfies @(tsee octal-digitp)
     (that this string is a singleton
     is proved in @(tsee grammar-octal-digitp)).
     The lemma is proved by exhaustively opening @(tsee abnf-tree-with-root-p),
     which splits into cases corresponding to
     the alternatives of the @('octal-digit') rule,
     thus prescribing the exact form of the tree in each case,
     and in particular its leaves.
     The theorem is then proved by instantiating the lemma
     to the witness tree of @(tsee grammar-octal-digitp)."))
  (implies (grammar-octal-digitp x)
           (octal-digitp (car x)))
  :enable grammar-octal-digitp
  :use (:instance lemma (tree (grammar-octal-digitp-witness x)))

  :prep-lemmas
  ((defrule lemma
     (implies (abnf-tree-with-root-p tree "octal-digit")
              (octal-digitp (car (abnf::tree->string tree))))
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

(defruled octal-digitp-is-grammar-octal-digitp
  :short "Equivalence of
          @(tsee octal-digitp) and @(tsee grammar-octal-digitp)."
  (equal (octal-digitp x)
         (grammar-octal-digitp (list x)))
  :use (grammar-octal-digitp-when-octal-digitp
        (:instance octal-digitp-when-grammar-octal-digitp (x (list x)))))
