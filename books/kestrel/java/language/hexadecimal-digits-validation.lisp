; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "hexadecimal-digits")
(include-book "grammar")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ hexadecimal-digits-grammar-validation
  :parents (hexadecimal-digits)
  :short "Validation of the definition of @(tsee hex-digitp)
          with respect to the ABNF grammar of Java."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate @(tsee hex-digitp) defines hexadecimal digits
     `directly', i.e. without reference to the grammar.
     Here we introduce an alternative predicate based on the grammar,
     and we show it equivalent to @(tsee hex-digitp)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk grammar-hex-digitp (x)
  :returns (yes/no booleanp)
  :short "Definition of hexadecimal digits based on the grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This defines a hexadecimal digit as a string at the leaves of
     a terminated tree rooted at the @('hex-digit') nonterminal.
     The string is always a singleton.")
   (xdoc::p
    "This characterizes a (singleton) list of Unicode characters,
     while @(tsee hex-digitp) characterizes a single Unicode character.
     Thus, the equivalence theorem has to take this into account."))
  (exists (tree)
          (and (abnf-tree-with-root-p tree "hex-digit")
               (equal (abnf::tree->string tree)
                      x)))
  :guard-hints (("Goal" :in-theory (enable abnf-tree-with-root-p)))
  ///

  (defruled singleton-when-grammar-hex-digitp
    (implies (grammar-hex-digitp x)
             (equal (len x) 1))
    :enable (grammar-hex-digitp
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

(define hex-digit-tree ((digit hex-digitp))
  :returns
  (tree (abnf-tree-with-root-p tree "hex-digit")
        :hints (("Goal"
                 :in-theory
                 (enable hex-digitp
                         hex-digit-fix
                         abnf-tree-with-root-p
                         abnf::tree-terminatedp
                         abnf::tree-match-element-p
                         abnf::tree-list-match-repetition-p-of-1-repetition
                         abnf::tree-match-char-val-p
                         abnf::nat-match-insensitive-char-p)
                 :expand ((:free (tree$ element)
                           (abnf::tree-match-element-p
                            tree$ element *grammar*))))))
  :short "Tree for a hexadecimal digit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in @(tsee grammar-hex-digitp-when-hex-digitp)."))
  (abnf::tree-nonleaf (abnf::rulename "hex-digit")
                      (list
                       (list
                        (abnf::tree-leafterm (list (hex-digit-fix digit))))))
  :guard-hints (("Goal" :in-theory (enable hex-digitp)))
  :hooks (:fix)
  ///

  (defrule tree->string-of-hex-digit-tree
    (equal (abnf::tree->string (hex-digit-tree digit))
           (list (hex-digit-fix digit)))
    :enable (abnf::tree->string hex-digitp hex-digit-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled grammar-hex-digitp-when-hex-digitp
  :short "Proof of @(tsee grammar-hex-digitp) from @(tsee hex-digitp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved using @(tsee hex-digit-tree)
     as witness for the existential quantification:
     if @('x') is a hexadecimal digit
     then we can use its tree as witness,
     since its leaves are the hexadecimal digit @('x') as well."))
  (implies (hex-digitp x)
           (grammar-hex-digitp (list x)))
  :use (:instance grammar-hex-digitp-suff
        (tree (hex-digit-tree x))
        (x (list x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled hex-digitp-when-grammar-hex-digitp
  :short "Proof of @(tsee hex-digitp) from @(tsee grammar-hex-digitp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved via a lemma asserting that
     a terminated tree rooted at @('hex-digit')
     has a string at the leaves whose only element satisfies @(tsee hex-digitp)
     (that this string is a singleton is proved in @(tsee grammar-hex-digitp)).
     The lemma is proved by exhaustively opening @(tsee abnf-tree-with-root-p),
     which splits into cases corresponding to
     the alternatives of the @('hex-digit') rule,
     thus prescribing the exact form of the tree in each case,
     and in particular its leaves.
     The theorem is then proved by instantiating the lemma
     to the witness tree of @(tsee grammar-hex-digitp)."))
  (implies (grammar-hex-digitp x)
           (hex-digitp (car x)))
  :enable grammar-hex-digitp
  :use (:instance lemma (tree (grammar-hex-digitp-witness x)))

  :prep-lemmas
  ((defrule lemma
     (implies (abnf-tree-with-root-p tree "hex-digit")
              (hex-digitp (car (abnf::tree->string tree))))
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

(defruled hex-digitp-is-grammar-hex-digitp
  :short "Equivalence of
          @(tsee hex-digitp) and @(tsee grammar-hex-digitp)."
  (equal (hex-digitp x)
         (grammar-hex-digitp (list x)))
  :use (grammar-hex-digitp-when-hex-digitp
        (:instance hex-digitp-when-grammar-hex-digitp (x (list x)))))
