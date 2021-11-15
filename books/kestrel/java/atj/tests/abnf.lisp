; Java Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/abnf/concrete-syntax" :dir :system)
(include-book "kestrel/utilities/messages" :dir :system)
(include-book "misc/seq" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ABNF grammar parser.

; This is the same as the one in [books]/kestrel/abnf/parser.lisp,
; except that PARSE-ANY does not fix its input to NAT-LISTP (via MBE),
; because this makes the parser unduly slow when executed
; with guard checking :NONE or in AIJ.
; As a consequence, a hypothesis that the input satisfies NAT-LISTP
; has to be added to the return type theorems.
; The theorems saying that the parsing functions fix their inputs
; are also removed, since they no longer hold.
; To avoid using the ABNF package here,
; this version of the parser is in the ACL2 package;
; as a consequence, some symbols from the ABNF package have to be qualified.
; We also remove all the XDOCumentation.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following functions are not part of the parser proper.
; They are variants of functions
; from general libraries and from the ABNF semantics.
; These variants avoid the use of MBE with PROGN as the first argument,
; which are currently not handled by ATJ.
; The parser proper calls these functions.

(define downcase ((x :type character))
  (b* ((code (char-code x)))
    (if (and (<= (str::big-a) code)
             (<= code (str::big-z)))
        (code-char (+ code (str::case-delta)))
      (char-fix x)))
  :inline t
  :no-function t)

(define upcase ((x :type character))
  (b* ((code (char-code x)))
    (if (and (<= (str::little-a) code)
             (<= code (str::little-z)))
        (code-char (- code (str::case-delta)))
      (char-fix x)))
  :inline t
  :no-function t)

(define nat-match-insensitive-char-p ((nat natp) (char characterp))
  (or (equal nat (char-code char))
      (equal nat (char-code (upcase char)))
      (equal nat (char-code (downcase char))))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is the parser proper.

(defval *grammar-parser-error-msg*
  (msg "ABNF Grammar Parser Error."))

(define parse-any ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (nat? (and (maybe-natp nat?)
                          (implies (not error?) (natp nat?))
                          (implies error? (not nat?)))
                     :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (if (consp input)
      (mv nil (car input) (cdr input))
    (mv *grammar-parser-error-msg* nil input))
  :no-function t
  ///

  (more-returns
   (nat? (implies (not error?)
                  (natp nat?))
         :hyp (nat-listp input)
         :name natp-of-parse-any
         :rule-classes :type-prescription)
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-any-linear
               :rule-classes :linear)))

(define parse-exact ((nat natp) (input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (b* ((nat (mbe :logic (nfix nat) :exec nat)))
    (seq input
         (input-nat := (parse-any input))
         (unless (eql input-nat nat)
           (return-raw
            (mv *grammar-parser-error-msg* nil (cons input-nat input))))
         (return (abnf::tree-leafterm (list nat)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-exact-linear
               :rule-classes :linear)))

(define parse-in-range ((min natp) (max natp) (input nat-listp))
  :guard (<= min max)
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (b* ((min (mbe :logic (nfix min) :exec min))
       (max (mbe :logic (nfix max) :exec max)))
    (seq input
         (nat := (parse-any input))
         (unless (and (<= min nat) (<= nat max))
           (return-raw (mv *grammar-parser-error-msg* nil (cons nat input))))
         (return (abnf::tree-leafterm (list nat)))))
  :guard-hints (("Goal" :cases ((natp (mv-nth 1 (parse-any input))))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-in-range-linear
               :rule-classes :linear)))

(define parse-in-either-range ((min1 natp) (max1 natp)
                               (min2 natp) (max2 natp)
                               (input nat-listp))
  :guard (and (<= min1 max1)
              (< max1 min2)
              (<= min2 max2))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack input
                 ((tree := (parse-in-range min1 max1 input))
                  (return (abnf::make-tree-nonleaf :rulename? nil
                                                   :branches (list
                                                              (list tree)))))
                 ((tree := (parse-in-range min2 max2 input))
                  (return (abnf::make-tree-nonleaf :rulename? nil
                                                   :branches (list
                                                              (list tree))))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-in-either-range-linear
               :rule-classes :linear)))

(define parse-*-in-either-range ((min1 natp) (max1 natp)
                                 (min2 natp) (max2 natp)
                                 (input nat-listp))
  :guard (and (<= min1 max1)
              (< max1 min2)
              (<= min2 max2))
  :returns (mv (error? not)
               (trees abnf::tree-listp :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((tree := (parse-in-either-range min1 max1 min2 max2 input))
    (trees := (parse-*-in-either-range min1 max1 min2 max2 input))
    (return (cons tree trees)))
   ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*-in-either-range-linear
               :rule-classes :linear)))

(define parse-ichar ((char characterp) (input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (nat := (parse-any input))
       (unless (nat-match-insensitive-char-p nat char)
         (return-raw (mv *grammar-parser-error-msg* nil (cons nat input))))
       (return (abnf::tree-leafterm (list nat))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-ichar-linear
               :rule-classes :linear)))

(define parse-ichars ((char1 characterp) (char2 characterp) (input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (nat1 := (parse-any input))
       (unless (nat-match-insensitive-char-p nat1 char1)
         (return-raw (mv *grammar-parser-error-msg* nil (cons nat1 input))))
       (nat2 := (parse-any input))
       (unless (nat-match-insensitive-char-p nat2 char2)
         (return-raw (mv *grammar-parser-error-msg* nil (cons nat2 input))))
       (return (abnf::tree-leafterm (list nat1 nat2))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-ichars-linear
               :rule-classes :linear)))

(define parse-alpha ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack input
                 ((tree := (parse-in-range #x41 #x5a input))
                  (return (abnf::make-tree-nonleaf :rulename? abnf::*alpha*
                                                   :branches (list
                                                              (list tree)))))
                 ((tree := (parse-in-range #x61 #x7a input))
                  (return (abnf::make-tree-nonleaf :rulename? abnf::*alpha*
                                                   :branches (list
                                                              (list tree))))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-alpha-linear
               :rule-classes :linear)))

(define parse-bit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack input
                 ((tree := (parse-ichar #\0 input))
                  (return (abnf::make-tree-nonleaf :rulename? abnf::*bit*
                                                   :branches (list
                                                              (list tree)))))
                 ((tree := (parse-ichar #\1 input))
                  (return (abnf::make-tree-nonleaf :rulename? abnf::*bit*
                                                   :branches (list
                                                              (list tree))))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-bit-linear
               :rule-classes :linear)))

(define parse-cr ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-exact #x0d input))
       (return (abnf::make-tree-nonleaf :rulename? abnf::*cr*
                                        :branches (list (list tree)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-cr-linear
               :rule-classes :linear)))

(define parse-digit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-in-range #x30 #x39 input))
       (return (abnf::make-tree-nonleaf :rulename? abnf::*digit*
                                        :branches (list (list tree)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-digit-linear
               :rule-classes :linear)))

(define parse-dquote ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-exact #x22 input))
       (return
        (abnf::make-tree-nonleaf :rulename? abnf::*dquote*
                                 :branches (list (list tree)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-dquote-linear
               :rule-classes :linear)))

(define parse-htab ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-exact #x09 input))
       (return (abnf::make-tree-nonleaf :rulename? abnf::*htab*
                                        :branches (list (list tree)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-htab-linear
               :rule-classes :linear)))

(define parse-lf ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-exact #x0a input))
       (return (abnf::make-tree-nonleaf :rulename? abnf::*lf*
                                        :branches (list (list tree)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-lf-linear
               :rule-classes :linear)))

(define parse-sp ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-exact #x20 input))
       (return (abnf::make-tree-nonleaf :rulename? abnf::*sp*
                                        :branches (list (list tree)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-sp-linear
               :rule-classes :linear)))

(define parse-vchar ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-in-range #x21 #x7e input))
       (return
        (abnf::make-tree-nonleaf :rulename? abnf::*vchar*
                                 :branches (list (list tree)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-vchar-<
               :rule-classes :linear)))

(define parse-crlf ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree-cr := (parse-cr input))
       (tree-lf := (parse-lf input))
       (return
        (abnf::make-tree-nonleaf :rulename? abnf::*crlf*
                                 :branches (list (list tree-cr)
                                                 (list tree-lf)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-crlf-linear
               :rule-classes :linear)))

(define parse-hexdig ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((tree := (parse-digit input))
    (return (abnf::make-tree-nonleaf :rulename? abnf::*hexdig*
                                     :branches (list (list tree)))))
   ((tree := (parse-ichar #\A input))
    (return (abnf::make-tree-nonleaf :rulename? abnf::*hexdig*
                                     :branches (list (list tree)))))
   ((tree := (parse-ichar #\B input))
    (return (abnf::make-tree-nonleaf :rulename? abnf::*hexdig*
                                     :branches (list (list tree)))))
   ((tree := (parse-ichar #\C input))
    (return (abnf::make-tree-nonleaf :rulename? abnf::*hexdig*
                                     :branches (list (list tree)))))
   ((tree := (parse-ichar #\D input))
    (return (abnf::make-tree-nonleaf :rulename? abnf::*hexdig*
                                     :branches (list (list tree)))))
   ((tree := (parse-ichar #\E input))
    (return (abnf::make-tree-nonleaf :rulename? abnf::*hexdig*
                                     :branches (list (list tree)))))
   ((tree := (parse-ichar #\F input))
    (return (abnf::make-tree-nonleaf :rulename? abnf::*hexdig*
                                     :branches (list (list tree))))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-hexdig-linear
               :rule-classes :linear)))

(define parse-wsp ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((tree := (parse-sp input))
    (return (abnf::make-tree-nonleaf :rulename? abnf::*wsp*
                                     :branches (list (list tree)))))
   ((tree := (parse-htab input))
    (return (abnf::make-tree-nonleaf :rulename? abnf::*wsp*
                                     :branches (list (list tree))))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-wsp-linear
               :rule-classes :linear)))

(define parse-prose-val ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree-open-angle := (parse-ichar #\< input))
       (trees-text := (parse-*-in-either-range #x20 #x3d #x3f #x7e input))
       (tree-close-angle := (parse-ichar #\> input))
       (return
        (abnf::make-tree-nonleaf :rulename? abnf::*prose-val*
                                 :branches (list (list tree-open-angle)
                                                 trees-text
                                                 (list tree-close-angle)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-prose-val-linear
               :rule-classes :linear)))

(define parse-*bit ((input nat-listp))
  :returns (mv (error? not)
               (trees abnf::tree-listp :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack input
                 ((tree := (parse-bit input))
                  (trees := (parse-*bit input))
                  (return (cons tree trees)))
                 ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*bit-linear
               :rule-classes :linear)))

(define parse-*digit ((input nat-listp))
  :returns (mv (error? not)
               (trees abnf::tree-listp :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack input
                 ((tree := (parse-digit input))
                  (trees := (parse-*digit input))
                  (return (cons tree trees)))
                 ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*digit-linear
               :rule-classes :linear)))

(define parse-*hexdig ((input nat-listp))
  :returns (mv (error? not)
               (trees abnf::tree-listp :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack input
                 ((tree := (parse-hexdig input))
                  (trees := (parse-*hexdig input))
                  (return (cons tree trees)))
                 ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*hexdig-linear
               :rule-classes :linear)))

(define parse-1*bit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (trees (and (abnf::tree-listp trees)
                           (implies error? (not trees)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-bit input))
       (trees := (parse-*bit input))
       (return (cons tree trees)))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-1*bit-linear
               :rule-classes :linear)))

(define parse-1*digit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (trees (and (abnf::tree-listp trees)
                           (implies error? (not trees)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-digit input))
       (trees := (parse-*digit input))
       (return (cons tree trees)))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-1*digit-linear
               :rule-classes :linear)))

(define parse-1*hexdig ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (trees (and (abnf::tree-listp trees)
                           (implies error? (not trees)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-hexdig input))
       (trees := (parse-*hexdig input))
       (return (cons tree trees)))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-1*hexdig-linear
               :rule-classes :linear)))

(define parse-dot-1*bit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-ichar #\. input))
       (trees := (parse-1*bit input))
       (return
        (abnf::make-tree-nonleaf :rulename? nil
                                 :branches (list (list tree) trees))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-dot-*1bit-linear
               :rule-classes :linear)))

(define parse-dot-1*digit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-ichar #\. input))
       (trees := (parse-1*digit input))
       (return
        (abnf::make-tree-nonleaf :rulename? nil
                                 :branches (list (list tree) trees))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-dot-*1digit-linear
               :rule-classes :linear)))

(define parse-dot-1*hexdig ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-ichar #\. input))
       (trees := (parse-1*hexdig input))
       (return
        (abnf::make-tree-nonleaf :rulename? nil
                                 :branches (list (list tree) trees))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-dot-*1hexdig-linear
               :rule-classes :linear)))

(define parse-dash-1*bit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-ichar #\- input))
       (trees := (parse-1*bit input))
       (return
        (abnf::make-tree-nonleaf :rulename? nil
                                 :branches (list (list tree) trees))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-dash-*1bit-linear
               :rule-classes :linear)))

(define parse-dash-1*digit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-ichar #\- input))
       (trees := (parse-1*digit input))
       (return
        (abnf::make-tree-nonleaf :rulename? nil
                                 :branches (list (list tree) trees))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-dash-*1digit-linear
               :rule-classes :linear)))

(define parse-dash-1*hexdig ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-ichar #\- input))
       (trees := (parse-1*hexdig input))
       (return
        (abnf::make-tree-nonleaf :rulename? nil
                                 :branches (list (list tree) trees))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-dash-*1hexdig-linear
               :rule-classes :linear)))

(define parse-*-dot-1*bit ((input nat-listp))
  :returns (mv (error? not)
               (trees abnf::tree-listp :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((tree := (parse-dot-1*bit input))
    (trees := (parse-*-dot-1*bit input))
    (return (cons tree trees)))
   ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*-dot-*1bit-linear
               :rule-classes :linear)))

(define parse-*-dot-1*digit ((input nat-listp))
  :returns (mv (error? not)
               (trees abnf::tree-listp :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((tree := (parse-dot-1*digit input))
    (trees := (parse-*-dot-1*digit input))
    (return (cons tree trees)))
   ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*-dot-*1digit-linear
               :rule-classes :linear)))

(define parse-*-dot-1*hexdig ((input nat-listp))
  :returns (mv (error? not)
               (trees abnf::tree-listp :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((tree := (parse-dot-1*hexdig input))
    (trees := (parse-*-dot-1*hexdig input))
    (return (cons tree trees)))
   ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*-dot-*1hexdig-linear
               :rule-classes :linear)))

(define parse-1*-dot-1*bit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (trees (and (abnf::tree-listp trees)
                           (implies error? (not trees)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-dot-1*bit input))
       (trees := (parse-*-dot-1*bit input))
       (return (cons tree trees)))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-1*-dot-1*bit-linear
               :rule-classes :linear)))

(define parse-1*-dot-1*digit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (trees (and (abnf::tree-listp trees)
                           (implies error? (not trees)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-dot-1*digit input))
       (trees := (parse-*-dot-1*digit input))
       (return (cons tree trees)))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-1*-dot-1*digit-linear
               :rule-classes :linear)))

(define parse-1*-dot-1*hexdig ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (trees (and (abnf::tree-listp trees)
                           (implies error? (not trees)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-dot-1*hexdig input))
       (trees := (parse-*-dot-1*hexdig input))
       (return (cons tree trees)))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-1*-dot-1*hexdig-linear
               :rule-classes :linear)))

(define parse-bin-val-rest ((input nat-listp))
  :returns (mv (error? not)
               (tree abnf::treep :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((trees := (parse-1*-dot-1*bit input))
    (return (abnf::make-tree-nonleaf :rulename? nil :branches (list trees))))
   ((tree := (parse-dash-1*bit input))
    (return (abnf::make-tree-nonleaf :rulename? nil :branches (list
                                                               (list tree)))))
   ((return-raw (mv nil
                    (abnf::make-tree-nonleaf :rulename? nil :branches nil)
                    (nat-list-fix input)))))
  :no-function t
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-bin-val-rest-linear
               :rule-classes :linear)))

(define parse-dec-val-rest ((input nat-listp))
  :returns (mv (error? not)
               (tree abnf::treep :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((trees := (parse-1*-dot-1*digit input))
    (return (abnf::make-tree-nonleaf :rulename? nil :branches (list trees))))
   ((tree := (parse-dash-1*digit input))
    (return (abnf::make-tree-nonleaf :rulename? nil :branches (list
                                                               (list tree)))))
   ((return-raw (mv nil
                    (abnf::make-tree-nonleaf :rulename? nil :branches nil)
                    (nat-list-fix input)))))
  :no-function t
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-dec-val-rest-linear
               :rule-classes :linear)))

(define parse-hex-val-rest ((input nat-listp))
  :returns (mv (error? not)
               (tree abnf::treep :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((trees := (parse-1*-dot-1*hexdig input))
    (return (abnf::make-tree-nonleaf :rulename? nil :branches (list trees))))
   ((tree := (parse-dash-1*hexdig input))
    (return (abnf::make-tree-nonleaf :rulename? nil :branches (list
                                                               (list tree)))))
   ((return-raw (mv nil
                    (abnf::make-tree-nonleaf :rulename? nil :branches nil)
                    (nat-list-fix input)))))
  :no-function t
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-hex-val-rest-linear
               :rule-classes :linear)))

(define parse-bin-val ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-ichar #\b input))
       (trees := (parse-1*bit input))
       (tree-rest := (parse-bin-val-rest input))
       (return
        (abnf::make-tree-nonleaf :rulename? abnf::*bin-val*
                                 :branches (list (list tree)
                                                 trees
                                                 (list tree-rest)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name parse-bin-val-linear
               :rule-classes :linear)))

(define parse-dec-val ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-ichar #\d input))
       (trees := (parse-1*digit input))
       (tree-rest := (parse-dec-val-rest input))
       (return
        (abnf::make-tree-nonleaf :rulename? abnf::*dec-val*
                                 :branches (list (list tree)
                                                 trees
                                                 (list tree-rest)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-dec-val-linear
               :rule-classes :linear)))

(define parse-hex-val ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-ichar #\x input))
       (trees := (parse-1*hexdig input))
       (tree-rest := (parse-hex-val-rest input))
       (return
        (abnf::make-tree-nonleaf :rulename? abnf::*hex-val*
                                 :branches (list (list tree)
                                                 trees
                                                 (list tree-rest)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-hex-val-linear
               :rule-classes :linear)))

(define parse-bin/dec/hex-val ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((tree := (parse-bin-val input))
    (return (abnf::make-tree-nonleaf :rulename? nil
                                     :branches (list (list tree)))))
   ((tree := (parse-dec-val input))
    (return (abnf::make-tree-nonleaf :rulename? nil
                                     :branches (list (list tree)))))
   ((tree := (parse-hex-val input))
    (return (abnf::make-tree-nonleaf :rulename? nil
                                     :branches (list (list tree))))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-bin/dec/hex-val-linear
               :rule-classes :linear)))

(define parse-num-val ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree-% := (parse-ichar #\% input))
       (tree-val := (parse-bin/dec/hex-val input))
       (return
        (abnf::make-tree-nonleaf :rulename? abnf::*num-val*
                                 :branches (list (list tree-%)
                                                 (list tree-val)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-num-val-linear
               :rule-classes :linear)))

(define parse-quoted-string ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree-open-quote := (parse-dquote input))
       (trees := (parse-*-in-either-range #x20 #x21 #x23 #x7e input))
       (tree-close-quote := (parse-dquote input))
       (return (abnf::make-tree-nonleaf :rulename? abnf::*quoted-string*
                                        :branches (list
                                                   (list tree-open-quote)
                                                   trees
                                                   (list tree-close-quote)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-quoted-string-linear
               :rule-classes :linear)))

(define parse-?%i ((input nat-listp))
  :returns (mv (error? not)
               (tree abnf::treep :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((tree := (parse-ichars #\% #\i input))
    (return (abnf::make-tree-nonleaf :rulename? nil
                                     :branches (list (list tree)))))
   ((return-raw (mv nil
                    (abnf::make-tree-nonleaf :rulename? nil :branches nil)
                    (nat-list-fix input)))))
  :no-function t
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-?%i-rest-linear
               :rule-classes :linear)))

(define parse-case-insensitive-string ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree-%i := (parse-?%i input))
       (tree-qstring := (parse-quoted-string input))
       (return (abnf::make-tree-nonleaf
                :rulename? abnf::*case-insensitive-string*
                :branches (list (list tree-%i)
                                (list tree-qstring)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-case-insensitive-string-linear
               :rule-classes :linear)))

(define parse-case-sensitive-string ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree-%s := (parse-ichars #\% #\s input))
       (tree-qstring := (parse-quoted-string input))
       (return (abnf::make-tree-nonleaf
                :rulename? abnf::*case-sensitive-string*
                :branches (list (list tree-%s)
                                (list tree-qstring)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-case-sensitive-string-linear
               :rule-classes :linear)))

(define parse-char-val ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((tree := (parse-case-insensitive-string input))
    (return (abnf::make-tree-nonleaf :rulename? abnf::*char-val*
                                     :branches (list (list tree)))))
   ((tree := (parse-case-sensitive-string input))
    (return (abnf::make-tree-nonleaf :rulename? abnf::*char-val*
                                     :branches (list (list tree))))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-char-val-linear
               :rule-classes :linear)))

(define parse-wsp/vchar ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((tree := (parse-wsp input))
    (return (abnf::make-tree-nonleaf :rulename? nil
                                     :branches (list (list tree)))))
   ((tree := (parse-vchar input))
    (return (abnf::make-tree-nonleaf :rulename? nil
                                     :branches (list (list tree))))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-wsp/vchar-linear
               :rule-classes :linear)))

(define parse-*wsp/vchar ((input nat-listp))
  :returns (mv (error? not)
               (trees abnf::tree-listp :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack input
                 ((tree := (parse-wsp/vchar input))
                  (trees := (parse-*wsp/vchar input))
                  (return (cons tree trees)))
                 ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*wsp/vchar-linear
               :rule-classes :linear)))

(define parse-comment ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree-semicolon := (parse-ichar #\; input))
       (trees-text := (parse-*wsp/vchar input))
       (tree-crlf := (parse-crlf input))
       (return (abnf::make-tree-nonleaf :rulename? abnf::*comment*
                                        :branches (list (list tree-semicolon)
                                                        trees-text
                                                        (list tree-crlf)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-comment-linear
               :rule-classes :linear)))

(define parse-cnl ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((tree := (parse-comment input))
    (return (abnf::make-tree-nonleaf :rulename? abnf::*c-nl*
                                     :branches (list (list tree)))))
   ((tree := (parse-crlf input))
    (return (abnf::make-tree-nonleaf :rulename? abnf::*c-nl*
                                     :branches (list (list tree))))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-cnl-linear
               :rule-classes :linear)))

(define parse-cnl-wsp ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree-cnl := (parse-cnl input))
       (tree-wsp := (parse-wsp input))
       (return (abnf::make-tree-nonleaf :rulename? nil
                                        :branches (list (list tree-cnl)
                                                        (list tree-wsp)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-cnl-wsp-linear
               :rule-classes :linear)))

(define parse-cwsp ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((tree := (parse-wsp input))
    (return (abnf::make-tree-nonleaf :rulename? abnf::*c-wsp*
                                     :branches (list (list tree)))))
   ((tree := (parse-cnl-wsp input))
    (return (abnf::make-tree-nonleaf :rulename? abnf::*c-wsp*
                                     :branches (list (list tree))))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-cwsp-linear
               :rule-classes :linear)))

(define parse-*cwsp ((input nat-listp))
  :returns (mv (error? not)
               (trees abnf::tree-listp :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack input
                 ((tree := (parse-cwsp input))
                  (trees := (parse-*cwsp input))
                  (return (cons tree trees)))
                 ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*cwsp-linear
               :rule-classes :linear)))

(define parse-1*cwsp ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (trees (and (abnf::tree-listp trees)
                           (implies error? (not trees)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-cwsp input))
       (trees := (parse-*cwsp input))
       (return (cons tree trees)))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-1*cwsp-linear
               :rule-classes :linear)))

(define parse-*digit-star-*digit ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (trees1 := (parse-*digit input))
       (tree := (parse-ichar #\* input))
       (trees2 := (parse-*digit input))
       (return (abnf::make-tree-nonleaf :rulename? nil
                                        :branches (list trees1
                                                        (list tree)
                                                        trees2))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-*digit-star-*digit-linear
               :rule-classes :linear)))

(define parse-repeat ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((tree := (parse-*digit-star-*digit input))
    (return (abnf::make-tree-nonleaf :rulename? abnf::*repeat*
                                     :branches (list (list tree)))))
   ((trees := (parse-1*digit input))
    (return (abnf::make-tree-nonleaf :rulename? abnf::*repeat*
                                     :branches (list trees)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-repeat-linear
               :rule-classes :linear)))

(define parse-?repeat ((input nat-listp))
  :returns (mv (error? not)
               (tree abnf::treep :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((tree := (parse-repeat input))
    (return (abnf::make-tree-nonleaf :rulename? nil
                                     :branches (list (list tree)))))
   ((return-raw (mv nil
                    (abnf::make-tree-nonleaf :rulename? nil :branches nil)
                    (nat-list-fix input)))))
  :no-function t
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-?repeat-linear
               :rule-classes :linear)))

(define parse-alpha/digit/dash ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((tree := (parse-alpha input))
    (return (abnf::make-tree-nonleaf :rulename? nil
                                     :branches (list (list tree)))))
   ((tree := (parse-digit input))
    (return (abnf::make-tree-nonleaf :rulename? nil
                                     :branches (list (list tree)))))
   ((tree := (parse-ichar #\- input))
    (return (abnf::make-tree-nonleaf :rulename? nil
                                     :branches (list (list tree))))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-alpha/digit/dash-linear
               :rule-classes :linear)))

(define parse-*-alpha/digit/dash ((input nat-listp))
  :returns (mv (error? not)
               (trees abnf::tree-listp :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack input
                 ((tree := (parse-alpha/digit/dash input))
                  (trees := (parse-*-alpha/digit/dash input))
                  (return (cons tree trees)))
                 ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*-alpha/digit/dash-linear
               :rule-classes :linear)))

(define parse-rulename ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-alpha input))
       (trees := (parse-*-alpha/digit/dash input))
       (return (abnf::make-tree-nonleaf :rulename? abnf::*rulename*
                                        :branches (list (list tree) trees))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-rulename-linear
               :rule-classes :linear)))

(defines parse-alt/conc/rep/elem/group/option
  :verify-guards nil ; done below
  :flag-local nil

  (define parse-alternation ((input nat-listp))
    :returns (mv (error? maybe-msgp)
                 (tree? (and (abnf::tree-optionp tree?)
                             (implies (not error?) (abnf::treep tree?))
                             (implies error? (not tree?)))
                        :hyp (nat-listp input))
                 (rest-input nat-listp :hyp (nat-listp input)))
    (b* (((mv error? tree input1) (parse-concatenation input))
         ((when error?) (mv error? nil input1))
         ((unless (mbt (< (len input1) (len input)))) (mv "" nil nil))
         ((mv error? trees input2) (parse-alt-rest input1))
         ((when error?) (mv error? nil input2)))
      (mv nil
          (abnf::make-tree-nonleaf :rulename? abnf::*alternation*
                                   :branches (list (list tree) trees))
          input2))
    :measure (two-nats-measure (len input) 9)
    :no-function t)

  (define parse-concatenation ((input nat-listp))
    :returns (mv (error? maybe-msgp)
                 (tree? (and (abnf::tree-optionp tree?)
                             (implies (not error?) (abnf::treep tree?))
                             (implies error? (not tree?)))
                        :hyp (nat-listp input))
                 (rest-input nat-listp :hyp (nat-listp input)))
    (b* (((mv error? tree input1) (parse-repetition input))
         ((when error?) (mv error? nil input1))
         ((unless (mbt (< (len input1) (len input)))) (mv "" nil nil))
         ((mv error? trees input2) (parse-conc-rest input1))
         ((when error?) (mv error? nil input2)))
      (mv nil
          (abnf::make-tree-nonleaf :rulename? abnf::*concatenation*
                                   :branches (list (list tree) trees))
          input2))
    :measure (two-nats-measure (len input) 8)
    :no-function t)

  (define parse-repetition ((input nat-listp))
    :returns (mv (error? maybe-msgp)
                 (tree? (and (abnf::tree-optionp tree?)
                             (implies (not error?) (abnf::treep tree?))
                             (implies error? (not tree?)))
                        :hyp (nat-listp input))
                 (rest-input nat-listp :hyp (nat-listp input)))
    (seq input
         (tree-repeat := (parse-?repeat input))
         (tree-element := (parse-element input))
         (return (abnf::make-tree-nonleaf :rulename? abnf::*repetition*
                                          :branches (list
                                                     (list tree-repeat)
                                                     (list tree-element)))))
    :measure (two-nats-measure (len input) 7)
    :no-function t)

  (define parse-element ((input nat-listp))
    :returns (mv (error? maybe-msgp)
                 (tree? (and (abnf::tree-optionp tree?)
                             (implies (not error?) (abnf::treep tree?))
                             (implies error? (not tree?)))
                        :hyp (nat-listp input))
                 (rest-input nat-listp :hyp (nat-listp input)))
    (seq-backtrack input
                   ((tree := (parse-rulename input))
                    (return (abnf::make-tree-nonleaf :rulename? abnf::*element*
                                                     :branches (list
                                                                (list tree)))))
                   ((tree := (parse-group input))
                    (return (abnf::make-tree-nonleaf :rulename? abnf::*element*
                                                     :branches (list
                                                                (list tree)))))
                   ((tree := (parse-option input))
                    (return (abnf::make-tree-nonleaf :rulename? abnf::*element*
                                                     :branches (list
                                                                (list tree)))))
                   ((tree := (parse-char-val input))
                    (return (abnf::make-tree-nonleaf :rulename? abnf::*element*
                                                     :branches (list
                                                                (list tree)))))
                   ((tree := (parse-num-val input))
                    (return (abnf::make-tree-nonleaf :rulename? abnf::*element*
                                                     :branches (list
                                                                (list tree)))))
                   ((tree := (parse-prose-val input))
                    (return (abnf::make-tree-nonleaf :rulename? abnf::*element*
                                                     :branches (list
                                                                (list tree))))))
    :measure (two-nats-measure (len input) 6)
    :no-function t)

  (define parse-group ((input nat-listp))
    :returns (mv (error? maybe-msgp)
                 (tree? (and (abnf::tree-optionp tree?)
                             (implies (not error?) (abnf::treep tree?))
                             (implies error? (not tree?)))
                        :hyp (nat-listp input))
                 (rest-input nat-listp :hyp (nat-listp input)))
    (seq input
         (tree-open-round := (parse-ichar #\( input))
         (trees-open-pad := (parse-*cwsp input))
         (tree-alt := (parse-alternation input))
         (trees-close-pad := (parse-*cwsp input))
         (tree-close-round := (parse-ichar #\) input))
         (return (abnf::make-tree-nonleaf :rulename? abnf::*group*
                                          :branches (list
                                                     (list tree-open-round)
                                                     trees-open-pad
                                                     (list tree-alt)
                                                     trees-close-pad
                                                     (list tree-close-round)))))
    :measure (two-nats-measure (len input) 5)
    :no-function t)

  (define parse-option ((input nat-listp))
    :returns (mv (error? maybe-msgp)
                 (tree? (and (abnf::tree-optionp tree?)
                             (implies (not error?) (abnf::treep tree?))
                             (implies error? (not tree?)))
                        :hyp (nat-listp input))
                 (rest-input nat-listp :hyp (nat-listp input)))
    (seq input
         (tree-open-square := (parse-ichar #\[ input))
         (trees-open-pad := (parse-*cwsp input))
         (tree-alt := (parse-alternation input))
         (trees-close-pad := (parse-*cwsp input))
         (tree-close-square := (parse-ichar #\] input))
         (return (abnf::make-tree-nonleaf :rulename? abnf::*option*
                                          :branches (list
                                                     (list tree-open-square)
                                                     trees-open-pad
                                                     (list tree-alt)
                                                     trees-close-pad
                                                     (list
                                                      tree-close-square)))))
    :measure (two-nats-measure (len input) 4)
    :no-function t)

  (define parse-alt-rest ((input nat-listp))
    :returns (mv (error? not)
                 (trees abnf::tree-listp :hyp (nat-listp input))
                 (rest-input nat-listp :hyp (nat-listp input)))
    (b* (((mv error? tree input1)
          (parse-alt-rest-comp input))
         ((when error?) (mv nil nil (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input)))) (mv nil nil nil))
         ((mv & trees input2) (parse-alt-rest input1)))
      (mv nil (cons tree trees) input2))
    :measure (two-nats-measure (len input) 3)
    :no-function t)

  (define parse-alt-rest-comp ((input nat-listp))
    :returns (mv (error? maybe-msgp)
                 (tree? (and (abnf::tree-optionp tree?)
                             (implies (not error?) (abnf::treep tree?))
                             (implies error? (not tree?)))
                        :hyp (nat-listp input))
                 (rest-input nat-listp :hyp (nat-listp input)))
    (seq input
         (trees1 := (parse-*cwsp input))
         (tree-slash := (parse-ichar #\/ input))
         (trees2 := (parse-*cwsp input))
         (tree-conc := (parse-concatenation input))
         (return (abnf::make-tree-nonleaf :rulename? nil
                                          :branches (list trees1
                                                          (list tree-slash)
                                                          trees2
                                                          (list tree-conc)))))
    :measure (two-nats-measure (len input) 2)
    :no-function t)

  (define parse-conc-rest ((input nat-listp))
    :returns (mv (error? not)
                 (trees abnf::tree-listp :hyp (nat-listp input))
                 (rest-input nat-listp :hyp (nat-listp input)))
    (b* (((mv error? tree input1)
          (parse-conc-rest-comp input))
         ((when error?) (mv nil nil (nat-list-fix input)))
         ((unless (mbt (< (len input1) (len input)))) (mv nil nil nil))
         ((mv & trees input2) (parse-conc-rest input1)))
      (mv nil (cons tree trees) input2))
    :measure (two-nats-measure (len input) 1)
    :no-function t)

  (define parse-conc-rest-comp ((input nat-listp))
    :returns (mv (error? maybe-msgp)
                 (tree? (and (abnf::tree-optionp tree?)
                             (implies (not error?) (abnf::treep tree?))
                             (implies error? (not tree?)))
                        :hyp (nat-listp input))
                 (rest-input nat-listp :hyp (nat-listp input)))
    (seq input
         (trees := (parse-1*cwsp input))
         (tree := (parse-repetition input))
         (return (abnf::make-tree-nonleaf :rulename? nil
                                          :branches (list trees (list tree)))))
    :measure (two-nats-measure (len input) 0)
    :no-function t)

  ///

  (defthm-parse-alt/conc/rep/elem/group/option-flag

    (defthm len-of-parse-alternation-linear-1
      (<= (len (mv-nth 2 (parse-alternation input)))
          (len input))
      :rule-classes :linear
      :flag parse-alternation)

    (defthm len-of-parse-concatenation-linear-1
      (<= (len (mv-nth 2 (parse-concatenation input)))
          (len input))
      :rule-classes :linear
      :flag parse-concatenation)

    (defthm len-of-parse-repetition-linear-1
      (<= (len (mv-nth 2 (parse-repetition input)))
          (len input))
      :rule-classes :linear
      :flag parse-repetition)

    (defthm len-of-parse-element-linear-1
      (<= (len (mv-nth 2 (parse-element input)))
          (len input))
      :rule-classes :linear
      :flag parse-element)

    (defthm len-of-parse-group-linear-1
      (<= (len (mv-nth 2 (parse-group input)))
          (len input))
      :rule-classes :linear
      :flag parse-group)

    (defthm len-of-parse-option-linear-1
      (<= (len (mv-nth 2 (parse-option input)))
          (len input))
      :rule-classes :linear
      :flag parse-option)

    (defthm len-of-parse-alt-rest-linear-1
      (<= (len (mv-nth 2 (parse-alt-rest input)))
          (len input))
      :rule-classes :linear
      :flag parse-alt-rest)

    (defthm len-of-parse-alt-rest-comp-linear-1
      (<= (len (mv-nth 2 (parse-alt-rest-comp input)))
          (len input))
      :rule-classes :linear
      :flag parse-alt-rest-comp)

    (defthm len-of-parse-conc-rest-linear-1
      (<= (len (mv-nth 2 (parse-conc-rest input)))
          (len input))
      :rule-classes :linear
      :flag parse-conc-rest)

    (defthm len-of-parse-conc-rest-comp-linear-1
      (<= (len (mv-nth 2 (parse-conc-rest-comp input)))
          (len input))
      :rule-classes :linear
      :flag parse-conc-rest-comp))

  (defrule len-of-parse-conc-rest-comp-linear-2
    (implies (not (mv-nth 0 (parse-conc-rest-comp input)))
             (< (len
                 (mv-nth 2 (parse-conc-rest-comp input)))
                (len input)))
    :rule-classes :linear
    :expand ((parse-conc-rest-comp input)))

  (defrule len-of-parse-alt-rest-comp-linear-2
    (implies (not (mv-nth 0 (parse-alt-rest-comp input)))
             (< (len
                 (mv-nth 2 (parse-alt-rest-comp input)))
                (len input)))
    :rule-classes :linear
    :expand ((parse-alt-rest-comp input)))

  (defrule len-of-parse-option-linear-2
    (implies (not (mv-nth 0 (parse-option input)))
             (< (len (mv-nth 2 (parse-option input)))
                (len input)))
    :rule-classes :linear
    :expand ((parse-option input)))

  (defrule len-of-parse-group-linear-2
    (implies (not (mv-nth 0 (parse-group input)))
             (< (len (mv-nth 2 (parse-group input)))
                (len input)))
    :rule-classes :linear
    :expand ((parse-group input)))

  (defrule len-of-parse-element-linear-2
    (implies (not (mv-nth 0 (parse-element input)))
             (< (len (mv-nth 2 (parse-element input)))
                (len input)))
    :rule-classes :linear
    :expand ((parse-element input)))

  (defrule len-of-parse-repetition-linear-2
    (implies (not (mv-nth 0 (parse-repetition input)))
             (< (len (mv-nth 2 (parse-repetition input)))
                (len input)))
    :rule-classes :linear
    :expand ((parse-repetition input)))

  (defrule len-of-parse-concatenation-linear-2
    (implies (not (mv-nth 0 (parse-concatenation input)))
             (< (len (mv-nth 2 (parse-concatenation input)))
                (len input)))
    :rule-classes :linear
    :expand ((parse-concatenation input)))

  (defrule len-of-parse-alternation-linear-2
    (implies (not (mv-nth 0 (parse-alternation input)))
             (< (len (mv-nth 2 (parse-alternation input)))
                (len input)))
    :rule-classes :linear
    :expand ((parse-alternation input)))

  (verify-guards parse-alternation))

(define parse-elements ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-alternation input))
       (trees := (parse-*cwsp input))
       (return (abnf::make-tree-nonleaf :rulename? abnf::*elements*
                                        :branches (list (list tree) trees))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-elements-linear
               :rule-classes :linear)))

(define parse-equal-/-equal-slash ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((tree := (parse-ichars #\= #\/ input))
    (return (abnf::make-tree-nonleaf :rulename? nil
                                     :branches (list (list tree)))))
   ((tree := (parse-ichar #\= input))
    (return (abnf::make-tree-nonleaf :rulename? nil
                                     :branches (list (list tree))))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-equal-/-equal-slash-linear
               :rule-classes :linear)))

(define parse-defined-as ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (trees1 := (parse-*cwsp input))
       (tree := (parse-equal-/-equal-slash input))
       (trees2 := (parse-*cwsp input))
       (return (abnf::make-tree-nonleaf :rulename? abnf::*defined-as*
                                        :branches (list trees1
                                                        (list tree)
                                                        trees2))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-defined-as-linear
               :rule-classes :linear)))

(define parse-rule ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree1 := (parse-rulename input))
       (tree2 := (parse-defined-as input))
       (tree3 := (parse-elements input))
       (tree4 := (parse-cnl input))
       (return (abnf::make-tree-nonleaf :rulename? abnf::*rule*
                                        :branches (list (list tree1)
                                                        (list tree2)
                                                        (list tree3)
                                                        (list tree4)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-rule-linear
               :rule-classes :linear)))

(define parse-*cwsp-cnl ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (trees := (parse-*cwsp input))
       (tree := (parse-cnl input))
       (return (abnf::make-tree-nonleaf :rulename? nil
                                        :branches (list trees (list tree)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-*cwsp-cnl-linear
               :rule-classes :linear)))

(define parse-rule-/-*cwsp-cnl ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((tree := (parse-rule input))
    (return (abnf::make-tree-nonleaf :rulename? nil
                                     :branches (list (list tree)))))
   ((tree := (parse-*cwsp-cnl input))
    (return (abnf::make-tree-nonleaf :rulename? nil
                                     :branches (list (list tree))))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-rule-/-*cwsp-cnl-linear
               :rule-classes :linear)))

(define parse-*-rule-/-*cwsp-cnl ((input nat-listp))
  :returns (mv (error? not)
               (trees abnf::tree-listp :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq-backtrack
   input
   ((tree := (parse-rule-/-*cwsp-cnl input))
    (trees := (parse-*-rule-/-*cwsp-cnl input))
    (return (cons tree trees)))
   ((return-raw (mv nil nil (nat-list-fix input)))))
  :measure (len input)
  :ruler-extenders :all
  :no-function t
  ///

  (more-returns
   (rest-input (<= (len rest-input) (len input))
               :name len-of-parse-*-rule-/-*cwsp-cnl-linear
               :rule-classes :linear)))

(define parse-rulelist ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (abnf::tree-optionp tree?)
                           (implies (not error?) (abnf::treep tree?))
                           (implies error? (not tree?)))
                      :hyp (nat-listp input))
               (rest-input nat-listp :hyp (nat-listp input)))
  (seq input
       (tree := (parse-rule-/-*cwsp-cnl input))
       (trees := (parse-*-rule-/-*cwsp-cnl input))
       (return (abnf::make-tree-nonleaf :rulename? abnf::*rulelist*
                                        :branches (list (cons tree trees)))))
  :no-function t
  ///

  (more-returns
   (rest-input (and (<= (len rest-input) (len input))
                    (implies (not error?)
                             (< (len rest-input) (len input))))
               :name len-of-parse-rulelist-linear
               :rule-classes :linear)))

(define parse-grammar ((nats nat-listp))
  :returns (tree? abnf::tree-optionp :hyp (nat-listp nats))
  (b* (((mv error? tree? rest) (parse-rulelist nats))
       ((when error?) nil)
       ((when rest) nil))
    tree?)
  :no-function t)
