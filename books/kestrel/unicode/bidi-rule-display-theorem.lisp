; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-rule-display-order")
(include-book "bidi-rule-display-levels")

(local (include-book "bidi-left-to-right"))
(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A name that the wide rule allows is one paragraph.

(defrulel bidi-paragraph-length-when-wide
  (implies (bidi-rule-wide-code-points-p name ver)
           (equal (bidi-paragraph-length (code-points-to-bidi-chars name ver))
                  (len name)))
  :induct (len name)
  :expand ((code-points-to-bidi-chars name ver)
           (:free (a b) (bidi-paragraph-length (cons a b)))
           (bidi-paragraph-length nil))
  :enable (len
           code-point-bidi-char
           bidi-rule-wide-code-point-p))

; A name without a letter of class R or AL and without a digit of class AN
; is described as displayed in the order in which it is stored.

(defrulel bidi-name-start-when-no-letter
  (implies (and (not (bidi-class-kind-present-p :right-to-left name ver))
                (not (bidi-class-kind-present-p :arabic-letter name ver)))
           (equal (bidi-name-start name ver)
                  (len name)))
  :induct (len name)
  :enable (len
           bidi-name-start
           bidi-right-to-left-letter-p)
  :expand ((bidi-class-kind-present-p :right-to-left name ver)
           (bidi-class-kind-present-p :arabic-letter name ver)))

(defrulel bidi-name-display-when-not-right-to-left-label
  (implies (not (bidi-right-to-left-label-p name ver))
           (equal (bidi-name-display name ver)
                  (code-point-list-fix name)))
  :enable (bidi-name-display
           bidi-right-to-left-label-p)
  :use (:instance bidi-name-end-upper-bound
                  (name (code-point-list-fix name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-rule-display-theorem
  :parents (bidi-rule-display)
  :short "Theorems that the Unicode Bidirectional Algorithm,
          in a paragraph from left to right,
          displays a name that the wide rule allows
          as @(tsee bidi-name-display) says,
          and that no two such names are displayed alike."

  (defrule bidi-display-when-bidi-rule-wide-p
    (implies (and (bidi-rule-wide-p name ver)
                  (equal (paragraph-direction-kind direction) :left-to-right))
             (equal (bidi-display name direction ver)
                    (bidi-name-display name ver)))
    :cases ((bidi-right-to-left-label-p name ver))
    :enable (bidi-display
             bidi-arrange-paragraph
             bidi-paragraph-embedding-level
             bidi-paragraph-all-levels-when-bidi-rule-wide-p
             right-to-left-free-p-when-bidi-rule-wide-p
             bidi-rule-wide-p))

  (defrule bidi-display-is-one-to-one-when-bidi-rule-wide-p
    (implies (and (bidi-rule-wide-p name1 ver)
                  (bidi-rule-wide-p name2 ver)
                  (equal (paragraph-direction-kind direction) :left-to-right)
                  (equal (bidi-display name1 direction ver)
                         (bidi-display name2 direction ver)))
             (equal (code-point-list-fix name1)
                    (code-point-list-fix name2)))
    :rule-classes nil
    :use bidi-name-display-is-one-to-one))
