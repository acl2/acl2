; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/utilities/polarity" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(include-book "misc/total-order" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled <<-irreflexive-backchain
  (implies (equal x y)
           (not (<< x y))))

(defruled <<-irreflexive-backchain-cheap
  (implies (equal x y)
           (not (<< x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by <<-irreflexive-backchain)

(defruled not-<<-transitive
  (implies (and (not (<< x y))
                (not (<< y z)))
           (not (<< x z)))
  :cases ((equal y z)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy <<-rules
  '(acl2::<<-irreflexive
    acl2::<<-asymmetric
    acl2::<<-transitive
    acl2::<<-trichotomy
    acl2::<<-implies-lexorder
    <<-irreflexive-backchain-cheap
    not-<<-transitive
    ))

(in-theory (disable <<-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled <<-case-split
  (equal (<< x y)
         (and (not (equal x y))
              (not (<< y x))))
  :enable (<<-rules
           acl2::equal-of-booleans-cheap))

(defruled <<-case-split-clause
  (implies (syntaxp (acl2::want-to-strengthen (<< x y)))
           ;; The LHS is misleading here. Using want-to-strengthen, we are
           ;; limiting ourselves to rewriting the negation of the LHS.
           (equal (<< x y)
                  (and (not (equal x y))
                       (not (<< y x)))))
  :by <<-case-split)

;; This will loop with not-<<-case-split-clause.
;; Perhaps what we want is to only fire this when stable-under-simplificationp.
;; But that requires a computed hint.
;; Or perhaps we can do something with mfcs.
(defruled not-<<-case-split
  (equal (not (<< x y))
         (or (equal x y)
             (<< y x)))
  :enable (<<-rules
           acl2::equal-of-booleans-cheap))

(defruled not-<<-case-split-clause
  (implies (syntaxp (acl2::want-to-weaken (<< x y)))
           ;; The LHS is misleading here. Using want-to-strengthen, we are
           ;; limiting ourselves to rewriting the negation of the LHS.
           (equal (<< x y)
                  (and (not (equal x y))
                       (not (<< y x)))))
  :by <<-case-split)

;;;;;;;;;;;;;;;;;;;;

(defthy <<-to-not-<<
  '(;; <<-case-split
    <<-case-split-clause
    ))

(defthy not-<<-to-<<
  '(;; not-<<-case-split
    not-<<-case-split-clause
    ))

(defthy <<-expensive-rules
  '(<<-rules
    not-<<-to-<<
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-<<
  ((x acl2-numberp)
   (y acl2-numberp))
  (mbe :logic (<< x y)
       :exec (if (complex/complex-rationalp x)
                 (and (complex/complex-rationalp y)
                      (or (< (realpart x)
                             (realpart y))
                          (and (= (realpart x)
                                  (realpart y))
                               (< (imagpart x)
                                  (imagpart y)))))
               (or (complex/complex-rationalp y)
                   (< x y))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable << lexorder alphorder))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-<<
  ((x symbolp)
   (y symbolp))
  (mbe :logic (<< x y)
       :exec (and (symbol< x y)
                  t))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable << lexorder alphorder))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eqlable-<<
  ((x eqlablep)
   (y eqlablep))
  (mbe :logic (<< x y)
       :exec (cond ((integerp x)
                    (cond ((integerp y) (< x y))
                          ((real/rationalp y)
                           (< x y))
                          (t t)))
                   ((symbolp x)
                    (if (symbolp y)
                        (and (not (eq x y))
                             (symbol< x y)
                             t)
                      (not (or (integerp y)
                               (characterp y)
                               (real/rationalp y)
                               (complex/complex-rationalp y)))))
                   ((characterp x)
                    (cond
                      ((characterp y)
                       (< (char-code x)
                          (char-code y)))
                      (t (not (or (integerp y)
                                  (real/rationalp y)
                                  (complex/complex-rationalp y))))))
                   ((real/rationalp x)
                    (cond ((integerp y) (< x y))
                          ((real/rationalp y)
                           (< x y))
                          (t t)))
                   ((real/rationalp y) nil)
                   ((complex/complex-rationalp x)
                    (cond ((complex/complex-rationalp y)
                           (or (< (realpart x)
                                  (realpart y))
                               (and (= (realpart x)
                                       (realpart y))
                                    (< (imagpart x)
                                       (imagpart y)))))
                          (t t)))
                   (t nil)))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable << lexorder alphorder)))
  :prepwork
  ((defrulel equal-of-char-code-char-code
     (implies (and (characterp x)
                   (characterp y))
              (equal (equal (char-code x) (char-code y))
                     (equal x y)))
     :use (:instance equal-char-code
                     (acl2::x x)
                     (acl2::y y)))))
