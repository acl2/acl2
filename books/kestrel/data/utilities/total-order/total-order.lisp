; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
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

(include-book "misc/total-order" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled <<-irreflexive-backchain
  (implies (equal x y)
           (not (<< x y))))

;; TODO: is this any better than acl2::<<-irreflexive ?
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

(defruled <<-becomes-cases
  (equal (<< x y)
         (and (not (equal x y))
              (not (<< y x))))
  :use (:instance acl2::<<-trichotomy
                  (x y)
                  (y x))
  :enable <<-rules
  :disable acl2::<<-trichotomy)

(defruled not-<<-case-split
  (implies (syntaxp (acl2::want-to-strengthen (<< x y)))
           ;; The LHS is misleading here. Using want-to-strengthen, we are
           ;; limiting ourselves to rewriting the negation of the LHS.
           (equal (<< x y)
                  (and (not (equal x y))
                       (not (<< y x)))))
  :by <<-becomes-cases)

(defthy <<-expensive-rules
  '(<<-rules
    not-<<-case-split
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
       :exec (and (not (eq x y))
                  (symbol< x y)
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
