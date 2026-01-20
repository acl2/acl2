; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "misc/total-order" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy <<-rules
  #!ACL2
  '(<<-irreflexive
    <<-asymmetric
    <<-transitive
    <<-trichotomy
    <<-implies-lexorder))

(in-theory (disable <<-rules))

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
