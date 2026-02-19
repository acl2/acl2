; A utility for making an IF-term in a propositional context

; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This requires the TEST to not be constant, because we can do better if it may be.
;; The result is equivalent to (if test then else) under iff.
(defund make-if-term (test then else)
  (declare (xargs :guard (and (pseudo-termp test)
                              (not (quotep test))
                              (pseudo-termp then)
                              (pseudo-termp else))))
  (if (equal then else)
      then
    (if (and (equal then *t*)
             (equal else *nil*))
        test ; avoids (if <test> t nil)
      `(if ,test ,then ,else))))

(defthm pseudo-termp-of-make-if-term
  (implies (and (pseudo-termp test)
                (pseudo-termp then)
                (pseudo-termp else))
           (pseudo-termp (make-if-term test then else)))
  :hints (("Goal" :in-theory (enable make-if-term))))

(defthm termp-of-make-if-term
  (implies (and (equal 3 (arity 'if w))
                (termp test w)
                (termp then w)
                (termp else w))
           (termp (make-if-term test then else) w))
  :hints (("Goal" :in-theory (enable make-if-term))))

(defthm logic-fnsp-of-make-if-term
  (implies (and (logicp 'if w)
                (logic-fnsp test w)
                (logic-fnsp then w)
                (logic-fnsp else w))
           (logic-fnsp (make-if-term test then else) w))
  :hints (("Goal" :in-theory (enable make-if-term))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The result is equivalent to (if test then else) under iff.
(defund make-if-term-gen (test then else)
  (declare (xargs :guard (and (pseudo-termp test)
                              ;; (not (quotep test))
                              (pseudo-termp then)
                              (pseudo-termp else))))
  (if (quotep test)
      (if (unquote test)
          then
        else)
    (if (equal then else)
        then
      (if (and (equal then *t*)
               (equal else *nil*))
          test ; avoids (if <test> t nil)
        `(if ,test ,then ,else)))))

(defthm make-if-term-gen-of-t-and-nil
  (equal (make-if-term-gen test ''t ''nil)
         (if (quotep test)
             (if (unquote test) ''t ''nil)
           test))
  :hints (("Goal" :in-theory (enable make-if-term-gen))))

(defthm pseudo-termp-of-make-if-term-gen
  (implies (and (pseudo-termp test)
                (pseudo-termp then)
                (pseudo-termp else))
           (pseudo-termp (make-if-term-gen test then else)))
  :hints (("Goal" :in-theory (enable make-if-term-gen))))
