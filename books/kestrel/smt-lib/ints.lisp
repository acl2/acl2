; A model of the Ints theory of SMT-LIB
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; todo: use an SMT package?  but that name is already taken

(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See https://ints-lib.org/theories-Ints.shtml

;; Many of these are essentially the same as existing ACL2 functions, except for the guards.

;; todo: add support for using "-"
(defun ints-negate (m)
  (declare (xargs :guard (integerp m)))
  (- m))

;; todo: add support for using "-"
(defun ints-subtract (m n)
  (declare (xargs :guard (and (integerp m)
                              (integerp n))))
  (- m n))

(defun ints-+ (m n)
  (declare (xargs :guard (and (integerp m)
                              (integerp n))))
  (+ m n))

(defun ints-* (m n)
  (declare (xargs :guard (and (integerp m)
                              (integerp n))))
  (* m n))

(defun ints-div (m n)
  (declare (xargs :guard (and (integerp m)
                              (integerp n)
                              (not (equal n 0)) ; at least for now
                              )))
  (if (< 0 n)
      (floor m n)
    (ceiling m n)))

(defun ints-mod (m n)
  (declare (xargs :guard (and (integerp m)
                              (integerp n)
                              (not (equal n 0)) ; at least for now
                              )))
  (- m (* (ints-div m n) n)))

(defun ints-abs (m)
  (declare (xargs :guard (integerp m)))
  (abs m))

;; not chainable (yet)
(defun ints-<= (m n)
  (declare (xargs :guard (and (integerp m)
                              (integerp n)
                              (not (equal n 0)) ; at least for now
                              )))
  (<= m n))

;; not chainable (yet)
(defun ints-< (m n)
  (declare (xargs :guard (and (integerp m)
                              (integerp n)
                              (not (equal n 0)) ; at least for now
                              )))
  (< m n))

;; not chainable (yet)
(defun ints->= (m n)
  (declare (xargs :guard (and (integerp m)
                              (integerp n)
                              (not (equal n 0)) ; at least for now
                              )))
  (>= m n))

;; not chainable (yet)
(defun ints-> (m n)
  (declare (xargs :guard (and (integerp m)
                              (integerp n)
                              (not (equal n 0)) ; at least for now
                              )))
  (> m n))

;; TODO: Add divisible

;; TODO: Add an int version of equal?

;; Boute's Euclidean definition
(thm
  (implies (and (integerp m)
                (integerp n)
                (not (equal n 0)) ; todo: add "distinct"?
                )
           (let ((q (ints-div m n))
                 (r (ints-mod m n)))
             (and (equal m (ints-+ (ints-* n q) r))
                  (ints-<= 0 r)
                  (ints-<= r (ints-subtract (ints-abs n) 1))
                  )))
  :hints (("Goal" :cases ((< m 0) (equal m 0)))))
