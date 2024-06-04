; Cherry-pick the definitions from osets
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Including osets brings in some slow rules we don't want, such as
;; set::empty-set-unique and set::double-containment, so we just cherry-pick
;; some definitions.

(include-book "misc/total-order" :dir :system) ; for fast-<<
(local (include-book "std/osets/membership" :dir :system)) ;for set::in

(defun set::setp (x)
  (declare (xargs :guard t
                  ;;:verify-guards nil
                  ))
  (if (atom x)
      (null x)
    (or (null (cdr x))
        (and (consp (cdr x))
             (fast-<< (car x) (cadr x))
             (set::setp (cdr x))))))

(defun set::emptyp (x)
  (declare (xargs :guard (set::setp x)))
  (mbe :logic (or (null x) (not (set::setp x)))
       :exec (null x)))

(defun set::sfix (x)
  (declare (xargs :guard (set::setp x)))
  (mbe :logic (if (set::emptyp x) nil x)
       :exec x))

(defun set::head (x)
  (declare (xargs :guard (and (set::setp x)
                              (not (set::emptyp x)))))
  (mbe :logic (car (set::sfix x))
       :exec (car x)))

(defun set::tail (x)
  (declare (xargs :guard (and (set::setp x)
                              (not (set::emptyp x)))))
  (mbe :logic (cdr (set::sfix x))
       :exec (cdr x)))

(defun set::in (a x)
  (declare (xargs :guard (set::setp x)
                  :verify-guards nil))
  (mbe :logic (and (not (set::emptyp x))
                   (or (equal a (set::head x))
                       (set::in a (set::tail x))))
       :exec (and x
                  (or (equal a (car x))
                      (and (cdr x)
                           (or (equal a (cadr x))
                               (set::in a (cddr x))))))))
