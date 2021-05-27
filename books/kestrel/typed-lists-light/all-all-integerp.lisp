; A recognizer for lists of lists of integers
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-integerp")
(include-book "kestrel/sequences/defforall" :dir :system)

(defforall all-all-integerp (x) (all-integerp x) :declares ((type t x)))

;; ;use a defforall?
;; ;rename
;; (defun all-all-integerp (x)
;;   (declare (xargs :guard t))
;;   (if (consp x)
;;       (and (all-integerp (car x))
;;            (all-all-integerp (cdr x)))
;;       t))

;limit?
(defthmd all-integerp-of-car
  (implies (all-all-integerp x)
           (all-integerp (car x))))

;; ;limit?
;; (defthmd all-all-integerp-of-cdr
;;   (implies (all-all-integerp x)
;;            (all-all-integerp (cdr x))))
