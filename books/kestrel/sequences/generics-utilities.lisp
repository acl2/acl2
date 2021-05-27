; Utilities that support defforall, defmap, defexists, deffilter, etc.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "kestrel/terms-light/sublis-var-simple" :dir :system)
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))

;(theory-invariant (incompatible (:definition len) (:rewrite len-of-nthcdr-better)))

;why is this needed?
(defthmd <-of-if-arg1
  (equal (< (if test x y) k)
         (if test (< x k) (< y k))))

;; For each item in ITEMS, make a version of TERM where VAR is replaced by that
;; item.
;todo: rename?
(defun wrap-list (term var items)
  (declare (xargs :guard (and (true-listp items)
                              (symbolp var)
                              (pseudo-termp term))))
  (if (endp items)
      nil
    (cons (sublis-var-simple (acons var (car items) nil) term)
          (wrap-list term var (cdr items)))))

;put the items in for var in the terms that are also in targets, leave the others untouched
(defun wrap-targets (term var items targets)
  (declare (xargs :guard (and (true-listp items)
                              (symbolp var)
                              (pseudo-termp term)
                              (true-listp targets))))
  (if (endp items)
      nil
    (cons (if (member-equal (car items) targets)
              (sublis-var-simple (acons var (car items) nil) term)
            (car items))
          (wrap-targets term var (cdr items) targets))))

(defun wrap-target (term var target items)
  (declare (xargs :guard (and (true-listp items)
                              (symbolp var)
                              (pseudo-termp term))))
  (if (endp items)
      nil
    (cons (if (equal (car items) target)
              (sublis-var-simple (acons var (car items) nil) term)
            (car items))
          (wrap-target term var target (cdr items)))))


;; (defun make-cons-terms (xs ys)
;;   (if (endp xs)
;;       nil
;;     (cons `(cons ,(car xs) ,(car ys))
;;           (make-cons-terms (cdr xs) (cdr ys)))))

;; (defun make-car-terms (xs)
;;   (if (endp xs)
;;       nil
;;     (cons `(car ,(car xs))
;;           (make-car-terms (cdr xs)))))

;the numbering is 1-based
(defun position-of (elem lst)
  (declare (xargs :guard (true-listp lst)))
  (if (endp lst)
      0 ; indicates not present
    (if (equal elem (first lst))
        1
      (+ 1 (position-of elem (rest lst))))))

(defstub generic-predicate (x) t) ;constrain this to return a boolean?

(defstub generic-fn (x) t)
