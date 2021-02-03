; A structure that represents equality assumptions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/sequences/defforall" :dir :system)
(include-book "known-booleans")

;;;
;;; equality-pairsp (a structure that represents equality assumptions)
;;;

;; TODO: Use an alist sorted by function symbol (with a special entry using :var for variables)?  Or perhaps even a property-list

(defun equality-pairp (item)
  (declare (xargs :guard t))
  (and (consp item)
       (pseudo-termp (car item)) ;must be a function call?
       (pseudo-termp (cdr item))))

(defforall all-equality-pairp (items) (equality-pairp items)
  :declares ((type t items)))

(defund equality-pairsp (items)
  (declare (xargs :guard t))
  (and (true-listp items)
       (all-equality-pairp items)))

(defthmd pseudo-termp-of-car-of-car-when-equality-pairsp
  (implies (and (equality-pairsp equality-pairs)
                (consp equality-pairs))
           (pseudo-termp (car (car equality-pairs))))
  :hints (("Goal" :in-theory (enable equality-pairsp))))

;; Turns ASSUMPTION into a list of directed equalities (dotted pairs of terms)
;; when possible.  Extends ACC.  Each equality assumption returned is a dotted
;; pair of two terms, so the result is an alist.
(defun add-equality-pairs-for-assumption (assumption known-booleans acc)
  (declare (xargs :guard (and (pseudo-termp assumption)
                              (symbol-listp known-booleans))
                  :measure (acl2-count assumption)))
  (if (atom assumption) ;; Could add an assumption from (equal nil x) to nil...
      (prog2$ (cw "NOTE: add-equality-pairs-for-assumption is skipping assumption ~x0.~%" assumption)
              acc)
    (let ((fn (ffn-symb assumption)))
      (if (eq 'quote fn) ;can this happen?
          (prog2$ (cw "NOTE: add-equality-pairs-for-assumption is skipping assumption ~x0.~%" assumption)
                  acc)
        (if (eq 'equal fn) ;fixme consider more sophisticated tests to decide whether to turn around the assumption?
            (if (quotep (farg1 assumption))
                ;; (equal x y) becomes the pair (y . x) because x is a quotep
                (cons (cons (farg2 assumption) (farg1 assumption))
                      acc)
              ;; (equal x y) becomes the pair (x . y)
              (cons (cons (farg1 assumption) (farg2 assumption))
                    acc))
          (if (eq 'not fn)
              ;; (not x) becomes the pair (x . 'nil) ;;the case above for 'equal above handles the (equal x nil) phrasing for nots..
              (cons (cons (farg1 assumption) ''nil)
                    acc)
            (if (and (eq 'booland fn) ;; TODO: Other ways of stripping conjuncts?
                     (= 2 (len (fargs assumption)))) ;for termination
                ;; (booland x y) causes x and y to be processed recursively
                (add-equality-pairs-for-assumption (farg2 assumption)
                                                   known-booleans
                                                   (add-equality-pairs-for-assumption (farg1 assumption)
                                                                                      known-booleans
                                                                                      acc))
              ;; (<predicate> x ...) becomes the pair ((<predicate> x ...) . 't)
              (if (member-eq fn known-booleans) ;we test for not above so dont need to exclude it here?
                  (cons (cons assumption ''t)
                        acc)
                ;; TODO: Consider putting back this printing once we stop using member-equal for assumptions
                ;; about initialized classes:
                (prog2$ nil ;(cw "NOTE: add-equality-pairs-for-assumption is skipping a ~x0 assumption.~%" fn) ;todo: print the assumption if small?
                        acc)))))))))

(defthm equality-pairsp-of-add-equality-pairs-for-assumption
  (implies (and (equality-pairsp acc)
                (pseudo-termp assumption))
           (equality-pairsp (add-equality-pairs-for-assumption assumption known-booleans acc)))
  :hints (("Goal" :in-theory (enable equality-pairsp))))

(defund add-equality-pairs-for-assumptions (assumptions known-booleans acc)
  (declare (xargs :guard (and (pseudo-term-listp assumptions)
                              (symbol-listp known-booleans))))
  (if (endp assumptions)
      acc
    (add-equality-pairs-for-assumptions (rest assumptions)
                                        known-booleans
                                        (add-equality-pairs-for-assumption (first assumptions)
                                                                           known-booleans
                                                                           acc))))

(defthm equality-pairsp-of-add-equality-pairs-for-assumptions
  (implies (and (equality-pairsp acc)
                (pseudo-term-listp assumptions))
           (equality-pairsp (add-equality-pairs-for-assumptions assumptions known-booleans acc)))
  :hints (("Goal" :in-theory (enable add-equality-pairs-for-assumptions))))

;ASSUMPTIONS is a list of terms
;returns a list of dotted pairs of terms
(defun make-equality-pairs (assumptions wrld)
  (declare (xargs :guard (and (pseudo-term-listp assumptions)
                              (plist-worldp wrld))))
  (add-equality-pairs-for-assumptions assumptions (known-booleans wrld) nil))

(defthm equality-pairsp-of-make-equality-pairs
  (implies (pseudo-term-listp assumptions)
           (equality-pairsp (make-equality-pairs assumptions wrld))))
