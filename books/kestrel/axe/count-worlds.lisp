; Assigning counts to symbols
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

;; This book defines function to efficiently access and update dictionaries
;; from symbols to natural numbers (counts).

;; It is a generalization of the info-world idea in hit-counts.lisp.

(include-book "kestrel/typed-lists-light/all-consp" :dir :system)
(include-book "kestrel/alists-light/uniquify-alist-eq" :dir :system)
(include-book "kestrel/utilities/acons-fast" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))

;;
;; A world that associates symbols with counts (using a custom world)
;;

;; A true-list of triples of the form (sym prop . val).  See :doc world.
;; a specialization of plist-worldp that requires the values to be rationals.
(defund symbol-count-worldp (alist)
  (declare (xargs :guard t))
  (cond ((atom alist) (eq alist nil))
        (t (and (consp (car alist))
                (symbolp (car (car alist)))
                (consp (cdr (car alist)))
                (symbolp (cadr (car alist)))
                (rationalp (cddr (car alist))) ;new (could require natp)
                (symbol-count-worldp (cdr alist))))))

;limit?
(defthm plist-worldp-when-symbol-count-worldp
  (implies (symbol-count-worldp alist)
           (plist-worldp alist))
  :hints (("Goal" :in-theory (enable symbol-count-worldp plist-worldp))))

(defthm acl2-numberp-of-getprop-when-symbol-count-worldp
  (implies (and (symbol-count-worldp world)
                (acl2-numberp val))
           (acl2-numberp (sgetprop symbol key val world-name world)))
  :hints (("Goal" :in-theory (enable symbol-count-worldp))))

(defthm rationalp-of-getprop-when-symbol-count-worldp
  (implies (and (symbol-count-worldp world)
                (rationalp val))
           (rationalp (sgetprop symbol key val world-name world)))
  :hints (("Goal" :in-theory (enable symbol-count-worldp))))

;; TODO: Consider not calling extend-world each time (instead, maybe try every 20 times).
(defund increment-count-in-symbol-count-world (symbol world-name world)
  (declare (xargs :guard (and (symbolp symbol)
                              (symbolp world-name)
                              (symbol-count-worldp world))))
    (let* ((count (getprop symbol 'count 0 world-name world))
           (count (+ 1 count))
           (world (extend-world world-name (putprop symbol 'count count world))))
      world))

(defthm symbol-count-worldp-of-increment-count-in-symbol-count-world
  (implies (and (symbol-count-worldp world)
                (symbolp symbol))
           (symbol-count-worldp (increment-count-in-symbol-count-world symbol world-name world)))
  :hints (("Goal" :in-theory (enable increment-count-in-symbol-count-world SYMBOL-COUNT-WORLDP))))

(defund increment-counts-in-symbol-count-world (symbols world-name world)
  (declare (xargs :guard (and (symbol-listp symbols)
                              (symbolp world-name)
                              (symbol-count-worldp world))))
  (if (endp symbols)
      world
    (let ((world (increment-count-in-symbol-count-world (first symbols) world-name world)))
      (increment-counts-in-symbol-count-world (rest symbols)
                                              world-name
                                              world))))

(defthm symbol-count-worldp-of-increment-counts-in-symbol-count-world
  (implies (and (symbol-count-worldp world)
                (symbol-listp symbols))
           (symbol-count-worldp (increment-counts-in-symbol-count-world symbols world-name world)))
  :hints (("Goal" :in-theory (enable increment-counts-in-symbol-count-world))))


(defun empty-symbol-count-world (world-name)
  (declare (xargs :guard (symbolp world-name)))
  (prog2$ (retract-world world-name nil)
          ;setting :fake means that world is nil iff we are not tracking the world
          (increment-count-in-symbol-count-world :fake world-name nil)))

;; The world should be uniquify-ed before calling this.
(defun make-count-alist (world acc)
  (declare (xargs :guard (and (symbol-count-worldp world)
                              (alistp acc))
                  :guard-hints (("Goal" :in-theory (enable symbol-count-worldp)))))
  (if (endp world)
      acc
    (let* ((entry (car world))
           (symbol (car entry))
           ;;(key (cadr entry)) ;should be 'count
           (count (cddr entry)))
      (make-count-alist (cdr world) (if (eq :fake symbol) acc (acons-fast symbol count acc))))))

(defthm all-consp-of-make-count-alist
  (implies (all-consp acc)
           (all-consp (make-count-alist world acc))))

(defthm true-listp-of-make-count-alist
  (implies (true-listp acc)
           (true-listp (make-count-alist world acc))))

(defforall all-cdrs-rationalp (x) (rationalp (cdr x)) :guard (all-consp x))

(defthm all-cdrs-rationalp-of-make-count-alist
  (implies (and (symbol-count-worldp world)
                (all-cdrs-rationalp acc))
           (all-cdrs-rationalp (make-count-alist world acc)))
  :hints (("Goal" :in-theory (enable SYMBOL-COUNT-WORLDP))))

(defthm symbol-count-worldp-of-uniquify-alist-eq-aux
  (implies (and (symbol-count-worldp world)
                (symbol-count-worldp acc))
           (symbol-count-worldp (uniquify-alist-eq-aux world acc)))
  :hints (("Goal" :in-theory (enable symbol-count-worldp acons))))

(defthm symbol-alistp-when-symbol-count-worldp
  (implies (symbol-count-worldp world)
           (symbol-alistp world))
  :hints (("Goal" :in-theory (enable symbol-count-worldp))))


;; ;fixme redo this (and other!) merge sorts to follow the fast pattern in merge-sort.lisp

(defun merge-by-cdr-> (l1 l2 acc)
  (declare (xargs :measure (+ (len l1) (len l2))
                  :guard (and (all-consp l1)
                              (all-cdrs-rationalp l1)
                              (all-consp l2)
                              (all-cdrs-rationalp l2)
                              (true-listp acc))))
  (cond ((atom l1) (revappend acc l2))
        ((atom l2) (revappend acc l1))
        ((> (cdr (car l1)) (cdr (car l2)))
         (merge-by-cdr-> (cdr l1)
                         l2
                         (cons (car l1) acc)))
        (t (merge-by-cdr-> l1 (cdr l2)
                           (cons (car l2) acc)))))

(defthm acl2-count-of-evens-bound
  (implies (< 1 (len l))
           (< (acl2-count (evens l))
              (acl2-count l))))

(defthm <-of-acl2-count-of-evens
  (implies (consp (cdr l))
           (< (acl2-count (evens l))
              (acl2-count l)))
  :hints (("Goal" :in-theory (enable evens acl2-count))))

;fixme use defmergesort
(defun merge-sort-by-cdr-> (l)
  (declare (xargs :guard (and (true-listp l) ;why?
                              (all-consp l)
                              (all-cdrs-rationalp l))
                  :hints (("Goal" :in-theory (enable )))
                  :verify-guards nil ;done below
                  ))
  (cond ((atom (cdr l)) l)
        (t (merge-by-cdr-> (merge-sort-by-cdr-> (evens l))
                           (merge-sort-by-cdr-> (odds l))
                           nil))))

(defthm all-conps-of-evens
  (implies (all-consp x)
           (all-consp (evens x))))

(defthm all-consp-of-merge-by-cdr->
  (implies (and (all-consp x)
                (all-consp y)
                (all-consp acc))
           (all-consp (merge-by-cdr-> x y acc))))

(defthm all-consp-of-merge-sort-by-cdr->
  (implies (all-consp x)
           (all-consp (merge-sort-by-cdr-> x))))

(defthm all-cdrs-rationalp-of-evens
  (implies (all-cdrs-rationalp x)
           (all-cdrs-rationalp (evens x))))

(defthm all-cdrs-rationalp-of-merge-by-cdr->
  (implies (and (all-cdrs-rationalp x)
                (all-cdrs-rationalp y)
                (all-cdrs-rationalp acc))
           (all-cdrs-rationalp (merge-by-cdr-> x y acc))))

(defthm all-cdrs-rationalp-of-merge-sort-by-cdr->
  (implies (all-cdrs-rationalp x)
           (all-cdrs-rationalp (merge-sort-by-cdr-> x))))

(verify-guards merge-sort-by-cdr->)

;; TODO: Consider optimizing this by looping through all the rule names and
;; just looking up their counts, instead of calling uniquify-alist-eq.
(defun summarize-symbol-count-world (world)
  (declare (xargs :guard (symbol-count-worldp world)))
  (let* ((world (uniquify-alist-eq world)) ;does this not use the fast lookup into the world?
         (count-alist (make-count-alist world nil))
         ) ;removes shadowed bindings
    (merge-sort-by-cdr-> count-alist)))
