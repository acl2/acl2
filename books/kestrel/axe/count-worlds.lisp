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

(include-book "merge-sort-by-cdr-greater")
;(include-book "kestrel/typed-lists-light/all-consp" :dir :system)
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

;;(defforall all-cdrs-rationalp (x) (rationalp (cdr x)) :guard (all-consp x))
(defund all-cdrs-rationalp (x)
  (declare (xargs :guard (all-consp x)))
  (if (not (consp x))
      t
    (and (rationalp (cdr (first x)))
         (all-cdrs-rationalp (rest x)))))

(defthm all-cdrs-rationalp-of-make-count-alist
  (implies (and (symbol-count-worldp world)
                (all-cdrs-rationalp acc))
           (all-cdrs-rationalp (make-count-alist world acc)))
  :hints (("Goal" :in-theory (enable symbol-count-worldp all-cdrs-rationalp))))

(defthm symbol-count-worldp-of-uniquify-alist-eq-aux
  (implies (and (symbol-count-worldp world)
                (symbol-count-worldp acc))
           (symbol-count-worldp (uniquify-alist-eq-aux world acc)))
  :hints (("Goal" :in-theory (enable symbol-count-worldp acons))))

(defthm symbol-alistp-when-symbol-count-worldp
  (implies (symbol-count-worldp world)
           (symbol-alistp world))
  :hints (("Goal" :in-theory (enable symbol-count-worldp))))

;; TODO: Consider optimizing this by looping through all the rule names and
;; just looking up their counts, instead of calling uniquify-alist-eq.
(defun summarize-symbol-count-world (world)
  (declare (xargs :guard (symbol-count-worldp world)))
  (let* ((world (uniquify-alist-eq world)) ;does this not use the fast lookup into the world?
         (count-alist (make-count-alist world nil))
         ) ;removes shadowed bindings
    (merge-sort-by-cdr-> count-alist)))
