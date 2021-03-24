; ACL2 arrays that grow as needed
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

(include-book "acl2-arrays")
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))

;fixme could we relax the guard on the index (and the array length claim in array1p?) for aset1-expandable?  maybe save pairs with huge indices in an alist in the array header?  would be slow but correct for huge indices?

(defconst *print-when-expanding* nil)

(defthm bounded-integer-alistp-when-bounded-integer-alistp
  (implies (and (bounded-integer-alistp l free)
                (<= free n)
                (integerp free)
                (integerp n))
           (bounded-integer-alistp l n))
  :hints (("Goal" :in-theory (enable bounded-integer-alistp))))

;(local (in-theory (disable array1p)))

(defthmd integerp-of-car-of-assoc-equal
  (implies (and (bounded-integer-alistp l n)
                (assoc-equal i l)
                (not (equal (car (assoc-equal i l)) :header)))
           (integerp (car (assoc-equal i l))))
  :hints (("Goal" :in-theory (e/d (bounded-integer-alistp) (car-of-assoc-equal-cheap)))))

(defthmd non-neg-of-car-of-assoc-equal
  (implies (and (bounded-integer-alistp l n)
                (assoc-equal i l)
                (not (equal (car (assoc-equal i l)) :header)))
           (<= 0 (car (assoc-equal i l))))
  :hints (("Goal" :in-theory (e/d (bounded-integer-alistp) (car-of-assoc-equal-cheap)))))

(defthmd <-of-car-of-assoc-equal
  (implies (and (bounded-integer-alistp l n)
                (assoc-equal i l)
                (not (equal (car (assoc-equal i l)) :header)))
           (< (car (assoc-equal i l)) n))
  :hints (("Goal" :in-theory (e/d (assoc-equal
                                   bounded-integer-alistp)
                                  (CAR-OF-ASSOC-EQUAL-cheap)))))

;move?
(defthmd array1p-of-cons-when-header-and-expanding
  (implies (and (consp header)
                (equal :header (car header))
                ;; the array is getting bigger:
                (<= (alen1 array-name array)
                    (car (cadr (assoc-keyword :dimensions (cdr header)))))
                (array1p array-name array)
                (keyword-value-listp (cdr header))
                (<= (cadr (assoc-keyword :maximum-length (cdr header))) 2147483647)
                (integerp (car (cadr (assoc-keyword :dimensions (cdr header)))))
                (true-listp (cadr (assoc-keyword :dimensions (cdr header))))
                (equal 1 (len (cadr (assoc-keyword :dimensions (cdr header)))))
                (< (car (cadr (assoc-keyword :dimensions (cdr header))))
                   (cadr (assoc-keyword :maximum-length (cdr header))))
                (integerp (cadr (assoc-keyword :maximum-length (cdr header))))
                (< 0
                   (car (cadr (assoc-keyword :dimensions (cdr header))))))
           (array1p array-name (cons header array)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (array1p-rewrite
                           )
                           (ASSOC-EQUAL
                           )))))

;the :maximum-length field of an array1p is at most 2147483647=(expt 2 31)-1
;the length an array1p is at most 2147483646, since it must be < :maximum-length
;a valid index into an array1p is at most 2147483645, since it must be < the length
(defconst *max-1d-array-length* 2147483646)

;;;
;;; expand-array
;;;

; Expand the array L, whose name is NAME, so that INDEX is a valid index into
; the array after it is expanded.  New indices effectively get the default
; value (stored in the array header).  See also maybe-expand-array.
(defund expand-array (name l header-args index current-length)
  (declare (xargs :guard (and (array1p name l)
                              ;; passed in for efficiency since the caller already has this:
                              (equal header-args (cdr (header name l)))
                              ;; passed in for efficiency since the caller already has this:
                              (equal current-length (alen1 name l))
                              (natp index)
                              (<= index 2147483645))
                  :guard-hints (("Goal" :in-theory (enable array1p-rewrite)))
                  :split-types t)
           (type symbol name)
           (type (integer 0 2147483645) index)
           (type (integer 1 2147483646) current-length))
  (let* ( ;; Make sure that INDEX will be a valid index and also that we at least double the length.
         (desired-new-length (max (+ 1 index) (* 2 current-length)))
         ;; Ensure that the new length is not larger than is allowed:
         (new-length (min 2147483646 desired-new-length)))
    (prog2$ (and *print-when-expanding* (cw "Expanding size of array ~x0 from ~x1 to ~x2.~%" name current-length new-length)) ;drop?
            (let* ((default (cadr (assoc-keyword :default header-args)))
                   (l (compress1 name (cons `(:header :dimensions (,new-length)
                                                      :maximum-length ,(min 2147483647 (* 2 new-length))
                                                      :default ,default
                                                      :name ,name)
                                            l))))
              l))))

;; IFs in the conclusion can cause problems
(defthm alen1-of-expand-array
  (implies (and (equal (alen1 array-name array) current-length)
                ;(array1p array-name array)
                ;(keyword-value-listp header-args)
                (natp index)
                (<= index 2147483645)
                ;(posp current-length)
                (<= current-length 2147483646))
           (equal (alen1 array-name (expand-array array-name array header-args index current-length))
                  (min 2147483646
                       (max (+ 1 index) (* 2 current-length)))))
  :hints (("Goal" :in-theory (enable expand-array))))

;; The index is almost always in bounds after expand-array (that's the point of
;; expand-array), except when the index is huge.
(defthm <-of-alen1-of-expand-array
  (implies (natp index)
           (equal (< index (alen1 name (expand-array name l header-args index length)))
                  (<= index 2147483645)))
  :hints (("Goal" :in-theory (enable expand-array))))

(defthm <-of-alen1-of-expand-array-linear
  (implies (and (natp index)
                (<= index 2147483645))
           (< index (alen1 name (expand-array name l header-args index length))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable expand-array))))

(defthm array1p-of-expand-array
  (implies (and (<= (alen1 array-name array) index) ;else we shouldn't be calling expand-array
                (natp index)
                ;(<= index 2147483645)
                (array1p array-name array)
                (integerp length) ;should be (alen1 array-name array) in fact
                (equal header-args (cdr (header array-name array))))
           (array1p array-name (expand-array array-name array header-args index length)))
  :hints (("Goal" :in-theory (enable expand-array array1p-rewrite))))

;todo: more theorems about default
(defthm default-of-expand-array
  (implies (equal header-args (cdr (header array-name array)))
           (equal (default array-name (expand-array array-name array header-args index length))
                  (default array-name array)))
  :hints (("Goal" :in-theory (enable expand-array array1p-rewrite))))

(local
 (defthm aref1-of-expand-array-large
  (implies (and (< index index2) ;this case
                (natp index)
                (natp index2)
                (<= index 2147483645)
                (array1p array-name array)
                (= (alen1 array-name array) current-length)
                (<= (alen1 array-name array) index) ;else we shouldn't be calling expand-array
                (equal header-args (cdr (header array-name array)))
                )
           (equal (aref1 array-name (expand-array array-name array header-args index current-length) index2)
                  (default array-name array)))
  :hints (("Goal" :in-theory (enable EXPAND-ARRAY AREF1-WHEN-NOT-ASSOC-EQUAL
                                     aref1-when-too-large
                                     array1p-of-cons-when-header-and-expanding)))))

(local
 (defthm aref1-of-expand-array-small
  (implies (and (<= index2 index) ;this case
                (natp index)
                (natp index2)
                (<= index 2147483645)
                (array1p array-name array)
                (= (alen1 array-name array) current-length)
                (<= (alen1 array-name array) index) ;else we shouldn't be calling expand-array
                (equal header-args (cdr (header array-name array)))
                )
           (equal (aref1 array-name (expand-array array-name array header-args index current-length) index2)
                  (aref1 array-name array index2)))
  :hints (("Goal" :in-theory (enable EXPAND-ARRAY AREF1-WHEN-NOT-ASSOC-EQUAL
                                     array1p-of-cons-when-header-and-expanding)))))

;; After expanding, a lookup either gives the same value (if the index was
;; valid before) or the default value (if the index is beyond what was valid
;; before).
(defthm aref1-of-expand-array
  (implies (and (natp index)
                (natp index2)
                (<= index 2147483645)
                (array1p array-name array)
                (= (alen1 array-name array) current-length)
                (<= (alen1 array-name array) index) ;else we shouldn't be calling expand-array
                (equal header-args (cdr (header array-name array)))
                )
           (equal (aref1 array-name (expand-array array-name array header-args index current-length) index2)
                  (if (< index index2)
                      (default array-name array)
                    (aref1 array-name array index2)))))

;;;
;;; aset1-expandable
;;;

;like aset1, except the array can grow
;is this fast?
;use fixnums?
;watch for arrays that would be too big!
;only works when index <= 2147483645
(defund aset1-expandable (name l index val)
  (declare (xargs :guard (and (array1p name l)
                              (natp index)
                              (<= index 2147483645))
                  :guard-hints (("Goal" :in-theory (enable array1p-rewrite expand-array)))
                  :split-types t)
           (type symbol name)
           (type (integer 0 2147483645) index))
  (let* ((header-args (cdr (header name l)))
         (dimensions (cadr (assoc-keyword :dimensions header-args))) ;call dimensions here?  would that be slower?
         (length (the (integer 1 2147483646) (car dimensions))))
    (if (< index length)
        (aset1 name l index val)
      ;;otherwise, we need to expand the array first:
      (let ((l (expand-array name l header-args index length)))
        (aset1 name l index val)))))

(defthm index-in-bounds-after-aset1-expandable
  (implies (and (natp index)
                (<= index 2147483645))
           (< index (alen1 name (aset1-expandable name l index val))))
  :hints (("Goal" :in-theory (enable aset1-expandable)
           :expand (dimensions name l))))

(defthm array1p-of-aset1-expandable
  (implies (and (array1p array-name array)
                (natp len)
                (<= len 2147483645))
           (array1p array-name (aset1-expandable array-name array len val)))
  :hints (("Goal" :in-theory (e/d (aset1-expandable)
                                  (alen1-of-expand-array ;why?
                                   )))))

;;;
;;; maybe-expand-array
;;;

;; Expand the array L, which should be the semantic value of NAME, if necessary
;; so that INDEX will be a valid index into it.
(defund maybe-expand-array (name l index)
  (declare (xargs :guard (and (array1p name l)
                              (natp index)
                              (<= index 2147483645))
                  :guard-hints (("Goal" :in-theory (enable array1p-rewrite)))
                  :split-types t)
           (type symbol name)
           (type (integer 0 2147483645) index))
  (let* ((header-args (cdr (header name l)))
         (dimensions (cadr (assoc-keyword :dimensions header-args))) ;call the function dimensions?
         (length (the (integer 1 2147483646) (car dimensions))))
    (if (< index length)
        l
      (expand-array name l header-args index length))))

;; Recharacterize with nice (if slower) body
(defthmd maybe-expand-array-rewrite
  (equal (maybe-expand-array name l index)
         (let* ((header-args (cdr (header name l)))
                (dimensions (dimensions name l))
                (length (car dimensions)))
           (if (< index length)
               l
             (expand-array name l header-args index length))))
  :hints (("Goal" :in-theory (enable maybe-expand-array))))

(defthm array1p-of-maybe-expand-array
  (implies (and (natp index)
;                (<= index 21474836456)
                (array1p array-name array)
                )
           (array1p array-name (maybe-expand-array array-name array index)))
  :hints (("Goal" :in-theory (enable array1p expand-array maybe-expand-array header))))

(defthm integerp-of-alen1-of-maybe-expand-array
  (implies (and (natp index)
;                (<= index 2147483646)
;                (array1p array-name array)
                (integerp (alen1 array-name array))
 ;               (<= (alen1 array-name array) 2147483646)
                )
           (integerp (alen1 array-name (maybe-expand-array array-name array index))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable array1p-rewrite expand-array maybe-expand-array))))

(defthm default-of-maybe-expand-array
  (equal (default array-name (maybe-expand-array array-name array index))
         (default array-name array))
  :hints (("Goal" :in-theory (enable maybe-expand-array))))

(defthm index-in-bounds-after-maybe-expand-array
  (implies (and (natp index)
                (<= index 2147483645))
           (< index (alen1 name (maybe-expand-array name l index))))
  :rule-classes (:rewrite (:linear :trigger-terms ((alen1 name (maybe-expand-array name l index)))))
  :hints (("Goal" ;:expand (dimensions name l)
           :in-theory (enable maybe-expand-array))))

(defthm alen1-of-maybe-expand-array-bound
  (implies (and (natp index)
                (<= (alen1 array-name array) 2147483646) ; implied by array1p
                )
           (<= (alen1 array-name array)
               (alen1 array-name (maybe-expand-array array-name array index))))
  :rule-classes (:rewrite (:linear :trigger-terms ((alen1 array-name (maybe-expand-array array-name array index)))))
  :hints (("Goal" :in-theory (e/d (maybe-expand-array-rewrite expand-array
                                                        array1p-rewrite) ()))))

(defthm aref1-of-maybe-expand-array-small
  (implies (and (<= index2 (alen1 array-name array))
                (natp index)
                (natp index2)
                (<= index 2147483645)
                (array1p array-name array))
           (equal (aref1 array-name (maybe-expand-array array-name array index) index2)
                  (aref1 array-name array index2)))
  :hints (("Goal" :in-theory (enable maybe-expand-array EXPAND-ARRAY aref1
                                     array1p-of-cons-when-header-and-expanding))))

(defthm aref1-of-maybe-expand-array-large
  (implies (and ;(< index index2)
                (<= (alen1 array-name array) index2)
                (natp index)
                (natp index2)
                (<= index 2147483645)
                (array1p array-name array))
           (equal (aref1 array-name (maybe-expand-array array-name array index) index2)
                  (default array-name array)))
  :hints (("Goal" :in-theory (enable maybe-expand-array))))

(defthm aref1-of-maybe-expand-array
  (implies (and (natp index)
                (natp index2)
                (<= index 2147483645)
                (array1p array-name array))
           (equal (aref1 array-name (maybe-expand-array array-name array index) index2)
                  (aref1 array-name array index2)))
  :hints (("Goal" :in-theory (enable aref1-when-too-large maybe-expand-array))))

(defthm alen1-of-aset1-expandable
  (implies (and; (array1p array-name array)
                (natp index))
           (equal (alen1 array-name (aset1-expandable array-name array index val))
                  (alen1 array-name (maybe-expand-array array-name array index))))
  :hints (("Goal" :in-theory (e/d (maybe-expand-array aset1-expandable aset1)
                                  ()))))

(defthm <=-of-alen1-of-maybe-expand-array-and-max
  (implies (<= (alen1 array-name array) 2147483646)
           (<= (alen1 array-name (maybe-expand-array array-name array index)) 2147483646))
  :hints (("Goal" :in-theory (enable maybe-expand-array expand-array))))

;; (defthm dimensions-of-aset1-expandable
;;   (implies (and ;(array1p array-name array)
;;                 (natp index))
;;            (equal (dimensions array-name (aset1-expandable array-name array index val))
;;                   (dimensions array-name (maybe-expand-array array-name array index))))
;;   :hints (("Goal" :in-theory (e/d (maybe-expand-array aset1-expandable aset1)
;;                                   ()))))

;;;
;;; aref1-expandable
;;;

;returns the default value for indices that are too large
(defun aref1-expandable (name l index)
  (declare (xargs :guard (and (array1p name l)
                              (natp index)
                              (<= index 2147483645))
                  :guard-hints (("Goal" :in-theory (enable array1p-rewrite expand-array)))
                  :split-types t)
           (type symbol name)
           (type (integer 0 2147483645) index))
  (let* ((header-args (cdr (header name l)))
         (dimensions (cadr (assoc-keyword :dimensions header-args)))
         (length (car dimensions)))
    (if (< index length)
        (aref1 name l index)
      (cadr (assoc-keyword :default header-args)))))

;fixme prove aref1-expandable of aset1-expandable

;; (defthm assoc-equal-of-header-of-compress11
;;   (equal (assoc-equal :header (compress11 NAME L I N DEFAULT))
;;          (assoc-equal :header l))
;;   :hints (("Goal" :in-theory (enable compress11 header))))

(defthm aref1-of-aset1-expandable-small
  (implies (and (<= index2 index) ;drop?
                (natp index)
                (natp index2)
                (<= index 2147483645)
                (<= index2 2147483645)
                ;; (not (array-order (header array-name array)))
                ;; (< index (alen1 array-name array))
                ;; (< index2 (alen1 array-name array))
                (array1p array-name array))
           (equal (aref1 array-name (aset1-expandable array-name array index val) index2)
                  (if (equal index index2)
                      val
                    (aref1 array-name array index2))))
  :hints (("Goal" :in-theory (e/d (maybe-expand-array
                                   aset1-expandable)
                                  (alen1-of-expand-array ;why?
                                   )))))

(defthm maybe-expand-array-does-nothing
  (implies (< index (alen1 array-name array))
           (equal (maybe-expand-array array-name array index)
                  array))
  :hints (("Goal" :in-theory (enable maybe-expand-array))))

;;;
;;; size-of-expanded-array
;;;

(defund size-of-expanded-array (index current-length)
  (if (< index current-length)
      current-length
    (let* ((desired-new-length (max (+ 1 index) (* 2 current-length)))
           (new-length (min 2147483646 desired-new-length)))
      new-length)))

(defthm bound-on-size-of-expanded-array
  (implies (and (natp index)
                (<= index 2147483645))
           (<= current-length (size-of-expanded-array index current-length)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable size-of-expanded-array))))

;TODO keep enabled
(defthmd alen1-of-maybe-expand-array
  (equal (alen1 array-name (maybe-expand-array array-name array index))
         (size-of-expanded-array index (alen1 array-name array)))
  :hints (("Goal" :in-theory (enable size-of-expanded-array maybe-expand-array expand-array))))

(defthm <-of-alen1-of-maybe-expand-array
  (implies (< index 2147483646)
           (< index (alen1 array-name (maybe-expand-array array-name array index))))
  :hints (("Goal" :in-theory (enable maybe-expand-array expand-array))))

(defthm <-of-alen1-of-maybe-expand-array-linear
  (implies (and (< index 2147483646))
           (< index (alen1 array-name (maybe-expand-array array-name array index))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable maybe-expand-array expand-array))))

(defthm not-equal-of-alen1-of-maybe-expand-array
  (implies (and ;(array1p array-name array)
                (< index 2147483646))
           (not (equal index
                       (alen1 array-name (maybe-expand-array array-name array index)))))
  :hints (("Goal" :in-theory (enable maybe-expand-array expand-array))))
