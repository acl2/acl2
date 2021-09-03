; A stobj to track results of rewriting
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

;; Used by rewriter-new.lisp

(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/utilities/acons-fast" :dir :system)
(include-book "dags") ;for all-dargp

;a result-array maps nodenums to alists from rewrite-objectives to nodenums-or-quoteps (the alist is nil if the node is not yet rewritten)

;move to a stobj-helpers book?
(defthm len-of-resize-list
  ;; [Jared] tweaked from natp hyp to nfix conclusion, and renamed variables,
  ;; for compatibility with std/lists
  (equal (len (resize-list lst n default))
         (nfix n)))

(in-theory (disable resize-list))

(defund result-alistp (alist)
  (declare (xargs :guard t))
  (and (alistp alist)
       (subsetp-eq (strip-cars alist) '(? t nil))
       (all-dargp (strip-cdrs alist))))

(defthm result-alistp-of-cons
  (equal (result-alistp (cons entry alist))
         (and (member-eq (car entry) '(? t nil))
              (dargp (cdr entry))
              (result-alistp alist)))
  :hints (("Goal" :in-theory (enable result-alistp))))

(defthm result-alistp-forward-to-alistp
  (implies (result-alistp alist)
           (alistp alist))
  :hints (("Goal" :in-theory (enable result-alistp))))

(defthm result-alistp-forward-to-symbol-alistp
  (implies (result-alistp alist)
           (symbol-alistp alist))
  :hints (("Goal" :in-theory (enable result-alistp))))

;A stobj representing an unbounded array from natural number indices to values.
;The values are result-alistp (alists from rewrite-objectives to
;nodenums/quoteps).  The array is resized when an attempt is made to set an
;element outside of the current size.  Elements beyond the max array size are
;;stored in the extra-elements field (accessing them will be slow). ;fixme
;;implement this
;todo: use an intial size larger than 10
(defstobj result-array-stobj
;  (thearraylength :type (integer 0 *) :initially 10)
  (thearray :type (array (satisfies result-alistp) (10)) :resizable t)
;  (extra-elements :type t) ;fixme implement this..
;  (default-array-value :type t :initially nil)
  )

(defthmd result-alistp-of-nth-when-thearrayp
  (implies (and (thearrayp array)
                (natp n)
                (< n (len array)))
           (result-alistp (nth n array)))
  :hints (("Goal" :in-theory (enable thearrayp))))

(defthm result-alistp-of-thearrayi
  (implies (and (result-array-stobjp result-array-stobj)
                (natp n)
                (< n (thearray-length result-array-stobj)))
           (result-alistp (thearrayi n result-array-stobj)))
  :hints (("Goal" :in-theory (enable result-array-stobjp thearrayi thearrayp thearray-length))))

(defthm thearray-length-of-resize-thearray
  (equal (thearray-length (resize-thearray i result-array-stobj))
         (nfix i))
  :hints (("Goal" :in-theory (enable resize-thearray  thearray-length))))

(defthm thearrayi-of-update-thearrayi
  (equal (thearrayi index (update-thearrayi index value result-array-stobj))
         value)
  :hints (("Goal" :in-theory (enable update-thearrayi thearrayi))))

(defthm thearray-length-of-update-thearrayi
  (implies (and (natp index)
                (< index (thearray-length result-array-stobj)))
           (equal (thearray-length (update-thearrayi index value result-array-stobj))
                  (thearray-length result-array-stobj)))
  :hints (("Goal" :in-theory (enable update-thearrayi thearray-length))))

(in-theory (disable thearray-length
                    thearrayi
                    thearrayp
                    update-thearrayi
                    resize-thearray
                    result-array-stobjp))

(defthmd alistp-of-nth-when-thearrayp
  (implies (and (thearrayp array)
                (natp n)
                (< n (len array)))
           (alistp (nth n array)))
  :hints (("Goal" :in-theory (enable thearrayp))))
(local (in-theory (enable alistp-of-nth-when-thearrayp)))

(defthm alistp-of-thearrayi
  (implies (and (result-array-stobjp result-array-stobj)
                (natp n)
                (< n (thearray-length result-array-stobj)))
           (alistp (thearrayi n result-array-stobj)))
  :hints (("Goal" :in-theory (enable result-alistp result-array-stobjp thearrayi thearrayp THEARRAY-LENGTH))))

(defthmd symbol-alistp-of-nth-when-thearrayp
  (implies (and (thearrayp array)
                (natp n)
                (< n (len array)))
           (symbol-alistp (nth n array)))
  :hints (("Goal" :in-theory (enable thearrayp))))

(defthm symbol-alistp-of-thearrayi
  (implies (and (result-array-stobjp result-array-stobj)
                (natp n)
                (< n (thearray-length result-array-stobj)))
           (symbol-alistp (thearrayi n result-array-stobj)))
  :hints (("Goal" :in-theory (enable result-alistp result-array-stobjp thearrayi thearrayp THEARRAY-LENGTH))))


;; (defthm symbol-alistp-of-car-when-thearrayp
;;   (implies (and (thearrayp x)
;;                 (< 0 (len x)))
;;            (symbol-alistp (car x)))
;;   :hints (("Goal" :in-theory (enable result-alistp))))

(defun get-from-result-array-stobj (index result-array-stobj)
  (declare (xargs :stobjs result-array-stobj)
           (type (integer 0 *) index)
           )
  (let ((current-length (thearray-length result-array-stobj)))
    (if (< index current-length) ;todo: can we sometimes avoid this check?
        (thearrayi index result-array-stobj)
      nil ;(default-array-value result-array-stobj)
      )))

(defun set-in-result-array-stobj (index value result-array-stobj)
  (declare (xargs :stobjs result-array-stobj
                  :guard (result-alistp value))
           (type (integer 0 *) index)
           ;;interesting.  we don't need an upper bound on index, but this will give a hard error is index>=2^28-1
           )
  (let ((current-length (thearray-length result-array-stobj)))
    (if (< index current-length)
        (update-thearrayi index value result-array-stobj)
      ;;must expand the array so that INDEX is a valid index (always expand by at least a factor of 2)
      ;fixme handle the maximum array size
      (let ((result-array-stobj (resize-thearray (max (* 2 current-length) (+ 1 index)) result-array-stobj)))
        (update-thearrayi index value result-array-stobj)))))

(defthm get-from-result-array-stobj-of-set-in-result-array-stobj-same
  (implies (natp index)
           (equal (get-from-result-array-stobj index (set-in-result-array-stobj index value result-array-stobj))
                  value))
  :hints (("Goal" :in-theory (enable LEN-UPDATE-NTH)
           :do-not '(generalize eliminate-destructors))))

;; ;fixme
;; (thm
;;  (implies (and (natp n)
;;                (natp newsize)
;;                (<= (len lst) newsize)
;;                (< n newsize))
;;           (equal (nth n (resize-list lst newsize val))
;;                  (nth n lst)))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;           :in-theory (e/d (resize-list LIST::NTH-OF-CONS nth) (NTH-OF-CDR)))))

;; ;fixme
;; (defthm get-from-result-array-stobj-of-set-in-result-array-stobj-diff
;;   (implies (and (not (equal index index2))
;;                 (natp index)
;;                 (natp index2))
;;            (equal (get-from-result-array-stobj index (set-in-result-array-stobj index2 value result-array-stobj))
;;                   (get-from-result-array-stobj index result-array-stobj)))
;;   :hints (("Goal" :in-theory (enable LEN-UPDATE-NTH)
;;            :do-not '(generalize eliminate-destructors))))


;if nodenum is too big, returns nil
;make a macro?
;will we ever know nodenum is not too big?
(defun get-result (nodenum rewrite-objective result-array-stobj)
  (declare (type (integer 0 *) nodenum)
           (xargs :stobjs result-array-stobj
                  ;;:guard (< nodenum (thearray-length result-array-stobj))
                  ))
  ;;interesting.  we don't need an upper bound on index, but this will give a hard error is index>=2^28-1
  (let ((result (lookup-eq rewrite-objective (get-from-result-array-stobj nodenum result-array-stobj))))
    (prog2$ nil ;(if result (cw "hit~%") (cw "miss~%"))
            result)))

;make a macro?
;todo: nested induction
(defun set-result (nodenum rewrite-objective result result-array-stobj)
  (declare (type (integer 0 *) nodenum)
           (xargs :stobjs result-array-stobj
;:verify-guards nil
                  :guard (and (DARGP result)
                              (member-eq rewrite-objective '(? t nil))
                              (< nodenum (thearray-length result-array-stobj)))
                  :guard-hints (("Goal" :in-theory (enable ;RESULT-ALISTP
                                                    )))
                  )
           ;;interesting.  we don't need an upper bound on index, but this will give a hard error is index>=2^28-1
           )
  (set-in-result-array-stobj nodenum
                             (acons-fast rewrite-objective result
                                         (get-from-result-array-stobj nodenum result-array-stobj))
                             result-array-stobj))

;; test: (defconst-computed2 *bar* (mv '3 state result-array-stobj))

(defun lookup-args-in-result-array2 (args
                                     arg-objectives ;;a list of objectives, or nil (meaning use '? for all)
                                     result-array-stobj)
  (declare (xargs ;:verify-guards nil ;;fixme need to say that the array entires are alists..
            :guard (and (true-listp args)
                        (all-dargp-less-than args (thearray-length result-array-stobj))
                        (or (not arg-objectives)
                            (equal (len arg-objectives)
                                   (len args))))
                  :stobjs result-array-stobj
                  ))
  (if (endp args)
      nil
    (let ((arg (car args)))
      (if (consp arg)
          ;;it's a quotep:
          (cons arg
                (lookup-args-in-result-array2 (rest args) (rest arg-objectives) result-array-stobj))
        (cons (get-result arg
                          (if arg-objectives (first arg-objectives) '?)
                          result-array-stobj) ;(aref1 'result-array result-array arg)
              (lookup-args-in-result-array2 (rest args) (rest arg-objectives) result-array-stobj))))))

(defun clear-result-array-stobj-elements (index result-array-stobj)
  (declare (xargs :stobjs (result-array-stobj)
;                  :verify-guards nil
                  :guard (and (integerp index)
                              (<= -1 index)
                              (< index (thearray-length result-array-stobj)))
                  :measure (nfix (+ 1 index))
                  ))
  (if (not (natp index))
      result-array-stobj
    (let ((result-array-stobj (update-thearrayi index nil result-array-stobj)))
      (clear-result-array-stobj-elements (+ -1 index) result-array-stobj))))

(defun clear-result-array-stobj (result-array-stobj)
  (declare (xargs :stobjs (result-array-stobj)))
  (let* ((result-array-stobj (resize-thearray 100 result-array-stobj))
         (result-array-stobj (clear-result-array-stobj-elements 99 result-array-stobj)))
    result-array-stobj))

;fixme make a function to print the stobj?
