; Equivalence relations used by Axe
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Add a way for the user to soundly extend the equiv-alist used by Axe.

(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)

;; We may some day support more equivalence relation, but for now we only
;; support 'equal and 'iff.
(defund equivp (x)
  (declare (xargs :guard t))
  (member-equal x '(equal iff)))

(defthm equivp-forward-to-symbolp
  (implies (equivp x)
           (symbolp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable equivp))))

(defund equiv-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (equivp (first x))
         (equiv-listp (rest x)))))

(defthm equivp-of-car-when-equiv-listp
  (implies (and (equiv-listp x)
                (consp x))
           (equivp (car x)))
  :hints (("Goal" :in-theory (enable equiv-listp))))

(defthm equiv-listp-of-cdr
  (implies (equiv-listp equivs)
           (equiv-listp (cdr equivs)))
  :hints (("Goal" :in-theory (enable equiv-listp))))

(defun equiv-list-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (equiv-listp (first x))
         (equiv-list-listp (rest x)))))

;; Recognize an alist that maps symbols to lists of equivs
(defund symbol-to-equivs-alistp (x)
  (declare (xargs :guard t))
  (and (symbol-alistp x)
       (equiv-list-listp (strip-cdrs x))))

(defthm symbol-to-equivs-alistp-forward-to-symbol-alistp
  (implies (symbol-to-equivs-alistp x)
           (symbol-alistp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable symbol-to-equivs-alistp))))

(defthm equiv-listp-of-lookup-equal-when-symbol-to-equivs-alistp
  (implies (symbol-to-equivs-alistp alist)
           (equiv-listp (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable symbol-to-equivs-alistp))))

(defund all-symbol-to-equivs-alistp (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (symbol-to-equivs-alistp (first x))
         (all-symbol-to-equivs-alistp (rest x)))))

(defthm symbol-to-equivs-alistp-of-lookup-equal-when-all-symbol-to-equivs-alistp-of-strip-cdrs
  (implies (all-symbol-to-equivs-alistp (strip-cdrs alist))
           (symbol-to-equivs-alistp (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable all-symbol-to-equivs-alistp lookup-equal assoc-equal))))

(defthm symbol-alistp-of-lookup-equal-when-all-symbol-to-equivs-alistp-of-strip-cdrs
  (implies (all-symbol-to-equivs-alistp (strip-cdrs alist))
           (symbol-alistp (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable all-symbol-to-equivs-alistp lookup-equal assoc-equal))))

;;;
;;; equiv-alistp
;;;

;; Recognize an equiv-alist, which is used by the Axe Prover to decide which equivs to use when rewriting.
;; To use such a table, you look up the outer equivalence to preserve and, in the result of that, you look up the function being
;; rewritten.  The result is the list of equivalences to maintain when rewriting each of the function's arguments.
(defund equiv-alistp (equiv-alist)
  (declare (xargs :guard t))
  (and (symbol-alistp equiv-alist)
       (equiv-listp (strip-cars equiv-alist))
       (all-symbol-to-equivs-alistp (strip-cdrs equiv-alist))))

;;;
;;; get-equivs
;;;

;; Get the equivs that should be used when rewriting the args of FN, if we are to preserve OUTER-EQUIV on the call of FN.
(defund get-equivs (outer-equiv fn equiv-alist)
  (declare (xargs :guard (equiv-alistp equiv-alist)
                  :guard-hints (("Goal" :in-theory (enable equiv-alistp)))))
  (lookup-eq fn (lookup-eq outer-equiv equiv-alist)))

(defthm equiv-listp-of-get-equivs
  (implies (equiv-alistp equiv-alist)
           (equiv-listp (get-equivs outer-equiv fn equiv-alist)))
  :hints (("Goal" :in-theory (enable get-equivs equiv-alistp))))
