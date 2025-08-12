; Getting type information to support the STP translation
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "axe-types")
(include-book "kestrel/lists-light/len-at-least" :dir :system)
(include-book "kestrel/bv-lists/width-of-widest-int" :dir :system)
(include-book "axe-syntax-functions-bv") ;for maybe-get-type-of-bv-function-call, todo reduce
(include-book "known-predicates")
(include-book "var-type-alists")
(include-book "nodenum-type-alists")
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))

;; Gets the type of a constant (bv or boolean or bv-array).
;; Returns an axe-type, or nil if no type can be determined.
(defund maybe-get-type-of-val (val)
  (declare (xargs :guard t))
  (if (natp val)
      (if (= 0 val)
          ;; Special case for 0: We use a type of BV1 since BV0 is not allowed:
          (make-bv-type 1)
        (make-bv-type (integer-length val)))
    (if (booleanp val)
        (boolean-type)
      ;; this is the tightest possible type, but wider element widths would also work:
      (if (and (len-at-least 2 val) ; otherwise, it's not a legal array for STP
               (nat-listp val))
          (make-bv-array-type (max 1 (width-of-widest-int val)) ;fixme if the values are all 0, we consider the element-width to be 1
                              (len val))
        ;; Could not determine the type of the constant:
        nil))))

(local
  (defthm axe-typep-of-maybe-get-type-of-val
    (implies (maybe-get-type-of-val val)
             (axe-typep (maybe-get-type-of-val val)))
    :hints (("Goal" :in-theory (enable maybe-get-type-of-val)))))

(local
  (defthm bv-array-type-len-of-maybe-get-type-of-val-when-bv-array-typep
    (implies (bv-array-typep (maybe-get-type-of-val val))
             (equal (bv-array-type-len (maybe-get-type-of-val val))
                    (len val)))
    :hints (("Goal" :in-theory (enable maybe-get-type-of-val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an axe-type, or throws an error if no type can be determined.
;; TODO: Can we avoid using this?
(defund get-type-of-val-checked (val)
  (declare (xargs :guard t))
  (let ((maybe-type (maybe-get-type-of-val val)))
    (or maybe-type
        (er hard? 'get-type-of-val-checked "Trying to get type of unrecognized constant: ~x0" val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an axe-type, possibly (most-general-type).
(defund get-type-of-val-safe (val)
  (declare (xargs :guard t))
  (let ((maybe-type (maybe-get-type-of-val val)))
    (or maybe-type
        (most-general-type))))

(defthm axe-typep-of-get-type-of-val-safe
  (axe-typep (get-type-of-val-safe val))
  :hints (("Goal" :in-theory (enable get-type-of-val-safe))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund unquote-if-possible (x)
  (declare (xargs :guard t))
  (if (and (quotep x)
           (consp (cdr x)))
      (unquote x)
    nil))

;; Returns an axe-type, or nil (if we could not determine the type).
;should some of the nil cases here be errors or warnings?
;fixme handle tuples?
;the args are nodenums or quoteps - we don't deref nodenums that may point to quoteps
;fixme make sure all callers of this handle nil okay (would it ever be better to throw an error?)?
;what if the number of arguments is wrong?
;; TODO: Consider adding support for constant arrays
;; TODO: Exclude FN from being 'QUOTE?
;; TODO: Are there other functions like this to deprecate?
(defund maybe-get-type-of-function-call (fn dargs)
  (declare (xargs :guard (and (symbolp fn)
                              (darg-listp dargs))))
  (or (maybe-get-type-of-bv-function-call fn dargs)
      (cond
       ;; Functions that return bv-arrays:
       ((or (eq fn 'bv-array-write) ; (bv-array-write element-size len index val data)
            (eq fn 'bv-array-if)) ; (bv-array-if element-size len test array1 array2)
        (let ((element-size (unquote-if-possible (first dargs)))
              (len (unquote-if-possible (second dargs))))
          (if (and (posp element-size)  ;fixme what if the width is 0?
                   (natp len)
                   (<= 2 len) ;todo: what if not?
                   )
              (make-bv-array-type element-size len)
            nil                                     ;error?
            )))
       ;; Functions that return booleans:
       ((member-eq fn *known-predicates-basic* ; TODO: Use the known-boolean stuff, in case we want to stub out a user-defined boolean function?
                   )
        (boolean-type)) ; TTODO: make sure these are handled right downstream
       (t nil ; could redo things to return most-general-type here
          ))))

;; If it's non-nil, it's an Axe type.
(defthm axe-typep-of-maybe-get-type-of-function-call
  (implies (maybe-get-type-of-function-call fn dargs)
           (axe-typep (maybe-get-type-of-function-call fn dargs)))
  :hints (("Goal" :in-theory (enable maybe-get-type-of-function-call))))

;; should this be true?
;; (defthm not-equal-of-maybe-get-type-of-function-call-and-make-bv-type-of-0
;;   (implies (maybe-get-type-of-function-call fn dargs)
;;            (not (equal (make-bv-type 0) (maybe-get-type-of-function-call fn dargs))))
;;   :hints (("Goal" :in-theory (enable maybe-get-type-of-function-call
;;                                      maybe-get-type-of-bv-function-call
;;                                      member-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an axe-type, or nil if no type can be determined.
;; Consults the alist before examining the node.
(defund maybe-get-type-of-nodenum (nodenum
                                   dag-array-name
                                   dag-array
                                   nodenum-type-alist ;for cut nodes (esp. those that are not bv expressions) ;now includes true input vars (or do we always cut at a var?)!
                                   )
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                              (nodenum-type-alistp nodenum-type-alist))))
  ;; first check whether it is given a type in nodenum-type-alist (fffixme what if we could strengthen that type?):
  (or (lookup nodenum nodenum-type-alist)
      ;; otherwise, look up the expression at that nodenum:
      (let ((expr (aref1 dag-array-name dag-array nodenum)))
        (if (variablep expr)
            nil ; it wasn't in the alist, so we can't do anything
          (let ((fn (ffn-symb expr)))
            (if (eq 'quote fn)
                (maybe-get-type-of-val (unquote expr))
              ;; it's a function call:
              (maybe-get-type-of-function-call fn (dargs expr))))))))

(local
  (defthm axe-typep-of-maybe-get-type-of-nodenum
    (implies (nodenum-type-alistp nodenum-type-alist)
             (iff (axe-typep (maybe-get-type-of-nodenum nodenum dag-array-name dag-array nodenum-type-alist))
                  (maybe-get-type-of-nodenum nodenum dag-array-name dag-array nodenum-type-alist)))
    :hints (("Goal" :in-theory (enable maybe-get-type-of-nodenum)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an axe-type, or throws an error if no type can be determined.
;; todo: ensure the error is appropriate for all callers
;; Consults the alist before examining the node.
(defund get-type-of-nodenum-checked (nodenum
                                     dag-array-name
                                     dag-array
                                     nodenum-type-alist ;for cut nodes (esp. those that are not bv expressions) ;now includes true input vars (or do we always cut at a var?)!
                                     )
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                              (nodenum-type-alistp nodenum-type-alist))))
  (or (maybe-get-type-of-nodenum nodenum dag-array-name dag-array nodenum-type-alist)
      (er hard? 'get-type-of-nodenum-checked "couldn't find type for nodenum ~x0, which has expr ~x1" nodenum (aref1 dag-array-name dag-array nodenum))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an axe-type, possibly (most-general-type).
;instead of throwing an error when given a nodenum that has no type yet, this one may return (most-general-type)
;fixme combine with the non-safe version -- pull out a "maybe-get-type-of-nodenum"
;; Consults the alist before examining the node.
(defund get-type-of-nodenum-safe (nodenum
                                  dag-array-name
                                  dag-array
                                  nodenum-type-alist ;for cut nodes (esp. those that are not bv expressions) ;now includes true input vars (or do we always cut at a var?)!
                                  )
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum))
                              (nodenum-type-alistp nodenum-type-alist))))
  (or (maybe-get-type-of-nodenum nodenum dag-array-name dag-array nodenum-type-alist)
      (most-general-type)))

(defthm axe-typep-of-get-type-of-nodenum-safe
  (implies (nodenum-type-alistp nodenum-type-alist)
           (axe-typep (get-type-of-nodenum-safe nodenum dag-array-name dag-array nodenum-type-alist)))
  :hints (("Goal" :in-theory (enable get-type-of-nodenum-safe lookup-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;get a known type (either the obvious type from looking at an expr, or a type from known-nodenum-type-alist)
;; Returns an axe-type, or nil if there's no known type.
;; Consults the ALIST after examining the node.
;; todo: special version for nodenums?
;; todo: compare to get-type-of-arg-safe
(defund maybe-get-type-of-arg (arg dag-array known-nodenum-type-alist)
  (declare (xargs :guard (and (or (myquotep arg)
                                  (and (natp arg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 arg))))
                              (nodenum-type-alistp known-nodenum-type-alist))))
  (if (consp arg) ; checks for quotep
      (maybe-get-type-of-val (unquote arg))
    ;; it's a nodenum
    (let ((expr (aref1 'dag-array dag-array arg)))
      (if (atom expr)
          ;; variable:
          (lookup arg known-nodenum-type-alist)
        (if (quotep expr)
            ;; constant:
            (maybe-get-type-of-val (unquote expr))
          ;; function call (todo: which do we prefer here? or intersect them?):
          (or (maybe-get-type-of-function-call (ffn-symb expr) (dargs expr))
              (lookup arg known-nodenum-type-alist)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an axe-type, or throws an error if no type can be determined.
;ffixme can crash if given a weird constant or a nodenum of a weird constant
;; todo: ensure all callers can handle nil being returned.
;; Consults the alist before examining the node.
(defund get-type-of-arg-checked (arg ;a nodenum or quotep
                                 dag-array-name
                                 dag-array
                                 cut-nodenum-type-alist ;for cut nodes (esp. those that are not bv expressions) ;now includes true input vars (or do we always cut at a var?)!
                                 )
  (declare (xargs :guard (and (or (myquotep arg)
                                  (and (natp arg)
                                       (pseudo-dag-arrayp dag-array-name dag-array (+ 1 arg))))
                              (nodenum-type-alistp cut-nodenum-type-alist))))
  (if (consp arg) ; tests for quotep
      (get-type-of-val-checked (unquote arg))
    (get-type-of-nodenum-checked arg dag-array-name dag-array cut-nodenum-type-alist)))

(defthm bv-array-type-len-of-get-type-of-arg-checked-when-bv-array-typep
  (implies (and (consp x)
                (bv-array-typep (get-type-of-arg-checked x dag-array-name dag-array cut-nodenum-type-alist)))
           (equal (bv-array-type-len (get-type-of-arg-checked x dag-array-name dag-array cut-nodenum-type-alist))
                  (len (unquote x))))
  :hints (("Goal" :in-theory (enable get-type-of-arg-checked get-type-of-val-checked))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an axe-type, possibly (most-general-type).
;; deprecate?  only called once, in prove-with-stp.lisp.
;; Consults the alist before examining the node.
(defund get-type-of-arg-safe (arg ;a nodenum or quotep
                              dag-array-name
                              dag-array
                              nodenum-type-alist ;for cut nodes (esp. those that are not bv expressions) ;now includes true input vars (or do we always cut at a var?)!
                              )
  (declare (xargs :guard (and (or (myquotep arg)
                                  (and (natp arg)
                                       (pseudo-dag-arrayp dag-array-name dag-array (+ 1 arg))))
                              (nodenum-type-alistp nodenum-type-alist))))
  (if (consp arg) ; tests for quotep
      (get-type-of-val-safe (unquote arg))
    (get-type-of-nodenum-safe arg dag-array-name dag-array nodenum-type-alist)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;similar to get-type-of-nodenum-checked but this one takes the var-type-alist
;returns a type (bv type, array type, etc.)
; only used once, just below
(defun get-type-of-nodenum-during-cutting (n dag-array-name dag-array var-type-alist)
  (declare (xargs :guard (and (var-type-alistp var-type-alist)
                              (natp n)
                              ;;(< n (alen1 dag-array-name dag-array))
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 n)))
                  :guard-hints (("Goal" :in-theory (enable var-type-alistp)))))
  ;;otherwise, look up the expression at that nodenum:
  (let ((expr (aref1 dag-array-name dag-array n)))
    (if (variablep expr)
        (if (assoc-eq expr var-type-alist) ;clear this up if nil is not a type...
            (lookup-eq expr var-type-alist)
          (er hard? 'get-type-of-nodenum-during-cutting "can't find type of var: ~x0" expr))
      (let ((fn (ffn-symb expr)))
        (if (eq 'quote fn)
            (get-type-of-val-checked (unquote expr))
          ;;it's a regular function call:
          (or (maybe-get-type-of-function-call fn (dargs expr))
              (er hard? 'get-type-of-nodenum-during-cutting "couldn't find size for expr ~x0 at nodenum ~x1" expr n)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; note that this takes a var-type-alist
(defund get-type-of-arg-during-cutting (arg dag-array-name dag-array var-type-alist)
  (declare (xargs :guard (and (var-type-alistp var-type-alist)
                              (or (myquotep arg)
                                  (and (natp arg)
                                       (pseudo-dag-arrayp dag-array-name dag-array (+ 1 arg))
                                       (< arg (alen1 dag-array-name dag-array)))))))
  (if (consp arg) ;tests for quotep
      (get-type-of-val-checked (unquote arg))
    (get-type-of-nodenum-during-cutting arg dag-array-name dag-array var-type-alist)))
