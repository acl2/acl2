; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "strcpy-safe-support")

(include-book "../syntax/input-files")
(include-book "../syntax/abstract-syntax-formal-mapping-direct")

(local (include-book "std/basic/fix" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Turn C code into ACL2 representation.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Read C code into ACL2.
(c$::input-files :files '("strcpy_safe.c")
                 :preprocess :internal
                 :const *strcpy-safe*)

; Check that the C code is within the subset with formal semantics.
(assert-event
 (c$::trans-ensemble-formalp
  (c$::code-ensemble->trans-units *strcpy-safe*)))

; Map the code to the form over which the formal semantics is defined.
(defconst *strcpy-safe-formal*
  (b* (((mv & tunits)
        (c$::ldm-trans-ensemble
         (c$::code-ensemble->trans-units *strcpy-safe*))))
    tunits))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specify the desired properties.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Obtain the buffer size from the code.
(defconst *buffer-size*
  (b* ((ensemb (c$::code-ensemble->trans-units *strcpy-safe*))
       (units (c$::trans-ensemble->units ensemb))
       (unit (omap::lookup (c$::filepath "strcpy_safe.c") units))
       (items (c$::trans-unit->items unit))
       (item (car items))
       (declon (c$::trans-item-declon->declon item))
       (fundef (c$::ext-declon-fundef->fundef declon))
       (body (c$::fundef->body fundef))
       (items (c$::comp-stmt->items body))
       (item (car items))
       (declon (c$::block-item-declon->declon item))
       (declors (c$::declon-declon->declors declon))
       (declor (car declors))
       (initer (c$::init-declor->initer? declor))
       (expr (c$::initer-single->expr initer))
       (const (c$::expr-const->const expr))
       (iconst (c$::const-int->iconst const))
       (info (c$::iconst->info iconst)))
    (c$::iconst-info->value info)))

; The buffer size is not 0.
(assert-event (/= *buffer-size* 0))

; An array is, in essence, a sequence (i.e. list) of values,
; so we define some predicates and functions on lists of values.

; This is the assumption on the values that form the source array.
; Unless the source array contains a 0,
; the C code will try to read buffersize - 1 elements from it.
; So the source array must have at least those many elements,
; if it does not contain any 0.
(define src-assump ((src-array-vals c::value-listp))
  :returns (yes/no booleanp)
  (or (and (member-equal (c::value-uchar 0) (c::value-list-fix src-array-vals))
           t)
      (>= (len src-array-vals) (1- *buffer-size*))))

; This is the assumption on the values that form the destination array.
; The number of values is buffersize.
; Note that this is an asusmption on the size of the destination array,
; not on the particular values.
(define dst-assump ((dst-array-vals c::value-listp))
  :returns (yes/no booleanp)
  (= (len dst-array-vals) *buffer-size*))

; Given a list of values, take their prefix until we find a 0 or we run out.
; The 0 itself is not taken, i.e. it does not appear in the result
; (see theorem no-zero-in-take-to-zero-or-end below).
; This is used below to calculate which values are copied from the source array.
(define take-to-zero-or-end ((vals c::value-listp))
  :returns (new-vals c::value-listp)
  (b* (((when (endp vals)) nil)
       (val (c::value-fix (car vals)))
       ((when (equal val (c::value-uchar 0))) nil))
    (cons val (take-to-zero-or-end (cdr vals))))
  ///
  (defret no-zero-in-take-to-zero-or-end
    (not (member-equal (c::value-uchar 0) new-vals))
    :hints (("Goal" :induct t)))
  (defret len-of-take-to-zero-or-end-bound
    (<= (len new-vals) (len vals))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

; These are the values in the source array copied to the destination array.
; First, we truncate the source array values to buffersize - 1,
; and then we take all the values until we reach a 0 or the end.
(define src-values-to-copy ((src-array-vals c::value-listp))
  :returns (vals c::value-listp)
  (b* ((vals (if (>= (len src-array-vals) (1- *buffer-size*))
                 (take (1- *buffer-size*) src-array-vals)
               src-array-vals)))
    (take-to-zero-or-end vals))
  ///
  (defret len-of-src-values-to-copy-bound
    (<= (len vals) (1- *buffer-size*))
    :rule-classes :linear))

; Final values of the destination array.
; The final destination array is obtained by replacing
; its initial elements (possibly all of them)
; with the ones copied from the source array, plus a 0;
; the rest of the destination array (if any) is unchanged.
(define dst-final ((dst-array-vals c::value-listp)
                   (src-array-vals c::value-listp))
  :guard (dst-assump dst-array-vals)
  :returns (dst-array-vals-final c::value-listp)
  (b* ((vals-to-copy (src-values-to-copy src-array-vals))
       (vals-to-keep (nthcdr (1+ (len vals-to-copy))
                             (c::value-list-fix dst-array-vals))))
    (append vals-to-copy
            (list (c::value-uchar 0))
            vals-to-keep))
  ///
  (defret len-of-dst-final
    (equal (len dst-array-vals-final)
           *buffer-size*)
    :hyp (dst-assump dst-array-vals)
    :hints (("Goal" :in-theory (enable dst-assump natp)))))

; The above provides the essence of the functional properties
; that we expect the C code to satisfy.
; Now we use them to state properties on the C code itself,
; including memory safety properties.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Verify the above properties.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Since the code has a loop, we formulate and prove a loop invariant,
; which we leverage to prove the correctness of the whole C function.

; This is the loop invariant on the index i:
; it is a signed integer whose value is non-negative and below buffersize.
(define i-loop-invp ((i-val c::valuep))
  :returns (yes/no booleanp)
  (and (c::value-case i-val :sint)
       (b* ((i (c::value-sint->get i-val)))
         (and (<= 0 i)
              (< i *buffer-size*)))))

; This is the loop invariant on the values of the source array,
; which depends on i, whose loop invariant is assumed in the guard.
; The index i is within the range of the array,
; and the elements of the array before i are not 0.
(define src-loop-invp ((src-array-vals c::value-listp)
                       (i-val c::valuep))
  :guard (and (src-assump src-array-vals)
              (i-loop-invp i-val))
  :returns (yes/no booleanp)
  (b* ((i (c::value-sint->get i-val)))
    (and (< i (len src-array-vals))
         (not (member-equal (c::value-uchar 0)
                            (take i (c::value-list-fix src-array-vals))))))
  :guard-hints (("Goal" :in-theory (enable i-loop-invp))))

; This defines the values of the destination array
; at the beginning of the loop.
; It is like a loop invariant for the destination array,
; but formulated as a function that calculates the destination array values
; from its initial values, the current value of i, and the source array values;
; note that the latter never change.
; At the beginning of the loop,
; the destination array has the first i values from the source array,
; while it retains the remaining values.
(define dst-at-loop ((dst-array-vals-initial c::value-listp)
                     (i-val-at-loop c::valuep)
                     (src-array-vals c::value-listp))
  :guard (and (dst-assump dst-array-vals-initial)
              (i-loop-invp i-val-at-loop)
              (src-assump src-array-vals)
              (src-loop-invp src-array-vals i-val-at-loop))
  :returns (dst-array-vals-at-loop c::value-listp)
  (b* ((i (c::value-sint->get i-val-at-loop))
       (vals-to-copy (take i src-array-vals))
       (vals-to-keep (nthcdr i (c::value-list-fix dst-array-vals-initial))))
    (append (c::value-list-fix vals-to-copy) vals-to-keep))
  :guard-hints (("Goal" :in-theory (enable i-loop-invp src-loop-invp)))
  ///
  (defret len-of-dst-at-loop
    (equal (len dst-array-vals-at-loop)
           *buffer-size*)
    :hyp (and (dst-assump dst-array-vals-initial)
              (i-loop-invp i-val-at-loop))
    :hints (("Goal" :in-theory (enable dst-assump i-loop-invp natp)))))

; TODO: continue
