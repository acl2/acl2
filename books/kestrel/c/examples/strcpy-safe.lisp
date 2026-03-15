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

(include-book "kestrel/c/syntax/input-files" :dir :system)

(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file verifies the correctness of
; the safe version of the C library function strcpy(),
; in file strcpy_safe.c in this directory.
; The proof is carried out by unrolling the code,
; which is the reason why the code has a small buffer size, namely 4.
; This is just an initial feasibility experiment;
; a better generaal approach is to formulate and verify a loop invariant,
; for a generic buffer size,
; which we plan to do next.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Turn C code into ACL2 representation.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Read C code into ACL2.
(c$::input-files :files '("strcpy_safe.c")
                 :preprocess :internal
                 :const *strcpy-safe*)

; Check that the C code is within the subset with formal semantics.
(assert-event
 (c$::transunit-ensemble-formalp
  (c$::code-ensemble->transunits *strcpy-safe*)))

; Map the code to the form over which the formal semantics is defined.
(defconst *strcpy-safe-formal*
  (b* (((mv & tunits)
        (c$::ldm-transunit-ensemble
         (c$::code-ensemble->transunits *strcpy-safe*))))
    tunits))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specify the desired properties.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Symbolic constant for the size of the buffer.
(defconst *buffer-size* 4)

; An array is, in essence, a sequence (i.e. list) of values,
; so we define some preconditions and postconditions on lists of values.

; This is the precondition on the values that form the source array.
; Unless the source array contains a 0,
; the C code will try to read buffersize - 1 elements from it.
; So the source array must have at least those many elements,
; if it does not contain any 0.
(define src-precond ((src-array-vals c::value-listp))
  :returns (yes/no booleanp)
  (or (and (member-equal (c::value-uchar 0) src-array-vals) t)
      (>= (len src-array-vals) (1- *buffer-size*))))

; Given a list of values, take their prefix until we find a 0 or we run out.
; The 0 itself is not taken, i.e. it does not appear in the result
; (see theorem no-zero-in-take-to-zero-or-end below).
(define take-to-zero-or-end ((vals c::value-listp))
  :returns (new-vals c::value-listp)
  (b* (((when (endp vals)) nil)
       (val (c::value-fix (car vals)))
       ((when (equal val (c::value-uchar 0))) nil))
    (cons val (take-to-zero-or-end (cdr vals))))
  ///
  (defret no-zero-in-take-to-zero-or-end
    (not (member-equal (c::value-uchar 0) new-vals)))
  (defret len-of-take-to-zero-or-end-bound
    (<= (len new-vals) (len vals))
    :rule-classes :linear))

; These are the values in the source arrays copied to the destination array.
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

; This is the precondition on the values that form the destination array.
; The C code writes to the destination array
; the values copied from the source array, plus a final 0.
; So the destination array must contain enough values,
; i.e. one more than the ones copied from the source array.
; Note that this is a precondition on the size of the destination array,
; not on the particular values.
; While this precondition constains the destination array,
; it depends on the source array, whose values are passed as second parameter.
(define dst-precond ((dst-array-vals c::value-listp)
                     (src-array-vals c::value-listp))
  :returns (yes/no booleanp)
  (>= (len dst-array-vals) (1+ (len (src-values-to-copy src-array-vals)))))

; A postcondition is normally a predicate,
; but here we define it as a function that computes
; the new (i.e. final) values of the destination array,
; from the original (i.e. initial) values of the source and destination arrays.
; The postcondition predicate can be thought of as
; new-dst-array-vals = (dest-postcond dst-array-vals src-array-vals).
; The new destination array is obtained by replacing
; its initial elements (possibly all of them)
; with the ones copied from the source array, plus a 0;
; the rest of the destination array (if any) is unchanged.
(define dst-postcond ((dst-array-vals c::value-listp)
                      (src-array-vals c::value-listp))
  :guard (dst-precond dst-array-vals src-array-vals)
  :returns (new-dst-array-vals c::value-listp)
  (b* ((vals-to-copy (src-values-to-copy src-array-vals))
       (vals-to-keep (nthcdr (1+ (len vals-to-copy)) dst-array-vals)))
    (append vals-to-copy
            (list (c::value-uchar 0))
            (c::value-list-fix vals-to-keep)))
  ///
  (defret len-of-dst-postcond
    (equal (len new-dst-array-vals)
           (len dst-array-vals))
    :hyp (dst-precond dst-array-vals src-array-vals)
    :hints (("Goal" :in-theory (enable dst-precond)))))

; The above provides the essence of the functional properties
; that we expect the C code to satisfy.
; Now we use them to state properties on the C code itself,
; including memory safety properties.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Verify the above properties.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The precondition on src holds also on the prefix.

(make-event
 `(defruled src-precond-of-take
    (implies (src-precond src-array-vals)
             (src-precond (take ,(1- *buffer-size*) src-array-vals)))
    :enable src-precond))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Unrolling lemmas for src-values-to-copy.

(defruled src-values-to-copy-when-src0-is-0
  (implies (and (c::uchar-listp vals)
                (not (c::boolean-from-uchar (car vals))))
           (equal (src-values-to-copy vals)
                  nil))
  :enable (src-values-to-copy
           take-to-zero-or-end
           c::valuep-when-ucharp
           c::boolean-from-uchar
           c::equal-of-integer-from-uchar-to-uchar-from-integer))

(defruled src-values-to-copy-when-src1-is-0
  (implies (and (c::uchar-listp vals)
                (c::boolean-from-uchar (car vals))
                (not (c::boolean-from-uchar (cadr vals))))
           (equal (src-values-to-copy vals)
                  (list (car vals))))
  :enable (src-values-to-copy
           take-to-zero-or-end
           c::valuep-when-ucharp
           c::boolean-from-uchar
           c::equal-of-integer-from-uchar-to-uchar-from-integer))

(defruled src-values-to-copy-when-src2-is-0
  (implies (and (c::uchar-listp vals)
                (c::boolean-from-uchar (car vals))
                (c::boolean-from-uchar (cadr vals))
                (not (c::boolean-from-uchar (caddr vals))))
           (equal (src-values-to-copy vals)
                  (list (car vals) (cadr vals))))
  :enable (src-values-to-copy
           take-to-zero-or-end
           c::valuep-when-ucharp
           c::boolean-from-uchar
           c::equal-of-integer-from-uchar-to-uchar-from-integer))

(defruled src-values-to-copy-when-none-is-0
  (implies (and (c::uchar-listp vals)
                (c::boolean-from-uchar (car vals))
                (c::boolean-from-uchar (cadr vals))
                (c::boolean-from-uchar (caddr vals)))
           (equal (src-values-to-copy vals)
                  (list (car vals) (cadr vals) (caddr vals))))
  :enable (src-values-to-copy
           take-to-zero-or-end
           c::valuep-when-ucharp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Length bound lemmas for src.

;;;;;;;;;;;;;;;;;;;;

(defruled src-len-gt-1-when-src0-is-not-0
  (implies (and (src-precond src-array-vals)
                (not (equal (nth 0 src-array-vals) (c::value-uchar 0))))
           (< 1 (len src-array-vals)))
  :enable src-precond)

(defruled src-len-gt-2-when-src0/1-is-not-0
  (implies (and (src-precond src-array-vals)
                (not (equal (nth 0 src-array-vals) (c::value-uchar 0)))
                (not (equal (nth 1 src-array-vals) (c::value-uchar 0))))
           (< 2 (len src-array-vals)))
  :enable src-precond)

;;;;;;;;;;;;;;;;;;;;

(defruled src-len-gt-1-when-read-of-src0-is-not-0
  (implies (and (src-precond (c::value-array->elements src-array))
                (c::uchar-arrayp src-array)
                (c::boolean-from-uchar
                 (c::uchar-array-read src-array (c::sint-from-integer 0))))
           (< 1 (len (c::value-array->elements src-array))))
  :use (:instance src-len-gt-1-when-src0-is-not-0
                  (src-array-vals (c::value-array->elements src-array)))
  :enable (c::uchar-array-read
           c::uchar-array->elements-to-value-array->elements))

(defruled src-len-gt-2-when-read-of-src0/1-is-not-0
  (implies (and (src-precond (c::value-array->elements src-array))
                (c::uchar-arrayp src-array)
                (c::boolean-from-uchar
                 (c::uchar-array-read src-array (c::sint-from-integer 0)))
                (c::boolean-from-uchar
                 (c::uchar-array-read src-array (c::sint-from-integer 1))))
           (< 2 (len (c::value-array->elements src-array))))
  :use (:instance src-len-gt-2-when-src0/1-is-not-0
                  (src-array-vals (c::value-array->elements src-array)))
  :enable (c::uchar-array-read
           c::uchar-array->elements-to-value-array->elements))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Similar to the one just above, but without LEN.

(defruled cddr-of-src-array-when-read-of-src0/1-is-not-0
  (implies (and (src-precond (c::value-array->elements src-array))
                (c::uchar-arrayp src-array)
                (c::boolean-from-uchar
                 (c::uchar-array-read src-array (c::sint-from-integer 0)))
                (c::boolean-from-uchar
                 (c::uchar-array-read src-array (c::sint-from-integer 1))))
           (cddr (c::value-array->elements src-array)))
  :enable (src-len-gt-2-when-read-of-src0/1-is-not-0
           cddr-when-len-gt-2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Length bound lemmas for take-to-zero-or-end.

(defruled len-of-take-to-zero-or-end-geq-1-when-src0-is-not-0
  (implies (and (src-precond src-array-vals)
                (c::value-listp src-array-vals)
                (not (equal (nth 0 src-array-vals) (c::value-uchar 0))))
           (>= (len (take-to-zero-or-end src-array-vals)) 1))
  :rule-classes :linear
  :enable (src-precond take-to-zero-or-end))

(defruled len-of-take-to-zero-or-end-geq-2-when-src0/1-is-not-0
  (implies (and (src-precond src-array-vals)
                (c::value-listp src-array-vals)
                (not (equal (nth 0 src-array-vals) (c::value-uchar 0)))
                (not (equal (nth 1 src-array-vals) (c::value-uchar 0))))
           (>= (len (take-to-zero-or-end src-array-vals)) 2))
  :rule-classes :linear
  :enable (src-precond take-to-zero-or-end))

(defruled len-of-take-to-zero-or-end-geq-3-when-src0/1/2-is-not-0
  (implies (and (src-precond src-array-vals)
                (c::value-listp src-array-vals)
                (not (equal (nth 0 src-array-vals) (c::value-uchar 0)))
                (not (equal (nth 1 src-array-vals) (c::value-uchar 0)))
                (not (equal (nth 2 src-array-vals) (c::value-uchar 0))))
           (>= (len (take-to-zero-or-end src-array-vals)) 3))
  :rule-classes :linear
  :enable (src-precond take-to-zero-or-end))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Length bound lemmas for src-values-to-copy.

(make-event
 `(defruled len-of-src-values-to-copy-geq-1-when-src0-is-not-0
    (implies (and (src-precond src-array-vals)
                  (c::value-listp src-array-vals)
                  (not (equal (nth 0 src-array-vals) (c::value-uchar 0))))
             (>= (len (src-values-to-copy src-array-vals)) 1))
    :rule-classes :linear
    :use (len-of-take-to-zero-or-end-geq-1-when-src0-is-not-0
          (:instance len-of-take-to-zero-or-end-geq-1-when-src0-is-not-0
                     (src-array-vals (take ,(1- *buffer-size*)
                                           src-array-vals))))
    :enable (src-values-to-copy
             src-precond-of-take)))

(make-event
 `(defruled len-of-src-values-to-copy-geq-2-when-src0/1-is-not-0
    (implies (and (src-precond src-array-vals)
                  (c::value-listp src-array-vals)
                  (not (equal (nth 0 src-array-vals) (c::value-uchar 0)))
                  (not (equal (nth 1 src-array-vals) (c::value-uchar 0))))
             (>= (len (src-values-to-copy src-array-vals)) 2))
    :rule-classes :linear
    :use (len-of-take-to-zero-or-end-geq-2-when-src0/1-is-not-0
          (:instance len-of-take-to-zero-or-end-geq-2-when-src0/1-is-not-0
                     (src-array-vals (take ,(1- *buffer-size*)
                                           src-array-vals))))
    :enable (src-values-to-copy
             src-precond-of-take)))

(make-event
 `(defruled len-of-src-values-to-copy-geq-3-when-src0/1/2-is-not-0
    (implies (and (src-precond src-array-vals)
                  (c::value-listp src-array-vals)
                  (not (equal (nth 0 src-array-vals) (c::value-uchar 0)))
                  (not (equal (nth 1 src-array-vals) (c::value-uchar 0)))
                  (not (equal (nth 2 src-array-vals) (c::value-uchar 0))))
             (>= (len (src-values-to-copy src-array-vals)) 3))
    :rule-classes :linear
    :use (len-of-take-to-zero-or-end-geq-3-when-src0/1/2-is-not-0
          (:instance len-of-take-to-zero-or-end-geq-3-when-src0/1/2-is-not-0
                     (src-array-vals (take ,(1- *buffer-size*)
                                           src-array-vals))))
    :enable (src-values-to-copy
             src-precond-of-take)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Length bound lemmas for src.

;;;;;;;;;;;;;;;;;;;;

(defruled dst-len-gt-1-when-src0-is-not-0
  (implies (and (src-precond src-array-vals)
                (dst-precond dst-array-vals src-array-vals)
                (c::value-listp src-array-vals)
                (not (equal (nth 0 src-array-vals) (c::value-uchar 0))))
           (< 1 (len dst-array-vals)))
  :use len-of-src-values-to-copy-geq-1-when-src0-is-not-0
  :enable dst-precond)

(defruled dst-len-gt-2-when-src0/1-is-not-0
  (implies (and (src-precond src-array-vals)
                (dst-precond dst-array-vals src-array-vals)
                (c::value-listp src-array-vals)
                (not (equal (nth 0 src-array-vals) (c::value-uchar 0)))
                (not (equal (nth 1 src-array-vals) (c::value-uchar 0))))
           (< 2 (len dst-array-vals)))
  :use len-of-src-values-to-copy-geq-2-when-src0/1-is-not-0
  :enable dst-precond)

(defruled dst-len-gt-3-when-src0/1/2-is-not-0
  (implies (and (src-precond src-array-vals)
                (dst-precond dst-array-vals src-array-vals)
                (c::value-listp src-array-vals)
                (not (equal (nth 0 src-array-vals) (c::value-uchar 0)))
                (not (equal (nth 1 src-array-vals) (c::value-uchar 0)))
                (not (equal (nth 2 src-array-vals) (c::value-uchar 0))))
           (< 3 (len dst-array-vals)))
  :use len-of-src-values-to-copy-geq-3-when-src0/1/2-is-not-0
  :enable dst-precond)

;;;;;;;;;;;;;;;;;;;;

(defruled dst-len-gt-1-when-read-of-src0-is-not-0
  (implies (and (src-precond (c::value-array->elements src-array))
                (dst-precond (c::value-array->elements dst-array)
                             (c::value-array->elements src-array))
                (c::uchar-arrayp src-array)
                (c::boolean-from-uchar
                 (c::uchar-array-read src-array (c::sint-from-integer 0))))
           (< 1 (len (c::value-array->elements dst-array))))
  :use (:instance dst-len-gt-1-when-src0-is-not-0
                  (src-array-vals (c::value-array->elements src-array))
                  (dst-array-vals (c::value-array->elements dst-array)))
  :enable (c::uchar-array-read
           c::uchar-array->elements-to-value-array->elements))

(defruled dst-len-gt-2-when-read-of-src0/1-is-not-0
  (implies (and (src-precond (c::value-array->elements src-array))
                (dst-precond (c::value-array->elements dst-array)
                             (c::value-array->elements src-array))
                (c::uchar-arrayp src-array)
                (c::boolean-from-uchar
                 (c::uchar-array-read src-array (c::sint-from-integer 0)))
                (c::boolean-from-uchar
                 (c::uchar-array-read src-array (c::sint-from-integer 1))))
           (< 2 (len (c::value-array->elements dst-array))))
  :use (:instance dst-len-gt-2-when-src0/1-is-not-0
                  (src-array-vals (c::value-array->elements src-array))
                  (dst-array-vals (c::value-array->elements dst-array)))
  :enable (c::uchar-array-read
           c::uchar-array->elements-to-value-array->elements))

(defruled dst-len-gt-3-when-read-of-src0/1/2-is-not-0
  (implies (and (src-precond (c::value-array->elements src-array))
                (dst-precond (c::value-array->elements dst-array)
                             (c::value-array->elements src-array))
                (c::uchar-arrayp src-array)
                (c::boolean-from-uchar
                 (c::uchar-array-read src-array (c::sint-from-integer 0)))
                (c::boolean-from-uchar
                 (c::uchar-array-read src-array (c::sint-from-integer 1)))
                (c::boolean-from-uchar
                 (c::uchar-array-read src-array (c::sint-from-integer 2))))
           (< 3 (len (c::value-array->elements dst-array))))
  :use (:instance dst-len-gt-3-when-src0/1/2-is-not-0
                  (src-array-vals (c::value-array->elements src-array))
                  (dst-array-vals (c::value-array->elements dst-array)))
  :enable (c::uchar-array-read
           c::uchar-array->elements-to-value-array->elements))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lemma about the C function's information in the function environment.

(make-event
 `(defruled lookup-of-function
    (equal (c::fun-env-lookup (c::ident "strcpy_safe")
                              (c::init-fun-env
                               (c::preprocess *strcpy-safe-formal*)))
           ',(c::fun-env-lookup (c::ident "strcpy_safe")
                                (c::init-fun-env
                                 (c::preprocess *strcpy-safe-formal*))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Preconditions on computation state and parameters.

(defmacro precond ()
  '(and

    ;; This is the initial computation state.
    (c::compustatep compst)

    ;; The src parameter is a pointer value
    ;; whose referenced type is unsigned char.
    (c::valuep src)
    (c::value-case src :pointer)
    (equal (c::value-pointer->reftype src) (c::type-uchar))

    ;; The src pointer is valid (i.e. not null, not dangling),
    ;; and designates an array of unsigned chars in allocated storage.
    (c::value-pointer-validp src)
    (equal src-objdes (c::value-pointer->designator src))
    (c::objdesign-case src-objdes :alloc)
    (equal src-array (c::read-object src-objdes compst))
    (c::uchar-arrayp src-array)

    ;; The values of the source array
    ;; satisfy the precondition defined earlier.
    (equal src-array-vals (c::value-array->elements src-array))
    (src-precond src-array-vals)

    ;; The src parameter is a pointer value
    ;; whose referenced type is unsigned char.
    (c::valuep dst)
    (c::value-case dst :pointer)
    (equal (c::value-pointer->reftype dst) (c::type-uchar))

    ;; The dst pointer is valid (i.e. not null, not dangling),
    ;; and designates an array of unsigned chars in allocated storage.
    (c::value-pointer-validp dst)
    (equal dst-objdes (c::value-pointer->designator dst))
    (c::objdesign-case dst-objdes :alloc)
    (equal dst-array (c::read-object dst-objdes compst))
    (c::uchar-arrayp dst-array)

    ;; The values of the destination array
    ;; satisfy the precondition defined earlier.
    (equal dst-array-vals (c::value-array->elements dst-array))
    (dst-precond dst-array-vals src-array-vals)

    ;; The src and dst parameters point to disjoint objects.
    (c::object-disjointp src-objdes dst-objdes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Hypotheses and conclusions of the main correctness theorem.

(defmacro main-hyps ()
  '(and

    ;; Obtain function environment from ACL2 representation of the code.
    ;; A function environment contains information about
    ;; the C functions in the code (just one in this C code).
    (equal fenv (c::init-fun-env (c::preprocess *strcpy-safe-formal*)))

    ;; Name of the function of interest (the only one in the code).
    (equal fun (c::ident "strcpy_safe"))

    ;; Preconditions on computation state and function parameters.
    (precond)

    ;; We must provide an execution limit that suffices for the C code
    ;; (to prove total correctness, as opposed to only partial correctness).
    (integerp limit)
    (>= limit 1000) ; find suitable bound

    ;; Execute C function, obtaining result and final computation state.
    (equal result+new-compst
           (c::exec-fun fun (list dst src) compst fenv limit))
    (equal result (mv-nth 0 result+new-compst))
    (equal new-compst (mv-nth 1 result+new-compst))))

(defmacro main-concls ()
  '(and

    ;; The result is dst itself, and therefore not an error,
    ;; which implies no out-of-bound array access during execution.
    (equal result dst)

    ;; The final computation state is like the initial one,
    ;; except that the destination array has the contents
    ;; calculated by the postcondition function defined earlier.
    (equal new-compst
           (c::write-object dst-objdes
                            (c::make-value-array
                             :elemtype (c::type-uchar)
                             :elements (dst-postcond dst-array-vals
                                                     src-array-vals))
                            compst))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Case src[0] == 0.

(defrule correctness-when-src0-is-0
  (implies (and (main-hyps)
                ;; src[0] == 0
                (not (c::boolean-from-uchar
                      (c::uchar-array-read
                       (c::read-object (c::value-pointer->designator src)
                                       compst)
                       (c::sint-from-integer 0)))))
           (main-concls))
  :hints (;; First, do a full symbolic execution.
          ("Goal"
           :in-theory (union-theories
                       (expand-ruleset '(c::const-ast-accessors
                                         c::exec-stmt-openers
                                         c::exec-stmt-while-openers
                                         c::integer-const-folding
                                         c::array-index-const-folding)
                                       world)
                       *symb-exec-rules*))
          ;; Then, show the equality between
          ;; the destination array calculated by symbolic execution
          ;; and the one defined by the postcondition.
          (and stable-under-simplificationp
               '(:in-theory
                 (enable
                  c::uchar-array-read-of-sint-to-nth
                  c::uchar-array-write-of-sint-to-update-nth
                  c::value-array->elements-of-uchar-array-of
                  c::uchar-listp-of-value-array->elements-when-uchar-arrayp
                  dst-postcond
                  src-values-to-copy-when-src0-is-0
                  c::value-array-to-uchar-array-of))))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Case src[0] != 0 and src[1] == 0.

(defrule correctness-when-src1-is-0
  (implies (and (main-hyps)
                ;; src[0] != 0
                (c::boolean-from-uchar
                 (c::uchar-array-read
                  (c::read-object (c::value-pointer->designator src)
                                  compst)
                  (c::sint-from-integer 0)))
                ;; src[1] == 0
                (not (c::boolean-from-uchar
                      (c::uchar-array-read
                       (c::read-object (c::value-pointer->designator src)
                                       compst)
                       (c::sint-from-integer 1)))))
           (main-concls))
  :hints (;; First, do a full symbolic execution.
          ("Goal"
           :in-theory (union-theories
                       (expand-ruleset '(c::const-ast-accessors
                                         c::exec-stmt-openers
                                         c::exec-stmt-while-openers
                                         c::integer-const-folding
                                         c::array-index-const-folding)
                                       world)
                       (union-theories
                        *symb-exec-rules*
                        '(;; example-specific:
                          src-len-gt-1-when-read-of-src0-is-not-0
                          dst-len-gt-1-when-read-of-src0-is-not-0))))
          ;; Then, show the equality between
          ;; the destination array calculated by symbolic execution
          ;; and the one defined by the postcondition.
          (and stable-under-simplificationp
               '(:in-theory
                 (enable
                  c::uchar-array-read-of-sint-to-nth
                  c::uchar-array-write-of-sint-to-update-nth
                  c::value-array->elements-of-uchar-array-of
                  c::uchar-listp-of-value-array->elements-when-uchar-arrayp
                  len-cdr-lemma
                  src-len-gt-1-when-read-of-src0-is-not-0
                  dst-postcond
                  src-values-to-copy-when-src1-is-0
                  c::value-array-to-uchar-array-of)
                 :use (:instance
                       dst-len-gt-1-when-read-of-src0-is-not-0
                       (src-array (c::read-object
                                   (c::value-pointer->designator src)
                                   compst))
                       (dst-array (c::read-object
                                   (c::value-pointer->designator dst)
                                   compst))))))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Case src[0] != 0 and src[1] != 0 and src[2] == 0.

(defrule correctness-when-src2-is-0
  (implies (and (main-hyps)
                ;; src[0] != 0
                (c::boolean-from-uchar
                 (c::uchar-array-read
                  (c::read-object (c::value-pointer->designator src)
                                  compst)
                  (c::sint-from-integer 0)))
                ;; src[1] != 0
                (c::boolean-from-uchar
                 (c::uchar-array-read
                  (c::read-object (c::value-pointer->designator src)
                                  compst)
                  (c::sint-from-integer 1)))
                ;; src[2] == 0
                (not (c::boolean-from-uchar
                      (c::uchar-array-read
                       (c::read-object (c::value-pointer->designator src)
                                       compst)
                       (c::sint-from-integer 2)))))
           (main-concls))
  :hints (;; First, do a full symbolic execution.
          ("Goal"
           :in-theory (union-theories
                       (expand-ruleset '(c::const-ast-accessors
                                         c::exec-stmt-openers
                                         c::exec-stmt-while-openers
                                         c::integer-const-folding
                                         c::array-index-const-folding)
                                       world)
                       (union-theories
                        *symb-exec-rules*
                        '(;; example-specific:
                          src-len-gt-1-when-read-of-src0-is-not-0
                          src-len-gt-2-when-read-of-src0/1-is-not-0
                          dst-len-gt-1-when-read-of-src0-is-not-0
                          dst-len-gt-2-when-read-of-src0/1-is-not-0))))
          ;; Then, show the equality between
          ;; the destination array calculated by symbolic execution
          ;; and the one defined by the postcondition.
          (and stable-under-simplificationp
               '(:in-theory
                 (enable
                  c::uchar-array-read-of-sint-to-nth
                  c::uchar-array-write-of-sint-to-update-nth
                  c::value-array->elements-of-uchar-array-of
                  c::uchar-listp-of-value-array->elements-when-uchar-arrayp
                  len-cdr-lemma
                  len-cddr-lemma
                  src-len-gt-1-when-read-of-src0-is-not-0
                  src-len-gt-2-when-read-of-src0/1-is-not-0
                  dst-postcond
                  src-values-to-copy-when-src2-is-0
                  c::value-array-to-uchar-array-of)
                 :use ((:instance
                        dst-len-gt-1-when-read-of-src0-is-not-0
                        (src-array (c::read-object
                                    (c::value-pointer->designator src)
                                    compst))
                        (dst-array (c::read-object
                                    (c::value-pointer->designator dst)
                                    compst)))
                       (:instance
                        dst-len-gt-2-when-read-of-src0/1-is-not-0
                        (src-array (c::read-object
                                    (c::value-pointer->designator src)
                                    compst))
                        (dst-array (c::read-object
                                    (c::value-pointer->designator dst)
                                    compst)))))))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Case src[0] != 0 and src[1] != 0 and src[2] != 0.

(defrule correctness-when-none-is-0
  (implies (and (main-hyps)
                ;; src[0] != 0
                (c::boolean-from-uchar
                 (c::uchar-array-read
                  (c::read-object (c::value-pointer->designator src)
                                  compst)
                  (c::sint-from-integer 0)))
                ;; src[1] != 0
                (c::boolean-from-uchar
                 (c::uchar-array-read
                  (c::read-object (c::value-pointer->designator src)
                                  compst)
                  (c::sint-from-integer 1)))
                ;; src[2] != 0
                (c::boolean-from-uchar
                 (c::uchar-array-read
                  (c::read-object (c::value-pointer->designator src)
                                  compst)
                  (c::sint-from-integer 2))))
           (main-concls))
  :hints (;; First, do a full symbolic execution.
          ("Goal"
           :in-theory (union-theories
                       (expand-ruleset '(c::const-ast-accessors
                                         c::exec-stmt-openers
                                         c::exec-stmt-while-openers
                                         c::integer-const-folding
                                         c::array-index-const-folding)
                                       world)
                       (union-theories
                        *symb-exec-rules*
                        '(;; example-specific:
                          src-len-gt-1-when-read-of-src0-is-not-0
                          src-len-gt-2-when-read-of-src0/1-is-not-0
                          dst-len-gt-1-when-read-of-src0-is-not-0
                          dst-len-gt-2-when-read-of-src0/1-is-not-0
                          dst-len-gt-3-when-read-of-src0/1/2-is-not-0))))
          ;; Then, show the equality between
          ;; the destination array calculated by symbolic execution
          ;; and the one defined by the postcondition.
          (and stable-under-simplificationp
               '(:in-theory
                 (enable
                  c::uchar-array-read-of-sint-to-nth
                  c::uchar-array-write-of-sint-to-update-nth
                  c::value-array->elements-of-uchar-array-of
                  c::uchar-listp-of-value-array->elements-when-uchar-arrayp
                  len-cdr-lemma
                  len-cddr-lemma
                  len-cdddr-lemma
                  cddr-of-src-array-when-read-of-src0/1-is-not-0
                  nth
                  src-len-gt-1-when-read-of-src0-is-not-0
                  src-len-gt-2-when-read-of-src0/1-is-not-0
                  dst-postcond
                  src-values-to-copy-when-none-is-0
                  c::value-array-to-uchar-array-of)
                 :use ((:instance
                        dst-len-gt-1-when-read-of-src0-is-not-0
                        (src-array (c::read-object
                                    (c::value-pointer->designator src)
                                    compst))
                        (dst-array (c::read-object
                                    (c::value-pointer->designator dst)
                                    compst)))
                       (:instance
                        dst-len-gt-2-when-read-of-src0/1-is-not-0
                        (src-array (c::read-object
                                    (c::value-pointer->designator src)
                                    compst))
                        (dst-array (c::read-object
                                    (c::value-pointer->designator dst)
                                    compst)))
                       (:instance
                        dst-len-gt-3-when-read-of-src0/1/2-is-not-0
                        (src-array (c::read-object
                                    (c::value-pointer->designator src)
                                    compst))
                        (dst-array (c::read-object
                                    (c::value-pointer->designator dst)
                                    compst)))))))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Put together correctness proofs for the various cases,
; obtaining a general proof for the code.

(defrule correctness
  (implies (main-hyps)
           (main-concls))
  :cases (;; src[0] != 0 or not
          (c::boolean-from-uchar
           (c::uchar-array-read
            (c::read-object (c::value-pointer->designator src)
                            compst)
            (c::sint-from-integer 0)))
          ;; src[1] != 0 or not
          (c::boolean-from-uchar
           (c::uchar-array-read
            (c::read-object (c::value-pointer->designator src)
                            compst)
            (c::sint-from-integer 1)))
          ;; src[2] != 0 or not
          (c::boolean-from-uchar
           (c::uchar-array-read
            (c::read-object (c::value-pointer->designator src)
                            compst)
            (c::sint-from-integer 2))))
  :use (correctness-when-src0-is-0
        correctness-when-src1-is-0
        correctness-when-src2-is-0
        correctness-when-none-is-0)
  :rule-classes nil)
