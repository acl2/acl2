; Utilities dealing with types that Axe knows about
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/quote" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; most-general-type

;todo: use a different representation?
(defund most-general-type ()
  (declare (xargs :guard t))
  t)

(defund most-general-typep (type)
  (declare (xargs :guard t))
  (eq type (most-general-type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; empty-type

;the type containing no values
(defund empty-type () (declare (xargs :guard t)) :empty-type)

;make a macro?
(defund empty-typep (type) (declare (xargs :guard t)) (eq (empty-type) type))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The boolean type

;why the list wrapper? use :boolean?
;rename make-boolean-type..
(defmacro boolean-type () ''(boolean))

(defund boolean-typep (type)
  (declare (xargs :guard t))
  (equal type (boolean-type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BV types (types of BV expressions ,currently just naturals representing the
;; width).

;; todo: make these macros?

;may change
(defund bv-typep (type)
  (declare (xargs :guard t))
  (natp type))

;a BV type is (now) an positive integer representing the width (maybe 0 is allowed too?)
;may change
(defund-inline make-bv-type (width)
  (declare (xargs :guard t))
  width)

(defthm bv-typep-of-make-bv-type
  (equal (bv-typep (make-bv-type width))
         (natp width))
  :hints (("Goal" :in-theory (enable make-bv-type))))

;may change
(defund-inline bv-type-width (type)
  (declare (xargs :guard t))
  type)

(defthm bv-type-width-of-make-bv-type
  (equal (bv-type-width (make-bv-type element-width))
         element-width)
  :hints (("Goal" :in-theory (enable bv-type-width make-bv-type))))

(defthm rationalp-of-bv-type-width
  (implies (bv-typep bv-type)
           (rationalp (bv-type-width bv-type)))
  :hints (("Goal" :in-theory (enable bv-type-width bv-typep))))

(defthm natp-of-bv-type-width
  (implies (bv-typep bv-type)
           (natp (bv-type-width bv-type)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable bv-type-width bv-typep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The :list type: ;; TODO: Restrict the element type and length type (this should be mutually recursive with axe-typep?)

(defund list-typep (type)
  (declare (xargs :guard t))
  (and (true-listp type)
       (eql 3 (len type)) ;this might be overkill to check in some cases?
       (eq :list (first type))
       ))

(defund make-list-type (element-type len-type)
  (declare (xargs :guard t))
  `(:list ,element-type ,len-type))

(defthm list-typep-of-make-list-type
  (list-typep (make-list-type element-type len-type))
  :hints (("Goal" :in-theory (enable list-typep make-list-type))))

(defund list-type-element-type (type)
  (declare (xargs :guard (list-typep type)
                  :guard-hints (("Goal" :in-theory (enable list-typep)))))
  (second type))

(defund list-type-len-type (type)
  (declare (xargs :guard (list-typep type)
                  :guard-hints (("Goal" :in-theory (enable list-typep)))))
  (third type))

(defthm list-type-len-type-of-make-list-type
  (equal (list-type-len-type (make-list-type element-type len-type))
         len-type)
  :hints (("Goal" :in-theory (enable list-type-len-type make-list-type))))

(defthm list-type-element-type-of-make-list-type
  (equal (list-type-element-type (make-list-type element-type len-type))
         element-type)
  :hints (("Goal" :in-theory (enable list-type-element-type make-list-type))))

;todo
;; (thm
;;  (implies (list-typep type)
;;           (axe-typep (list-type-len-type type)))
;;  :hints (("Goal" :in-theory (enable list-type-len-type list-typep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; axe-typep

;todo: what about a quoted constant? isn't that also a type?  maybe only used for array lengths?
;todo: what about :range types? only used for list lengths?
(defund axe-typep (type)
  (declare (xargs :guard t))
  (or (bv-typep type)
      (list-typep type)
      ;(bv-array-typep type) a subtype of the list-type
      (boolean-typep type)
      (most-general-typep type)
      (empty-typep type)))

;; nil is not an Axe type.  Needed for functions like get-induced-type.
(defthm not-axe-typep-of-nil
  (not (axe-typep nil))
  :rule-classes nil)

(defthm axe-typep-of-make-bv-type
  (implies (natp element-width)
           (axe-typep (make-bv-type element-width)))
  :hints (("Goal" :in-theory (enable axe-typep))))

;;
;; The "BV array" type (now this is just particular kind of :list type - namely, one where the elements are BVs and the length is a constant)
;;

(defund bv-array-typep (type)
  (declare (xargs :guard t))
  (and (list-typep type)
       (bv-typep (list-type-element-type type))
       (myquotep (list-type-len-type type))
       (natp (unquote (list-type-len-type type)))))

(defthm bv-array-typep-forward-to-list-typep
  (implies (bv-array-typep type)
           (list-typep type))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bv-array-typep))))

;fixme consider what to do for arrays of all zeros..
;note that an array type is compatible with any wider array type.. (but not one with a different length)
(defund make-bv-array-type (element-width len) ;ffixme these args aren't really types.. should they be?
  (declare (xargs :guard t))
  (make-list-type (make-bv-type element-width) (enquote len)))

(defthm list-typep-of-make-bv-array-type
  (implies (and (natp element-width)
                (natp len))
           (list-typep (make-bv-array-type element-width len)))
  :hints (("Goal" :in-theory (enable make-bv-array-type))))

(defthm axe-typep-of-make-bv-array-type
  (implies (and (natp element-width)
                (natp len))
           (axe-typep (make-bv-array-type element-width len)))
  :hints (("Goal" :in-theory (enable axe-typep))))

(defund bv-array-type-element-width (type)
  (declare (xargs :guard (bv-array-typep type)))
  (bv-type-width (list-type-element-type type)) ;(second type)
  )

(defthm bv-array-type-element-width-of-make-bv-array-type
  (equal (bv-array-type-element-width (make-bv-array-type element-width len))
         element-width)
  :hints (("Goal" :in-theory (enable make-bv-array-type bv-array-type-element-width))))

(defthm natp-of-bv-type-element-width
  (implies (bv-array-typep bv-array-type)
           (natp (bv-array-type-element-width bv-array-type)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable bv-array-type-element-width bv-array-typep))))

 ;the args of array types are not currently quoted...
(defund bv-array-type-len (type)
  (declare (xargs :guard (bv-array-typep type)
                  :guard-hints (("Goal" :in-theory (enable BV-ARRAY-TYPEP)))))
  (unquote (list-type-len-type type)))

(defthm natp-of-bv-array-type-len
  (implies (bv-array-typep type)
           (natp (bv-array-type-len type)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable bv-array-type-len bv-array-typep))))

(defthm bv-array-type-len-of-make-bv-array-type
  (equal (bv-array-type-len (make-bv-array-type element-width len))
         len)
  :hints (("Goal" :in-theory (enable make-bv-array-type bv-array-type-len))))

;drop?
(defthm not-bv-array-typep-of-make-bv-type
  (implies (natp width)
           (not (bv-array-typep (make-bv-type width))))
  :hints (("Goal" :in-theory (enable bv-array-typep
                                     make-bv-type
                                     bv-typep
                                     list-type-len-type
                                     list-type-element-type
                                     list-typep))))

;bozo add support for everything in *operators-whose-size-we-know*
;bozo add and verify guard? -- the guard will need to say that the indices encountered are numbers if they are constants...
;put (ffn-symb term) in a let...
;this one includes bvnth, which we can't usefully tighten, in rules like BVXOR-TIGHTEN-ARG2.
;that's the difference
;; (defun unsigned-term-size2 (term)
;;   (declare (xargs :guard (pseudo-termp term)
;;                   :guard-hints (("Goal" ;:do-not '(generalize eliminate-destructors)
;;                                  :in-theory (e/d (;pseudo-termp-hack LIST::LEN-POS-REWRITE
;;                                                   ) ( ;CAR-BECOMES-NTH-OF-0 consp-cdr
;;                                                      3-cdrs
;;                                                      ))))))
;;   (if (not (consp term)) ;must be a variable
;;       nil
;;     (if (quotep term)
;;         nil
;;       (if (member-equal (ffn-symb term) '(getbit bitxor bitnot))
;;           1
;;         (if (member-equal (ffn-symb term) '(bvand bvor bvxor bvplus bvmult bvnth)) ;BBBOZO
;;             (if (quotep (farg1 term))
;;                 (unquote (farg1 term))
;;               nil)
;; ;BOZO move this case down -- or remove it?
;;           (if (member-equal (ffn-symb term) '(myif))
;;               (let ((arg2size (unsigned-term-size2 (farg2 term)))
;;                     (arg3size (unsigned-term-size2 (farg3 term))))
;;                 (if (equal arg2size arg3size)
;;                     arg2size
;;                   nil))
;;             (if (member-equal (ffn-symb term) '(bvchop ;$inline bvnot))
;;                 (if (quotep (farg1 term))
;;                     (unquote (farg1 term))
;;                   nil)
;;               (if (member-equal (ffn-symb term) '(slice)) ;fixme this shouldn't be negative..
;;                   (if (and (quotep (farg1 term))
;;                            (quotep (farg2 term)))
;;                       (+ 1
;;                          (- (fix (unquote (farg1 term)))
;;                             (fix (unquote (farg2 term)))))
;;                     nil)
;; ;trying
;;                 ;;                 ;bozo eventually remove this?
;;                 ;;                 (if (member-equal (ffn-symb term) '(logapp))
;;                 ;;                     (let ((arg3size (signed-term-size (farg3 term))))
;;                 ;;                       (if (and arg3size (quotep (farg1 term)))
;;                 ;;                           (+ arg3size (unquote (farg1 term)))
;;                 ;;                         nil))
;;                 (if (member-equal (ffn-symb term) '(bvcat
;;                                                    ))
;;                     (if (and (quotep (farg1 term))
;;                              (quotep (farg3 term)))
;;                         (+ (fix (unquote (farg1 term)))
;;                            (fix (unquote (farg3 term))))
;;                       nil)
;;                   (if (member-equal (ffn-symb term) '(bvif))
;;                       (if (quotep (farg1 term))
;;                           (unquote (farg1 term))
;;                         nil)
;;                     nil))))))))))

;fffixme flesh this out! handle ranges? constants? sets?
;; Callers that care about type mismatches should consider calling most-general-typep on the result.
(defund union-types (type1 type2)
  (declare (xargs :guard (and (axe-typep type1)
                              (axe-typep type2))))
  (cond ((and (bv-typep type1)
              (bv-typep type2))
         (make-bv-type (max (bv-type-width type1)
                            (bv-type-width type2))))
        ((and (boolean-typep type1)
              (boolean-typep type2))
         (boolean-type))
        ((most-general-typep type1) (most-general-type))
        ((most-general-typep type2) (most-general-type))
        ((empty-typep type1) type2)
        ((empty-typep type2) type1)
        ((and (bv-array-typep type1)
              (bv-array-typep type2))
         (if (equal (bv-array-type-len type1)
                    (bv-array-type-len type2))
             (make-bv-array-type (max (bv-array-type-element-width type1)
                                      (bv-array-type-element-width type2))
                                 (bv-array-type-len type1))
           (prog2$ (cw "WARNING: Array length mismatch: ~x0 and ~x1" type1 type2)
                   (most-general-type))))
        (t (prog2$ (cw "WARNING: Type mismatch: ~x0 and ~x1" type1 type2)
                   (most-general-type)))))

(defthm axe-typep-of-union-types
  (implies (and (axe-typep x)
                (axe-typep y))
           (axe-typep (union-types x y)))
  :hints (("Goal" :in-theory (enable axe-typep union-types))))

;fffixme flesh this out! handle ranges? constants? sets?
(defund intersect-types (type1 type2)
  (declare (xargs :guard (and (axe-typep type1)
                              (axe-typep type2))))
  (cond ((empty-typep type1) (empty-type))
        ((empty-typep type2) (empty-type))
        ((most-general-typep type1) type2)
        ((most-general-typep type2) type1)
        ((and (boolean-typep type1)
              (boolean-typep type2))
         (boolean-type))
        ((and (bv-typep type1)
              (bv-typep type2))
         (make-bv-type (min (bv-type-width type1)
                            (bv-type-width type2))))
        ;;ffixme make sure this is sound:
        ((and (bv-array-typep type1)
              (bv-array-typep type2))
         (if (equal (bv-array-type-len type1)
                    (bv-array-type-len type2))
             (make-bv-array-type (min (bv-array-type-element-width type1)
                                      (bv-array-type-element-width type2))
                                 (bv-array-type-len type1))
           (prog2$ (hard-error 'intersect-types "Array length mismatch." nil)
                   (empty-type))))
        (t (hard-error 'intersect-types "Type mismatch." nil)))) ;improve message!

(defund intersect-types-safe (type1 type2)
  (declare (xargs :guard t))
  (cond ((empty-typep type1) (empty-type))
        ((empty-typep type2) (empty-type))
        ((most-general-typep type1) type2)
        ((most-general-typep type2) type1)
        ((and (boolean-typep type1)
              (boolean-typep type2))
         (boolean-type))
        ((and (bv-typep type1)
              (bv-typep type2))
         (make-bv-type (min (bv-type-width type1)
                            (bv-type-width type2))))
        ;;ffixme make sure this is sound:
        ((and (bv-array-typep type1)
              (bv-array-typep type2))
         (if (equal (bv-array-type-len type1)
                    (bv-array-type-len type2))
             (make-bv-array-type (min (bv-array-type-element-width type1)
                                      (bv-array-type-element-width type2))
                                 (bv-array-type-len type1))
           (prog2$ (cw "WARNING: Array length mismatch: ~x0 and ~x1" type1 type2)
                   (empty-type))))
        (t (prog2$ (cw "WARNING: Type mismatch: ~x0 and ~x1" type1 type2)
                   (empty-type)))))

(defthm axe-typep-of-intersect-types-safe
  (implies (and (axe-typep x)
                (axe-typep y))
           (axe-typep (intersect-types-safe x y)))
  :hints (("Goal" :in-theory (enable intersect-types-safe))))
