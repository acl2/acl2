; Types in the JVM
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "kestrel/utilities/forms" :dir :system) ;; for farg1

;;;
;;; Primitive Types (see JVM Spec 2.3)
;;;

(defconst *integral-types* '(:byte :short :int :long :char))

(defconst *floating-point-types* '(:float :double))

(defconst *numeric-types* (append *integral-types* *floating-point-types*))

(defconst *primitive-types* (append *numeric-types*
                                    '(:boolean)
                                    ;;TODO: What about the return address type?
                                    ))

(defconst *one-slot-types* '(:byte :char :float :int :short :boolean))
(defconst *two-slot-types* '(:double :long))

;; These are types that are represented as bit-vectors:
(defconst *bv-types* (append *integral-types* '(:boolean)))

;; Note that Axe already has a function called bv-typep.
(defun bit-vector-typep (type)
  (declare (xargs :guard t))
  (if (member-eq type *bv-types*) t nil))

(defun primitive-typep (type)
  (declare (xargs :guard t))
  (if (member-eq type *primitive-types*) t nil))

;;;
;;; Reference Types (see JVM Spec 2.4)
;;;

(defund class-namep (name) (declare (xargs :guard t)) (stringp name))

;TODO: use this more instead of stringp and also, in many cases, instead of class-namep:
(defund class-or-interface-namep (name) (declare (xargs :guard t)) (stringp name))

(defthm class-or-interface-namep-forward-to-stringp
  (implies (class-or-interface-namep name)
           (stringp name))
  :rule-classes :forward-chaining)

;; TODO: Prove that the various types are disjoint.

(mutual-recursion
 ;; An array-typep represents the parsed form of an array type descriptor such
 ;; as "[[I".  This is our representation of the name of the array class. (The
 ;; JVM spec says "For such array classes, the name of the class is the
 ;; descriptor of the array type (4.3.2).")  TODO: Consider limiting the
 ;; number of dimensions to 255.
 (defun array-typep (type)
   (declare (xargs :guard t
                   :measure (make-ord 1 (+ 1 (acl2-count type)) 1)))
   (and (consp type) ;; (:array <component-type>), where <component-type> can itself be an array type
        (eq :array (car type))
        (consp (cdr type))
        (typep (cadr type))
        (null (cddr type))))

 (defun reference-typep (type)
   (declare (xargs :guard t
                   :measure (make-ord 1 (+ 1 (acl2-count type)) 2)))
   (or (class-or-interface-namep type)
       (array-typep type)))

 ;; A JVM type is a primitive type or a reference type (including the array types)
 (defund typep (type)
   (declare (xargs :guard t
                   :measure (make-ord 1 (+ 1 (acl2-count type)) 3)))
   (or (primitive-typep type)
       (reference-typep type))))

(defthm array-typep-forward-to-non-nil
  (implies (array-typep type)
           type)
  :rule-classes :forward-chaining)

(defun all-typep (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
      (and (typep (first x))
           (all-typep (rest x)))))

(defthm all-typep-of-append
  (equal (all-typep (append x y))
         (and (all-typep x)
              (all-typep y)))
  :hints (("Goal" :in-theory (enable all-typep))))

(defthm typep-of-car
  (implies (all-typep x)
           (equal (typep (car x))
                  (consp x)))
  :hints (("Goal" :in-theory (disable typep))))

;;;
;;; Representation of primitives types in the JVM model
;;;
;;; TODO: Should these be functions or macros?

;; Test whether a type is an array type.
(defund is-array-typep (type)
  (declare (xargs :guard (typep type)))
  (and (consp type)
       (eq :array (car type))))

(defthm is-array-typep-forward-to-consp
  (implies (is-array-typep type)
           (consp type))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable is-array-typep))))

(defun make-one-dim-array-type (component-type)
  (declare (xargs :guard (typep component-type)))
  (list :array component-type))

;; Test whether a type is a one-dimensional array type.
(defund is-one-dim-array-typep (type)
  (declare (xargs :guard (typep type)
                  :guard-hints (("Goal" :in-theory (enable typep
                                                           is-array-typep)))))
  (and (is-array-typep type)
       (not (is-array-typep (farg1 type)))))

(defund type-slot-count (type)
  (declare (xargs :guard (typep type)
                  :guard-hints (("Goal" :in-theory (enable typep
                                                           is-array-typep)))))
  (if (member-eq type *one-slot-types*)
      1
    (if (member-eq type *two-slot-types*)
        2
      (if (stringp type)
          1 ;it's a reference
        (if (is-array-typep type)
            1
          (prog2$ (er hard 'type-slot-count "Unrecognized type: ~x0." type)
                  1))))))

(defthm natp-of-type-slot-count
  (natp (type-slot-count param))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable type-slot-count typep))))

(defun count-slots-in-types (types)
  (declare (xargs :guard (and (true-listp types)
                              (all-typep types))))
  (if (endp types)
      0
    (+ (type-slot-count (first types))
       (count-slots-in-types (rest types)))))

(defun get-array-component-type (array-type)
  (declare (xargs :guard (and (typep array-type)
                              (is-array-typep array-type))
                  :guard-hints (("Goal" :in-theory (enable typep
                                                           is-array-typep)))))
  (farg1 array-type))

;get the element type (not the component type) of an array type
(defun get-array-element-type (type)
  (declare (xargs :guard (typep type)
                  :guard-hints (("Goal" :in-theory (enable typep
                                                           is-array-typep)))))
  (if (is-array-typep type)
      ;;strip off :array and recur:
      (get-array-element-type (farg1 type))
    type))

(defun make-array-type (dim-count element-type)
  (declare (xargs :guard (and (natp dim-count)
                              (typep element-type) ;require it to not be an array type?
                              )))
  (if (zp dim-count)
      element-type
    (list :array (make-array-type (+ -1 dim-count) element-type))))

(defthm consp-of-make-array-type
  (implies (and (typep element-type)
                (not (is-array-typep element-type)))
           (iff (consp (make-array-type dims element-type))
                (posp dims)))
  :hints (("Goal" :expand (make-array-type 1 element-type)
           :in-theory (enable make-array-type typep
                              is-array-typep))))

(defun number-of-array-dimensions (type)
  (declare (xargs :guard (typep type)
                  :guard-hints (("Goal" :in-theory (enable typep)))))
  (if (is-array-typep type)
      (+ 1 (number-of-array-dimensions (farg1 type)))
    0))

(defthm equal-of-number-of-array-dimensions-and-0
  (implies (typep type)
           (equal (equal (number-of-array-dimensions type) 0)
                  (not (is-array-typep type)))))

;TODO: Would be safer to split into 2 cases
(defthm number-of-array-dimensions-constant-opener
  (implies (syntaxp (quotep type))
           (equal (number-of-array-dimensions type)
                  (if (is-array-typep type)
                      (+ 1
                         (number-of-array-dimensions (farg1 type)))
                    0))))

(defthm number-of-array-dimensions-of-make-array-type
  (implies (and (typep element-type)
                (not (is-array-typep element-type)))
           (equal (number-of-array-dimensions (make-array-type dims element-type))
                  (nfix dims)))
  :hints (("Goal" :in-theory (enable is-array-typep))))

;; This is the size of the array element used to store TYPE. Note that several
;; of these types are usually converted to ints before they are operated on by
;; the JVM.
(defun size-of-array-element (type)
  (declare (xargs :guard (bit-vector-typep type)))
  (case type
    (:int 32)
    (:byte 8)
    (:boolean 1) ;; conceptually we use 8-bit bytes, but this restricts the 8-bit value used to be either 0 or 1
    (:short 16)
    (:char 16)
    (:long 64)))


;move up:


;; I am trying the following approach: is-array-typep is just for execution and
;; should be rewrittten away to array-typep when typep (note that
;; is-array-typep has a guard of typep)..
(defthm is-array-typep-rewrite
  (implies (typep x)
           (equal (is-array-typep x)
                  (array-typep x)))
  :hints (("Goal" :in-theory (enable typep
                                     is-array-typep))))

(defthm array-typep-when-not-other-types
 (implies (and (not (primitive-typep type))
               (not (class-or-interface-namep type))
               (typep type))
          (array-typep type))
 :rule-classes ((:rewrite :backchain-limit-lst (0 0 nil)))
 :hints (("Goal" :expand (array-typep type)
          :in-theory (enable typep array-typep reference-typep))))

(defthm typep-of-get-array-component-type
  (implies (array-typep type)
           (typep (get-array-component-type type)))
  :hints (("Goal" :expand ((TYPEP TYPE)
                           (REFERENCE-TYPEP TYPE))
           :in-theory (e/d (array-typep reference-typep
                              TYPEP
                              get-array-component-type)
                           ()))))

(defthm primitive-typep-forward-to-symbolp
  (implies (primitive-typep type)
           (symbolp type))
  :rule-classes :forward-chaining)

(defthm array-typep-forward-to-consp
  (implies (array-typep type)
           (consp type))
  :rule-classes :forward-chaining)

(defthm array-typep-forward-to-typep
  (implies (array-typep type)
           (typep type))
  :rule-classes :forward-chaining)

(defthm is-array-typep-forward-to-typep
  (implies (is-array-typep type)
           (consp type))
  :rule-classes :forward-chaining)

(defund return-typep (type)
  (declare (xargs :guard t))
  (or (typep type)
      (eq :void type)))
