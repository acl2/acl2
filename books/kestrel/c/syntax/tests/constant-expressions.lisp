; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../constant-expressions")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *constant-expressions-test-c17-dialect*
  (c::make-dialect :std (c::standard-c17)))

(defconst *constant-expressions-test-gcc-c17-dialect*
  (c::make-dialect :std (c::standard-c17) :gcc t))

(defconst *constant-expressions-test-one*
  (make-expr-const
   :const
   (const-int
    (make-iconst
     :core (dec/oct/hex-const-dec 1)
     :suffix? nil
     :info (make-iconst-vinfo :type (type-sint)
                              :value 1)))
   :info (make-type-vinfo :type (type-sint))))

(defconst *constant-expressions-test-variable*
  (make-expr-ident
   :ident (ident "x")
   :info (make-var-vinfo :type (type-sint)
                         :linkage (linkage-none)
                         :uid (uid 0))))

(defconst *constant-expressions-test-sint-tyname*
  (make-tyname
   :specquals (list (spec/qual-typespec (type-spec-int)))
   :declor? nil
   :info (make-type-vinfo :type (type-sint))))

(defconst *constant-expressions-test-double-tyname*
  (make-tyname
   :specquals (list (spec/qual-typespec (type-spec-double)))
   :declor? nil
   :info (make-type-vinfo :type (type-double))))

(defconst *constant-expressions-test-cast-to-double*
  (expr-cast *constant-expressions-test-double-tyname*
             *constant-expressions-test-one*))

(defconst *constant-expressions-test-cast-through-double*
  (expr-cast
   *constant-expressions-test-sint-tyname*
   *constant-expressions-test-cast-to-double*))

(defconst *constant-expressions-test-typeof-variable-tyname*
  (make-tyname
   :specquals
   (list
    (spec/qual-typespec
     (make-type-spec-typeof-expr
      :expr *constant-expressions-test-variable*
      :uscores (keyword-uscores-none))))
   :declor? nil
   :info (make-type-vinfo :type (type-sint))))

(define constant-expressions-test-pointer-to-array-tyname
  ((size exprp))
  :returns (tyname tynamep)
  (make-tyname
   :specquals (list (spec/qual-typespec (type-spec-int)))
   :declor?
   (make-absdeclor
    :pointers nil
    :direct?
    (make-dirabsdeclor-array
     :declor?
     (dirabsdeclor-paren
      (make-absdeclor :pointers (list nil)
                      :direct? nil))
     :qualspecs nil
     :size? size))
   :info
   (make-type-vinfo
    :type
    (make-type-pointer
     :to (make-type-array :of (type-sint)
                          :size nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Basic operands.

(acl2::assert-equal
 (expr-ice-p *constant-expressions-test-one*
             t
             *constant-expressions-test-c17-dialect*)
 t)

(acl2::assert-equal
 (expr-ice-p *constant-expressions-test-variable*
             t
             *constant-expressions-test-c17-dialect*)
 nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Cast restrictions.

(acl2::assert-equal
 (expr-ice-p *constant-expressions-test-cast-to-double*
             t
             *constant-expressions-test-c17-dialect*)
 nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Expression operands of sizeof.

(acl2::assert-equal
 (expr-ice-p
  (make-expr-unary
   :op (unop-sizeof)
   :arg *constant-expressions-test-variable*
   :info (make-type-vinfo :type (type-ulong)))
  t
  *constant-expressions-test-c17-dialect*)
 nil)

(acl2::assert-equal
 (expr-ice-p
  (make-expr-unary
   :op (unop-sizeof)
   :arg *constant-expressions-test-cast-to-double*
   :info (make-type-vinfo :type (type-ulong)))
  t
 *constant-expressions-test-c17-dialect*)
 t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Target type names of casts.

(acl2::assert-equal
 (expr-ice-p
  (make-expr-unary
   :op (unop-sizeof)
   :arg
   (expr-cast
    (constant-expressions-test-pointer-to-array-tyname
     *constant-expressions-test-variable*)
    *constant-expressions-test-one*)
   :info (make-type-vinfo :type (type-ulong)))
  t
  *constant-expressions-test-c17-dialect*)
 nil)

(acl2::assert-equal
 (expr-ice-p
  (make-expr-unary
   :op (unop-sizeof)
   :arg
   (expr-cast
    (constant-expressions-test-pointer-to-array-tyname
     *constant-expressions-test-cast-through-double*)
    *constant-expressions-test-one*)
   :info (make-type-vinfo :type (type-ulong)))
  t
  *constant-expressions-test-c17-dialect*)
 t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Type-name operands of sizeof.

(acl2::assert-equal
 (expr-ice-p
  (expr-sizeof
   (constant-expressions-test-pointer-to-array-tyname
    *constant-expressions-test-variable*))
  t
  *constant-expressions-test-c17-dialect*)
 nil)

;; The casts are exempted, but the bound may be evaluated, and this checker
;; does not establish the representability of the conversions.
(acl2::assert-equal
 (expr-ice-p
  (expr-sizeof
   (constant-expressions-test-pointer-to-array-tyname
    *constant-expressions-test-cast-through-double*))
  t
  *constant-expressions-test-c17-dialect*)
 :unknown)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Standard type-name operands of alignof.

(acl2::assert-equal
 (expr-ice-p
  (make-expr-alignof
   :type
   (constant-expressions-test-pointer-to-array-tyname
    *constant-expressions-test-variable*)
   :uscores (keyword-uscores-none))
  t
  *constant-expressions-test-c17-dialect*)
 nil)

;; Unlike the sizeof case above, the alignof operand is definitely unevaluated.
(acl2::assert-equal
 (expr-ice-p
  (make-expr-alignof
   :type
   (constant-expressions-test-pointer-to-array-tyname
    *constant-expressions-test-cast-through-double*)
   :uscores (keyword-uscores-none))
  t
  *constant-expressions-test-c17-dialect*)
 t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; GCC expression operands of alignof.

(acl2::assert-equal
 (expr-ice-p
  (make-expr-unary
   :op (unop-alignof (keyword-uscores-both))
   :arg *constant-expressions-test-variable*
   :info (make-type-vinfo :type (type-ulong)))
  t
  *constant-expressions-test-gcc-c17-dialect*)
 nil)

(acl2::assert-equal
 (expr-ice-p
  (make-expr-unary
   :op (unop-alignof (keyword-uscores-both))
   :arg *constant-expressions-test-one*
   :info (make-type-vinfo :type (type-ulong)))
  t
  *constant-expressions-test-gcc-c17-dialect*)
 :unknown)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Operands of typeof.

(acl2::assert-equal
 (expr-ice-p
  (expr-sizeof *constant-expressions-test-typeof-variable-tyname*)
  t
  *constant-expressions-test-gcc-c17-dialect*)
 nil)

(acl2::assert-equal
 (expr-ice-p
  (expr-sizeof
   (make-tyname
    :specquals
    (list
     (spec/qual-typespec
      (make-type-spec-typeof-type
       :type
       (constant-expressions-test-pointer-to-array-tyname
        *constant-expressions-test-variable*)
       :uscores (keyword-uscores-none))))
    :declor? nil
    :info (make-type-vinfo :type (type-sint))))
  t
  *constant-expressions-test-gcc-c17-dialect*)
 nil)
