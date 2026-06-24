; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../types-to-tynames")
(include-book "../printer")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Render a type to the string of its type name, using the GCC/C17 dialect
;; and the default printing options. Used below to check the result of
;; TYPE-TO-TYNAME against the expected source text.

(define render-type ((type typep))
  :returns (string stringp)
  :verify-guards nil
  (b* ((dialect (c::make-dialect :std (c::standard-c17) :gcc t))
       (ienv (ienv-default :dialect dialect))
       ((mv erp tyname) (type-to-tyname type ienv))
       ((when erp) "<error>")
       (pstate (init-pristate (default-priopt) dialect))
       (pstate (print-tyname tyname pstate)))
    (acl2::nats=>string (rev (pristate->bytes-rev pstate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Scalar, void, and boolean types.

(acl2::assert-equal (render-type (type-void)) "void")
(acl2::assert-equal (render-type (type-char)) "char")
(acl2::assert-equal (render-type (type-schar)) "signed char")
(acl2::assert-equal (render-type (type-uchar)) "unsigned char")
(acl2::assert-equal (render-type (type-sshort)) "short int")
(acl2::assert-equal (render-type (type-ushort)) "unsigned short int")
(acl2::assert-equal (render-type (type-sint)) "int")
(acl2::assert-equal (render-type (type-uint)) "unsigned int")
(acl2::assert-equal (render-type (type-slong)) "long int")
(acl2::assert-equal (render-type (type-ulong)) "unsigned long int")
(acl2::assert-equal (render-type (type-sllong)) "long long int")
(acl2::assert-equal (render-type (type-ullong)) "unsigned long long int")
(acl2::assert-equal (render-type (type-float)) "float")
(acl2::assert-equal (render-type (type-double)) "double")
(acl2::assert-equal (render-type (type-ldouble)) "long double")
(acl2::assert-equal (render-type (type-floatc)) "float _Complex")
(acl2::assert-equal (render-type (type-doublec)) "double _Complex")
(acl2::assert-equal (render-type (type-ldoublec)) "long double _Complex")
(acl2::assert-equal (render-type (type-bool)) "_Bool")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Pointer and array types, including the precedence/parenthesization cases.

(acl2::assert-equal (render-type (make-type-pointer :to (type-sint)))
              "int *")

(acl2::assert-equal (render-type (make-type-pointer
                             :to (make-type-pointer :to (type-sint))))
              "int **")

(acl2::assert-equal (render-type (make-type-array :of (type-sint) :size 10))
              "int [10]")

;; An array of unknown size.
(acl2::assert-equal (render-type (make-type-array :of (type-sint) :size nil))
              "int []")

;; An array of pointers (no parentheses).
(acl2::assert-equal (render-type (make-type-array
                             :of (make-type-pointer :to (type-sint))
                             :size 3))
              "int *[3]")

;; A pointer to an array (parenthesized).
(acl2::assert-equal (render-type (make-type-pointer
                             :to (make-type-array :of (type-sint) :size 3)))
              "int (*)[3]")

;; A two-dimensional array (outer dimension first).
(acl2::assert-equal (render-type (make-type-array
                             :of (make-type-array :of (type-sint) :size 4)
                             :size 2))
              "int [2][4]")

;; A size larger than INT_MAX gets a length suffix
;; (2^32 fits in long for the default implementation environment).
(acl2::assert-equal (render-type (make-type-array :of (type-sint)
                                                  :size (expt 2 32)))
              "int [4294967296l]")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Structure and union types.

;; A tagged structure renders as just the tag.
(acl2::assert-equal (render-type (make-type-struct
                             :uid (uid 0)
                             :tunit? nil
                             :tag/members (type-struni-tag/members-tagged
                                            (ident "foo"))))
              "struct foo")

;; A tagged union renders as just the tag.
(acl2::assert-equal (render-type (make-type-union
                             :uid (uid 0)
                             :tunit? nil
                             :tag/members (type-struni-tag/members-tagged
                                            (ident "bar"))))
              "union bar")

;; A pointer to a tagged structure.
(acl2::assert-equal (render-type (make-type-pointer
                             :to (make-type-struct
                                   :uid (uid 0)
                                   :tunit? nil
                                   :tag/members (type-struni-tag/members-tagged
                                                  (ident "foo")))))
              "struct foo *")

;; An untagged structure reconstructs its members.
(acl2::assert-equal
  (render-type (make-type-struct
                 :uid (uid 0)
                 :tunit? nil
                 :tag/members
                 (type-struni-tag/members-untagged
                   (list (make-type-struni-member :name? (ident "x")
                                                  :type (type-sint))
                         (make-type-struni-member
                           :name? (ident "y")
                           :type (make-type-pointer :to (type-char)))))))
  "struct { int x; char *y; }")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Function types.

;; A function prototype with parameters.
(acl2::assert-equal (render-type (make-type-function
                             :ret (type-sint)
                             :params (make-type-params-prototype
                                       :params (list (type-sint)
                                                     (make-type-pointer
                                                       :to (type-char)))
                                       :ellipsis nil)))
              "int (int, char *)")

;; A prototype with no parameters is the (void) case.
(acl2::assert-equal (render-type (make-type-function
                             :ret (type-void)
                             :params (make-type-params-prototype
                                       :params nil
                                       :ellipsis nil)))
              "void (void)")

;; A variadic prototype.
(acl2::assert-equal (render-type (make-type-function
                             :ret (type-sint)
                             :params (make-type-params-prototype
                                       :params (list (type-sint))
                                       :ellipsis t)))
              "int (int, ...)")

;; An unspecified parameter list.
(acl2::assert-equal (render-type (make-type-function
                             :ret (type-sint)
                             :params (type-params-unspecified)))
              "int ()")

;; A pointer to a function (parenthesized).
(acl2::assert-equal (render-type (make-type-pointer
                             :to (make-type-function
                                   :ret (type-sint)
                                   :params (make-type-params-prototype
                                             :params (list (type-sint))
                                             :ellipsis nil))))
              "int (*)(int)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Types with no source-level representation yield an error.

(acl2::assert! (mv-let (erp tyname)
                 (type-to-tyname (type-enum) (ienv-default))
                 (declare (ignore tyname))
                 erp))

(acl2::assert! (mv-let (erp tyname)
                 (type-to-tyname (type-unknown) (ienv-default))
                 (declare (ignore tyname))
                 erp))

(acl2::assert! (mv-let (erp tyname)
                 (type-to-tyname (type-unknown-scalar) (ienv-default))
                 (declare (ignore tyname))
                 erp))

;; An unrepresentable type nested inside a representable one
;; propagates the error.

(acl2::assert! (mv-let (erp tyname)
                 (type-to-tyname (make-type-pointer :to (type-unknown))
                                 (ienv-default))
                 (declare (ignore tyname))
                 erp))

(acl2::assert! (mv-let (erp tyname)
                 (type-to-tyname (make-type-array :of (type-enum) :size 4)
                                 (ienv-default))
                 (declare (ignore tyname))
                 erp))
