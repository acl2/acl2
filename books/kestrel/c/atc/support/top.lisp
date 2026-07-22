; C support for scalar types
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

;; TODO: Flesh out missing parts below

(include-book "uchar")
(include-book "ushort")
(include-book "uint")
(include-book "ulong")
(include-book "ullong")
(include-book "schar")
(include-book "sshort")
(include-book "sint")
(include-book "slong")
(include-book "sllong")
(include-book "def-array-support")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reverse order by size, so that rules about smaller types will be tried first
;; (e.g., for the strong replacement rules)
(def-array-support ullong)
(def-array-support ulong)
(def-array-support uint)
(def-array-support ushort)
(def-array-support uchar)

(def-array-support sllong)
(def-array-support slong)
(def-array-support sint)
(def-array-support sshort)
(def-array-support schar)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Move this (or make union-theories nary):

(defun acl2::union-theories*-fn (items)
  (declare (xargs :guard (true-listp items)))
  (if (endp items)
      nil
    (if (endp (rest items))
        (first items)
      `(union-theories ,(first items)
                       ,(acl2::union-theories*-fn (rest items))))))

;; Expands to a nest of binary union-theories calls over the ITEMS.
(defmacro acl2::union-theories* (&rest items)
  (acl2::union-theories*-fn items))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules mixing scalar types

;;todo: more like this
(defthmd ullong-integerp-integer-from-ulong
  (ullong-integerp (integer-from-ulong x))
  :hints (("Goal"
           :in-theory (enable integer-from-ullong
                              ulong-integerp
                              unsigned-byte-p
                              long-bits
                              ullong-integer-fix
                              ullong-integerp
                              llong-bits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftheory c-intro-rules
    (acl2::union-theories* (theory 'uchar-intro-rules)
                           (theory 'ushort-intro-rules)
                           (theory 'uint-intro-rules)
                           (theory 'ulong-intro-rules)
                           (theory 'ullong-intro-rules)
                           (theory 'schar-intro-rules)
                           (theory 'sshort-intro-rules)
                           (theory 'sint-intro-rules)
                           (theory 'slong-intro-rules)
                           (theory 'sllong-intro-rules)
                           (theory 'uchar-array-intro-rules)
                           (theory 'sint-array-intro-rules))
  :redundant-okp t)

;; Temporary alias, to be deprecated.
(deftheory acl2::c-intro-rules
    (theory 'c-intro-rules)
  :redundant-okp t)

(deftheory c-array-removal-rules
  '(uchar-array-index-okp ; these expose integer-from-cinteger, but we have enabled rules for that
    ushort-array-index-okp
    uint-array-index-okp
    ulong-array-index-okp
    ullong-array-index-okp
    schar-array-index-okp
    sshort-array-index-okp
    sint-array-index-okp
    slong-array-index-okp
    sllong-array-index-okp

    ;; We'll open the XXX-array-length functions because doing so exposes the
    ;; XXX-array->elements functions, which we often appear without the
    ;; surrounding calls of len.
    uchar-array-length
    ushort-array-length
    uint-array-length
    ulong-array-length
    ullong-array-length
    schar-array-length
    sshort-array-length
    sint-array-length
    slong-array-length
    sllong-array-length))

;; todo: add more
(deftheory mixed-scalar-rules
  '(sint-from-uchar-okp))

(deftheory c-removal-rules
    (acl2::union-theories* (theory 'c-array-removal-rules)
                           (theory 'mixed-scalar-rules)
                           (theory 'uchar-removal-rules)
                           (theory 'ushort-removal-rules)
                           (theory 'uint-removal-rules)
                           (theory 'ulong-removal-rules)
                           (theory 'ullong-removal-rules)
                           (theory 'schar-removal-rules)
                           (theory 'sshort-removal-rules)
                           (theory 'sint-removal-rules)
                           (theory 'slong-removal-rules)
                           (theory 'sllong-removal-rules))
  :redundant-okp t)

;; Temporary alias, to be deprecated.
(deftheory acl2::c-removal-rules
    (theory 'c-removal-rules)
  :redundant-okp t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Because uint-array-length is just an alias for len of the elements
;; TODO: More of these -- add to def-array-support.
;; TODO: Should this be a linear rule?
(defthm uint-array-length-def-forward
  (equal (uint-array-length array)
         (len (uint-array->elements array)))
  :rule-classes ((:forward-chaining :trigger-terms ((uint-array-length array))))
  :hints (("Goal" :in-theory (enable uint-array-length))))
