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
(c::def-array-support c::ullong)
(c::def-array-support c::ulong)
(c::def-array-support c::uint)
(c::def-array-support c::ushort)
(c::def-array-support c::uchar)

(c::def-array-support c::sllong)
(c::def-array-support c::slong)
(c::def-array-support c::sint)
(c::def-array-support c::sshort)
(c::def-array-support c::schar)

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
  (c::ullong-integerp (c::integer-from-ulong x))
  :hints (("Goal"
           :in-theory (enable c::integer-from-ullong
                              c::ulong-integerp
                              unsigned-byte-p
                              c::long-bits
                              c::ullong-integer-fix
                              c::ullong-integerp
                              c::llong-bits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftheory c-intro-rules
    (acl2::union-theories* ;; (theory 'uchar-intro-rules)
     (theory 'c::ushort-intro-rules)
     (theory 'c::uint-intro-rules)
     (theory 'c::ulong-intro-rules)
     (theory 'c::ullong-intro-rules)
     ;; (theory 'c::schar-intro-rules)
     ;; (theory 'c::sshort-intro-rules)
     (theory 'c::sint-intro-rules)
     ;; (theory 'c::slong-intro-rules)
     ;; (theory 'sllong-intro-rules)
     (theory 'c::uchar-array-intro-rules) ; todo: more
     (theory 'c::sint-array-intro-rules)
     )
  :redundant-okp t)

;; Temporary alias, to be deprecated.
(deftheory acl2::c-intro-rules
    (theory 'c-intro-rules)
  :redundant-okp t)

(deftheory c-array-removal-rules
  '(c::uchar-array-index-okp ; these expose c::integer-from-cinteger, but we have enabled rules for that
    c::ushort-array-index-okp
    c::uint-array-index-okp
    c::ulong-array-index-okp
    c::ullong-array-index-okp
    c::schar-array-index-okp
    c::sshort-array-index-okp
    c::sint-array-index-okp
    c::slong-array-index-okp
    c::sllong-array-index-okp

    ;; We'll open the XXX-array-length functions because doing so exposes the
    ;; XXX-array->elements functions, which we often appear without the
    ;; surrounding calls of len.
    c::uchar-array-length
    c::ushort-array-length
    c::uint-array-length
    c::ulong-array-length
    c::ullong-array-length
    c::schar-array-length
    c::sshort-array-length
    c::sint-array-length
    c::slong-array-length
    c::sllong-array-length))

;; todo: add more
(deftheory mixed-scalar-rules
  '(c::sint-from-uchar-okp))

(deftheory c-removal-rules
    (acl2::union-theories* (theory 'c-array-removal-rules)
                           (theory 'mixed-scalar-rules)
                           (theory 'c::uchar-removal-rules)
                           (theory 'c::ushort-removal-rules)
                           (theory 'c::uint-removal-rules)
                           (theory 'c::ulong-removal-rules)
                           (theory 'c::ullong-removal-rules)
                           (theory 'c::schar-removal-rules)
                           (theory 'c::sshort-removal-rules)
                           (theory 'c::sint-removal-rules)
                           (theory 'c::slong-removal-rules)
                           (theory 'c::sllong-removal-rules))
  :redundant-okp t)

;; Temporary alias, to be deprecated.
(deftheory acl2::c-removal-rules
    (theory 'c-removal-rules)
  :redundant-okp t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Because c::uint-array-length is just an alias for len of the elements
;; TODO: More of these -- add to def-array-support?
;; TODO: Should this be a linear rule?  Well, it might be good to have it in the type-alist.
;; Real question is why are we seeing both equivalent formulations?  Just enable c::uint-array-length?
(defthm uint-array-length-def-forward
  (equal (c::uint-array-length array)
         (len (c::uint-array->elements array)))
  :rule-classes ((:forward-chaining :trigger-terms ((c::uint-array-length array))))
  :hints (("Goal" :in-theory (enable c::uint-array-length))))
