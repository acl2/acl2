; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "implementation-environments/versions")

(include-book "std/util/defval" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ keywords
  :parents (language)
  :short "Keywords of C."
  :long
  (xdoc::topstring
   (xdoc::p
    "These depend on the "
    (xdoc::seetopic "versions" "C version")
    ", but they are all readily representable as ACL2 strings.")
   (xdoc::p
    "We introduce lists of ACL2 strings representing C keywords,
     parameterized over the C version."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *keywords-c17*
  :short "List of the C17 keywords [C17:6.4.1/1]."
  '("auto"
    "break"
    "case"
    "char"
    "const"
    "continue"
    "default"
    "do"
    "double"
    "else"
    "enum"
    "extern"
    "float"
    "for"
    "goto"
    "if"
    "inline"
    "int"
    "long"
    "register"
    "restrict"
    "return"
    "short"
    "signed"
    "sizeof"
    "static"
    "struct"
    "switch"
    "typedef"
    "union"
    "unsigned"
    "void"
    "volatile"
    "while"
    "_Alignas"
    "_Alignof"
    "_Atomic"
    "_Bool"
    "_Complex"
    "_Generic"
    "_Imaginary"
    "_Noreturn"
    "_Static_assert"
    "_Thread_local")
  ///
  (assert-event (string-listp *keywords-c17*))
  (assert-event (no-duplicatesp-equal *keywords-c17*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *keywords-c23*
  :short "List of C23 keywords [C23:6.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We include the alternative spellings
     listed in Table 6.1 of [C23]."))
  '("alignas" "_Alignas"
    "alignof" "_Alignof"
    "auto"
    "bool" "_Bool"
    "break"
    "case"
    "char"
    "const"
    "constexpr"
    "continue"
    "default"
    "do"
    "double"
    "else"
    "enum"
    "extern"
    "false"
    "float"
    "for"
    "goto"
    "if"
    "inline"
    "int"
    "long"
    "nullptr"
    "register"
    "restrict"
    "return"
    "short"
    "signed"
    "sizeof"
    "static"
    "static_assert" "_Static_assert"
    "struct"
    "switch"
    "thread_local" "_Thread_local"
    "true"
    "typedef"
    "typeof"
    "typeof_unqual"
    "union"
    "unsigned"
    "void"
    "volatile"
    "while"
    "_Atomic"
    "_BitInt"
    "_Complex"
    "_Decimal128"
    "_Decimal32"
    "_Decimal64"
    "_Generic"
    "_Imaginary"
    "_Noreturn"
   )
  ///
  (assert-event (string-listp *keywords-c23*))
  (assert-event (no-duplicatesp-equal *keywords-c23*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *keywords-gcc-c17*
  :short "List of the additional GCC keywords for C17 [GCCM]."
  :long
  (xdoc::topstring
   (xdoc::p
    "There seems to be no place, in the GCC documentation,
     that clearly lists these keywords, unlike the C standards.
     We gathered them based on GCC extensions we encountered in practical code;
     more may need to be added.")
   (xdoc::p
    "It is not even clear to us whether these should be actually keywords,
     as opposed to special identifiers somehow, but we treat them as keywords.")
   (xdoc::p
    "These are all disjoint from the standard keywords."))
  '("__alignof"
    "__alignof__"
    "asm"
    "__asm"
    "__asm__"
    "__attribute"
    "__attribute__"
    "__auto_type"
    "__builtin_offsetof"
    "__builtin_types_compatible_p"
    "__builtin_va_arg"
    "__builtin_va_list"
    "__declspec"
    "__extension__"
    "__float80"
    "__floar128"
    "_Float16"
    "_Float16x"
    "_Float32"
    "_Float32x"
    "_Float64"
    "_Float64x"
    "_Float128"
    "_Float128x"
    "__imag__"
    "__inline"
    "__inline__"
    "__int128"
    "__int128_t"
    "__label__"
    "__real__"
    "__restrict"
    "__restrict__"
    "__seg_fs"
    "__seg_gs"
    "__signed"
    "__signed__"
    "__stdcall"
    "__thread"
    "typeof"
    "__typeof"
    "__typeof__"
    "__volatile"
    "__volatile__")
  ///
  (assert-event (string-listp *keywords-gcc-c17*))
  (assert-event (no-duplicatesp-equal *keywords-gcc-c17*))
  (assert-event (not (intersectp-equal *keywords-gcc-c17* *keywords-c17*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *keywords-gcc-c23*
  :short "List of the additional GCC keywords for C23 [GCCM]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The same remarks made in @(tsee *keywords-gcc-c17*) apply here.")
   (xdoc::p
    "This is almost the same list as @(tsee *keywords-gcc-c17*),
     except that @('typeof') is absent here,
     because it is a standard keyword in C23."))
  '("__alignof"
    "__alignof__"
    "asm"
    "__asm"
    "__asm__"
    "__attribute"
    "__attribute__"
    "__auto_type"
    "__builtin_offsetof"
    "__builtin_types_compatible_p"
    "__builtin_va_arg"
    "__builtin_va_list"
    "__declspec"
    "__extension__"
    "__float80"
    "__floar128"
    "_Float16"
    "_Float16x"
    "_Float32"
    "_Float32x"
    "_Float64"
    "_Float64x"
    "_Float128"
    "_Float128x"
    "__imag__"
    "__inline"
    "__inline__"
    "__int128"
    "__int128_t"
    "__label__"
    "__real__"
    "__restrict"
    "__restrict__"
    "__seg_fs"
    "__seg_gs"
    "__signed"
    "__signed__"
    "__stdcall"
    "__thread"
    "__typeof"
    "__typeof__"
    "__volatile"
    "__volatile__")
  ///
  (assert-event (string-listp *keywords-gcc-c23*))
  (assert-event (no-duplicatesp-equal *keywords-gcc-c23*))
  (assert-event (not (intersectp-equal *keywords-gcc-c23* *keywords-c23*)))
  (assert-event (subsetp-equal *keywords-gcc-c23* *keywords-gcc-c17*))
  (assert-event (equal
                 (set-difference-equal *keywords-gcc-c17* *keywords-gcc-c23*)
                 (list "typeof"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define keywords ((version versionp))
  :returns (list string-listp)
  :short "List of keywords according to the C version."
  (version-case
   version
   :c17 *keywords-c17*
   :c17+gcc (append *keywords-c17* *keywords-gcc-c17*)
   :c23 *keywords-c23*
   :c23+gcc (append *keywords-c23* *keywords-gcc-c23*))
  :hooks (:fix)

  ///

  (more-returns
   (list no-duplicatesp-equal)))
