; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../language/keywords")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ keywords
  :parents (concrete-syntax)
  :short "Keywords of C, with and without GCC extensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The language formalization defines a constant with the "
    (xdoc::seetopic "c::keywords" "standard C keywords")
    ". Here we include that constant,
     and we also introduce a constant for
     the GCC keywords in the ABNF grammar.")
   (xdoc::p
    "At some point we should probably extend the language formalization
     with (optional) GCC extensions,
     and move this constant for GCC keywords there."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *gcc-keywords*
  :short "List of the GCC keywords, as ACL2 strings."
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
    "_Float32"
    "_Float32x"
    "_Float64"
    "_Float64x"
    "_Float128"
    "_Float128x"
    "__inline"
    "__inline__"
    "__int128"
    "__int128_t"
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
  (assert-event (string-listp *gcc-keywords*))
  (assert-event (no-duplicatesp-equal *gcc-keywords*)))
