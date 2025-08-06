; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "std/util/defval" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "abstract-syntax")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ gcc-builtins
  :parents (syntax-for-tools)
  :short "Constants for identifiers ``built-in'' to GCC C."
  :long
  (xdoc::topstring
   (xdoc::p
     "These constants enumerate a subset of the built-in functions and
      variables implicitly defined in GCC C.
      New values are generally added on demand as they are encountered in real
      code.")
   (xdoc::p
     "See the GCC manual, "
     (xdoc::ahref "https://gcc.gnu.org/onlinedocs/gcc/Built-in-Functions.html"
                  "``Built-in Functions Provided by GCC''")
     "."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *gcc-builtin-functions*
  :parents (*gcc-builtin*)
  :short "A partial list of functions built-in to GCC."
  :long
  (xdoc::topstring
    (xdoc::p
      "Some of the functions here do not seem to be documented in the GCC
       manual, but have been observed in real-world code accepted by GCC.
       In particular, the built-ins ending in @('\"_chk\"'),
       which were observed in glibc."))
  (list (ident "__atomic_signal_fence")
        (ident "__builtin___memcpy_chk")
        (ident "__builtin___memmove_chk")
        (ident "__builtin___mempcpy_chk")
        (ident "__builtin___memset_chk")
        (ident "__builtin___snprintf_chk")
        (ident "__builtin___sprintf_chk")
        (ident "__builtin___stpcpy_chk")
        (ident "__builtin___stpncpy_chk")
        (ident "__builtin___strcat_chk")
        (ident "__builtin___strcpy_chk")
        (ident "__builtin___strncat_chk")
        (ident "__builtin___strncpy_chk")
        (ident "__builtin___vsnprintf_chk")
        (ident "__builtin___vsprintf_chk")
        (ident "__builtin_add_overflow")
        (ident "__builtin_alloca")
        (ident "__builtin_apply")
        (ident "__builtin_apply_args")
        (ident "__builtin_bswap16")
        (ident "__builtin_bswap32")
        (ident "__builtin_bswap64")
        (ident "__builtin_choose_expr")
        (ident "__builtin_clz")
        (ident "__builtin_clzl")
        (ident "__builtin_clzll")
        (ident "__builtin_constant_p")
        (ident "__builtin_ctzl")
        (ident "__builtin_dynamic_object_size")
        (ident "__builtin_expect")
        (ident "__builtin_memchr")
        (ident "__builtin_memcmp")
        (ident "__builtin_memcpy")
        (ident "__builtin_memset")
        (ident "__builtin_mul_overflow")
        (ident "__builtin_object_size")
        (ident "__builtin_return_address")
        (ident "__builtin_strcpy")
        (ident "__builtin_strlen")
        (ident "__builtin_strncat")
        (ident "__builtin_strncpy")
        (ident "__builtin_sub_overflow")
        (ident "__builtin_unreachable")
        (ident "__builtin_va_arg_pack")
        (ident "__builtin_va_arg_pack_len")
        (ident "__builtin_va_end")
        (ident "__builtin_va_start")
        (ident "__sync_add_and_fetch")
        (ident "__sync_and_and_fetch")
        (ident "__sync_bool_compare_and_swap")
        (ident "__sync_fetch_and_add")
        (ident "__sync_fetch_and_and")
        (ident "__sync_fetch_and_nand")
        (ident "__sync_fetch_and_or")
        (ident "__sync_fetch_and_sub")
        (ident "__sync_fetch_and_xor")
        (ident "__sync_lock_release")
        (ident "__sync_lock_test_and_set")
        (ident "__sync_nand_and_fetch")
        (ident "__sync_or_and_fetch")
        (ident "__sync_sub_and_fetch")
        (ident "__sync_synchronize")
        (ident "__sync_val_compare_and_swap")
        (ident "__sync_xor_and_fetch"))
  ///
  (assert-event (ident-listp *gcc-builtin-functions*))
  (assert-event (no-duplicatesp-equal *gcc-builtin-functions*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *gcc-builtin-vars*
  :parents (*gcc-builtin*)
  :short "A partial list of variables built-in to GCC."
  :long
  (xdoc::topstring
    (xdoc::p
      "This list consists of variables corresponding to certain x86 registers.
       We could not find mention of these variables in the GCC manual,
       but they have been observed in practical code.")
    (xdoc::p
      "See @(tsee dimb-transunit) for further discussion of these variables."))
  (list (ident "__eax")
        (ident "__ebp")
        (ident "__ebx")
        (ident "__ecx")
        (ident "__edi")
        (ident "__edx")
        (ident "__esi")
        (ident "__esp"))
  ///
  (assert-event (ident-listp *gcc-builtin-vars*))
  (assert-event (no-duplicatesp-equal *gcc-builtin-vars*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *gcc-builtin*
  :short "A list of identifiers built-in to GCC."
  (append *gcc-builtin-functions*
          *gcc-builtin-vars*)
  ///
  (assert-event (ident-listp *gcc-builtin*))
  (assert-event (no-duplicatesp-equal *gcc-builtin*)))
