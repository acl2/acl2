; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "std/util/defval" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "abstract-syntax-trees")

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
     "See the GCC manual, ``Built-in Functions Provided by GCC'' "
     (xdoc::ahref "https://gcc.gnu.org/onlinedocs/gcc/Built-in-Functions.html"
                  "[GCCM:7]")
     ".")
   (xdoc::p
     "Currently, we do not differentiate between GCC and Clang built-ins.
      If either GCC or Clang language extensions are enabled,
      we consider all the @(see gcc-builtins) to be defined
      for the purpose of validation.
      In the future, it may become necessary to differentiate
      the built-ins recognized by Clang as opposed to GCC."))
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
  (list (ident "__atomic_compare_exchange_n")
        (ident "__atomic_exchange_n")
        (ident "__atomic_fetch_add")
        (ident "__atomic_fetch_and")
        (ident "__atomic_fetch_or")
        (ident "__atomic_fetch_xor")
        (ident "__atomic_load_n")
        (ident "__atomic_signal_fence")
        (ident "__atomic_store_n")
        (ident "__atomic_thread_fence")
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
        (ident "__builtin_add_overflow_p")
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
        (ident "__builtin_copysign")
        (ident "__builtin_copysignf")
        (ident "__builtin_copysignf128")
        (ident "__builtin_copysignl")
        (ident "__builtin_ctz")
        (ident "__builtin_ctzl")
        (ident "__builtin_ctzll")
        (ident "__builtin_dynamic_object_size")
        (ident "__builtin_expect")
        (ident "__builtin_extract_return_addr")
        (ident "__builtin_fabs")
        (ident "__builtin_fabsf")
        (ident "__builtin_fabsf128")
        (ident "__builtin_fabsl")
        (ident "__builtin_fma")
        (ident "__builtin_fpclassify")
        (ident "__builtin_huge_val")
        (ident "__builtin_huge_valf")
        (ident "__builtin_huge_valf128")
        (ident "__builtin_huge_vall")
        (ident "__builtin_ia32_cvtpd2ps")
        (ident "__builtin_ia32_rdtsc")
        (ident "__builtin_inff")
        (ident "__builtin_isfinite")
        (ident "__builtin_isgreater")
        (ident "__builtin_isgreaterequal")
        (ident "__builtin_isinf_sign")
        (ident "__builtin_isless")
        (ident "__builtin_islessequal")
        (ident "__builtin_isnan")
        (ident "__builtin_memchr")
        (ident "__builtin_memcmp")
        (ident "__builtin_memcpy")
        (ident "__builtin_mempcpy")
        (ident "__builtin_memset")
        (ident "__builtin_mul_overflow")
        (ident "__builtin_nan")
        (ident "__builtin_nanf")
        (ident "__builtin_nanf128")
        (ident "__builtin_nanl")
        (ident "__builtin_object_size")
        (ident "__builtin_popcount")
        (ident "__builtin_popcountll")
        (ident "__builtin_return_address")
        (ident "__builtin_signbit")
        (ident "__builtin_signbitl")
        (ident "__builtin_sqrt")
        (ident "__builtin_sqrtf")
        (ident "__builtin_sqrtl")
        (ident "__builtin_stpcpy")
        (ident "__builtin_strcpy")
        (ident "__builtin_strlen")
        (ident "__builtin_strncat")
        (ident "__builtin_strncpy")
        (ident "__builtin_sub_overflow")
        (ident "__builtin_thread_pointer")
        (ident "__builtin_trap")
        (ident "__builtin_unreachable")
        (ident "__builtin_va_arg_pack")
        (ident "__builtin_va_arg_pack_len")
        (ident "__builtin_va_copy")
        (ident "__builtin_va_end")
        (ident "__builtin_va_start")
        (ident "__builtin_vacopy")
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
      "This list contains variables corresponding to certain x86 registers.
       We could not find mention of these variables in the GCC manual,
       but they have been observed in practical code.
       See @(tsee dimb-transunit) for further discussion of these variables.")
    (xdoc::p
      "We also include @('latent_entropy').
       This variable was observed in the preprocessed output
       of a kernel module
       This is presumably introduced by the ``latent entropy'' GCC plugin."))
  (list (ident "__eax")
        (ident "__ebp")
        (ident "__ebx")
        (ident "__ecx")
        (ident "__edi")
        (ident "__edx")
        (ident "__esi")
        (ident "__esp")
        (ident "latent_entropy"))
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
