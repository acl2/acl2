; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)
; Contributing Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "std/util/defval" :dir :system)

(include-book "../language/implementation-environments/dialects")

(include-book "abstract-syntax-trees")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ built-ins
  :parents (syntax-for-tools)
  :short "Built-in functions and objects in C dialects."
  :long
  (xdoc::topstring
   (xdoc::p
     "Compilers implementing an extended dialect of C often provide
      a variety of ``built-in'' functions and objects.
      Such functions and objects may be used despite never being declared.
      Therefore, some information about built-ins must be hard-coded
      in order to "
     (xdoc::seetopic "disambiguation" "disambiguate")
     " and "
     (xdoc::seetopic "validation" "validate")
     " C programs written in those dialects.")
   (xdoc::p
     "Currently, the only information we track about built-ins
      is the identifier and whether it is a function or an object.
      Eventually, we may wish to add more information,
      such as the precise type of each built-in."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *gcc/clang-built-in-functions*
  :parents (*gcc/clang-built-in*)
  :short "A partial list of functions built-in to GCC and Clang."
  :long
  (xdoc::topstring
    (xdoc::p
     "This list is likely incomplete.
      New built-ins are generally added on demand
      as they are encountered in real programs.")
    (xdoc::p
     "Many built-in functions are documented in the GCC manual "
     (xdoc::ahref "https://gcc.gnu.org/onlinedocs/gcc/Built-in-Functions.html"
                  "[GCCM:7]")
     ". Some built-ins do not seem to be documented,
      but are nonetheless added after having been observed
      in real-world code accepted by GCC.
      In particular, the built-ins ending in @('\"_chk\"')
      were all observed in glibc.")
    (xdoc::p
     "Some of these built-ins are also documented in [CLE],
      but in any case Clang generally follows GCC.
      We have not yet observed cases in which they differ."))
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
  (assert-event (ident-listp *gcc/clang-built-in-functions*))
  (assert-event (no-duplicatesp-equal *gcc/clang-built-in-functions*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *gcc/clang-built-in-vars*
  :parents (*gcc/clang-built-in*)
  :short "A partial list of variables built-in to GCC and Clang."
  :long
  (xdoc::topstring
   (xdoc::p
    "This list is likely incomplete.
     New built-ins are generally added on demand
     as they are encountered in real programs.")
   (xdoc::p
    "This list contains variables corresponding to certain x86 registers.
     We could not find mention of these variables in [GCCM],
     but they have been observed in practical code.
     Experiments suggest that these variables are somewhat restricted in usage.
     The normal pattern seems to be something like")
   (xdoc::codeblock
    "unsigned long __eax = __eax;")
   (xdoc::p
    "after which one can use @('__eax') as a regular variable.
     However, without the declaration above,
     @('__eax') cannot be used as a regular variable.
     This is odd, because the validity of the declaration above
     presupposes that @('__eax') is already in scope.
     It is not clear why such a declaration is needed in the first place.
     To add to the strangeness,
     one can change the above initializer to @('__eax + 1')
     (and presumably other similar expressions)
     and the compiler accepts it.
     Nonetheless, we need to regard these as built-in variables.
     These variables only make sense on an x86 platform:
     we should refine our implementation environments with
     a richer description of the C implementation.")
   (xdoc::p
    "We also include @('latent_entropy').
     This variable was observed in the preprocessed output
     of a kernel module
     This is presumably introduced by the ``latent entropy'' GCC plugin.")
   (xdoc::p
    "Similarly to built-in functions,
     we regard this list as also being built-in to Clang.
     This may need revision at some point."))
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
  (assert-event (ident-listp *gcc/clang-built-in-vars*))
  (assert-event (no-duplicatesp-equal *gcc/clang-built-in-vars*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *gcc/clang-built-in*
  :short "A list of functions and variables built-in to GCC and Clang."
  (append *gcc/clang-built-in-functions*
          *gcc/clang-built-in-vars*)
  ///
  (assert-event (ident-listp *gcc/clang-built-in*))
  (assert-event (no-duplicatesp-equal *gcc/clang-built-in*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *cheri-built-in-functions*
  :short "The list of functions built-in to CHERI."
  :long
  (xdoc::topstring-p
    "This list contains all functions listed in [CHERI:Table 4.2].")
  (list (ident "__builtin_memcap_length_set")
        (ident "__builtin_memcap_length_get")
        (ident "__builtin_memcap_bounds_set")
        (ident "__builtin_memcap_base_increment")
        (ident "__builtin_memcap_base_get")
        (ident "__builtin_memcap_perms_and")
        (ident "__builtin_memcap_perms_get")
        (ident "__builtin_memcap_type_set")
        (ident "__builtin_memcap_type_get")
        (ident "__builtin_memcap_tag_get")
        (ident "__builtin_memcap_sealed_get")
        (ident "__builtin_memcap_tag_clear")
        (ident "__builtin_memcap_seal")
        (ident "__builtin_memcap_unseal")
        (ident "__builtin_memcap_perms_check")
        (ident "__builtin_memcap_type_check")
        (ident "__builtin_memcap_offset_increment")
        (ident "__builtin_memcap_offset_set")
        (ident "__builtin_memcap_offset_get")
        (ident "__builtin_memcap_program_counter_get")
        (ident "__builtin_memcap_global_data_get")
        (ident "__builtin_memcap_stack_get")
        (ident "__builtin_cheri_cause.get")
        (ident "__builtin_cheri_cause.set")
        (ident "__builtin_cheri_invoke_data_cap_get")
        ;; Note: this is listed twice in Table 4.2. Typo?
        (ident "__builtin_cheri_kernel_cap1_get")
        (ident "__builtin_cheri_kernel_code_cap_get")
        (ident "__builtin_cheri_kernel_data_cap_get")
        (ident "__builtin_cheri_exception_program_counter_cap_get"))
  ///
  (assert-event (ident-listp *cheri-built-in-functions*))
  (assert-event (no-duplicatesp-equal *cheri-built-in-functions*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *cheri-built-in*
  :short "A list of functions and variables built-in to CHERI."
  *cheri-built-in-functions*
  ///
  (assert-event (ident-listp *cheri-built-in*))
  (assert-event (no-duplicatesp-equal *cheri-built-in*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define built-in-functions-for ((dialect c::dialectp))
  :returns (built-ins ident-listp)
  :short "List of built-ins functions according to the C dialect."
  (b* (((c::dialect dialect) dialect)
       (gcc/clang-built-ins (if (or dialect.gcc dialect.clang)
                                *gcc/clang-built-in-functions*
                              nil)))
    (if dialect.cheri
        (append *cheri-built-in-functions* gcc/clang-built-ins)
      gcc/clang-built-ins))

  ///
  (more-returns
   (built-ins true-listp :rule-classes :type-prescription)
   (built-ins no-duplicatesp-equal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define built-in-vars-for ((dialect c::dialectp))
  :returns (built-ins ident-listp)
  :short "List of built-ins variables according to the C dialect."
  (if (c::dialect-gcc/clangp dialect)
      *gcc/clang-built-in-vars*
    nil)

  ///
  (more-returns
   (built-ins true-listp :rule-classes :type-prescription)
   (built-ins no-duplicatesp-equal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define built-ins-for ((dialect c::dialectp))
  :returns (built-ins ident-listp)
  :short "List of built-ins according to the C dialect."
  (append (built-in-vars-for dialect)
          (built-in-functions-for dialect))

  ///
  (more-returns
   (built-ins true-listp :rule-classes :type-prescription)
   (built-ins no-duplicatesp-equal
              :hints (("Goal" :in-theory (enable built-in-vars-for
                                                 built-in-functions-for))))))
