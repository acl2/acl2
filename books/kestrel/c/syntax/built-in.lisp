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

(include-book "types")

(include-book "../language/implementation-environments/dialects")

(include-book "std/util/defval" :dir :system)

(local (include-book "std/typed-lists/string-listp" :dir :system))

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

(fty::defprod built-in-fun
  :short "Fixtype of information about a built-in function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of
     the name (an ACL2 string),
     the return type,
     and the parameter types."))
  ((name string)
   (ret type)
   (params type-params))
  :pred built-in-funp)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist built-in-fun-list
  :short "Fixtype of lists of information about built-in functions."
  :elt-type built-in-fun
  :true-listp t
  :elementp-of-nil nil
  :pred built-in-fun-listp)

;;;;;;;;;;

(std::defprojection built-in-fun-list->name ((x built-in-fun-listp))
  :returns (names string-listp)
  :short "Lift @(tsee built-in-fun->name) to lists."
  (built-in-fun->name x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod built-in-var
  :short "Fixtype of information about a built-in-variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of
     the name (an ACL2 string)
     and the type."))
  ((name string)
   (type type))
  :pred built-in-varp)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist built-in-var-list
  :short "Fixtype of lists of information about built-in variables."
  :elt-type built-in-var
  :true-listp t
  :elementp-of-nil nil
  :pred built-in-var-listp)

;;;;;;;;;;

(std::defprojection built-in-var-list->name ((x built-in-var-listp))
  :returns (names string-listp)
  :short "Lift @(tsee built-in-var->name) to lists."
  (built-in-var->name x))

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
  (list (built-in-fun "__atomic_compare_exchange_n"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__atomic_exchange_n"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__atomic_fetch_add"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__atomic_fetch_and"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__atomic_fetch_or"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__atomic_fetch_xor"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__atomic_load_n"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__atomic_signal_fence"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__atomic_store_n"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__atomic_thread_fence"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin___memcpy_chk"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin___memmove_chk"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin___mempcpy_chk"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin___memset_chk"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin___snprintf_chk"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin___sprintf_chk"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin___stpcpy_chk"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin___stpncpy_chk"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin___strcat_chk"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin___strcpy_chk"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin___strncat_chk"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin___strncpy_chk"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin___vsnprintf_chk"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin___vsprintf_chk"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_add_overflow"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_add_overflow_p"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_alloca"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_apply"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_apply_args"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_bswap16"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_bswap32"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_bswap64"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_choose_expr"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_clz"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_clzl"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_clzll"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_constant_p"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_copysign"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_copysignf"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_copysignf128"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_copysignl"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_ctz"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_ctzl"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_ctzll"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_dynamic_object_size"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_expect"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_extract_return_addr"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_fabs"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_fabsf"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_fabsf128"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_fabsl"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_fma"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_fpclassify"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_huge_val"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_huge_valf"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_huge_valf128"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_huge_vall"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_ia32_cvtpd2ps"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_ia32_rdtsc"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_inff"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_isfinite"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_isgreater"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_isgreaterequal"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_isinf_sign"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_isless"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_islessequal"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_isnan"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memchr"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcmp"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcpy"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_mempcpy"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memset"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_mul_overflow"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_nan"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_nanf"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_nanf128"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_nanl"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_object_size"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_popcount"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_popcountll"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_return_address"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_signbit"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_signbitl"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_sqrt"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_sqrtf"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_sqrtl"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_stpcpy"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_strcpy"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_strlen"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_strncat"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_strncpy"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_sub_overflow"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_thread_pointer"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_trap"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_unreachable"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_va_arg_pack"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_va_arg_pack_len"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_va_copy"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_va_end"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_va_start"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_vacopy"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__sync_add_and_fetch"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__sync_and_and_fetch"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__sync_bool_compare_and_swap"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__sync_fetch_and_add"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__sync_fetch_and_and"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__sync_fetch_and_nand"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__sync_fetch_and_or"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__sync_fetch_and_sub"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__sync_fetch_and_xor"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__sync_lock_release"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__sync_lock_test_and_set"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__sync_nand_and_fetch"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__sync_or_and_fetch"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__sync_sub_and_fetch"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__sync_synchronize"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__sync_val_compare_and_swap"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__sync_xor_and_fetch"
                      (type-unknown)
                      (type-params-unspecified)))
  ///
  (assert-event (built-in-fun-listp *gcc/clang-built-in-functions*))
  (assert-event (no-duplicatesp-equal
                 (built-in-fun-list->name *gcc/clang-built-in-functions*))))

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
  (list (built-in-var "__eax" (type-unknown))
        (built-in-var "__ebp" (type-unknown))
        (built-in-var "__ebx" (type-unknown))
        (built-in-var "__ecx" (type-unknown))
        (built-in-var "__edi" (type-unknown))
        (built-in-var "__edx" (type-unknown))
        (built-in-var "__esi" (type-unknown))
        (built-in-var "__esp" (type-unknown))
        (built-in-var "latent_entropy" (type-unknown)))
  ///
  (assert-event (built-in-var-listp *gcc/clang-built-in-vars*))
  (assert-event (no-duplicatesp-equal
                 (built-in-var-list->name *gcc/clang-built-in-vars*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *gcc/clang-built-in-fun/var-names*
  :short "A list of names of functions and variables built-in to GCC and Clang."
  (append (built-in-fun-list->name *gcc/clang-built-in-functions*)
          (built-in-var-list->name *gcc/clang-built-in-vars*))
  ///
  (assert-event (string-listp *gcc/clang-built-in-fun/var-names*))
  (assert-event (no-duplicatesp-equal *gcc/clang-built-in-fun/var-names*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *cheri-built-in-functions*
  :short "The list of functions built-in to CHERI."
  :long
  (xdoc::topstring-p
   "This list contains all functions listed in [CHERI:Table 4.2].")
  (list (built-in-fun "__builtin_memcap_length_set"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_length_get"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_bounds_set"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_base_increment"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_base_get"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_perms_and"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_perms_get"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_type_set"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_type_get"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_tag_get"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_sealed_get"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_tag_clear"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_seal"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_unseal"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_perms_check"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_type_check"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_offset_increment"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_offset_set"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_offset_get"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_program_counter_get"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_global_data_get"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_memcap_stack_get"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_cheri_cause.get"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_cheri_cause.set"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_cheri_invoke_data_cap_get"
                      (type-unknown)
                      (type-params-unspecified))
        ;; Note: this is listed twice in Table 4.2. Typo?
        (built-in-fun "__builtin_cheri_kernel_cap1_get"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_cheri_kernel_code_cap_get"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_cheri_kernel_data_cap_get"
                      (type-unknown)
                      (type-params-unspecified))
        (built-in-fun "__builtin_cheri_exception_program_counter_cap_get"
                      (type-unknown)
                      (type-params-unspecified)))
  ///
  (assert-event (built-in-fun-listp *cheri-built-in-functions*))
  (assert-event (no-duplicatesp-equal
                 (built-in-fun-list->name *cheri-built-in-functions*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *cheri-built-in-fun/var-names*
  :short "A list of functions and variables built-in to CHERI."
  (built-in-fun-list->name *cheri-built-in-functions*)
  ///
  (assert-event (string-listp *cheri-built-in-fun/var-names*))
  (assert-event (no-duplicatesp-equal *cheri-built-in-fun/var-names*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define built-in-functions-for ((dialect c::dialectp))
  :returns (built-ins built-in-fun-listp)
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
   (built-ins true-listp :rule-classes :type-prescription))

  (defret no-duplicatesp-equal-of-names-of-built-in-functions-for
    (no-duplicatesp-equal (built-in-fun-list->name built-ins))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define built-in-vars-for ((dialect c::dialectp))
  :returns (built-ins built-in-var-listp)
  :short "List of built-ins variables according to the C dialect."
  (if (c::dialect-gcc/clangp dialect)
      *gcc/clang-built-in-vars*
    nil)

  ///

  (more-returns
   (built-ins true-listp :rule-classes :type-prescription))

  (defret no-duplicatesp-equal-of-names-of-built-in-vars-for
    (no-duplicatesp-equal (built-in-var-list->name built-ins))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define built-in-fun/var-names-for ((dialect c::dialectp))
  :returns (built-ins string-listp)
  :short "List of built-ins according to the C dialect."
  (append (built-in-var-list->name (built-in-vars-for dialect))
          (built-in-fun-list->name (built-in-functions-for dialect)))

  ///

  (more-returns
   (built-ins true-listp :rule-classes :type-prescription)
   (built-ins no-duplicatesp-equal
              :hints (("Goal" :in-theory (enable built-in-vars-for
                                                 built-in-functions-for))))))
