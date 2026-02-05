; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../language/implementation-environments/top")

(include-book "std/util/defirrelevant" :dir :system)

(local (include-book "arithmetic/top" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ implementation-environments
  :parents (syntax-for-tools)
  :short "Implementation environments for the C syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are similar to the "
    (xdoc::seetopic "c::implementation-environments"
                    "implementation environments")
    " that are part of our C language formalization,
     but they are simpler and meant for efficient execution.
     The implementation environments in the language formalization
     are richer, and meant for specification;
     in particular, in the future they may include data
     that may be inefficient to construct in execution.")
   (xdoc::p
    "We provide a mapping from these simplified implementation environments
     to the more complex ones in the language formalization.
     We also prove that
     the operations on implementation environments defined here
     are consistent with
     the corresponding operations in the language formalization,
     according to the aforementioned mapping.")
   (xdoc::p
    "The implementation environments we define here
     parameterize some aspects of our "
    (xdoc::seetopic "syntax-for-tools" "C syntax for use by tools")
    "."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ienv
  :short "Fixtype of implementation environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "We include an indication of the version of C; see @(tsee c::version).
     Currently we mainly support C17,
     with and without GCC and Clang extensions,
     but we are starting to adding some support for C23 as well.")
   (xdoc::p
    "We assume that bytes are 8 bits,
     that signed integers use two's complement,
     and that there are no padding bits or trap representations
     (except for @('_Bool')s, which are padded to at least one byte).
     Therefore, the characteristics of the integer types
     are defined by five numbers,
     i.e. the numbers of bytes of @('_Bool'), and (signed and unsigned)
     @('short'), @('int'), @('long'), and @('long long');
     constraints on those number are derived from
     [C17:5.2.4.2.1] (for the minima)
     and [C17:6.2.5/8] (for the increasing sizes).")
   (xdoc::p
    "The floating types are characterized by their sizes.
     We make no assumptions about their respective sizes for now.")
   (xdoc::p
    "We include a field for the size of pointers.
     We assume that all pointers are the same size.
     This is a safe assumption on most modern systems,
     but it is not true for certain older architectures
     and embedded platforms.")
   (xdoc::p
    "We also need a flag saying whether the plain @('char') type
     has the same range as @('signed char') or not [C17:6.2.5/15].
     If the flag is false, it has the same range as @('unsigned char').")
   (xdoc::p
    "This type will likely be expanded in the future
     to include further information about the environment.
     This may include details about standard library types
     (such as @('size_t'), @('ptrdiff_t'), etc.),
     alignment and padding policies,
     endianness,
     and so on."))
  ((version c::version)
   (bool-bytes pos)
   (short-bytes pos
                :reqfix (if (and (<= short-bytes int-bytes)
                                 (<= int-bytes long-bytes)
                                 (<= long-bytes llong-bytes)
                                 (<= 2 short-bytes)
                                 (<= 2 int-bytes)
                                 (<= 4 long-bytes)
                                 (<= 8 llong-bytes))
                            short-bytes
                          2))
   (int-bytes pos
              :reqfix (if (and (<= short-bytes int-bytes)
                               (<= int-bytes long-bytes)
                               (<= long-bytes llong-bytes)
                               (<= 2 short-bytes)
                               (<= 2 int-bytes)
                               (<= 4 long-bytes)
                               (<= 8 llong-bytes))
                          int-bytes
                        2))
   (long-bytes pos
               :reqfix (if (and (<= short-bytes int-bytes)
                                (<= int-bytes long-bytes)
                                (<= long-bytes llong-bytes)
                                (<= 2 short-bytes)
                                (<= 2 int-bytes)
                                (<= 4 long-bytes)
                                (<= 8 llong-bytes))
                           long-bytes
                         4))
   (llong-bytes pos
                :reqfix (if (and (<= short-bytes int-bytes)
                                 (<= int-bytes long-bytes)
                                 (<= long-bytes llong-bytes)
                                 (<= 2 short-bytes)
                                 (<= 2 int-bytes)
                                 (<= 4 long-bytes)
                                 (<= 8 llong-bytes))
                            llong-bytes
                          8))
   (float-bytes pos)
   (double-bytes pos)
   (ldouble-bytes pos)
   (pointer-bytes pos)
   (plain-char-signedp bool))
  :require (and (<= short-bytes int-bytes)
                (<= int-bytes long-bytes)
                (<= long-bytes llong-bytes)
                (<= 2 short-bytes)
                (<= 2 int-bytes)
                (<= 4 long-bytes)
                (<= 8 llong-bytes))
  :pred ienvp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-ienv
  :short "An irrelevant implementation environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This has no particular significance,
     but we set all the byte sizes to their minima,
     and the plain @('char') flag to @('nil') (i.e. unsigned);
     we also disable GCC extensions.")
   (xdoc::p
    "This can be used as a dummy value of the type."))
  :type ienvp
  :body (make-ienv :version (c::irr-version)
                   :bool-bytes 1
                   :short-bytes 2
                   :int-bytes 2
                   :long-bytes 4
                   :llong-bytes 8
                   :float-bytes 1
                   :double-bytes 1
                   :ldouble-bytes 1
                   :pointer-bytes 1
                   :plain-char-signedp nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ldm-ienv ((ienv ienvp))
  :returns (ienv1 c::ienvp)
  :short "Map an implementation environment of type @(tsee ienv)
          to one in the language formalization of type @(tsee c::ienv)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('ldm') part of this function's name
     is related to the one used for the functions in
     @(see mapping-to-language-definition),
     since we are mapping from the C syntax for tools
     to the formal language definition.")
   (xdoc::p
    "Given our assumptions (stated in @(tsee ienv))
     that bytes are 8 bits,
     that signed integers are two's complement,
     and that there are no padding bits and no trap representations,
     this mapping could still be defined in different ways,
     based on the exact choice of bit layouts,
     which is captured in @(tsee c::ienv) but not in @(tsee ienv).
     We pick a simple layout, already defined in the language formalization,
     consisting of increasing bit values,
     ended by the sign bit for signed integers.
     The exact choice of bit layout does not matter,
     since the main purpose of the mapping is to exhibit a correspondence."))
  (b* (((ienv ienv) ienv)
       (uchar-format (c::uchar-format-8))
       (schar-format (c::schar-format-8tcnt))
       (char-format (c::char-format ienv.plain-char-signedp))
       (short-format (c::integer-format-inc-sign-tcnpnt (* 8 ienv.short-bytes)))
       (int-format (c::integer-format-inc-sign-tcnpnt (* 8 ienv.int-bytes)))
       (long-format (c::integer-format-inc-sign-tcnpnt (* 8 ienv.long-bytes)))
       (llong-format (c::integer-format-inc-sign-tcnpnt (* 8 ienv.llong-bytes)))
       (bool-format (c::bool-format-lsb))
       (char+short+int+long+llong+bool-format
        (c::char+short+int+long+llong+bool-format uchar-format
                                                  schar-format
                                                  char-format
                                                  short-format
                                                  int-format
                                                  long-format
                                                  llong-format
                                                  bool-format)))
    (c::make-ienv
     :version ienv.version
     :char+short+int+long+llong+bool-format
     char+short+int+long+llong+bool-format))
  :guard-hints (("Goal" :in-theory (enable ldm-ienv-wfp-lemma)))

  :prepwork
  ((defruled ldm-ienv-wfp-lemma
     (c::char+short+int+long+llong+bool-format-wfp
      (c::char+short+int+long+llong+bool-format
       '((c::size . 8))
       '((c::signed :twos-complement) (c::trap))
       char-format
       (c::integer-format-inc-sign-tcnpnt (* 8 (ienv->short-bytes ienv)))
       (c::integer-format-inc-sign-tcnpnt (* 8 (ienv->int-bytes ienv)))
       (c::integer-format-inc-sign-tcnpnt (* 8 (ienv->long-bytes ienv)))
       (c::integer-format-inc-sign-tcnpnt (* 8 (ienv->llong-bytes ienv)))
       '((byte-size . 1) (c::value-index . 0) (c::trap))))
     :use (:instance ienv-requirements (x ienv))
     :enable (c::char+short+int+long+llong+bool-format-wfp
              c::integer-format-short-wfp-of-integer-format-inc-sign-tcnpnt
              c::integer-format-int-wfp-of-integer-format-inc-sign-tcnpnt
              c::integer-format-long-wfp-of-integer-format-inc-sign-tcnpnt
              c::integer-format-llong-wfp-of-integer-format-inc-sign-tcnpnt
              c::bool-format-wfp
              fix)
     :disable ienv-requirements)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->integer-max-bytes ((ienv ienvp))
  :returns (bytes posp :rule-classes (:rewrite :type-prescription))
  :short "Number of bytes of the largest integer types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the number of bytes of
     the @('intmax_t') and @('uintmax_t') types [C17:7.20.1.5].
     Currently this is the same number of bytes as
     the @('long long') and @('unsigned long long') types,
     which are the largest integer types that we support."))
  (ienv->llong-bytes ienv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->uchar-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('UCHAR_MAX') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Although this currently does not depend on the implementation environment,
     we make that an input to this function for uniformity and extensibility."))
  (declare (ignore ienv))
  255
  :type-prescription (and (posp (ienv->uchar-max ienv))
                          (> (ienv->uchar-max ienv) 1))

  ///

  (defruled ienv->uchar-max-correct
    (equal (ienv->uchar-max ienv)
           (c::ienv->uchar-max (ldm-ienv ienv)))
    :enable (ldm-ienv
             c::ienv->uchar-max)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->schar-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('SCHAR_MAX') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Although this currently does not depend on the implementation environment,
     we make that an input to this function for uniformity and extensibility."))
  (declare (ignore ienv))
  127
  :type-prescription (and (posp (ienv->schar-max ienv))
                          (> (ienv->schar-max ienv) 1))

  ///

  (defruled ienv->schar-max-correct
    (equal (ienv->schar-max ienv)
           (c::ienv->schar-max (ldm-ienv ienv)))
    :enable (ldm-ienv
             c::ienv->schar-max)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->schar-min ((ienv ienvp))
  :returns (min integerp)
  :short "The ACL2 integer value of @('SCHAR_MIN') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Although this currently does not depend on the implementation environment,
     we make that an input to this function for uniformity and extensibility."))
  (declare (ignore ienv))
  -128
  :type-prescription (integerp (ienv->schar-min ienv))

  ///

  (defruled ienv->schar-min-correct
    (equal (ienv->schar-min ienv)
           (c::ienv->schar-min (ldm-ienv ienv)))
    :enable (ldm-ienv
             c::ienv->schar-min)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->char-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('CHAR_MAX') [C17:5.2.4.2.1/1]."
  (if (ienv->plain-char-signedp ienv)
      127
    255)
  :type-prescription (and (posp (ienv->char-max ienv))
                          (> (ienv->char-max ienv) 1))

  ///

  (defruled ienv->char-max-correct
    (equal (ienv->char-max ienv)
           (c::ienv->char-max (ldm-ienv ienv)))
    :enable (ldm-ienv
             c::ienv->char-max
             ldm-ienv-wfp-lemma)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->char-min ((ienv ienvp))
  :returns (min integerp)
  :short "The ACL2 integer value of @('CHAR_MAX') [C17:5.2.4.2.1/1]."
  (if (ienv->plain-char-signedp ienv)
      -128
    0)
  :type-prescription (integerp (ienv->char-min ienv))

  ///

  (defruled ienv->char-min-correct
    (equal (ienv->char-min ienv)
           (c::ienv->char-min (ldm-ienv ienv)))
    :enable (ldm-ienv
             c::ienv->char-min
             ldm-ienv-wfp-lemma)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->ushort-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('USHRT_MAX') [C17:5.2.4.2.1]."
  (1- (expt 2 (* 8 (ienv->short-bytes ienv))))

  ///

  (defret ienv->ushort-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription)

  (defruled ienv->ushort-max-correct
    (equal (ienv->ushort-max ienv)
           (c::ienv->ushort-max (ldm-ienv ienv)))
    :enable (ldm-ienv
             c::ienv->ushort-max
             c::integer-format->unsigned-max-of-integer-format-inc-sign-tcnpnt
             ldm-ienv-wfp-lemma)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sshort-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('SHRT_MAX') [C17:5.2.4.2.1]."
  (1- (expt 2 (1- (* 8 (ienv->short-bytes ienv)))))

  ///

  (defret ienv->sshort-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription)

  (defruled ienv->sshort-max-correct
    (equal (ienv->sshort-max ienv)
           (c::ienv->sshort-max (ldm-ienv ienv)))
    :enable (ldm-ienv
             c::ienv->sshort-max
             c::integer-format->signed-max-of-integer-format-inc-sign-tcnpnt
             ldm-ienv-wfp-lemma)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sshort-min ((ienv ienvp))
  :returns (min integerp :rule-classes (:rewrite :type-prescription))
  :short "The ACL2 integer value of @('SHRT_MIN') [C17:5.2.4.2.1]."
  (- (expt 2 (1- (* 8 (ienv->short-bytes ienv)))))

  ///

  (defruled ienv->sshort-min-correct
    (equal (ienv->sshort-min ienv)
           (c::ienv->sshort-min (ldm-ienv ienv)))
    :enable (ldm-ienv
             c::ienv->sshort-min
             c::integer-format->signed-min-of-integer-format-inc-sign-tcnpnt
             ldm-ienv-wfp-lemma)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->uint-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('UINT_MAX') [C17:5.2.4.2.1]."
  (1- (expt 2 (* 8 (ienv->int-bytes ienv))))

  ///

  (defret ienv->uint-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription)

  (defruled ienv->uint-max-correct
    (equal (ienv->uint-max ienv)
           (c::ienv->uint-max (ldm-ienv ienv)))
    :enable (ldm-ienv
             c::ienv->uint-max
             c::integer-format->unsigned-max-of-integer-format-inc-sign-tcnpnt
             ldm-ienv-wfp-lemma)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sint-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('INT_MAX') [C17:5.2.4.2.1]."
  (1- (expt 2 (1- (* 8 (ienv->int-bytes ienv)))))

  ///

  (defret ienv->sint-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription)

  (defruled ienv->sint-max-correct
    (equal (ienv->sint-max ienv)
           (c::ienv->sint-max (ldm-ienv ienv)))
    :enable (ldm-ienv
             c::ienv->sint-max
             c::integer-format->signed-max-of-integer-format-inc-sign-tcnpnt
             ldm-ienv-wfp-lemma)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sint-min ((ienv ienvp))
  :returns (min integerp :rule-classes (:rewrite :type-prescription))
  :short "The ACL2 integer value of @('INT_MIN') [C17:5.2.4.2.1]."
  (- (expt 2 (1- (* 8 (ienv->int-bytes ienv)))))

  ///

  (defruled ienv->sint-min-correct
    (equal (ienv->sint-min ienv)
           (c::ienv->sint-min (ldm-ienv ienv)))
    :enable (ldm-ienv
             c::ienv->sint-min
             c::integer-format->signed-min-of-integer-format-inc-sign-tcnpnt
             ldm-ienv-wfp-lemma)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->ulong-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('ULONG_MAX') [C17:5.2.4.2.1]."
  (1- (expt 2 (* 8 (ienv->long-bytes ienv))))

  ///

  (defret ienv->ulong-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription)

  (defruled ienv->ulong-max-correct
    (equal (ienv->ulong-max ienv)
           (c::ienv->ulong-max (ldm-ienv ienv)))
    :enable (ldm-ienv
             c::ienv->ulong-max
             c::integer-format->unsigned-max-of-integer-format-inc-sign-tcnpnt
             ldm-ienv-wfp-lemma)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->slong-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('LONG_MAX') [C17:5.2.4.2.1]."
  (1- (expt 2 (1- (* 8 (ienv->long-bytes ienv)))))

  ///

  (defret ienv->slong-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription)

  (defruled ienv->slong-max-correct
    (equal (ienv->slong-max ienv)
           (c::ienv->slong-max (ldm-ienv ienv)))
    :enable (ldm-ienv
             c::ienv->slong-max
             c::integer-format->signed-max-of-integer-format-inc-sign-tcnpnt
             ldm-ienv-wfp-lemma)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->slong-min ((ienv ienvp))
  :returns (min integerp :rule-classes (:rewrite :type-prescription))
  :short "The ACL2 integer value of @('LONG_MIN') [C17:5.2.4.2.1]."
  (- (expt 2 (1- (* 8 (ienv->long-bytes ienv)))))

  ///

  (defruled ienv->slong-min-correct
    (equal (ienv->slong-min ienv)
           (c::ienv->slong-min (ldm-ienv ienv)))
    :enable (ldm-ienv
             c::ienv->slong-min
             c::integer-format->signed-min-of-integer-format-inc-sign-tcnpnt
             ldm-ienv-wfp-lemma)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->ullong-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('ULLONG_MAX') [C17:5.2.4.2.1]."
  (1- (expt 2 (* 8 (ienv->llong-bytes ienv))))

  ///

  (defret ienv->ullong-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription)

  (defruled ienv->ullong-max-correct
    (equal (ienv->ullong-max ienv)
           (c::ienv->ullong-max (ldm-ienv ienv)))
    :enable (ldm-ienv
             c::ienv->ullong-max
             c::integer-format->unsigned-max-of-integer-format-inc-sign-tcnpnt
             ldm-ienv-wfp-lemma)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sllong-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('LLONG_MAX') [C17:5.2.4.2.1]."
  (1- (expt 2 (1- (* 8 (ienv->llong-bytes ienv)))))

  ///

  (defret ienv->sllong-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription)

  (defruled ienv->sllong-max-correct
    (equal (ienv->sllong-max ienv)
           (c::ienv->sllong-max (ldm-ienv ienv)))
    :enable (ldm-ienv
             c::ienv->sllong-max
             c::integer-format->signed-max-of-integer-format-inc-sign-tcnpnt
             ldm-ienv-wfp-lemma)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sllong-min ((ienv ienvp))
  :returns (min integerp :rule-classes (:rewrite :type-prescription))
  :short "The ACL2 integer value of @('LLONG_MIN') [C17:5.2.4.2.1]."
  (- (expt 2 (1- (* 8 (ienv->llong-bytes ienv)))))

  ///

  (defruled ienv->sllong-min-correct
    (equal (ienv->sllong-min ienv)
           (c::ienv->sllong-min (ldm-ienv ienv)))
    :enable (ldm-ienv
             c::ienv->sllong-min
             c::integer-format->signed-min-of-integer-format-inc-sign-tcnpnt
             ldm-ienv-wfp-lemma)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->uinteger-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('UINTMAX_MAX') [C17:7.20.2.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is currently the same as @(tsee ienv->ullong-max),
     but this may change in the future,
     if we add support for extended integer types."))
  (ienv->ullong-max ienv)

  ///

  (defret ienv->uinteger-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sinteger-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('INTMAX_MAX') [C17:7.20.2.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is currently the same as @(tsee ienv->sllong-max),
     but this may change in the future,
     if we add support for extended integer types."))
  (ienv->sllong-max ienv)

  ///

  (defret ienv->sinteger-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sinteger-min ((ienv ienvp))
  :returns (min integerp :rule-classes (:rewrite :type-prescription))
  :short "The ACL2 integer value of @('INTMAX_MIN') [C17:7.20.2.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is currently the same as @(tsee ienv->sllong-min),
     but this may change in the future,
     if we add support for extended integer types."))
  (ienv->sllong-min ienv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-uchar-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('unsigned char')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ienv->uchar-max ienv)))

  ///

  (defruled ienv-uchar-rangep-correct
    (equal (ienv-uchar-rangep val ienv)
           (c::ienv-uchar-rangep val (ldm-ienv ienv)))
    :enable (c::ienv-uchar-rangep
             ienv->uchar-max-correct)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-schar-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('signed char')."
  (and (<= (ienv->schar-min ienv) (ifix val))
       (<= (ifix val) (ienv->schar-max ienv)))

  ///

  (defruled ienv-schar-rangep-correct
    (equal (ienv-schar-rangep val ienv)
           (c::ienv-schar-rangep val (ldm-ienv ienv)))
    :enable (c::ienv-schar-rangep
             ienv->schar-max-correct
             ienv->schar-min-correct)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-char-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('char')."
  (and (<= (ienv->char-min ienv) (ifix val))
       (<= (ifix val) (ienv->char-max ienv)))

  ///

  (defruled ienv-char-rangep-correct
    (equal (ienv-char-rangep val ienv)
           (c::ienv-char-rangep val (ldm-ienv ienv)))
    :enable (c::ienv-char-rangep
             ienv->char-max-correct
             ienv->char-min-correct)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-ushort-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('unsigned short')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ienv->ushort-max ienv)))

  ///

  (defruled ienv-ushort-rangep-correct
    (equal (ienv-ushort-rangep val ienv)
           (c::ienv-ushort-rangep val (ldm-ienv ienv)))
    :enable (c::ienv-ushort-rangep
             ienv->ushort-max-correct)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-sshort-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('signed short')."
  (and (<= (ienv->sshort-min ienv) (ifix val))
       (<= (ifix val) (ienv->sshort-max ienv)))

  ///

  (defruled ienv-sshort-rangep-correct
    (equal (ienv-sshort-rangep val ienv)
           (c::ienv-sshort-rangep val (ldm-ienv ienv)))
    :enable (c::ienv-sshort-rangep
             ienv->sshort-max-correct
             ienv->sshort-min-correct)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-uint-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('unsigned int')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ienv->uint-max ienv)))

  ///

  (defruled ienv-uint-rangep-correct
    (equal (ienv-uint-rangep val ienv)
           (c::ienv-uint-rangep val (ldm-ienv ienv)))
    :enable (c::ienv-uint-rangep
             ienv->uint-max-correct)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-sint-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('signed int')."
  (and (<= (ienv->sint-min ienv) (ifix val))
       (<= (ifix val) (ienv->sint-max ienv)))

  ///

  (defruled ienv-sint-rangep-correct
    (equal (ienv-sint-rangep val ienv)
           (c::ienv-sint-rangep val (ldm-ienv ienv)))
    :enable (c::ienv-sint-rangep
             ienv->sint-max-correct
             ienv->sint-min-correct)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-ulong-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('unsigned long')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ienv->ulong-max ienv)))

  ///

  (defruled ienv-ulong-rangep-correct
    (equal (ienv-ulong-rangep val ienv)
           (c::ienv-ulong-rangep val (ldm-ienv ienv)))
    :enable (c::ienv-ulong-rangep
             ienv->ulong-max-correct)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-slong-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('signed long')."
  (and (<= (ienv->slong-min ienv) (ifix val))
       (<= (ifix val) (ienv->slong-max ienv)))

  ///

  (defruled ienv-slong-rangep-correct
    (equal (ienv-slong-rangep val ienv)
           (c::ienv-slong-rangep val (ldm-ienv ienv)))
    :enable (c::ienv-slong-rangep
             ienv->slong-max-correct
             ienv->slong-min-correct)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-ullong-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('unsigned long long')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ienv->ullong-max ienv)))

  ///

  (defruled ienv-ullong-rangep-correct
    (equal (ienv-ullong-rangep val ienv)
           (c::ienv-ullong-rangep val (ldm-ienv ienv)))
    :enable (c::ienv-ullong-rangep
             ienv->ullong-max-correct)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-sllong-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACl2 integer is
          in the range of (i.e. representable in) type @('signed long long')."
  (and (<= (ienv->sllong-min ienv) (ifix val))
       (<= (ifix val) (ienv->sllong-max ienv)))

  ///

  (defruled ienv-sllong-rangep-correct
    (equal (ienv-sllong-rangep val ienv)
           (c::ienv-sllong-rangep val (ldm-ienv ienv)))
    :enable (c::ienv-sllong-rangep
             ienv->sllong-max-correct
             ienv->sllong-min-correct)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-uinteger-max-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 integer is
          in the range of (i.e. representable in) type @('uintmax_t')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ienv->uinteger-max ienv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-sinteger-max-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 integer is
          in the range of (i.e. representable in) type @('intmax_t')."
  (and (<= (ienv->sinteger-min ienv) (ifix val))
       (<= (ifix val) (ienv->sinteger-max ienv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->gcc ((ienv ienvp))
  :returns (yes/no booleanp)
  :short "Flag saying whether GCC extensions are enabled or not."
  (c::version-gccp (ienv->version ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->clang ((ienv ienvp))
  :returns (yes/no booleanp)
  :short "Flag saying whether Clang extensions are enabled or not."
  (c::version-clangp (ienv->version ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->gcc/clang ((ienv ienvp))
  :returns (yes/no booleanp)
  :short "Flag saying whether GCC/Clang extensions are enabled or not."
  :long
  (xdoc::topstring
   (xdoc::p
    "There is very large overlap between the of extensions
     supported by GCC and by Clang.
     Therefore, it is most often sufficient to check
     if the version includes either."))
  (c::version-gcc/clangp (ienv->version ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->std ((ienv ienvp))
  :returns (number posp
                   :rule-classes (:rewrite :type-prescription)
                   :hints (("Goal" :in-theory (enable c::version-std-c17p
                                                      c::version-std-c23p))))
  :short "Numeric version of the C standard (regardless of GCC extensions)."
  (b* (((ienv ienv) ienv))
    (cond ((c::version-std-c17p ienv.version) 17)
          ((c::version-std-c23p ienv.version) 23)))
  :guard-hints (("Goal" :in-theory (enable c::version-std-c17p
                                           c::version-std-c23p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-default (&key
                      ((std (or (eq std :auto)
                                (equal std 17)
                                (equal std 23)))
                       ':auto)
                      ((extensions (or (eq extensions nil)
                                       (eq extensions :gcc)
                                       (eq extensions :clang)))
                       'nil))
  :short "A default implementation environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the default used by @(tsee input-files), but it is more general.
     In particular, it could be used as default for tests
     that do not necessarily involve @(tsee input-files).")
   (xdoc::p
    "We default to the C17 standard without GCC extensions.
     This is the C version with the strongest support.
     Optionally, this can be overridden
     with the @(':std') and @(':extensions') keyword arguments.
     The legal arguments for @(':std') are @(':auto'), @('17'), and @('23').
     The legal arguments for @(':extensions') are
     @('nil'), @(':gcc'), and @(':clang').")
   (xdoc::p
    "For the type sizes and signedness options,
     we use values which have anecdotally appeared common
     on 64-bit machines."))
  (b* ((std (if (eq std :auto) 17 std))
       (version (if (int= std 17)
                    (cond ((eq extensions nil) (c::version-c17))
                          ((eq extensions :gcc) (c::version-c17+gcc))
                          (t ; :clang
                           (c::version-c17+clang)))
                  (cond
                   ((eq extensions nil) (c::version-c23))
                   ((eq extensions :gcc) (c::version-c23+gcc))
                   (t ; :clang
                    (c::version-c23+clang))))))
    (make-ienv :version version
               :bool-bytes 1
               :short-bytes 2
               :int-bytes 4
               :long-bytes 8
               :llong-bytes 8
               :float-bytes 4
               :double-bytes 8
               :ldouble-bytes 16
               :pointer-bytes 8
               :plain-char-signedp nil)))
