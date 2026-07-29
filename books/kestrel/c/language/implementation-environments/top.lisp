; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2026 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "dialects")
(include-book "uchar-formats")
(include-book "signed-formats")
(include-book "schar-formats")
(include-book "char-formats")
(include-book "bool-formats")
(include-book "integer-format-templates")
(include-book "integer-formats")
(include-book "character-sets")

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ implementation-environments
  :parents (language)
  :short "Implementation environments for C."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some aspects of the syntax and semantics of C are implementation-dependent.
     [C17:5] introduces the notion of translation and execution environments,
     which specify those aspects.
     In our formalization, we introduce a notion of implementation environment,
     which puts together the translation and execution environments in [C17].
     That is, an implementation environment
     specifies the implementation-dependent aspects of C.
     We prefer to formalize one (implementation) environment,
     instead of two (translation and execution) environments,
     because the latter two share several aspects (e.g. integer sizes),
     and therefore it seems simpler to have one notion.")
   (xdoc::p
    "We start by capturing some aspects of the C implementation environment.
     More will be added in the future.")
   (xdoc::p
    "Initially, our formalization of implementation environments
     is not used in other parts of the C formalization;
     furthermore, it captures notions already captured elsewhere,
     such as the "
    (xdoc::seetopic "integer-formats" "integer formats")
    ". But we plan to update the rest of the formalization to use this,
     also removing those then-redundant parts."))
  :order-subtopics (uchar-formats
                    signed-formats
                    schar-formats
                    char-formats
                    bool-formats
                    integer-format-templates
                    integer-formats
                    character-sets
                    t)
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-requirep ((uchar uchar-formatp)
                       (schar schar-formatp)
                       (short integer-formatp)
                       (int integer-formatp)
                       (long integer-formatp)
                       (llong integer-formatp)
                       (bool bool-formatp))
  :returns (yes/no booleanp)
  :short "Requirements for @(tsee ienv)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This captures requirements involving
     multiple components of @(tsee ienv),
     used in the @(':require') of that fixtype definition."))
  (and (integer-format-short-wfp short uchar schar)
       (integer-format-int-wfp int uchar short)
       (integer-format-long-wfp long uchar int)
       (integer-format-llong-wfp llong uchar long)
       (bool-format-wfp bool uchar)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ienv
  :short "Fixtype of implementation environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now this only contains the following information:")
   (xdoc::ul
    (xdoc::li
     "The dialect of C.")
    (xdoc::li
     "The formats of the three character types.")
    (xdoc::li
     "The formats of the standard signed integer types
      and their unsigned counterparts.")
    (xdoc::li
     "The format of the boolean type
      (which is a standard unsigned integer type,
      but has no signed counterpart)."))
   (xdoc::p
    "We plan to add more information."))
  ((dialect dialectp)
   (uchar uchar-format
          :reqfix (if (ienv-requirep uchar schar short int long llong bool)
                      uchar
                    (uchar-format-8)))
   (schar schar-format
          :reqfix (if (ienv-requirep uchar schar short int long llong bool)
                      schar
                    (schar-format-8tcnt)))
   (char char-format
         :reqfix (if (ienv-requirep uchar schar short int long llong bool)
                     char
                   (char-format-8u)))
   (short integer-format
          :reqfix (if (ienv-requirep uchar schar short int long llong bool)
                      short
                    (short-format-16tcnt)))
   (int integer-format
        :reqfix (if (ienv-requirep uchar schar short int long llong bool)
                    int
                  (int-format-16tcnt)))
   (long integer-format
         :reqfix (if (ienv-requirep uchar schar short int long llong bool)
                     long
                   (long-format-32tcnt)))
   (llong integer-format
          :reqfix (if (ienv-requirep uchar schar short int long llong bool)
                      llong
                    (llong-format-64tcnt)))
   (bool bool-format
         :reqfix (if (ienv-requirep uchar schar short int long llong bool)
                     bool
                   (bool-format-lsb))))
  :require (ienv-requirep uchar schar short int long llong bool)
  :pred ienvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->char-size ((ienv ienvp))
  :returns (size posp)
  :short "The ACL2 integer value of @('CHAR_BIT') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the size, in bits, of
     (possibly @('unsigned') or @('signed')) @('char') objects."))
  (uchar-format->size (ienv->uchar ienv))

  ///

  (defret ienv->char-size-type-prescription
    (and (posp size)
         (> size 1))
    :rule-classes :type-prescription)

  (defret ienv->char-size-lower-bound
    (>= size 8)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->uchar-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('UCHAR_MAX') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee uchar-format->max)."))
  (uchar-format->max (ienv->uchar ienv))

  ///

  (defret ienv->uchar-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription)

  (defret ienv->uchar-max-lower-bound
    (>= max 255)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->schar-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('SCHAR_MAX') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee schar-format->max)."))
  (schar-format->max (ienv->schar ienv) (ienv->uchar ienv))

  ///

  (defret ienv->schar-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription)

  (defret ienv->schar-max-lower-bound
    (>= max 127)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->schar-min ((ienv ienvp))
  :returns (min integerp)
  :short "The ACL2 integer value of @('SCHAR_MIN') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee schar-format->min)."))
  (schar-format->min (ienv->schar ienv) (ienv->uchar ienv))

  ///

  (defret ienv->schar-min-type-prescription
    (and (integerp min)
         (< min 0))
    :rule-classes :type-prescription)

  (defret ienv->schar-min-upper-bound
    (<= min -127)
    :rule-classes ((:linear :trigger-terms ((ienv->schar-min ienv))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->char-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('CHAR_MAX') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee char-format->max)."))
  (char-format->max (ienv->char ienv) (ienv->uchar ienv) (ienv->schar ienv))

  ///

  (defret ienv->char-max-type-prescription
    (and (posp max)
         (> max 1))
    :rule-classes :type-prescription)

  (defret ienv->char-max-lower-bound
    (>= max 127)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->char-min ((ienv ienvp))
  :returns (min integerp)
  :short "The ACL2 integer value of @('CHAR_MIN') [C17:5.2.4.2.1/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee char-format->min)."))
  (char-format->min (ienv->char ienv) (ienv->uchar ienv) (ienv->schar ienv))

  ///

  (defret ienv->char-min-type-prescription
    (and (integerp min)
         (<= min 0))
    :rule-classes :type-prescription)

  (defret ienv->char-min-upper-bound
    (<= min 0)
    :rule-classes ((:linear :trigger-terms ((ienv->char-min ienv))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->short-bit-size ((ienv ienvp))
  :returns (size posp)
  :short "Number of bits of unsigned and signed @('short') objects."
  (integer-format->bit-size (ienv->short ienv))

  ///

  (defret ienv->short-bit-size-type-prescription
    (and (posp size)
         (> size 1))
    :rule-classes :type-prescription)

  (defret ienv->short-bit-size-lower-bound
    (>= size 16)
    :rule-classes :linear
    :hints (("Goal"
             :use (:instance ienv-requirements (x ienv))
             :in-theory (e/d (ienv-requirep)
                             (ienv-requirements))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->short-byte-size ((ienv ienvp))
  :returns
  (size posp
        :hints (("Goal"
                 :in-theory (e/d (posp
                                  ienv-requirep
                                  integer-format-short-wfp
                                  ienv->char-size
                                  ienv->short-bit-size)
                                 (ienv-requirements))
                 :use (:instance ienv-requirements (x ienv))
                )))
  :short "Number of bytes of unsigned and signed @('short') objects."
  (/ (ienv->short-bit-size ienv)
     (ienv->char-size ienv))

  ///

  (defret ienv->short-byte-size-type-prescription
    (posp size)
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (disable ienv->short-byte-size)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->int-bit-size ((ienv ienvp))
  :returns (size posp)
  :short "Number of bits of unsigned and signed @('int') objects."
  (integer-format->bit-size (ienv->int ienv))

  ///

  (defret ienv->int-bit-size-type-prescription
    (and (posp size)
         (> size 1))
    :rule-classes :type-prescription)

  (defret ienv->int-bit-size-lower-bound
    (>= size 16)
    :rule-classes :linear
    :hints (("Goal"
             :use (:instance ienv-requirements (x ienv))
             :in-theory (e/d (ienv-requirep)
                             (ienv-requirements))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->int-byte-size ((ienv ienvp))
  :returns
  (size posp
        :hints (("Goal"
                 :in-theory (e/d (posp
                                  ienv-requirep
                                  integer-format-int-wfp
                                  ienv->char-size
                                  ienv->int-bit-size)
                                 (ienv-requirements))
                 :use (:instance ienv-requirements (x ienv))
                )))
  :short "Number of bytes of unsigned and signed @('int') objects."
  (/ (ienv->int-bit-size ienv)
     (ienv->char-size ienv))

  ///

  (defret ienv->int-byte-size-type-prescription
    (posp size)
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (disable ienv->int-byte-size)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->long-bit-size ((ienv ienvp))
  :returns (size posp)
  :short "Number of bits of unsigned and signed @('long') objects."
  (integer-format->bit-size (ienv->long ienv))

  ///

  (defret ienv->long-bit-size-type-prescription
    (and (posp size)
         (> size 1))
    :rule-classes :type-prescription)

  (defret ienv->long-bit-size-lower-bound
    (>= size 32)
    :rule-classes :linear
    :hints (("Goal"
             :use (:instance ienv-requirements (x ienv))
             :in-theory (e/d (ienv-requirep)
                             (ienv-requirements))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->long-byte-size ((ienv ienvp))
  :returns
  (size posp
        :hints (("Goal"
                 :in-theory (e/d (posp
                                  ienv-requirep
                                  integer-format-long-wfp
                                  ienv->char-size
                                  ienv->long-bit-size)
                                 (ienv-requirements))
                 :use (:instance ienv-requirements (x ienv))
                )))
  :short "Number of bytes of unsigned and signed @('long') objects."
  (/ (ienv->long-bit-size ienv)
     (ienv->char-size ienv))

  ///

  (defret ienv->long-byte-size-type-prescription
    (posp size)
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (disable ienv->long-byte-size)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->llong-bit-size ((ienv ienvp))
  :returns (size posp)
  :short "Number of bits of unsigned and signed @('long long') objects."
  (integer-format->bit-size (ienv->llong ienv))

  ///

  (defret ienv->llong-bit-size-type-prescription
    (and (posp size)
         (> size 1))
    :rule-classes :type-prescription)

  (defret ienv->llong-bit-size-lower-bound
    (>= size 64)
    :rule-classes :linear
    :hints (("Goal"
             :use (:instance ienv-requirements (x ienv))
             :in-theory (e/d (ienv-requirep)
                             (ienv-requirements))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->llong-byte-size ((ienv ienvp))
  :returns
  (size posp
        :hints (("Goal"
                 :in-theory (e/d (posp
                                  ienv-requirep
                                  integer-format-llong-wfp
                                  ienv->char-size
                                  ienv->llong-bit-size)
                                 (ienv-requirements))
                 :use (:instance ienv-requirements (x ienv))
                )))
  :short "Number of bytes of unsigned and signed @('long long') objects."
  (/ (ienv->llong-bit-size ienv)
     (ienv->char-size ienv))

  ///

  (defret ienv->llong-byte-size-type-prescription
    (posp size)
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (disable ienv->llong-byte-size)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->bool-bit-size ((ienv ienvp))
  :returns (size posp)
  :short "Number of bits of @('_Bool') objects."
  (* (bool-format->byte-size (ienv->bool ienv))
     (uchar-format->size (ienv->uchar ienv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->bool-byte-size ((ienv ienvp))
  :returns (size posp)
  :short "Number of bytes of @('_Bool') objects."
  (bool-format->byte-size (ienv->bool ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->ushort-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('USHRT_MAX') [C17:5.2.4.2.1]."
  (integer-format->unsigned-max (ienv->short ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sshort-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('SHRT_MAX') [C17:5.2.4.2.1]."
  (integer-format->signed-max (ienv->short ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sshort-min ((ienv ienvp))
  :returns (min integerp)
  :short "The ACL2 integer value of @('SHRT_MIN') [C17:5.2.4.2.1]."
  (integer-format->signed-min (ienv->short ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->uint-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('UINT_MAX') [C17:5.2.4.2.1]."
  (integer-format->unsigned-max (ienv->int ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sint-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('INT_MAX') [C17:5.2.4.2.1]."
  (integer-format->signed-max (ienv->int ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sint-min ((ienv ienvp))
  :returns (min integerp)
  :short "The ACL2 integer value of @('INT_MIN') [C17:5.2.4.2.1]."
  (integer-format->signed-min (ienv->int ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->ulong-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('ULONG_MAX') [C17:5.2.4.2.1]."
  (integer-format->unsigned-max (ienv->long ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->slong-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('LONG_MAX') [C17:5.2.4.2.1]."
  (integer-format->signed-max (ienv->long ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->slong-min ((ienv ienvp))
  :returns (min integerp)
  :short "The ACL2 integer value of @('LONG_MIN') [C17:5.2.4.2.1]."
  (integer-format->signed-min (ienv->long ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->ullong-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('ULLONG_MAX') [C17:5.2.4.2.1]."
  (integer-format->unsigned-max (ienv->llong ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sllong-max ((ienv ienvp))
  :returns (max posp)
  :short "The ACL2 integer value of @('LLONG_MAX') [C17:5.2.4.2.1]."
  (integer-format->signed-max (ienv->llong ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv->sllong-min ((ienv ienvp))
  :returns (min integerp)
  :short "The ACL2 integer value of @('LLONG_MIN') [C17:5.2.4.2.1]."
  (integer-format->signed-min (ienv->llong ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-uchar-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 integer is
          in the range of (i.e. representable in) type @('unsigned char')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ienv->uchar-max ienv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-schar-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 integer is
          in the range of (i.e. representable in) type @('signed char')."
  (and (<= (ienv->schar-min ienv) (ifix val))
       (<= (ifix val) (ienv->schar-max ienv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-char-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 integer is
          in the range of (i.e. representable in) type @('char')."
  (and (<= (ienv->char-min ienv) (ifix val))
       (<= (ifix val) (ienv->char-max ienv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-ushort-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 integer is
          in the range of (i.e. representable in) type @('unsigned short')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ienv->ushort-max ienv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-sshort-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 integer is
          in the range of (i.e. representable in) type @('signed short')."
  (and (<= (ienv->sshort-min ienv) (ifix val))
       (<= (ifix val) (ienv->sshort-max ienv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-uint-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 integer is
          in the range of (i.e. representable in) type @('unsigned int')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ienv->uint-max ienv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-sint-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 integer is
          in the range of (i.e. representable in) type @('signed int')."
  (and (<= (ienv->sint-min ienv) (ifix val))
       (<= (ifix val) (ienv->sint-max ienv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-ulong-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 integer is
          in the range of (i.e. representable in) type @('unsigned long')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ienv->ulong-max ienv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-slong-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 integer is
          in the range of (i.e. representable in) type @('signed long')."
  (and (<= (ienv->slong-min ienv) (ifix val))
       (<= (ifix val) (ienv->slong-max ienv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-ullong-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 integer is
          in the range of (i.e. representable in) type @('unsigned long long')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ienv->ullong-max ienv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-sllong-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 integer is
          in the range of (i.e. representable in) type @('signed long long')."
  (and (<= (ienv->sllong-min ienv) (ifix val))
       (<= (ifix val) (ienv->sllong-max ienv))))
