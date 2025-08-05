; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ implementation-environments
  :parents (syntax-for-tools)
  :short "Implementation environments for the C syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are similar in purpose to the "
    (xdoc::seetopic "c::implementation-environments"
                    "implementation environments")
    " that are part of our formalization of C.
     We need to use implementation environments also for our C syntax for tools,
     specifically for certain tools that operate on it.
     We created this notion anew here,
     instead of using the one from the language formalization,
     because at that time the latter lacked some information needed here.
     Now the information has been added there,
     so we plan soon to remove this notion here
     and use the one from the language formalization."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ienv
  :short "Fixtype of implementation environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only need to capture
     certain characteristics of the integer types.
     We assume that bytes are 8 bits,
     that signed integers use two's complement,
     and that there are no padding bits
     or trap representations.
     Therefore, the characteristics of the integer types
     are mainly defined by four numbers,
     i.e. the numbers of bytes of (signed and unsigned)
     @('short'), @('int'), @('long'), and @('long long').
     These correspond to the "
    (xdoc::seetopic "c::integer-formats" "integer formats")
    " of our C formalization:
     see that topic for more information,
     also on the allowed ranges and relative constraints.
     We also need a flag saying whether the plain @('char') type
     has the same range as @('signed char') or not [C17:6.2.5/15];
     if the flag is false, it has the same range as @('unsigned char').")
   (xdoc::p
    "We also include a flag saying whether GCC extensions are enabled or not."))
  ((short-bytes pos
                :reqfix (if (and (<= short-bytes int-bytes)
                                 (<= int-bytes long-bytes)
                                 (<= long-bytes llong-bytes)
                                 (<= 2 short-bytes)
                                 (<= 4 int-bytes)
                                 (<= 8 long-bytes)
                                 (<= 8 llong-bytes))
                            short-bytes
                          2))
   (int-bytes pos
              :reqfix (if (and (<= short-bytes int-bytes)
                               (<= int-bytes long-bytes)
                               (<= long-bytes llong-bytes)
                               (<= 2 short-bytes)
                               (<= 4 int-bytes)
                               (<= 8 long-bytes)
                               (<= 8 llong-bytes))
                          int-bytes
                        4))
   (long-bytes pos
               :reqfix (if (and (<= short-bytes int-bytes)
                                (<= int-bytes long-bytes)
                                (<= long-bytes llong-bytes)
                                (<= 2 short-bytes)
                                (<= 4 int-bytes)
                                (<= 8 long-bytes)
                                (<= 8 llong-bytes))
                           long-bytes
                         8))
   (llong-bytes pos
                :reqfix (if (and (<= short-bytes int-bytes)
                                 (<= int-bytes long-bytes)
                                 (<= long-bytes llong-bytes)
                                 (<= 2 short-bytes)
                                 (<= 4 int-bytes)
                                 (<= 8 long-bytes)
                                 (<= 8 llong-bytes))
                            llong-bytes
                          8))
   (plain-char-signedp bool)
   (gcc bool))
  :require (and (<= short-bytes int-bytes)
                (<= int-bytes long-bytes)
                (<= long-bytes llong-bytes)
                (<= 2 short-bytes)
                (<= 4 int-bytes)
                (<= 8 long-bytes)
                (<= 8 llong-bytes))
  :pred ienvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-default ()
  :short "A default implementation environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This has no particular significance,
     but we set all the byte sizes to their minima,
     and the plain @('char') flag to @('nil') (i.e. unsigned);
     we also disable GCC extensions."))
  (make-ienv :short-bytes 2
             :int-bytes 4
             :long-bytes 8
             :llong-bytes 8
             :plain-char-signedp nil
             :gcc nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schar-min ()
  :returns (val integerp)
  :short "Minimum mathematical integer value of type @('signed char')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given the assumptions explained in @(tsee ienv), this is @'-128').")
   (xdoc::p
    "We keep this nullary function closed for more abstraction."))
  -128
  ///
  (in-theory (disable (:e schar-min))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schar-max ()
  :returns (val natp)
  :short "Maximum mathematical integer value of type @('signed char')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given the assumptions explained in @(tsee ienv), this is @('+127').")
   (xdoc::p
    "We keep this nullary function closed for more abstraction."))
  +127
  ///
  (in-theory (disable (:e schar-max))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uchar-max ()
  :returns (val natp)
  :short "Maximum mathematical integer value of type @('unsigned char')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given the assumptions explained in @(tsee ienv), this is @('255').")
   (xdoc::p
    "Note that the minimum @('unsigned char') is just 0,
     so there is no need to introduce a function for it.")
   (xdoc::p
    "We keep this nullary function closed for more abstraction."))
  255
  ///
  (in-theory (disable (:e schar-max))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-min ((ienv ienvp))
  :returns (val integerp)
  :short "Minimum mathematical integer value of the type @('char')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is either @(tsee schar-min) or 0,
     based on the flag in the implementation environment."))
  (if (ienv->plain-char-signedp ienv)
      (schar-min)
    0)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-max ((ienv ienvp))
  :returns (val integerp)
  :short "Maximum mathematical integer value of the type @('char')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is either @(tsee schar-max) or @(tsee uchar-max),
     based on the flag in the implementation environment."))
  (if (ienv->plain-char-signedp ienv)
      (schar-max)
    (uchar-max))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sshort-min ((ienv ienvp))
  :returns (val integerp :rule-classes (:rewrite :type-prescription))
  :short "Minimum mathematical integer value of type @('signed short')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This depends on the implementation environment."))
  (- (expt 2 (1- (* 8 (ienv->short-bytes ienv)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sshort-max ((ienv ienvp))
  :returns (val natp :rule-classes (:rewrite :type-prescription))
  :short "Maximum mathematical integer value of type @('signed short')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This depends on the implementation environment."))
  (1- (expt 2 (1- (* 8 (ienv->short-bytes ienv)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ushort-max ((ienv ienvp))
  :returns (val natp :rule-classes (:rewrite :type-prescription))
  :short "Maximum mathematical integer value of type @('unsigned short')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This depends on the implementation environment.")
   (xdoc::p
    "Note that the minimum @('unsigned signed') is just 0,
     so there is no need to introduce a function for it."))
  (1- (expt 2 (* 8 (ienv->short-bytes ienv))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-min ((ienv ienvp))
  :returns (val integerp :rule-classes (:rewrite :type-prescription))
  :short "Minimum mathematical integer value of type @('signed int')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This depends on the implementation environment."))
  (- (expt 2 (1- (* 8 (ienv->int-bytes ienv)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-max ((ienv ienvp))
  :returns (val natp :rule-classes (:rewrite :type-prescription))
  :short "Maximum mathematical integer value of type @('signed int')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This depends on the implementation environment."))
  (1- (expt 2 (1- (* 8 (ienv->int-bytes ienv)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uint-max ((ienv ienvp))
  :returns (val natp :rule-classes (:rewrite :type-prescription))
  :short "Maximum mathematical integer value of type @('unsigned int')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This depends on the implementation environment.")
   (xdoc::p
    "Note that the minimum @('unsigned signed') is just 0,
     so there is no need to introduce a function for it."))
  (1- (expt 2 (* 8 (ienv->int-bytes ienv))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define slong-min ((ienv ienvp))
  :returns (val integerp :rule-classes (:rewrite :type-prescription))
  :short "Minimum mathematical integer value of type @('signed long')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This depends on the implementation environment."))
  (- (expt 2 (1- (* 8 (ienv->long-bytes ienv)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define slong-max ((ienv ienvp))
  :returns (val natp :rule-classes (:rewrite :type-prescription))
  :short "Maximum mathematical integer value of type @('signed long')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This depends on the implementation environment."))
  (1- (expt 2 (1- (* 8 (ienv->long-bytes ienv)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ulong-max ((ienv ienvp))
  :returns (val natp :rule-classes (:rewrite :type-prescription))
  :short "Maximum mathematical integer value of type @('unsigned long')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This depends on the implementation environment.")
   (xdoc::p
    "Note that the minimum @('unsigned signed') is just 0,
     so there is no need to introduce a function for it."))
  (1- (expt 2 (* 8 (ienv->long-bytes ienv))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sllong-min ((ienv ienvp))
  :returns (val integerp :rule-classes (:rewrite :type-prescription))
  :short "Minimum mathematical integer value of type @('signed long long')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This depends on the implementation environment."))
  (- (expt 2 (1- (* 8 (ienv->llong-bytes ienv)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sllong-max ((ienv ienvp))
  :returns (val natp :rule-classes (:rewrite :type-prescription))
  :short "Maximum mathematical integer value of type @('signed long long')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This depends on the implementation environment."))
  (1- (expt 2 (1- (* 8 (ienv->llong-bytes ienv)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ullong-max ((ienv ienvp))
  :returns (val natp :rule-classes (:rewrite :type-prescription))
  :short "Maximum mathematical integer value of type @('unsigned long long')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This depends on the implementation environment.")
   (xdoc::p
    "Note that the minimum @('unsigned signed') is just 0,
     so there is no need to introduce a function for it."))
  (1- (expt 2 (* 8 (ienv->llong-bytes ienv))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schar-rangep ((val integerp))
  :returns (yes/no booleanp)
  :short "Check if a mathematical integer is
          in the range of (i.e. representable in) type @('signed char')."
  (and (<= (schar-min) (ifix val))
       (<= (ifix val) (schar-max)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uchar-rangep ((val integerp))
  :returns (yes/no booleanp)
  :short "Check if a mathematical integer is
          in the range of (i.e. representable in) type @('unsigned char')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (uchar-max)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sshort-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if a mathematical integer is
          in the range of (i.e. representable in) type @('signed short')."
  (and (<= (sshort-min ienv) (ifix val))
       (<= (ifix val) (sshort-max ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ushort-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if a mathematical integer is
          in the range of (i.e. representable in) type @('unsigned short')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ushort-max ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sint-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if a mathematical integer is
          in the range of (i.e. representable in) type @('signed int')."
  (and (<= (sint-min ienv) (ifix val))
       (<= (ifix val) (sint-max ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uint-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if a mathematical integer is
          in the range of (i.e. representable in) type @('unsigned int')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (uint-max ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define slong-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if a mathematical integer is
          in the range of (i.e. representable in) type @('signed long')."
  (and (<= (slong-min ienv) (ifix val))
       (<= (ifix val) (slong-max ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ulong-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if a mathematical integer is
          in the range of (i.e. representable in) type @('unsigned long')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ulong-max ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sllong-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if a mathematical integer is
          in the range of (i.e. representable in) type @('signed long long')."
  (and (<= (sllong-min ienv) (ifix val))
       (<= (ifix val) (sllong-max ienv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ullong-rangep ((val integerp) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check if a mathematical integer is
          in the range of (i.e. representable in) type @('unsigned long long')."
  (and (<= 0 (ifix val))
       (<= (ifix val) (ullong-max ienv)))
  :hooks (:fix))
