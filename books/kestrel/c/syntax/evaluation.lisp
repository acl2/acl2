; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-operations")
(include-book "implementation-environments")

(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "centaur/fty/deftypes" :dir :system)

(include-book "kestrel/utilities/arith-fix-and-equiv-defs" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/arithmetic-light/less-than-or-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/log2" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ evaluation
  :parents (syntax-for-tools)
  :short "Evaluation of C @(see abstract-syntax) trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide partial support for evaluation of "
    (xdoc::seetopic "purity" "pure")
    " expressions.")
   (xdoc::p
    "The implementation is based on our "
    (xdoc::seetopic "c::dynamic-semantics" "dynamic semantics")
    ", but generalizing when necessary,
     i.e. to accommodate implementations with different integer sizes."))
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum pointer
  :parents (value)
  :short "Fixtype of pointer values."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now, we only distinguish between null and non-null pointers.
     By ``non-null'', we mean any pointer to an object or a function.
     Such a pointer will compare unequal to a null pointer [C17:6.3.2.3/3].
     Note that there is only one null pointer value,
     in the sense that null pointers always compare equal [C17:6.3.2.3/3].")
   (xdoc::p
    "We also include an @(':unknown') case."))
  (:unknown ())
  (:null ())
  (:non-null ())
  :pred pointerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes values/value-list
  :short "Fixtypes of values and value lists."

  (fty::deftagsum value
    :short "Fixtype of values."
    :long
    (xdoc::topstring
     (xdoc::p
      "We only model a subset of C values for the moment.
       We include an @(':unknown') case which may represent values
       for which there is not yet another representation.")
     (xdoc::p
      "The character types are constrained to one byte.
       The integer types of greater rank are unconstrained here.
       We introduce a separate predicate, @(see well-formed-value-p),
       which recognizes values which are valid with respect to an "
      (xdoc::seetopic "implementation-environments"
                      "implementation environment")
      "."))
    (:unknown ())
    (:bool    ((get bit)))
    (:uchar   ((get nat
                    :reqfix (if (unsigned-byte-p 8 get) get 0)))
     :require (unsigned-byte-p 8 get))
    (:schar   ((get int
                    :reqfix (if (signed-byte-p 8 get) get 0)))
     :require (signed-byte-p 8 get))
    (:ushort  ((get nat)))
    (:sshort  ((get int)))
    (:uint    ((get nat)))
    (:sint    ((get int)))
    (:ulong   ((get nat)))
    (:slong   ((get int)))
    (:ullong  ((get nat)))
    (:sllong  ((get int)))
    (:pointer ((get pointer)))
    (:array   ((elements value-list)))
    :pred valuep
    :prepwork ((local (in-theory (enable nfix ifix)))))

  (fty::deflist value-list
    :short "Fixtype of lists of values."
    :elt-type value
    :true-listp t
    :elementp-of-nil nil
    :pred value-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule value-uchar->get-linear
  (<= (value-uchar->get val) 255)
  :rule-classes :linear
  :enable (value-uchar->get
           unsigned-byte-p))

(defrule value-schar->get-min-linear
  (<= -128 (value-schar->get val))
  :rule-classes :linear
  :enable (value-schar->get
           signed-byte-p))

(defrule value-schar->get-max-linear
  (<= (value-schar->get val) 127)
  :rule-classes :linear
  :enable (value-schar->get
           signed-byte-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-unsigned-integerp ((val valuep))
  :returns (yes/no booleanp)
  :parents (value)
  :short "Recognize values with unsigned integer type [C17:6.2.5/6]."
  :long
  (xdoc::topstring-p
   "This predicate is overapproximate in the sense that
    it also recognizes unknown values &mdash;
    i.e. values which <emph>might</emph> have unsigned integer type.")
  (and (value-case val '(:unknown :bool :uchar :ushort :uint :ulong :ullong))
       t)
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-signed-integerp ((val valuep))
  :returns (yes/no booleanp)
  :parents (value)
  :short "Recognize values with signed integer type [C17:6.2.5/4]."
  :long
  (xdoc::topstring-p
   "This predicate is overapproximate in the sense that
    it also recognizes unknown values &mdash;
    i.e. values which <emph>might</emph> have signed integer type.")
  (and (value-case val '(:unknown :schar :sshort :sint :slong :sllong))
       t)
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-integerp ((val valuep))
  :returns (yes/no booleanp)
  :parents (value)
  :short "Recognize values with integer type."
  :long
  (xdoc::topstring-p
   "This predicate is overapproximate in the sense that
    it also recognizes unknown values &mdash;
    i.e. values which <emph>might</emph> have integer type.")
  (or (value-unsigned-integerp val)
      (value-signed-integerp val))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule value-integerp-when-value-unsigned-integerp-forward-chaining
  (implies (value-unsigned-integerp val)
           (value-integerp val))
  :rule-classes :forward-chaining
  :enable value-integerp)

(defrule value-integerp-when-value-signed-integerp-forward-chaining
  (implies (value-signed-integerp val)
           (value-integerp val))
  :rule-classes :forward-chaining
  :enable value-integerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-arithmeticp ((val valuep))
  :returns (yes/no booleanp)
  :short "Recognize values with arithmetic type [C17:6.2.5/18]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This predicate is overapproximate in the sense that
     it also recognizes unknown values &mdash;
     i.e. values which <emph>might</emph> have type.")
   (xdoc::p
    "Currently, we do not model any floating types,
     and so the arithmetic types are equivalent to the integer types."))
  (value-integerp val)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule value-arithmeticp-when-value-integerp-forward-chaining
  (implies (value-integerp val)
           (value-arithmeticp val))
  :rule-classes :forward-chaining
  :enable value-arithmeticp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines well-formed-value/value-list-p
  (define well-formed-value-p ((val valuep) (ienv ienvp))
    :returns (yes/no booleanp)
    :parents (value)
    :short "Recognize valid values under a particular implementation
            environment."
    :long
    (xdoc::topstring-p
     "This predicate checks that the integer values
      fit into the number of bytes available for their type
      according to the "
     (xdoc::seetopic "implementation-environments"
                     "implementation environment")
     ".")
    (b* (((ienv ienv) ienv))
      (value-case
        val
        :ushort (unsigned-byte-p (* 8 ienv.short-bytes) val.get)
        :sshort (signed-byte-p (* 8 ienv.short-bytes) val.get)
        :uint (unsigned-byte-p (* 8 ienv.int-bytes) val.get)
        :sint (signed-byte-p (* 8 ienv.int-bytes) val.get)
        :ulong (unsigned-byte-p (* 8 ienv.long-bytes) val.get)
        :slong (signed-byte-p (* 8 ienv.long-bytes) val.get)
        :ullong (unsigned-byte-p (* 8 ienv.llong-bytes) val.get)
        :sllong (signed-byte-p (* 8 ienv.llong-bytes) val.get)
        :array (well-formed-value-list-p val.elements ienv)
        :otherwise t))
    :measure (value-count val))

  (define well-formed-value-list-p ((values value-listp) (ienv ienvp))
    :returns (yes/no booleanp)
    (or (endp values)
        (and (well-formed-value-p (first values) ienv)
             (well-formed-value-list-p (rest values) ienv)))
    :measure (value-list-count values))

  ///
  (fty::deffixequiv-mutual well-formed-value/value-list-p))

;;;;;;;;;;;;;;;;;;;;

(defrule value-ushort->get-when-well-formed-value-p-linear
  (implies (well-formed-value-p val ienv)
           (<= (value-ushort->get val)
               (+ -1 (expt 2 (* 8 (ienv->short-bytes ienv))))))
  :rule-classes ((:linear :trigger-terms ((value-ushort->get val))))
  :enable (value-ushort->get
           well-formed-value-p
           unsigned-byte-p
           integer-range-p))

(defrule value-sshort->get-min-when-well-formed-value-p-linear
  (implies (well-formed-value-p val ienv)
           (<= (- (expt 2 (+ -1 (* 8 (ienv->short-bytes ienv)))))
               (value-sshort->get val)))
  :rule-classes ((:linear :trigger-terms ((value-sshort->get val))))
  :enable (value-sshort->get
           well-formed-value-p
           signed-byte-p
           integer-range-p))

(defrule value-sshort->get-max-when-well-formed-value-p-linear
  (implies (well-formed-value-p val ienv)
           (<= (value-sshort->get val)
               (+ -1 (expt 2 (+ -1 (* 8 (ienv->short-bytes ienv)))))))
  :rule-classes ((:linear :trigger-terms ((value-sshort->get val))))
  :enable (value-sshort->get
           well-formed-value-p
           signed-byte-p
           integer-range-p))

(defrule value-uint->get-when-well-formed-value-p-linear
  (implies (well-formed-value-p val ienv)
           (<= (value-uint->get val)
               (+ -1 (expt 2 (* 8 (ienv->int-bytes ienv))))))
  :rule-classes ((:linear :trigger-terms ((value-uint->get val))))
  :enable (value-uint->get
           well-formed-value-p
           unsigned-byte-p
           integer-range-p))

(defrule value-sint->get-min-when-well-formed-value-p-linear
  (implies (well-formed-value-p val ienv)
           (<= (- (expt 2 (+ -1 (* 8 (ienv->int-bytes ienv)))))
               (value-sint->get val)))
  :rule-classes ((:linear :trigger-terms ((value-sint->get val))))
  :enable (value-sint->get
           well-formed-value-p
           signed-byte-p
           integer-range-p))

(defrule value-sint->get-max-when-well-formed-value-p-linear
  (implies (well-formed-value-p val ienv)
           (<= (value-sint->get val)
               (+ -1 (expt 2 (+ -1 (* 8 (ienv->int-bytes ienv)))))))
  :rule-classes ((:linear :trigger-terms ((value-sint->get val))))
  :enable (value-sint->get
           well-formed-value-p
           signed-byte-p
           integer-range-p))

(defrule value-ulong->get-when-well-formed-value-p-linear
  (implies (well-formed-value-p val ienv)
           (<= (value-ulong->get val)
               (+ -1 (expt 2 (* 8 (ienv->long-bytes ienv))))))
  :rule-classes ((:linear :trigger-terms ((value-ulong->get val))))
  :enable (value-ulong->get
           well-formed-value-p
           unsigned-byte-p
           integer-range-p))

(defrule value-slong->get-min-when-well-formed-value-p-linear
  (implies (well-formed-value-p val ienv)
           (<= (- (expt 2 (+ -1 (* 8 (ienv->long-bytes ienv)))))
               (value-slong->get val)))
  :rule-classes ((:linear :trigger-terms ((value-slong->get val))))
  :enable (value-slong->get
           well-formed-value-p
           signed-byte-p
           integer-range-p))

(defrule value-slong->get-max-when-well-formed-value-p-linear
  (implies (well-formed-value-p val ienv)
           (<= (value-slong->get val)
               (+ -1 (expt 2 (+ -1 (* 8 (ienv->long-bytes ienv)))))))
  :rule-classes ((:linear :trigger-terms ((value-slong->get val))))
  :enable (value-slong->get
           well-formed-value-p
           signed-byte-p
           integer-range-p))

(defrule value-ullong->get-when-well-formed-value-p-linear
  (implies (well-formed-value-p val ienv)
           (<= (value-ullong->get val)
               (+ -1 (expt 2 (* 8 (ienv->llong-bytes ienv))))))
  :rule-classes ((:linear :trigger-terms ((value-ullong->get val))))
  :enable (value-ullong->get
           well-formed-value-p
           unsigned-byte-p
           integer-range-p))

(defrule value-sllong->get-min-when-well-formed-value-p-linear
  (implies (well-formed-value-p val ienv)
           (<= (- (expt 2 (+ -1 (* 8 (ienv->llong-bytes ienv)))))
               (value-sllong->get val)))
  :rule-classes ((:linear :trigger-terms ((value-sllong->get val))))
  :enable (value-sllong->get
           well-formed-value-p
           signed-byte-p
           integer-range-p))

(defrule value-sllong->get-max-when-well-formed-value-p-linear
  (implies (well-formed-value-p val ienv)
           (<= (value-sllong->get val)
               (+ -1 (expt 2 (+ -1 (* 8 (ienv->llong-bytes ienv)))))))
  :rule-classes ((:linear :trigger-terms ((value-sllong->get val))))
  :enable (value-sllong->get
           well-formed-value-p
           signed-byte-p
           integer-range-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-uint-mod ((get integerp) (ienv ienvp))
  :returns (val valuep)
  :parents (value)
  :short "Construct a well-formed unsigned integer,
          by taking the @('mod') of the value."
  :long
  (xdoc::topstring-p
   "Unsigned arithmetic is modular [C17:6.2.5/9].
    We therefore commonly use this ``smart constructor''
    in arithmetic operations.")
  (value-uint (mod (lifix get) (expt 2 (* 8 (ienv->int-bytes ienv)))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule value-kind-of-value-uint-mod
  (equal (value-kind (value-uint-mod get ienv))
         :uint)
  :enable value-uint-mod)

(defruled value-uint->get-of-value-uint-mod
  (equal (value-uint->get (value-uint-mod get ienv))
         (mod (ifix get) (expt 2 (* 8 (ienv->int-bytes ienv)))))
  :enable value-uint-mod)

(defrule well-formed-value-p-of-value-uint-mod
  (well-formed-value-p (value-uint-mod get ienv) ienv)
  :enable (value-uint-mod
           well-formed-value-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-ulong-mod ((get integerp) (ienv ienvp))
  :returns (val valuep)
  :parents (value)
  :short "Construct a well-formed unsigned long,
          by taking the @('mod') of the value."
  :long
  (xdoc::topstring-p
   "Unsigned arithmetic is modular [C17:6.2.5/9].
    We therefore commonly use this ``smart constructor''
    in arithmetic operations.")
  (value-ulong (mod (lifix get) (expt 2 (* 8 (ienv->long-bytes ienv)))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule value-kind-of-value-ulong-mod
  (equal (value-kind (value-ulong-mod get ienv))
         :ulong)
  :enable value-ulong-mod)

(defruled value-ulong->get-of-value-ulong-mod
  (equal (value-ulong->get (value-ulong-mod get ienv))
         (mod (ifix get) (expt 2 (* 8 (ienv->long-bytes ienv)))))
  :enable value-ulong-mod)

(defrule well-formed-value-p-of-value-ulong-mod
  (well-formed-value-p (value-ulong-mod get ienv) ienv)
  :enable (value-ulong-mod
           well-formed-value-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-ullong-mod ((get integerp) (ienv ienvp))
  :returns (val valuep)
  :parents (value)
  :short "Construct a well-formed unsigned long long,
          by taking the @('mod') of the value."
  :long
  (xdoc::topstring-p
   "Unsigned arithmetic is modular [C17:6.2.5/9].
    We therefore commonly use this ``smart constructor''
    in arithmetic operations.")
  (value-ullong (mod (lifix get) (expt 2 (* 8 (ienv->llong-bytes ienv)))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule value-kind-of-value-ullong-mod
  (equal (value-kind (value-ullong-mod get ienv))
         :ullong)
  :enable value-ullong-mod)

(defruled value-ullong->get-of-value-ullong-mod
  (equal (value-ullong->get (value-ullong-mod get ienv))
         (mod (ifix get) (expt 2 (* 8 (ienv->llong-bytes ienv)))))
  :enable value-ullong-mod)

(defrule well-formed-value-p-of-value-ullong-mod
  (well-formed-value-p (value-ullong-mod get ienv) ienv)
  :enable (value-ullong-mod
           well-formed-value-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define try-value-sint ((get integerp) (ienv ienvp))
  :returns (val valuep)
  :parents (value)
  :short "Construct a signed integer if it would be well-formed,
          or else an unknown value."
  :long
  (xdoc::topstring-p
   "If the intended result of a signed integer operation
    is not representable (i.e. it ``overflows''),
    the behavior is undefined [C17:6.5/5].
    Therefore, this ``smart constructor'' returns the unknown value
    when the intended integer is not representable
    according to the "
   (xdoc::seetopic "implementation-environments"
                   "implementation environment")
   ".")
  (if (signed-byte-p (* 8 (ienv->int-bytes ienv)) (lifix get))
      (value-sint get)
    (value-unknown))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule well-formed-value-p-of-try-value-sint
  (well-formed-value-p (try-value-sint get ienv) ienv)
  :enable (try-value-sint
           well-formed-value-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define try-value-slong ((get integerp) (ienv ienvp))
  :returns (val valuep)
  :parents (value)
  :short "Construct a signed long if it would be well-formed,
          or else an unknown value."
  :long
  (xdoc::topstring-p
   "If the intended result of a signed integer operation
    is not representable (i.e. it ``overflows''),
    the behavior is undefined [C17:6.5/5].
    Therefore, this ``smart constructor'' returns the unknown value
    when the intended integer is not representable
    according to the "
   (xdoc::seetopic "implementation-environments"
                   "implementation environment")
   ".")
  (if (signed-byte-p (* 8 (ienv->long-bytes ienv)) (lifix get))
      (value-slong get)
    (value-unknown))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule well-formed-value-p-of-try-value-slong
  (well-formed-value-p (try-value-slong get ienv) ienv)
  :enable (try-value-slong
           well-formed-value-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define try-value-sllong ((get integerp) (ienv ienvp))
  :returns (val valuep)
  :parents (value)
  :short "Construct a signed long long if it would be well-formed,
          or else an unknown value."
  :long
  (xdoc::topstring-p
   "If the intended result of a signed integer operation
    is not representable (i.e. it ``overflows''),
    the behavior is undefined [C17:6.5/5].
    Therefore, this ``smart constructor'' returns the unknown value
    when the intended integer is not representable
    according to the "
   (xdoc::seetopic "implementation-environments"
                   "implementation environment")
   ".")
  (if (signed-byte-p (* 8 (ienv->llong-bytes ienv)) (lifix get))
      (value-sllong get)
    (value-unknown))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule well-formed-value-p-of-try-value-sllong
  (well-formed-value-p (try-value-sllong get ienv) ienv)
  :enable (try-value-sllong
           well-formed-value-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-promote-value ((val valuep) (ienv ienvp))
  :returns (new-val valuep)
  :short "Perform integer promotion [C17:6.3.1.1/2]."
  :long
  (xdoc::topstring-p
   "Values of non-integer type are not affected.")
  (b* (((ienv ienv) ienv))
    (value-case
      val
      :bool (value-sint val.get)
      :uchar (if (< 1 ienv.int-bytes)
                 (value-sint val.get)
               (value-uint val.get))
      :schar (value-sint val.get)
      :ushort (if (< ienv.short-bytes ienv.int-bytes)
                 (value-sint val.get)
               (value-uint val.get))
      :sshort (value-sint val.get)
      :otherwise (value-fix val))))

;;;;;;;;;;;;;;;;;;;;

(defrule well-formed-value-p-of-integer-promote-value
  (implies (well-formed-value-p val ienv)
           (well-formed-value-p (integer-promote-value val ienv) ienv))
  ;; TODO: why aren't the linear rules sufficient?
  ;;   If it is sensible that linear isn't enough here,
  ;;   perhaps consider forward-chaining these requirements.
  :use ((:instance ienv-requirements (x ienv))
        (:instance value-schar-requirements (x val))
        (:instance value-uchar-requirements (x val)))
  :enable (integer-promote-value
           well-formed-value-p
           signed-byte-p
           unsigned-byte-p
           integer-range-p
           ifix)
  :disable (ienv-requirements
            value-schar-requirements
            value-uchar-requirements))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: consider adding a guard such that the :otherwise cases can be made
;;   unreachable.
(define uaconvert-signed-values ((val1 valuep) (val2 valuep))
  :returns (mv (new-val1 valuep) (new-val2 valuep))
  :parents (uaconvert-values)
  :short "The @(see uaconvert-values) case for two signed integers after
          promotion."
  :long
  (xdoc::topstring-p
   "The type of less integer conversion rank is converted up to the
    greater-ranked type [C17:6.3.1.8/1].")
  (value-case
    val1
    :sint (value-case
            val2
            :slong (mv (value-slong (value-sint->get val1))
                       (value-fix val2))
            :sllong (mv (value-sllong (value-sint->get val1))
                        (value-fix val2))
            :otherwise (mv (value-unknown) (value-unknown)))
    :slong (value-case
             val2
             :sint (mv (value-fix val1)
                       (value-slong (value-sint->get val2)))
             :sllong (mv (value-sllong (value-slong->get val1))
                         (value-fix val2))
             :otherwise (mv (value-unknown) (value-unknown)))
    :sllong (value-case
              val2
              :sint (mv (value-fix val1)
                        (value-sllong (value-sint->get val2)))
              :slong (mv (value-fix val1)
                         (value-sllong (value-slong->get val2)))
              :otherwise (mv (value-unknown) (value-unknown)))
    :otherwise (mv (value-unknown) (value-unknown)))
  :inline t)

;;;;;;;;;;

(defrule well-formed-value-p-of-uaconvert-signed-values.new-val1
  (implies (well-formed-value-p val1 ienv)
           (well-formed-value-p
             (mv-nth 0 (uaconvert-signed-values val1 val2)) ienv))
  :use (:instance ienv-requirements (x ienv))
  :enable (uaconvert-signed-values
           well-formed-value-p
           signed-byte-p
           integer-range-p
           ifix)
  :disable ienv-requirements)

(defrule well-formed-value-p-of-uaconvert-signed-values.new-val2
  (implies (well-formed-value-p val2 ienv)
           (well-formed-value-p
             (mv-nth 1 (uaconvert-signed-values val1 val2)) ienv))
  :use (:instance ienv-requirements (x ienv))
  :enable (uaconvert-signed-values
           well-formed-value-p
           signed-byte-p
           integer-range-p
           ifix)
  :disable ienv-requirements)

;;;;;;;;;;;;;;;;;;;;

;; TODO: consider adding a guard such that the :otherwise cases can be made
;;   unreachable.
(define uaconvert-unsigned-values ((val1 valuep) (val2 valuep))
  :returns (mv (new-val1 valuep) (new-val2 valuep))
  :parents (uaconvert-values)
  :short "The @(see uaconvert-values) case for two unsigned integers after
          promotion."
  :long
  (xdoc::topstring-p
   "The type of less integer conversion rank is converted up to the
    greater-ranked type [C17:6.3.1.8/1].")
  (value-case
    val1
    :uint (value-case
            val2
            :ulong (mv (value-ulong (value-uint->get val1))
                       (value-fix val2))
            :ullong (mv (value-ullong (value-uint->get val1))
                        (value-fix val2))
            :otherwise (mv (value-unknown) (value-unknown)))
    :ulong (value-case
             val2
             :uint (mv (value-fix val1)
                       (value-ulong (value-uint->get val2)))
             :ullong (mv (value-ullong (value-ulong->get val1))
                         (value-fix val2))
             :otherwise (mv (value-unknown) (value-unknown)))
    :ullong (value-case
              val2
              :uint (mv (value-fix val1)
                        (value-ullong (value-uint->get val2)))
              :ulong (mv (value-fix val1)
                         (value-ullong (value-ulong->get val2)))
              :otherwise (mv (value-unknown) (value-unknown)))
    :otherwise (mv (value-unknown) (value-unknown)))
  :inline t)

;;;;;;;;;;

(defrule well-formed-value-p-of-uaconvert-unsigned-values.new-val1
  (implies (well-formed-value-p val1 ienv)
           (well-formed-value-p
             (mv-nth 0 (uaconvert-unsigned-values val1 val2)) ienv))
  :use (:instance ienv-requirements (x ienv))
  :enable (uaconvert-unsigned-values
           well-formed-value-p
           unsigned-byte-p
           integer-range-p
           ifix)
  :disable ienv-requirements)

(defrule well-formed-value-p-of-uaconvert-unsigned-values.new-val2
  (implies (well-formed-value-p val2 ienv)
           (well-formed-value-p
             (mv-nth 1 (uaconvert-unsigned-values val1 val2)) ienv))
  :use (:instance ienv-requirements (x ienv))
  :enable (uaconvert-unsigned-values
           well-formed-value-p
           unsigned-byte-p
           integer-range-p
           ifix)
  :disable ienv-requirements)

;;;;;;;;;;;;;;;;;;;;

;; TODO: consider adding a guard such that the :otherwise cases can be made
;;   unreachable.
(define uaconvert-mixed-values ((signed-val valuep) (unsigned-val valuep) (ienv ienvp))
  :returns (mv (new-signed-val valuep) (new-unsigned-val valuep))
  :parents (uaconvert-values)
  :short "The @(see uaconvert-values) case for one signed integer and one
          unsigned after promotion."
  :long
  (xdoc::topstring-p
   "If the integer conversion rank of the signed integer
    is less than the unsigned integer,
    the signed integer is converted to the unsigned type.
    Otherwise, if the signed type includes all values of the unsigned type,
    the unsigned integer is converted to the signed type.
    Otherwise, convert both values to the unsigned version
    of the signed integer type [C17:6.3.1.8/1].")
  (b* (((ienv ienv) ienv)
       (signed-val (value-fix signed-val))
       (unsigned-val (value-fix unsigned-val)))
    (value-case
      unsigned-val
      :uint
      (value-case
        signed-val
        :sint (mv (value-uint-mod (value-sint->get signed-val) ienv)
                  unsigned-val)
        :slong (if (< ienv.int-bytes ienv.long-bytes)
                   (mv signed-val (value-slong (value-uint->get unsigned-val)))
                 (mv (value-ulong-mod (value-slong->get signed-val) ienv)
                     (value-ulong (value-uint->get unsigned-val))))
        :sllong (if (< ienv.int-bytes ienv.llong-bytes)
                    (mv signed-val (value-sllong (value-uint->get unsigned-val)))
                  (mv (value-ullong-mod (value-sllong->get signed-val) ienv)
                      (value-ullong (value-uint->get unsigned-val))))
        :otherwise (mv (value-unknown) (value-unknown)))
      :ulong
      (value-case
        signed-val
        :sint (mv (value-ulong-mod (value-sint->get signed-val) ienv)
                  unsigned-val)
        :slong (mv (value-ulong-mod (value-slong->get signed-val) ienv)
                   unsigned-val)
        :sllong (if (< ienv.long-bytes ienv.llong-bytes)
                    (mv signed-val (value-sllong (value-ulong->get unsigned-val)))
                  (mv (value-ullong-mod (value-sllong->get signed-val) ienv)
                      (value-ullong (value-ulong->get unsigned-val))))
        :otherwise (mv (value-unknown) (value-unknown)))
      :ullong
      (value-case
        signed-val
        :sint (mv (value-ullong-mod (value-sint->get signed-val) ienv)
                  unsigned-val)
        :slong (mv (value-ullong-mod (value-slong->get signed-val) ienv)
                   unsigned-val)
        :sllong (mv (value-ullong-mod (value-sllong->get signed-val) ienv)
                    unsigned-val)
        :otherwise (mv (value-unknown) (value-unknown)))
      :otherwise (mv (value-unknown) (value-unknown)))))

;;;;;;;;;;

(defrule well-formed-value-p-of-uaconvert-mixed-values.new-val1
  (implies (well-formed-value-p val1 ienv)
           (well-formed-value-p
             (mv-nth 0 (uaconvert-mixed-values val1 val2 ienv)) ienv))
  :use (:instance ienv-requirements (x ienv))
  :enable (uaconvert-mixed-values
           well-formed-value-p
           unsigned-byte-p
           integer-range-p
           ifix)
  :disable ienv-requirements)

(defrule well-formed-value-p-of-uaconvert-mixed-values.new-val2
  (implies (well-formed-value-p val2 ienv)
           (well-formed-value-p
             (mv-nth 1 (uaconvert-mixed-values val1 val2 ienv)) ienv))
  :use (:instance ienv-requirements (x ienv))
  :enable (uaconvert-mixed-values
           well-formed-value-p
           unsigned-byte-p
           signed-byte-p
           integer-range-p
           ifix)
  :disable ienv-requirements)

;;;;;;;;;;;;;;;;;;;;

(define uaconvert-values ((val1 valuep) (val2 valuep) (ienv ienvp))
  :returns (mv (new-val1 valuep)
               (new-val2 valuep))
  :short "Perform the usual arithmetic conversions [C17:6.3.1.8/1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Non-arithmetic types should not be subjected
     to the usual arithmetic conversions;
     we therefore return the unknown type in such cases.")
   (xdoc::p
    "We do not yet model any floating point value,
     so we begin by "
    (xdoc::seetopic "integer-promote-value" "promoting")
    " the integer values.
     When they have the same type, we are done.
     Otherwise, we proceed to the sub-cases."))
  (b* (((when (or (not (value-arithmeticp val1))
                  (not (value-arithmeticp val2))
                  (value-case val1 :unknown)
                  (value-case val2 :unknown)))
        (mv (value-unknown) (value-unknown)))
       (promoted1 (integer-promote-value val1 ienv))
       (promoted2 (integer-promote-value val2 ienv))
       ((when (eq (value-kind promoted1) (value-kind promoted2)))
        (mv promoted1 promoted2))
       ((when (and (value-signed-integerp promoted1)
                   (value-signed-integerp promoted2)))
        (uaconvert-signed-values promoted1 promoted2))
       ((when (and (value-unsigned-integerp promoted1)
                   (value-unsigned-integerp promoted2)))
        (uaconvert-unsigned-values promoted1 promoted2))
       ((when (value-signed-integerp promoted1))
        (uaconvert-mixed-values promoted1 promoted2 ienv))
       ((mv new2 new1) (uaconvert-mixed-values promoted2 promoted1 ienv)))
    (mv new1 new2)))

;;;;;;;;;;

(defrule value-kind-of-uaconvert-values.val2
  (equal (value-kind (mv-nth 1 (uaconvert-values val1 val2 ienv)))
         (value-kind (mv-nth 0 (uaconvert-values val1 val2 ienv))))
  :enable (uaconvert-values
           uaconvert-signed-values
           uaconvert-unsigned-values
           uaconvert-mixed-values))

(defrule well-formed-value-p-of-uaconvert-values.new-val1
  (implies (well-formed-value-p val1 ienv)
           (well-formed-value-p
             (mv-nth 0 (uaconvert-values val1 val2 ienv)) ienv))
  :enable (uaconvert-values
           well-formed-value-p))

(defrule well-formed-value-p-of-uaconvert-values.new-val2
  (implies (well-formed-value-p val2 ienv)
           (well-formed-value-p
             (mv-nth 1 (uaconvert-values val1 val2 ienv)) ienv))
  :enable (uaconvert-values
           well-formed-value-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-to-integer ((val valuep))
  :returns (integer? acl2::maybe-integerp)
  :parents (value)
  :short "Attempt to extract an integer from a value."
  (value-case
   val
   :unknown nil
   :bool val.get
   :uchar val.get
   :schar val.get
   :ushort val.get
   :sshort val.get
   :uint val.get
   :sint val.get
   :ulong val.get
   :slong val.get
   :ullong val.get
   :sllong val.get
   :pointer nil
   :array nil)
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-to-nat ((val valuep))
  :returns (nat? acl2::maybe-natp)
  :parents (value)
  :short "Attempt to extract a natural number from a value."
  (b* ((int (value-to-integer val)))
    (if (natp int)
        int
      nil))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-iconst ((iconst iconstp) (ienv ienvp))
  :returns (val valuep)
  :short "Evaluate an integer constant [C17:6.4.4.1/5]."
  (b* (((iconst iconst) iconst)
       ((ienv ienv) ienv)
       (num (dec/oct/hex-const->value iconst.core)))
    (isuffix-option-case
      iconst.suffix?
      :some (isuffix-case
              iconst.suffix?.val
              :u (cond ((unsigned-byte-p (* 8 ienv.int-bytes) num)
                        (value-uint num))
                       ((unsigned-byte-p (* 8 ienv.long-bytes) num)
                        (value-ulong num))
                       ((unsigned-byte-p (* 8 ienv.llong-bytes) num)
                        (value-ullong num))
                       (t
                        (value-unknown)))
              :l (if (lsuffix-case iconst.suffix?.val.length
                                   '(:locase-l :upcase-l))
                     (cond ((signed-byte-p (* 8 ienv.long-bytes) num)
                            (value-slong num))
                           ((signed-byte-p (* 8 ienv.llong-bytes) num)
                            (value-sllong num))
                           (t (value-unknown)))
                   ;; lsuffix-kind is :locase-ll or :upcase-ll
                   (cond ((signed-byte-p (* 8 ienv.llong-bytes) num)
                          (value-sllong num))
                         (t (value-unknown))))
              :ul (if (lsuffix-case iconst.suffix?.val.length
                                   '(:locase-l :upcase-l))
                     (cond ((unsigned-byte-p (* 8 ienv.long-bytes) num)
                            (value-ulong num))
                           ((unsigned-byte-p (* 8 ienv.llong-bytes) num)
                            (value-ullong num))
                           (t (value-unknown)))
                   ;; lsuffix-kind is :locase-ll or :upcase-ll
                   (cond ((unsigned-byte-p (* 8 ienv.llong-bytes) num)
                          (value-ullong num))
                         (t (value-unknown))))
              :lu (if (lsuffix-case iconst.suffix?.val.length
                                    '(:locase-l :upcase-l))
                      (cond ((unsigned-byte-p (* 8 ienv.long-bytes) num)
                             (value-ulong num))
                            ((unsigned-byte-p (* 8 ienv.llong-bytes) num)
                             (value-ullong num))
                            (t (value-unknown)))
                    ;; lsuffix-kind is :locase-ll or :upcase-ll
                    (cond ((unsigned-byte-p (* 8 ienv.llong-bytes) num)
                           (value-ullong num))
                          (t (value-unknown)))))
      :none (dec/oct/hex-const-case
              iconst.core
              :dec (cond ((signed-byte-p (* 8 ienv.int-bytes) num)
                          (value-sint num))
                         ((signed-byte-p (* 8 ienv.long-bytes) num)
                          (value-slong num))
                         ((signed-byte-p (* 8 ienv.llong-bytes) num)
                          (value-sllong num))
                         (t (value-unknown)))
              :otherwise (cond ((signed-byte-p (* 8 ienv.int-bytes) num)
                                (value-sint num))
                               ((unsigned-byte-p (* 8 ienv.int-bytes) num)
                                (value-uint num))
                               ((signed-byte-p (* 8 ienv.long-bytes) num)
                                (value-slong num))
                               ((unsigned-byte-p (* 8 ienv.long-bytes) num)
                                (value-ulong num))
                               ((signed-byte-p (* 8 ienv.llong-bytes) num)
                                (value-sllong num))
                               ((unsigned-byte-p (* 8 ienv.llong-bytes) num)
                                (value-ullong num))
                               (t (value-unknown)))))))

;;;;;;;;;;;;;;;;;;;;

(defrule well-formed-value-p-of-eval-iconst
  (well-formed-value-p (eval-iconst iconst ienv) ienv)
  :enable (eval-iconst
           well-formed-value-p
           ifix
           nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-const ((const constp) (ienv ienvp))
  :returns (val valuep)
  :short "Evaluate a constant."
  :long
  (xdoc::topstring-p
   "For now, we only evaluate integer constants.")
  (const-case
    const
    :int (eval-iconst const.iconst ienv)
    :float (value-unknown)
    :enum (value-unknown)
    :char (value-unknown)))

;;;;;;;;;;;;;;;;;;;;

(defrule well-formed-value-p-of-eval-const
  (well-formed-value-p (eval-const const ienv) ienv)
  :enable (eval-const
           well-formed-value-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-unop ((op unopp) (val valuep) (ienv ienvp))
  :returns (new-val valuep)
  :short "Apply a unary operator to a value."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('&') operator is documented in [C17:6.5.3.2/3].
     In our approximate representation of values,
     we can only represent null or non-null pointers.
     Since we assume the expression is well-typed,
     we know that a real evaluation
     would be a pointer to an object or function,
     which must be non-null [6.3.2.3/3].
     This seems unlikely to be respected by GCC/Clang dialects,
     so we are conservative and return an unknown pointer in such cases.")
   (xdoc::p
    "The @('+') prefix operator is documented in [C17:6.5.3.3/2]")
   (xdoc::p
    "The @('-') operator is documented in [C17:6.5.3.3/3]")
   (xdoc::p
    "The @('~') operator is documented in [C17:6.5.3.3/4]")
   (xdoc::p
    "The @('!') operator is documented in [C17:6.5.3.3/5]"))
  (unop-case
   op
   :address (if (ienv->gcc/clang ienv)
                (value-pointer (pointer-unknown))
              (value-pointer (pointer-non-null)))
   :plus (if (value-integerp val)
             (integer-promote-value val ienv)
           (value-unknown))
   :minus (b* (((unless (value-integerp val))
                (value-unknown))
               (promoted (integer-promote-value val ienv)))
            (value-case
              promoted
              :uint (value-uint-mod (- promoted.get) ienv)
              :sint (try-value-sint (- promoted.get) ienv)
              :ulong (value-ulong-mod (- promoted.get) ienv)
              :slong (try-value-slong (- promoted.get) ienv)
              :ullong (value-ullong-mod (- promoted.get) ienv)
              :sllong (try-value-sllong (- promoted.get) ienv)
              :otherwise (value-unknown)))
   :bitnot (b* (((unless (value-integerp val))
                 (value-unknown))
                (promoted (integer-promote-value val ienv)))
             (value-case
               promoted
               :uint (value-uint-mod (lognot promoted.get) ienv)
               :sint (try-value-sint (lognot promoted.get) ienv)
               :ulong (value-ulong-mod (lognot promoted.get) ienv)
               :slong (try-value-slong (lognot promoted.get) ienv)
               :ullong (value-ullong-mod (lognot promoted.get) ienv)
               :sllong (try-value-sllong (lognot promoted.get) ienv)
               :otherwise (value-unknown)))
   :lognot (b* (((unless (value-arithmeticp val))
                 (value-unknown))
                ((mv - converted)
                 (uaconvert-values (value-sint 0) val ienv)))
             (value-case
               converted
               :uint (value-sint (acl2::bool->bit
                                   (= 0 (the unsigned-byte converted.get))))
               :sint (value-sint (acl2::bool->bit
                                   (= 0 (the integer converted.get))))
               :ulong (value-sint (acl2::bool->bit
                                    (= 0 (the unsigned-byte converted.get))))
               :slong (value-sint (acl2::bool->bit
                                    (= 0 (the integer converted.get))))
               :ullong (value-sint (acl2::bool->bit
                                     (= 0 (the unsigned-byte converted.get))))
               :sllong (value-sint (acl2::bool->bit
                                     (= 0 (the integer converted.get))))
               :otherwise (value-unknown)))
   ;; We can't add this until we have a chance of representing a size_t
   ;; value. Perhaps we should add a field, `size-t-type` to the
   ;; implementation environment. When the type is not unknown, we could
   ;; evaluate.
   :sizeof (value-unknown)
   :otherwise (value-unknown)))

;;;;;;;;;;;;;;;;;;;;

(defrule well-formed-value-p-of-eval-unop
  (implies (well-formed-value-p val ienv)
           (well-formed-value-p (eval-unop op val ienv) ienv))
  :enable (eval-unop
           well-formed-value-p
           acl2::bool->bit
           signed-byte-p
           integer-range-p
           ifix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-binop ((op binopp) (val1 valuep) (val2 valuep) (ienv ienvp))
  :returns (new-val valuep)
  :short "Apply a binary operator to two values."
  (b* (((mv val1 val2) (uaconvert-values val1 val2 ienv))
       ((when (or (not (value-arithmeticp val1))
                  (not (value-arithmeticp val2))
                  (value-case val1 :unknown)
                  (value-case val2 :unknown)))
        (value-unknown)))
    (binop-case
      op
      ;; 6.5.5/4
      :mul (value-case
             val1
             :uint (value-uint-mod (* val1.get (value-uint->get val2)) ienv)
             :sint (try-value-sint (* val1.get (value-sint->get val2)) ienv)
             :ulong (value-ulong-mod (* val1.get (value-ulong->get val2)) ienv)
             :slong (try-value-slong (* val1.get (value-slong->get val2)) ienv)
             :ullong (value-ulong-mod (* val1.get (value-ullong->get val2)) ienv)
             :sllong (try-value-sllong (* val1.get (value-sllong->get val2)) ienv)
             ;; TODO: prove that uaconverted, arithmetic, and non-unknown gives
             ;;   us one of the above cases.
             ;; :otherwise (prog2$ (impossible) (value-unknown))
             :otherwise (value-unknown)
             )
      ;; TODO
      ;; 6.5.5/5
      :div (value-case
             val1
             :uint (b* ((val2.get (value-uint->get val2))
                        ((when (= 0 (the unsigned-byte val2.get)))
                         (value-unknown)))
                     (value-uint-mod (truncate val1.get val2.get) ienv))
             :sint (b* ((val2.get (value-sint->get val2))
                        ((when (= 0 (the integer val2.get)))
                         (value-unknown)))
                     (try-value-sint (truncate val1.get val2.get) ienv))
             :ulong (b* ((val2.get (value-ulong->get val2))
                         ((when (= 0 (the unsigned-byte val2.get)))
                          (value-unknown)))
                      (value-ulong-mod (truncate val1.get val2.get) ienv))
             :slong (b* ((val2.get (value-slong->get val2))
                         ((when (= 0 (the integer val2.get)))
                          (value-unknown)))
                      (try-value-slong (truncate val1.get val2.get) ienv))
             :ullong (b* ((val2.get (value-ullong->get val2))
                          ((when (= 0 (the unsigned-byte val2.get)))
                           (value-unknown)))
                       (value-ulong-mod (truncate val1.get val2.get) ienv))
             :sllong (b* ((val2.get (value-sllong->get val2))
                          ((when (= 0 (the integer val2.get)))
                           (value-unknown)))
                       (try-value-sllong (truncate val1.get val2.get) ienv))
             :otherwise (value-unknown))
      ;; TODO
      :rem (value-unknown)
      ;; 6.5.6/5
      :add (value-case
             val1
             :uint (value-uint-mod (+ val1.get (value-uint->get val2)) ienv)
             :sint (try-value-sint (+ val1.get (value-sint->get val2)) ienv)
             :ulong (value-ulong-mod (+ val1.get (value-ulong->get val2)) ienv)
             :slong (try-value-slong (+ val1.get (value-slong->get val2)) ienv)
             :ullong (value-ulong-mod (+ val1.get (value-ullong->get val2)) ienv)
             :sllong (try-value-sllong (+ val1.get (value-sllong->get val2)) ienv)
             :otherwise (value-unknown))
      ;; 6.5.6/6
      :sub (value-case
             val1
             :uint (value-uint-mod (- val1.get (value-uint->get val2)) ienv)
             :sint (try-value-sint (- val1.get (value-sint->get val2)) ienv)
             :ulong (value-ulong-mod (- val1.get (value-ulong->get val2)) ienv)
             :slong (try-value-slong (- val1.get (value-slong->get val2)) ienv)
             :ullong (value-ulong-mod (- val1.get (value-ullong->get val2)) ienv)
             :sllong (try-value-sllong (- val1.get (value-sllong->get val2)) ienv)
             :otherwise (value-unknown))
      ;; TODO
      :shl (value-unknown)
      ;; TODO
      :shr (value-unknown)
      ;; TODO
      :lt (value-unknown)
      ;; TODO
      :gt (value-unknown)
      ;; TODO
      :le (value-unknown)
      ;; TODO
      :eq (value-unknown)
      ;; TODO
      :ne (value-unknown)
      ;; TODO
      :bitand (value-unknown)
      ;; TODO
      :bitxor (value-unknown)
      ;; TODO
      :bitior (value-unknown)
      ;; TODO
      :logand (value-unknown)
      ;; TODO
      :logor (value-unknown)
      :otherwise (value-unknown))))

;;;;;;;;;;;;;;;;;;;;

(defrule well-formed-value-p-of-eval-binop
  (implies (well-formed-value-p val ienv)
           (well-formed-value-p (eval-binop op val1 val2 ienv) ienv))
  :enable (eval-binop
           well-formed-value-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define const-eval-expr ((expr exprp) (ienv ienvp))
  :returns (val valuep)
  :short "Perform constant evaluation of an expression."
  :long
  (xdoc::topstring-p
   "If the expression is not in fact constant
    (in the sense that it has a variable,
    unrelated to the syntactic @(see const-expr)),
    the unknown value is returned.")
  (expr-case
    expr
    :const (eval-const expr.const ienv)
    :paren (const-eval-expr expr.inner ienv)
    ;; TODO
    :gensel (value-unknown)
    ;; TODO
    :arrsub (value-unknown)
    :unary (eval-unop expr.op (const-eval-expr expr.arg ienv) ienv)
    ;; TODO
    :sizeof (value-unknown)
    ;; TODO
    :cast (value-unknown)
    :binary (b* ((arg1 (const-eval-expr expr.arg1 ienv))
                 (arg2 (const-eval-expr expr.arg2 ienv)))
              (eval-binop expr.op arg1 arg2 ienv))
    :comma (const-eval-expr expr.next ienv)
    :otherwise (value-unknown))
  :measure (expr-count expr)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule well-formed-value-p-of-const-eval-expr
  (well-formed-value-p (const-eval-expr expr ienv) ienv)
  :induct t
  :enable (const-eval-expr
           well-formed-value-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define const-eval-const-expr ((expr const-exprp) (ienv ienvp))
  :returns (val valuep)
  :short "Perform constant evaluation of a constant expression."
  (const-eval-expr (const-expr->expr expr) ienv))

;;;;;;;;;;;;;;;;;;;;

(defrule well-formed-value-p-of-eval-const-expr
  (well-formed-value-p (const-eval-const-expr expr ienv) ienv)
  :enable (const-eval-const-expr
           well-formed-value-p))
