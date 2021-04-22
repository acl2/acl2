; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "integer-formats")
(include-book "types")

(include-book "kestrel/fty/defbyte" :dir :system)
(include-book "kestrel/std/system/pseudo-event-form-listp" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-integers
  :parents (atc-dynamic-semantics)
  :short "A model of C integers for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a model of the C standard signed and unsigned integer values,
     except @('_Bool') for now,
     based on their "
    (xdoc::seetopic "atc-integer-formats" "format definitions")
    ". As mentioned there, the definitions of values we give here
     should still work if the format definitions are changed.")
   (xdoc::p
    "For each C integer type covered by our model,
     we define ACL2 signed or unsigned integers corresponding to them
     (via @(tsee fty::defbyte)), and
     we define the C values by wrapping those signed or unsigned integers.
     We also define maximum and (for signed) minimum integers,
     prove some linear rules about them,
     and prove rules that provide alternative definitions
     of the signed and unsigned ACL2 integers in terms of minima and maxima.
     This gives us the ability to view the integer ranges
     as ACL2's @(tsee signed-byte-p) and @(tsee unsigned-byte-p) values,
     which is useful for bitwise operations,
     but also as plain integers in certain ranges,
     which should lead to simpler reasoning about ranges.")
   (xdoc::p
    "For the unsigned types,
     we also introduce ACL2 functions
     to turn ACL2 integers into values of those types
     by reducing them modulo one plus the maximum value of the type.
     These functions are used
     to define certain C integer conversions and operations,
     which are modular for unsigned integer types."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-integer-type-string ((type typep))
  :guard (type-integerp type)
  :returns (string stringp)
  :short "Documentation (sub)string that describes a C integer type."
  (b* ((core (case (type-kind type)
               (:char "char")
               (:schar "signed char")
               (:uchar "unsigned char")
               (:sshort "signed short")
               (:ushort "unsigned short")
               (:sint "signed int")
               (:uint "unsigned int")
               (:slong "signed long")
               (:ulong "unsigned long")
               (:sllong "signed long long")
               (:ullong "unsigned long long")
               (t (prog2$ (impossible) "")))))
    (str::cat "type @('" core "')"))
  :guard-hints (("Goal" :in-theory (enable type-integerp
                                           type-unsigned-integerp
                                           type-signed-integerp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-integer-type-fixtype ((type typep))
  :guard (type-integerp type)
  :returns (fixtype symbolp)
  :short "Name of the fixtype of the values of a C integer type."
  :long
  (xdoc::topstring-p
   "This is the symbol in the @('\"C\"') package
    with the same name as the keyword kind of the type
    (e.g. it is @('uchar') for @('(type-uchar)')).")
  (intern$ (symbol-name (type-kind type)) "C"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-integer-type-bits ((type typep))
  :guard (type-integerp type)
  :returns (bits symbolp)
  :short "Name of the nullary function that defines
          the size in bits of a C integer type."
  :long
  (xdoc::topstring-p
   "We take the name of the kind,
    remove the initial @('s') or @('u'),
    and add @('-bits') at the end.")
  (b* ((char/short/int/long/llong
        (if (type-case type :char)
            "CHAR"
          (str::implode (cdr (str::explode (symbol-name (type-kind type))))))))
    (pack char/short/int/long/llong '-bits))
  :prepwork
  ((local (include-book "std/typed-lists/character-listp" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-integer-type-minbits ((type typep))
  :guard (type-integerp type)
  :returns (minbits posp :rule-classes :type-prescription)
  :short "Minimum number of bits that forms a value of a C integer type."
  (case (type-kind type)
    ((:char :schar :uchar) 8)
    ((:sshort :ushort) 16)
    ((:sint :uint) 16)
    ((:slong :ulong) 32)
    ((:sllong :ullong) 64)
    (t (prog2$ (impossible) 1)))
  :guard-hints (("Goal" :in-theory (enable type-integerp
                                           type-unsigned-integerp
                                           type-signed-integerp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-values ((type typep))
  :guard (type-integerp type)
  :returns (event pseudo-event-formp)
  :short "Event to generate the model of the values of a C integer type."

  (b* ((type-string (atc-integer-type-string type))
       (minbits (atc-integer-type-minbits type))
       (signedp (type-signed-integerp type))
       (maxbound (if signedp
                     (1- (expt 2 (1- minbits)))
                   (1- (expt 2 minbits))))
       (minbound (if signedp
                     (- (expt 2 (1- minbits)))
                   0))
       (<type>-bits (atc-integer-type-bits type))
       (<type> (atc-integer-type-fixtype type))
       (<type>p (pack <type> 'p))
       (<type>-integer (pack <type> '-integer))
       (<type>-integerp (pack <type>-integer 'p))
       (<type>-integerp-alt-def (pack <type>-integerp '-alt-def))
       (<type>-integer-fix (pack <type>-integer '-fix))
       (<type>-max (pack <type> '-max))
       (<type>-min (pack <type> '-min))
       (<type>->get (pack <type> '->get))
       (<type>-list (pack <type> '-list))
       (<type>-listp (pack <type>-list 'p))
       (<type>-mod (pack <type> '-mod)))

    `(progn

       ,@(and (type-case type :char)
              (raise "Type ~x0 not supported." type))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (fty::defbyte ,<type>-integer
         :short ,(str::cat "Fixtype of ACL2 integers in the range of "
                           type-string
                           ".")
         :size (,<type>-bits)
         :signed ,signedp
         :pred ,<type>-integerp)

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<type>-max ()
         :returns (,<type>-max integerp :rule-classes :type-prescription)
         :short ,(str::cat "Maximum ACL2 integer value of " type-string ".")
         (1- (expt 2 ,(if signedp
                          `(1- (,<type>-bits))
                        `(,<type>-bits))))
         ///

         (in-theory (disable (:e ,<type>-max)))

         (defrule ,(pack <type>-max '-bound)
           (>= (,<type>-max) ,maxbound)
           :rule-classes :linear
           :enable ,<type>-max
           :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
                 (m ,(if signedp (1- minbits) minbits))
                 (n ,(if signedp `(1- (,<type>-bits)) `(,<type>-bits)))
                 (x 2))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ,@(and
          signedp
          `((define ,<type>-min ()
              :returns (,<type>-min integerp :rule-classes :type-prescription)
              :short ,(str::cat
                       "Minimum ACL2 integer value of " type-string ".")
              (- (expt 2 (1- (,<type>-bits))))
              ///

              (in-theory (disable (:e ,<type>-min)))

              (defrule ,(pack <type>-min '-bound)
                (<= (,<type>-min) ,minbound)
                :rule-classes :linear
                :enable ,<type>-min
                :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
                      (m ,(1- minbits))
                      (n (1- (,<type>-bits)))
                      (x 2))))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defruled ,<type>-integerp-alt-def
         :short ,(str::cat "Alternative definition of @(tsee "
                           (str::downcase-string (symbol-name <type>-integerp))
                           ") as integer range.")
         (equal (,<type>-integerp x)
                (and (integerp x)
                     (<= ,(if signedp `(,<type>-min) 0) x)
                     (<= x (,<type>-max))))
         :enable (,<type>-integerp ,<type>-max ,@(and signedp `(,<type>-min))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (fty::defprod ,<type>
         :short ,(str::cat "Fixtype of values of " type-string ".")
         ((get ,<type>-integer))
         :tag ,(type-kind type)
         :layout :list
         :pred ,<type>p
         ///

         (defrule ,(pack <type>->get '-upper-bound)
           (<= (,<type>->get x) (,<type>-max))
           :rule-classes :linear
           :enable (,<type>->get
                    ,<type>-integer-fix
                    ,<type>-integerp-alt-def))

         ,@(and
            signedp
            `((defrule ,(pack <type>->get '-lower-bound)
                (>= (,<type>->get x) (,<type>-min))
                :rule-classes :linear
                :enable (,<type>->get
                         ,<type>-integer-fix
                         ,<type>-integerp-alt-def)))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<type>-mod ((x integerp))
         :returns (result ,<type>p)
         (,<type> (mod (ifix x) (1+ (,<type>-max))))
         :guard-hints (("Goal" :in-theory (enable ,<type>-integerp-alt-def)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (fty::deflist ,<type>-list
         :short ,(str::cat "Fixtype of lists of values of " type-string ".")
         :elt-type ,<type>
         :true-listp t
         :elementp-of-nil nil
         :pred ,<type>-listp)

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-values-loop ((types type-listp))
  :guard (type-integer-listp types)
  :returns (events pseudo-event-form-listp)
  :short "Events to generate the models of the values of some C integer types."
  (cond ((endp types) nil)
        (t (cons (atc-def-integer-values (car types))
                 (atc-def-integer-values-loop (cdr types))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 (b* ((types (list (type-schar)
                   (type-uchar)
                   (type-sshort)
                   (type-ushort)
                   (type-sint)
                   (type-uint)
                   (type-slong)
                   (type-ulong)
                   (type-sllong)
                   (type-ullong))))
   `(progn ,@(atc-def-integer-values-loop types))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule uchar-max-vs-ushort-max
    :parents (uchar-max ushort-max)
    :short "Relation between
            @('unsigned char') and @('unsigned short') maxima."
    ,(if (= (char-bits) (short-bits))
         '(= (uchar-max) (ushort-max))
       '(< (uchar-max) (ushort-max)))
    :rule-classes :linear
    ,@(if (= (char-bits) (short-bits))
          '(:enable (uchar-max ushort-max)
            :use char-bits-vs-short-bits)
        '(:enable (uchar-max ushort-max char-bits-vs-short-bits)
          :use (:instance
                acl2::expt-is-increasing-for-base->-1
                (m (char-bits)) (n (short-bits)) (x 2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule ushort-max-vs-uint-max
    :parents (ushort-max uint-max)
    :short "Relation between
            @('unsigned short') and @('unsigned int') maxima."
    ,(if (= (short-bits) (int-bits))
         '(= (ushort-max) (uint-max))
       '(< (ushort-max) (uint-max)))
    :rule-classes :linear
    ,@(if (= (short-bits) (int-bits))
          '(:enable (ushort-max uint-max)
            :use short-bits-vs-int-bits)
        '(:enable (ushort-max uint-max short-bits-vs-int-bits)
          :use (:instance
                acl2::expt-is-increasing-for-base->-1
                (m (short-bits)) (n (int-bits)) (x 2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule uint-max-vs-ulong-max
    :parents (uint-max ulong-max)
    :short "Relation between
            @('unsigned int') and @('unsigned long') maxima."
    ,(if (= (int-bits) (long-bits))
         '(= (uint-max) (ulong-max))
       '(< (uint-max) (ulong-max)))
    :rule-classes :linear
    ,@(if (= (int-bits) (long-bits))
          '(:enable (uint-max ulong-max)
            :use int-bits-vs-long-bits)
        '(:enable (uint-max ulong-max int-bits-vs-long-bits)
          :use (:instance
                acl2::expt-is-increasing-for-base->-1
                (m (int-bits)) (n (long-bits)) (x 2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule ulong-max-vs-ullong-max
    :parents (ulong-max ullong-max)
    :short "Relation between
            @('unsigned long') and @('unsigned long long') maxima."
    ,(if (= (long-bits) (llong-bits))
         '(= (ulong-max) (ullong-max))
       '(< (ulong-max) (ullong-max)))
    :rule-classes :linear
    ,@(if (= (long-bits) (llong-bits))
          '(:enable (ulong-max ullong-max)
            :use long-bits-vs-llong-bits)
        '(:enable (ulong-max ullong-max long-bits-vs-llong-bits)
          :use (:instance
                acl2::expt-is-increasing-for-base->-1
                (m (long-bits)) (n (llong-bits)) (x 2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule schar-min-vs-sshort-min
    :parents (schar-min schar-min)
    :short "Relation between
            @('signed char') and @('signed short') minima."
    ,(if (= (char-bits) (short-bits))
         '(= (schar-min) (sshort-min))
       '(>= (schar-min) (sshort-min)))
    :rule-classes :linear
    ,@(if (= (char-bits) (short-bits))
          '(:enable (schar-min sshort-min)
            :use char-bits-vs-short-bits)
        '(:enable (schar-min sshort-min char-bits-vs-short-bits)
          :use (:instance
                acl2::expt-is-increasing-for-base->-1
                (m (char-bits)) (n (short-bits)) (x 2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule sshort-min-vs-sint-min
    :parents (sshort-min sint-min)
    :short "Relation between
            @('signed short') and @('signed int') minima."
    ,(if (= (short-bits) (int-bits))
         '(= (sshort-min) (sint-min))
       '(> (sshort-min) (sint-min)))
    :rule-classes :linear
    ,@(if (= (char-bits) (short-bits))
          '(:enable (sshort-min sint-min)
            :use short-bits-vs-int-bits)
        '(:enable (sshort-min sint-min short-bits-vs-int-bits)
          :use (:instance
                acl2::expt-is-increasing-for-base->-1
                (m (short-bits)) (n (int-bits)) (x 2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule sint-min-vs-slong-min
    :parents (sint-min slong-min)
    :short "Relation between
            @('signed int') and @('signed long') minima."
    ,(if (= (int-bits) (long-bits))
         '(= (sint-min) (slong-min))
       '(> (sint-min) (slong-min)))
    :rule-classes :linear
    ,@(if (= (int-bits) (long-bits))
          '(:enable (sint-min slong-min)
            :use int-bits-vs-long-bits)
        '(:enable (sint-min slong-min int-bits-vs-long-bits)
          :use (:instance
                acl2::expt-is-increasing-for-base->-1
                (m (int-bits)) (n (long-bits)) (x 2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule slong-min-vs-sllong-min
    :parents (slong-min sllong-min)
    :short "Relation between
            @('signed long') and @('signed long long') minima."
    ,(if (= (long-bits) (llong-bits))
         '(= (slong-min) (sllong-min))
       '(> (slong-min) (sllong-min)))
    :rule-classes :linear
    ,@(if (= (long-bits) (llong-bits))
          '(:enable (slong-min sllong-min)
            :use long-bits-vs-llong-bits)
        '(:enable (slong-min sllong-min long-bits-vs-llong-bits)
          :use (:instance
                acl2::expt-is-increasing-for-base->-1
                (m (long-bits)) (n (llong-bits)) (x 2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule schar-max-vs-sshort-max
    :parents (schar-max sshort-max)
    :short "Relation between
            @('signed char') and @('signed short') maxima."
    ,(if (= (char-bits) (short-bits))
         '(= (schar-max) (sshort-max))
       '(< (schar-max) (sshort-max)))
    :rule-classes :linear
    ,@(if (= (char-bits) (short-bits))
          '(:enable (schar-max sshort-max)
            :use char-bits-vs-short-bits)
        '(:enable (schar-max sshort-max char-bits-vs-short-bits)
          :use (:instance
                acl2::expt-is-increasing-for-base->-1
                (m (char-bits)) (n (short-bits)) (x 2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule sshort-max-vs-sint-max
    :parents (sshort-max sint-max)
    :short "Relation between
            @('signed short') and @('signed int') maxima."
    ,(if (= (short-bits) (int-bits))
         '(= (sshort-max) (sint-max))
       '(< (sshort-max) (sint-max)))
    :rule-classes :linear
    ,@(if (= (char-bits) (short-bits))
          '(:enable (sshort-max sint-max)
            :use short-bits-vs-int-bits)
        '(:enable (sshort-max sint-max short-bits-vs-int-bits)
          :use (:instance
                acl2::expt-is-increasing-for-base->-1
                (m (short-bits)) (n (int-bits)) (x 2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule sint-max-vs-slong-max
    :parents (sint-max slong-max)
    :short "Relation between
            @('signed int') and @('signed long') maxima."
    ,(if (= (int-bits) (long-bits))
         '(= (sint-max) (slong-max))
       '(< (sint-max) (slong-max)))
    :rule-classes :linear
    ,@(if (= (int-bits) (long-bits))
          '(:enable (sint-max slong-max)
            :use int-bits-vs-long-bits)
        '(:enable (sint-max slong-max int-bits-vs-long-bits)
          :use (:instance
                acl2::expt-is-increasing-for-base->-1
                (m (int-bits)) (n (long-bits)) (x 2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule slong-max-vs-sllong-max
    :parents (slong-max sllong-max)
    :short "Relation between
            @('signed long') and @('signed long long') maxima."
    ,(if (= (long-bits) (llong-bits))
         '(= (slong-max) (sllong-max))
       '(< (slong-max) (sllong-max)))
    :rule-classes :linear
    ,@(if (= (long-bits) (llong-bits))
          '(:enable (slong-max sllong-max)
            :use long-bits-vs-llong-bits)
        '(:enable (slong-max sllong-max long-bits-vs-llong-bits)
          :use (:instance
                acl2::expt-is-increasing-for-base->-1
                (m (long-bits)) (n (llong-bits)) (x 2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule uchar-max-vs-sint-max
    :parents (uchar-max sint-max)
    :short "Relation between
            @('unsigned char') and @('signed int') maxima."
    ,(if (<= (uchar-max) (sint-max))
         '(<= (uchar-max) (sint-max))
       '(> (uchar-max) (sint-max)))
    :rule-classes ((:linear :trigger-terms ((uchar-max) (sint-max))))
    :enable (uchar-max
             sint-max
             char-bits-vs-short-bits
             short-bits-vs-int-bits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule ushort-max-vs-sint-max
    :parents (ushort-max sint-max)
    :short "Relation between
            @('unsigned short') and @('signed int') maxima."
    ,(if (<= (ushort-max) (sint-max))
         '(<= (ushort-max) (sint-max))
       '(> (ushort-max) (sint-max)))
    :rule-classes ((:linear :trigger-terms ((ushort-max) (sint-max))))
    :enable (ushort-max
             sint-max
             short-bits-vs-int-bits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule uchar-max-vs-slong-max
    :parents (uchar-max slong-max)
    :short "Relation between
            @('unsigned char') and @('signed int') maxima."
    ,(if (<= (uchar-max) (slong-max))
         '(<= (uchar-max) (slong-max))
       '(> (uchar-max) (slong-max)))
    :rule-classes ((:linear :trigger-terms ((uchar-max) (slong-max))))
    :enable (uchar-max
             slong-max
             char-bits-vs-short-bits
             short-bits-vs-int-bits
             int-bits-vs-long-bits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule ushort-max-vs-slong-max
    :parents (ushort-max slong-max)
    :short "Relation between
            @('unsigned char') and @('signed int') maxima."
    ,(if (<= (ushort-max) (slong-max))
         '(<= (ushort-max) (slong-max))
       '(> (ushort-max) (slong-max)))
    :rule-classes ((:linear :trigger-terms ((ushort-max) (slong-max))))
    :enable (ushort-max
             slong-max
             short-bits-vs-int-bits
             int-bits-vs-long-bits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule uint-max-vs-slong-max
    :parents (uint-max slong-max)
    :short "Relation between
            @('unsigned int') and @('signed long') maxima."
    ,(if (<= (uint-max) (slong-max))
         '(<= (uint-max) (slong-max))
       '(> (uint-max) (slong-max)))
    :rule-classes ((:linear :trigger-terms ((uint-max) (slong-max))))
    :enable (uint-max
             slong-max
             int-bits-vs-long-bits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule uchar-max-vs-sllong-max
    :parents (uchar-max sllong-max)
    :short "Relation between
            @('unsigned int') and @('signed long long') maxima."
    ,(if (<= (uchar-max) (sllong-max))
         '(<= (uchar-max) (sllong-max))
       '(> (uchar-max) (sllong-max)))
    :rule-classes ((:linear :trigger-terms ((uchar-max) (sllong-max))))
    :enable (uchar-max
             sllong-max
             char-bits-vs-short-bits
             short-bits-vs-int-bits
             int-bits-vs-long-bits
             long-bits-vs-llong-bits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule ushort-max-vs-sllong-max
    :parents (ushort-max sllong-max)
    :short "Relation between
            @('unsigned int') and @('signed long long') maxima."
    ,(if (<= (ushort-max) (sllong-max))
         '(<= (ushort-max) (sllong-max))
       '(> (ushort-max) (sllong-max)))
    :rule-classes ((:linear :trigger-terms ((ushort-max) (sllong-max))))
    :enable (ushort-max
             sllong-max
             short-bits-vs-int-bits
             int-bits-vs-long-bits
             long-bits-vs-llong-bits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule uint-max-vs-sllong-max
    :parents (uint-max sllong-max)
    :short "Relation between
            @('unsigned int') and @('signed long long') maxima."
    ,(if (<= (uint-max) (sllong-max))
         '(<= (uint-max) (sllong-max))
       '(> (uint-max) (sllong-max)))
    :rule-classes ((:linear :trigger-terms ((uint-max) (sllong-max))))
    :enable (uint-max
             sllong-max
             int-bits-vs-long-bits
             long-bits-vs-llong-bits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defrule ulong-max-vs-sllong-max
    :parents (ulong-max sllong-max)
    :short "Relation between
            @('unsigned long') and @('signed long long') maxima."
    ,(if (<= (ulong-max) (sllong-max))
         '(<= (ulong-max) (sllong-max))
       '(> (ulong-max) (sllong-max)))
    :rule-classes ((:linear :trigger-terms ((ulong-max) (sllong-max))))
    :enable (ulong-max
             sllong-max
             long-bits-vs-llong-bits)))
