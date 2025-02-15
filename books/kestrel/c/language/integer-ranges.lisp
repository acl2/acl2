; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)
; Supporting author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "integer-formats")
(include-book "types")

(include-book "kestrel/fty/defbyte" :dir :system)
(include-book "std/system/pseudo-event-form-listp" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "std/typed-lists/atom-listp" :dir :system))

;; to have FTY::DEFLIST generate theorems about NTH:
(local (include-book "std/lists/nth" :dir :system))

;; to have FTY::DEFLIST generate theorems about UPDATE-NTH:
(local (include-book "std/lists/update-nth" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ integer-ranges
  :parents (language)
  :short "Ranges of the integer types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Based on the nullary functions defined in @(see integer-formats),
     for each standard signed and unsigned integer type except @('_Bool'),
     we define the following:")
   (xdoc::ul
    (xdoc::li
     "A fixtype of the ACL2 integers in the range of the types.")
    (xdoc::li
     "A fixtype of the lists of the above ACL2 integers.")
    (xdoc::li
     "A nullary function returning the maximum ACL2 integer in the range.")
    (xdoc::li
     "A nullary function returning the minimum ACL2 integer in the range,
      if the type is signed (if it is unsigned, the minimum is just 0).")
    (xdoc::li
     "Theorems about the above items."))
   (xdoc::p
    "We use @(tsee fty::defbyte) to define the ranges,
     but we also prove theorems providing alternative definitions
     of the signed and unsigned ACL2 integers in terms of minima and maxima.
     This gives us the ability to view the integer ranges
     as ACL2's @(tsee signed-byte-p) and @(tsee unsigned-byte-p) values,
     which is useful for bitwise operations,
     but also as plain integers in certain ranges,
     which should lead to simpler reasoning about ranges.")
   (xdoc::p
    "As mentioned in @(see integer-formats),
     the definitions of ranges we give here
     should still work if the format definitions are changed."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-integer-range ((type typep))
  :guard (type-nonchar-integerp type)
  :returns (event pseudo-event-formp)
  :short "Event to generate fixtypes, functions, and theorems
          for ranges of integer types."

  (b* ((type-string (integer-type-xdoc-string type))
       (minbits (integer-type-minbits type))
       (signedp (type-signed-integerp type))
       (maxbound (if signedp
                     (1- (expt 2 (1- minbits)))
                   (1- (expt 2 minbits))))
       (minbound (if signedp
                     (- (expt 2 (1- minbits)))
                   0))
       (<type>-bits (integer-type-bits-nulfun type))
       (<type> (intern$ (symbol-name (type-kind type)) "C"))
       (<type>-integer (pack <type> '-integer))
       (<type>-integerp (pack <type>-integer 'p))
       (<type>-integerp-alt-def (pack <type>-integerp '-alt-def))
       (<type>-integer-list (pack <type>-integer '-list))
       (<type>-integer-listp (pack <type>-integer-list 'p))
       (<type>-max (pack <type> '-max))
       (<type>-min (pack <type> '-min)))

    `(progn

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (fty::defbyte ,<type>-integer
         :short ,(str::cat "Fixtype of ACL2 integers in the range of "
                           type-string
                           ".")
         :size (,<type>-bits)
         :signed ,signedp
         :pred ,<type>-integerp)

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (fty::deflist ,<type>-integer-list
         :short ,(str::cat "Fixtype of lists of ACL2 integers in the range of "
                           type-string
                           ".")
         :elt-type ,<type>-integer
         :true-listp t
         :elementp-of-nil nil
         :pred ,<type>-integer-listp)

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
         :enable (,<type>-integerp
                  ,<type>-max
                  ,@(and signedp `(,<type>-min))))))

  :guard-hints (("Goal" :in-theory (enable string-listp)))

  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-integer-range-loop ((types type-listp))
  :guard (type-nonchar-integer-listp types)
  :returns (events pseudo-event-form-listp)
  :short "Events to generate fixtypes, functions, and theorems
          for ranges of integer types."
  (cond ((endp types) nil)
        (t (cons (def-integer-range (car types))
                 (def-integer-range-loop (cdr types)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(encapsulate ()
    (local (in-theory (enable nfix
                              not
                              integer-range-p
                              signed-byte-p
                              unsigned-byte-p)))
    ,@(def-integer-range-loop *nonchar-integer-types*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following theorems hold for all bit width values consistent with [C17].
; They are therefore enabled.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule uchar-max-<=-ushort-max
  :parents (uchar-max ushort-max)
  :short "General relation between
          @('unsigned char') and @('unsigned short') maxima."
  (<= (uchar-max) (ushort-max))
  :rule-classes :linear
  :enable (uchar-max ushort-max char-bits-vs-short-bits))

(defrule ushort-max-<=-uint-max
  :parents (ushort-max uint-max)
  :short "General relation between
          @('unsigned short') and @('unsigned int') maxima."
  (<= (ushort-max) (uint-max))
  :rule-classes :linear
  :enable (ushort-max uint-max short-bits-vs-int-bits))

(defrule uint-max-<=-ulong-max
  :parents (uint-max ulong-max)
  :short "General relation between
          @('unsigned int') and @('unsigned long') maxima."
  (<= (uint-max) (ulong-max))
  :rule-classes :linear
  :enable (uint-max ulong-max int-bits-vs-long-bits))

(defrule ulong-max-<=-ullong-max
  :parents (ulong-max ullong-max)
  :short "General relation between
          @('unsigned long') and @('unsigned long long') maxima."
  (<= (ulong-max) (ullong-max))
  :rule-classes :linear
  :enable (ulong-max ullong-max long-bits-vs-llong-bits))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule schar-max-<=-sshort-max
  :parents (schar-max sshort-max)
  :short "General relation between
          @('signed char') and @('signed short') maxima."
  (<= (schar-max) (sshort-max))
  :rule-classes :linear
  :enable (schar-max sshort-max char-bits-vs-short-bits))

(defrule sshort-max-<=-sint-max
  :parents (sshort-max sint-max)
  :short "General relation between
          @('signed short') and @('signed int') maxima."
  (<= (sshort-max) (sint-max))
  :rule-classes :linear
  :enable (sshort-max sint-max short-bits-vs-int-bits))

(defrule sint-max-<=-slong-max
  :parents (sint-max slong-max)
  :short "General relation between
          @('signed int') and @('signed long') maxima."
  (<= (sint-max) (slong-max))
  :rule-classes :linear
  :enable (sint-max slong-max int-bits-vs-long-bits))

(defrule slong-max-<=-sllong-max
  :parents (slong-max sllong-max)
  :short "General relation between
          @('signed long') and @('signed long long') maxima."
  (<= (slong-max) (sllong-max))
  :rule-classes :linear
  :enable (slong-max sllong-max long-bits-vs-llong-bits))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule sshort-min-<=-schar-min
  :parents (sshort-min schar-min)
  :short "General relation between
          @('signed short') and @('signed char') minima."
  (<= (sshort-min) (schar-min))
  :rule-classes :linear
  :enable (sshort-min schar-min char-bits-vs-short-bits))

(defrule sint-min-<=-sshort-min
  :parents (sint-min sshort-min)
  :short "General relation between
          @('signed int') and @('signed short') minima."
  (<= (sint-min) (sshort-min))
  :rule-classes :linear
  :enable (sint-min sshort-min short-bits-vs-int-bits))

(defrule slong-min-<=-sint-min
  :parents (slong-min sint-min)
  :short "General relation between
          @('signed long') and @('signed int') minima."
  (<= (slong-min) (sint-min))
  :rule-classes :linear
  :enable (slong-min sint-min int-bits-vs-long-bits))

(defrule sllong-min-<=-slong-min
  :parents (sllong-min slong-min)
  :short "General relation between
          @('signed long long') and @('signed long') minima."
  (<= (sllong-min) (slong-min))
  :rule-classes :linear
  :enable (sllong-min slong-min long-bits-vs-llong-bits))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The theorems generated by the following code are stronger than the ones above,
; but they hold for some choices of bit width values consistent with [C17].
; The code to generate the rules is the same for all choices,
; but the exact resulting rules depend on some choices.
; The rules are disabled, so it is clear when they are used,
; i.e. when there are dependencies on the choice of values.
; They are collected in the theory 'bit-width-value-choices.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defruled uchar-max-vs-ushort-max
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

(make-event
 `(defruled ushort-max-vs-uint-max
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

(make-event
 `(defruled uint-max-vs-ulong-max
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

(make-event
 `(defruled ulong-max-vs-ullong-max
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defruled schar-min-vs-sshort-min
    :parents (schar-min sshort-min)
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

(make-event
 `(defruled sshort-min-vs-sint-min
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

(make-event
 `(defruled sint-min-vs-slong-min
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

(make-event
 `(defruled slong-min-vs-sllong-min
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defruled schar-max-vs-sshort-max
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

(make-event
 `(defruled sshort-max-vs-sint-max
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

(make-event
 `(defruled sint-max-vs-slong-max
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

(make-event
 `(defruled slong-max-vs-sllong-max
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(defruled uchar-max-vs-sint-max
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

(make-event
 `(defruled ushort-max-vs-sint-max
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

(make-event
 `(defruled uchar-max-vs-slong-max
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

(make-event
 `(defruled ushort-max-vs-slong-max
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

(make-event
 `(defruled uint-max-vs-slong-max
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

(make-event
 `(defruled uchar-max-vs-sllong-max
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

(make-event
 `(defruled ushort-max-vs-sllong-max
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

(make-event
 `(defruled uint-max-vs-sllong-max
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

(make-event
 `(defruled ulong-max-vs-sllong-max
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftheory-static bit-width-value-choices
  '(uchar-max-vs-ushort-max
    ushort-max-vs-uint-max
    uint-max-vs-ulong-max
    ulong-max-vs-ullong-max
    schar-min-vs-sshort-min
    sshort-min-vs-sint-min
    sint-min-vs-slong-min
    slong-min-vs-sllong-min
    schar-max-vs-sshort-max
    sshort-max-vs-sint-max
    sint-max-vs-slong-max
    slong-max-vs-sllong-max
    uchar-max-vs-sint-max
    ushort-max-vs-sint-max
    uchar-max-vs-slong-max
    ushort-max-vs-slong-max
    uint-max-vs-slong-max
    uchar-max-vs-sllong-max
    ushort-max-vs-sllong-max
    uint-max-vs-sllong-max
    ulong-max-vs-sllong-max))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-type-min ((type typep))
  :guard (type-nonchar-integerp type)
  :returns (min integerp)
  :short "Minimum mathematical integer value of an integer type."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we exclude the plain @('char') type, via the guard.
     However, we prefer to keep the name of this function more general,
     in anticipation for extending it to those two types."))
  (cond ((type-case type :schar) (schar-min))
        ((type-case type :uchar) 0)
        ((type-case type :sshort) (sshort-min))
        ((type-case type :ushort) 0)
        ((type-case type :sint) (sint-min))
        ((type-case type :uint) 0)
        ((type-case type :slong) (slong-min))
        ((type-case type :ulong) 0)
        ((type-case type :sllong) (sllong-min))
        ((type-case type :ullong) 0)
        (t (prog2$ (impossible) 0)))
  :guard-hints (("Goal" :in-theory (enable type-nonchar-integerp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-type-max ((type typep))
  :guard (type-nonchar-integerp type)
  :returns (min integerp)
  :short "Maximum mathematical integer value of an integer type."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we exclude the plain @('char') type, via the guard.
     However, we prefer to keep the name of this function more general,
     in anticipation for extending it to those two types."))
  (cond ((type-case type :schar) (schar-max))
        ((type-case type :uchar) (uchar-max))
        ((type-case type :sshort) (sshort-max))
        ((type-case type :ushort) (ushort-max))
        ((type-case type :sint) (sint-max))
        ((type-case type :uint) (uint-max))
        ((type-case type :slong) (slong-max))
        ((type-case type :ulong) (ulong-max))
        ((type-case type :sllong) (sllong-max))
        ((type-case type :ullong) (ullong-max))
        (t (prog2$ (impossible) 0)))
  :guard-hints (("Goal" :in-theory (enable type-nonchar-integerp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-type-rangep ((mathint integerp) (type typep))
  :guard (type-nonchar-integerp type)
  :returns (yes/no booleanp)
  :short "Check if a mathematical integer is in the range of an integer type."
  :long
  (xdoc::topstring
   (xdoc::p
    "Fot now we exclude the plain @('char') type, via the guard.
     However, we prefer to keep the name of this function more general,
     in anticipation for extending it to those two types."))
  (and (<= (integer-type-min type) (ifix mathint))
       (<= (ifix mathint) (integer-type-max type)))
  :hooks (:fix)
  ///

  (defruled integer-type-rangep-to-signed-byte-p
    (implies (and (type-signed-integerp type)
                  (integerp int))
             (equal (integer-type-rangep int type)
                    (signed-byte-p (integer-type-bits type) int)))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             type-signed-integerp
             integer-type-bits
             schar-min
             schar-max
             sshort-min
             sshort-max
             sint-min
             sint-max
             slong-min
             slong-max
             sllong-min
             sllong-max
             ifix
             signed-byte-p
             integer-range-p))

  (defruled integer-type-rangep-to-unsigned-byte-p
    (implies (and (type-unsigned-integerp type)
                  (integerp int))
             (equal (integer-type-rangep int type)
                    (unsigned-byte-p (integer-type-bits type) int)))
    :enable (integer-type-rangep
             integer-type-min
             integer-type-max
             type-unsigned-integerp
             integer-type-bits
             uchar-max
             ushort-max
             uint-max
             ulong-max
             ullong-max
             ifix
             unsigned-byte-p
             integer-range-p)))
