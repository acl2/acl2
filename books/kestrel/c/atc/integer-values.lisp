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

(include-book "kestrel/fty/defbyte" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-integer-values
  :parents (atc-integers)
  :short "C integer values for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a model of the C standard signed and unsigned integer values
     (except @('_Bool') for now),
     based on their "
    (xdoc::seetopic "atc-integer-formats" "format definitions")
    ". As mentioned there, the definitions of values we give here
     should still work if the format definitions are changed.")
   (xdoc::p
    "For each of @('char'), @('short'), @('int'), @('long'), and @('long long'),
     we define ACL2 unsigned and signed integers for them
     (via @(tsee fty::defbyte)), and
     we define C values by wrapping those unsigned and signed integers.
     We also define maximum and (for signed) minimum integers,
     prove some linear rules about them,
     and prove rules that provide alternative definitions
     of the unsigned and signed ACL2 integers in terms of minima and maxima.
     This way we have the ability to view the integer ranges
     as ACL2's @(tsee unsigned-byte-p) and @(tsee signed-byte-p) values,
     which is useful for bitwise operations,
     but also as plain integers in certain ranges,
     which may lead to simpler reasoning about ranges."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ atc-def-integer-values (type)
  (declare (xargs :guard (member-eq type '(:char :short :int :long :llong))))
  :short "Macro to generate the models of the C integer values."

  (b* ((type-string (acl2::string-downcase
                     (if (eq type :llong) "LONG LONG" (symbol-name type))))
       (type-bits (acl2::packn-pos (list type "-BITS") 'atc))
       (type-bits-bound (case type
                          (:char 8)
                          (:short 16)
                          (:int 16)
                          (:long 32)
                          (:llong 64)))
       (utype (acl2::packn-pos (list "U" type) 'atc))
       (stype (acl2::packn-pos (list "S" type) 'atc))
       (utypep (add-suffix utype "P"))
       (stypep (add-suffix stype "P"))
       (utype-list (add-suffix utype "-LIST"))
       (stype-list (add-suffix stype "-LIST"))
       (utype-listp (add-suffix utype "-LISTP"))
       (stype-listp (add-suffix stype "-LISTP"))
       (utype-integer (add-suffix utype "-INTEGER"))
       (stype-integer (add-suffix stype "-INTEGER"))
       (utype-integerp (add-suffix utype "-INTEGERP"))
       (stype-integerp (add-suffix stype "-INTEGERP"))
       (utype-max (add-suffix utype "-MAX"))
       (utype-max-bound (1- (expt 2 type-bits-bound)))
       (stype-min (add-suffix stype "-MIN"))
       (stype-min-bound (- (expt 2 (1- type-bits-bound))))
       (stype-max (add-suffix stype "-MAX"))
       (stype-max-bound (1- (expt 2 (1- type-bits-bound)))))

    `(encapsulate ()

       (local (include-book "arithmetic-3/top" :dir :system))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (fty::defbyte ,utype-integer
         :short ,(concatenate
                  'string
                  "Fixtype of ACL2 integers in the range of @('unsigned "
                  type-string
                  "')s.")
         :size (,type-bits)
         :signed nil
         :pred ,utype-integerp)

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (fty::defbyte ,stype-integer
         :short ,(concatenate
                  'string
                  "Fixtype of ACL2 integers in the range of @('signed "
                  type-string
                  "')s.")
         :size (,type-bits)
         :signed t
         :pred ,stype-integerp)

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,utype-max ()
         :returns (,utype-max integerp :rule-classes :type-prescription)
         :short ,(concatenate 'string
                              "Maximum integer value of C @('unsigned "
                              type-string
                              "')s.")
         (1- (expt 2 (,type-bits)))
         ///

         (in-theory (disable (:e ,utype-max)))

         (defrule ,(add-suffix utype-max "-BOUND")
           (>= (,utype-max) ,utype-max-bound)
           :rule-classes :linear
           :enable ,utype-max
           :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
                 (m ,type-bits-bound) (n (,type-bits)) (x 2)))

         ,@(case type
             (:char nil)
             (:short '((defrule ushort-max->=-uchar-max
                         (>= (ushort-max) (uchar-max))
                         :rule-classes :linear
                         :enable uchar-max
                         :use (:instance
                               acl2::expt-is-weakly-increasing-for-base->-1
                               (m (char-bits)) (n (short-bits)) (x 2)))))
             (:int '((defrule uint-max->=-ushort-max
                       (>= (uint-max) (ushort-max))
                       :rule-classes :linear
                       :enable ushort-max
                       :use (:instance
                             acl2::expt-is-weakly-increasing-for-base->-1
                             (m (short-bits)) (n (int-bits)) (x 2)))))
             (:long '((defrule ulong-max->=-uint-max
                        (>= (ulong-max) (uint-max))
                        :rule-classes :linear
                        :enable uint-max
                        :use (:instance
                              acl2::expt-is-weakly-increasing-for-base->-1
                              (m (int-bits)) (n (long-bits)) (x 2)))))
             (:llong '((defrule ullong-max->=-ulong-max
                         (>= (ullong-max) (ulong-max))
                         :rule-classes :linear
                         :enable ulong-max
                         :use (:instance
                               acl2::expt-is-weakly-increasing-for-base->-1
                               (m (long-bits)) (n (llong-bits)) (x 2)))))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-min ()
         :returns (,stype-min integerp :rule-classes :type-prescription)
         :short ,(concatenate 'string
                              "Minimum integer value of C @('signed "
                              type-string
                              "')s.")
         (- (expt 2 (1- (,type-bits))))
         ///

         (in-theory (disable (:e ,stype-min)))

         (defrule ,(add-suffix stype-min "-BOUND")
           (<= (,stype-min) ,stype-min-bound)
           :rule-classes :linear
           :enable ,stype-min
           :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
                 (m ,(1- type-bits-bound)) (n (1- (,type-bits))) (x 2)))

         ,@(case type
             (:char nil)
             (:short '((defrule sshort-min-<=-schar-min
                         (<= (sshort-min) (schar-min))
                         :rule-classes :linear
                         :enable schar-min
                         :use (:instance
                               acl2::expt-is-weakly-increasing-for-base->-1
                               (m (char-bits)) (n (short-bits)) (x 2)))))
             (:int '((defrule sint-min-<=-sshort-min
                       (<= (sint-min) (sshort-min))
                       :rule-classes :linear
                       :enable sshort-min
                       :use (:instance
                             acl2::expt-is-weakly-increasing-for-base->-1
                             (m (short-bits)) (n (int-bits)) (x 2)))))
             (:long '((defrule slong-min-<=-sint-min
                        (<= (slong-min) (sint-min))
                        :rule-classes :linear
                        :enable sint-min
                        :use (:instance
                              acl2::expt-is-weakly-increasing-for-base->-1
                              (m (int-bits)) (n (long-bits)) (x 2)))))
             (:llong '((defrule sllong-min-<=-slong-min
                         (<= (sllong-min) (slong-min))
                         :rule-classes :linear
                         :enable slong-min
                         :use (:instance
                               acl2::expt-is-weakly-increasing-for-base->-1
                               (m (long-bits)) (n (llong-bits)) (x 2)))))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,stype-max ()
         :returns (,stype-max integerp :rule-classes :type-prescription)
         :short ,(concatenate 'string
                              "Maximumm integer value of C @('signed "
                              type-string
                              "')s.")
         (1- (expt 2 (1- (,type-bits))))
         ///

         (in-theory (disable (:e ,stype-max)))

         (defrule ,(add-suffix stype-max "-BOUND")
           (>= (,stype-max) ,stype-max-bound)
           :rule-classes :linear
           :enable ,stype-max
           :use (:instance acl2::expt-is-weakly-increasing-for-base->-1
                 (m ,(1- type-bits-bound)) (n (1- (,type-bits))) (x 2)))

         ,@(case type
             (:char nil)
             (:short '((defrule sshort-max->=-schar-max
                         (>= (sshort-max) (schar-max))
                         :rule-classes :linear
                         :enable schar-max
                         :use (:instance
                               acl2::expt-is-weakly-increasing-for-base->-1
                               (m (char-bits)) (n (short-bits)) (x 2)))))
             (:int '((defrule sint-max->=-sshort-max
                       (>= (sint-max) (sshort-max))
                       :rule-classes :linear
                       :enable sshort-max
                       :use (:instance
                             acl2::expt-is-weakly-increasing-for-base->-1
                             (m (short-bits)) (n (int-bits)) (x 2)))))
             (:long '((defrule slong-max->=-sint-max
                        (>= (slong-max) (sint-max))
                        :rule-classes :linear
                        :enable sint-max
                        :use (:instance
                              acl2::expt-is-weakly-increasing-for-base->-1
                              (m (int-bits)) (n (long-bits)) (x 2)))))
             (:llong '((defrule sllong-max->=-slong-max
                         (>= (sllong-max) (slong-max))
                         :rule-classes :linear
                         :enable slong-max
                         :use (:instance
                               acl2::expt-is-weakly-increasing-for-base->-1
                               (m (long-bits)) (n (llong-bits)) (x 2)))))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defruled ,(add-suffix utype-integerp "-ALT-DEF")
         :short ,(concatenate 'string
                              "Alternative definition of @(tsee "
                              (acl2::string-downcase
                               (symbol-name utype-integerp))
                              ") as integer range.")
         (equal (,utype-integerp x)
                (and (integerp x)
                     (<= 0 x)
                     (<= x (,utype-max))))
         :enable (,utype-integerp ,utype-max))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defruled ,(add-suffix stype-integerp "-ALT-DEF")
         :short ,(concatenate 'string
                              "Alternative definition of @(tsee "
                              (acl2::string-downcase
                               (symbol-name stype-integerp))
                              ") as integer range.")
         (equal (,stype-integerp x)
                (and (integerp x)
                     (<= (,stype-min) x)
                     (<= x (,stype-max))))
         :enable (,stype-integerp ,stype-min ,stype-max))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (fty::defprod ,utype
         :short ,(concatenate 'string
                              "Fixtype of C @('unsigned "
                              type-string
                              "') values.")
         ((get ,utype-integer))
         :tag ,(intern (symbol-name utype) "KEYWORD")
         :layout :list
         :pred ,utypep)

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (fty::deflist ,utype-list
         :short ,(concatenate 'string
                              "Fixtype of lists of C @('unsigned "
                              type-string
                              "') values.")
         :elt-type ,utype
         :true-listp t
         :elementp-of-nil nil
         :pred ,utype-listp)

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (fty::defprod ,stype
         :short ,(concatenate 'string
                              "Fixtype of C @('signed "
                              type-string
                              "') values.")
         ((get ,stype-integer))
         :tag ,(intern (symbol-name stype) "KEYWORD")
         :layout :list
         :pred ,stypep)

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (fty::deflist ,stype-list
         :short ,(concatenate 'string
                              "Fixtype of lists of C @('signed "
                              type-string
                              "') values.")
         :elt-type ,stype
         :true-listp t
         :elementp-of-nil nil
         :pred ,stype-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(atc-def-integer-values :char)

(atc-def-integer-values :short)

(atc-def-integer-values :int)

(atc-def-integer-values :long)

(atc-def-integer-values :llong)
