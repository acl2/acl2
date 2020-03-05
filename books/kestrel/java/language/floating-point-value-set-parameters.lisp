; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ floating-point-value-set-parameters
  :parents (semantics)
  :short "Floating-point value set parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides the required support for the float and double value sets,
     a Java implementation may provide support for either or both of
     a float-extended-exponent value set and
     a double-extended-exponent value set
     [JLS:4.2.3].
     The support for each extended-exponent value set, if present,
     is described by a parameter @($K$) [JLS:4.2.3].")
   (xdoc::p
    "Thus, we parameterize our formal model of Java with an indication,
     for each extended-exponent value set,
     of whether such a set is supported and, if so, of the value of @($K$).
     We introduce two recognizers for the valid values of these parameters
     (one for each extended-exponent value set),
     and two constrained nullary functions that are the two parameters
     and that are required to have values allowed by the recognizers."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define floatx-param-p (k)
  :returns (yes/no booleanp)
  :short "Recognize the possible parameters that describe
          a Java implementation's support of
          the float-extended-exponent value set [JLS:4.2.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Java implementation
     may support a float-extended-exponent value set or not.
     If it does, an implementation-dependent constant @($K$) [JLS:4.2.3]
     determines the exact values supported.")
   (xdoc::p
    "Our Java formalization is parameterized over the specifics of this support,
     via the value of the nullary function @(tsee floatx-param),
     which is constrained to be either @('nil') (indicating no support)
     or a positive integer that is at least 11 (the value of @($K$))."))
  (or (null k)
      (and (natp k)
           (>= k 11))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection floatx-param
  :short "Parameter that describes the support of
          the float-extended-exponent value set [JLS:4.2.3]."
  :long (xdoc::topstring-@def "floatx-param")

  (encapsulate
    (((floatx-param) => *))
    (local (defun floatx-param () 11))
    (defrule floatx-param-p-of-floatx-param
      (floatx-param-p (floatx-param))))

  (defrule posp-of-floatx-param-when-non-nil
    (implies (floatx-param)
             (posp (floatx-param)))
    :use floatx-param-p-of-floatx-param
    :disable floatx-param-p-of-floatx-param
    :enable floatx-param-p)

  (defrule floatx-param-lower-bound-when-non-nil
    (implies (floatx-param)
             (>= (floatx-param) 11))
    :rule-classes :linear
    :use floatx-param-p-of-floatx-param
    :disable floatx-param-p-of-floatx-param
    :enable floatx-param-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define doublex-param-p (k)
  :returns (yes/no booleanp)
  :short "Recognize the possible parameters that describe
          a Java implementation's support of
          the double-extended-exponent value set [JLS:4.2.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Java implementation
     may support a double-extended-exponent value set or not.
     If it does, an implementation-dependent constant @($K$) [JLS:4.2.3]
     determines the exact values supported.")
   (xdoc::p
    "Our Java formalization is parameterized over the specifics of this support,
     via the value of the nullary function @(tsee doublex-param),
     which is constrained to be either @('nil') (indicating no support)
     or a positive integer that is at least 15 (the value of @($K$))."))
  (or (null k)
      (and (natp k)
           (>= k 15))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection doublex-param
  :short "Parameter that describes the support of
          the double-extended-exponent value set."
  :long (xdoc::topstring-@def "doublex-param")

  (encapsulate
    (((doublex-param) => *))
    (local (defun doublex-param () 15))
    (defrule doublex-param-p-of-doublex-param
      (doublex-param-p (doublex-param))))

  (defrule posp-of-doublex-param-when-non-nil
    (implies (doublex-param)
             (posp (doublex-param)))
    :use doublex-param-p-of-doublex-param
    :disable doublex-param-p-of-doublex-param
    :enable doublex-param-p)

  (defrule doublex-param-lower-bound-when-non-nil
    (implies (doublex-param)
             (>= (doublex-param) 15))
    :rule-classes :linear
    :use doublex-param-p-of-doublex-param
    :disable doublex-param-p-of-doublex-param
    :enable doublex-param-p))
