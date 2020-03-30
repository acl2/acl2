; Fixtypes for Unsigned and Signed Bytes
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defrule" :dir :system)
; (include-book "kestrel/utilities/event-forms" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc unsigned-and-signed-bytes
  :parents (kestrel-utilities fty::fty)
  :short "<see topic='@(url fty)'>Fixtypes</see> for
          unsigned and signed bytes."
  :long
  "<p>
   Currently fixtypes can only be associated to unary predicates,
   but @(tsee unsigned-byte-p) and @(tsee signed-byte-p) are binary predicates.
   </p>
   <p>
   These utilities provide macros to define unary predicates,
   and associated fixtypes,
   for unsigned and signed bytes of specified sizes,
   as well as for @('nil')-terminated lists thereof.
   These utilities also use the macros to generate fixtypes
   for (lists of) unsigned and signed bytes of several sizes.
   </p>
   <p>
   If fixtypes for (lists of) unsigned or signed bytes for a certain size
   are needed but are not among the ones defined here,
   these utilities can be easily extended to include such fixtypes.
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defubyte-fn ((n posp))
;  :returns (event pseudo-event-formp)
  :verify-guards nil
  :parents (unsigned-and-signed-bytes)
  :short "Event form to introduce fixtypes for
          unsigned bytes of a given size
          and @('nil')-terminated lists thereof."
  :long
  "<p>
   This is used by the @(tsee defubyte) macro.
   The size is @('n').
   </p>
   <p>
   The event introduces a unary predicate, a fixing function, and a fixtype
   for unsigned bytes of size @('n');
   it also introduces a fixtype
   for @('nil')-terminated lists of unsigned bytes of size @('n').
   Each of these items include documentation.
   </p>"
  (b* ((ubyte<n> (packn (list 'ubyte n)))
       (ubyte<n>p (packn (list ubyte<n> 'p)))
       (ubyte<n>-fix (packn (list ubyte<n> '-fix)))
       (ubyte<n>-equiv (packn (list ubyte<n> '-equiv)))
       (ubyte<n>-fix-when-ubyte<n>p (packn
                                     (list ubyte<n>-fix '-when- ubyte<n>p)))
       (ubyte<n>-list (packn (list ubyte<n> '-list)))
       (ubyte<n>-listp (packn (list ubyte<n>-list 'p)))
       (<n>string (coerce (explode-nonnegative-integer n 10 nil) 'string)))
    `(progn
       (define ,ubyte<n>p (x)
         :returns (yes/no booleanp)
         :parents (unsigned-and-signed-bytes)
         :short ,(concatenate 'string
                              "Recognize unsigned bytes of size "
                              <n>string
                              ".")
         (unsigned-byte-p ,n x)
         :no-function t)
       (define ,ubyte<n>-fix ((x ,ubyte<n>p))
         :returns (fixed-x ,ubyte<n>p)
         :parents (unsigned-and-signed-bytes)
         :short ,(concatenate 'string
                              "Fixing function for @(tsee ubyte"
                              <n>string
                              "p).")
         (mbe :logic (if (,ubyte<n>p x) x 0)
              :exec x)
         :no-function t
         ///
         (defrule ,ubyte<n>-fix-when-ubyte<n>p
           (implies (,ubyte<n>p x)
                    (equal (,ubyte<n>-fix x) x))
           :enable ,ubyte<n>p))
       (defsection ,ubyte<n>
         :parents (unsigned-and-signed-bytes)
         :short ,(concatenate 'string
                              "<see topic='@(url fty)'>Fixtype</see> of "
                              "unsigned bytes of size "
                              <n>string
                              ".")
         (fty::deffixtype ,ubyte<n>
           :pred ,ubyte<n>p
           :fix ,ubyte<n>-fix
           :equiv ,ubyte<n>-equiv
           :define t
           :forward t))
       (fty::deflist ,ubyte<n>-list
         :elt-type ,ubyte<n>
         :parents (unsigned-and-signed-bytes)
         :short ,(concatenate 'string
                              "@('nil')-terminated lists of "
                              "unsigned bytes of size "
                              <n>string
                              ".")
         :true-listp t
         :pred ,ubyte<n>-listp))))

(defsection defubyte
  :parents (unsigned-and-signed-bytes)
  :short "Introduce fixtypes for
          unsigned bytes of a given size
          and @('nil')-terminated lists thereof."
  :long "@(def defubyte)"
  (defmacro defubyte (size)
    (declare (xargs :guard (posp size)))
    `(make-event (defubyte-fn ,size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defsbyte-fn ((n posp))
;  :returns (event pseudo-event-formp)
  :verify-guards nil
  :parents (unsigned-and-signed-bytes)
  :short "Event form to introduce fixtypes for
          signed bytes of a given size
          and @('nil')-terminated lists thereof."
  :long
  "<p>
   This is used by the @(tsee defsbyte) macro.
   The size is @('n').
   </p>
   <p>
   The event introduces a unary predicate, a fixing function, and a fixtype
   for signed bytes of size @('n');
   it also introduces a fixtype
   for @('nil')-terminated lists of signed bytes of size @('n').
   Each of these items include documentation.
   </p>"
  (b* ((sbyte<n> (packn (list 'sbyte n)))
       (sbyte<n>p (packn (list sbyte<n> 'p)))
       (sbyte<n>-fix (packn (list sbyte<n> '-fix)))
       (sbyte<n>-equiv (packn (list sbyte<n> '-equiv)))
       (sbyte<n>-fix-when-sbyte<n>p (packn
                                     (list sbyte<n>-fix '-when- sbyte<n>p)))
       (sbyte<n>-list (packn (list sbyte<n> '-list)))
       (sbyte<n>-listp (packn (list sbyte<n>-list 'p)))
       (<n>string (coerce (explode-nonnegative-integer n 10 nil) 'string)))
    `(progn
       (define ,sbyte<n>p (x)
         :returns (yes/no booleanp)
         :parents (unsigned-and-signed-bytes)
         :short ,(concatenate 'string
                              "Recognize signed bytes of size "
                              <n>string
                              ".")
         (signed-byte-p ,n x)
         :no-function t)
       (define ,sbyte<n>-fix ((x ,sbyte<n>p))
         :returns (fixed-x ,sbyte<n>p)
         :parents (unsigned-and-signed-bytes)
         :short ,(concatenate 'string
                              "Fixing function for @(tsee sbyte"
                              <n>string
                              "p).")
         (mbe :logic (if (,sbyte<n>p x) x 0)
              :exec x)
         :no-function t
         ///
         (defrule ,sbyte<n>-fix-when-sbyte<n>p
           (implies (,sbyte<n>p x)
                    (equal (,sbyte<n>-fix x) x))
           :enable ,sbyte<n>p))
       (defsection ,sbyte<n>
         :parents (unsigned-and-signed-bytes)
         :short ,(concatenate 'string
                              "<see topic='@(url fty)'>Fixtype</see> of "
                              "signed bytes of size "
                              <n>string
                              ".")
         (fty::deffixtype ,sbyte<n>
           :pred ,sbyte<n>p
           :fix ,sbyte<n>-fix
           :equiv ,sbyte<n>-equiv
           :define t
           :forward t))
       (fty::deflist ,sbyte<n>-list
         :elt-type ,sbyte<n>
         :parents (unsigned-and-signed-bytes)
         :short ,(concatenate 'string
                              "@('nil')-terminated lists of "
                              "signed bytes of size "
                              <n>string
                              ".")
         :true-listp t
         :pred ,sbyte<n>-listp))))

(defsection defsbyte
  :parents (unsigned-and-signed-bytes)
  :short "Introduce fixtypes for
          signed bytes of a given size
          and @('nil')-terminated lists thereof."
  :long "@(def defsbyte)"
  (defmacro defsbyte (size)
    (declare (xargs :guard (posp size)))
    `(make-event (defsbyte-fn ,size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defubyte 1)
(defubyte 4)
(defubyte 8)
(defubyte 16)
(defubyte 32)
(defubyte 64)
(defubyte 128)
(defubyte 256)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsbyte 1)
(defsbyte 4)
(defsbyte 8)
(defsbyte 16)
(defsbyte 32)
(defsbyte 64)
(defsbyte 128)
(defsbyte 256)
