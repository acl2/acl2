; String Utilities
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides some utilities for strings.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "characters")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc string-utilities
  :parents (kestrel-utilities)
  :short "Some utilities for @(see strings).")

(define string-list-fix ((x string-listp))
  :returns (fixed-x string-listp)
  :parents (string-utilities)
  :short "Fix to @('nil')-terminated list of @(see strings)."
  (cond ((endp x) nil)
        (t (cons (str-fix (car x))
                 (string-list-fix (cdr x)))))
  ///

  (defrule string-list-fix-when-string-listp
    (implies (string-listp x)
             (equal (string-list-fix x) x))))

(defsection string-list
  :parents (string-utilities)
  :short "<see topic='@(url fty)'>Fixtype</see> of
          @('nil')-terminated lists of @(see strings)."
  :long
  "@(def string-listp)
   @(def string-list-fix)
   @(def string-list-equiv)"
  (fty::deffixtype string-list
    :pred string-listp
    :fix string-list-fix
    :equiv string-list-equiv
    :define t
    :forward t))

(define nonempty-stringp (x)
  :returns (yes/no booleanp)
  :parents (string-utilities)
  :short "Non-empty strings."
  (not (equal (str-fix x) ""))
  ///

  (defrule stringp-when-nonempty-stringp
    (implies (nonempty-stringp x)
             (stringp x))))

(std::deflist nonempty-string-listp (x)
  (nonempty-stringp x)
  :parents (string-utilities)
  :short "@('Nil')-terminated lists of nonempty strings."
  :true-listp t
  :elementp-of-nil nil)

(define nats=>string ((nats (unsigned-byte-listp 8 nats)))
  :returns (string stringp :rule-classes (:rewrite :type-prescription))
  :parents (string-utilities)
  :short "Convert a list of natural numbers below 256
          to the corresponding string."
  (implode (nats=>chars nats)))

(define string=>nats ((string stringp))
  :returns (nats (unsigned-byte-listp 8 nats))
  :parents (string-utilities)
  :short "Convert a string
          to the corresponding list of natural numbers below 256."
  (chars=>nats (explode string))
  ///

  (more-returns
   (nats true-listp
         :name true-listp-of-string=>nats
         :rule-classes :type-prescription)
   (nats nat-listp
         :name nat-listp-of-string=>nats)))
