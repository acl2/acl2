; String Utilities
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides utilities for strings.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/strings/case-conversion" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "system/kestrel" :dir :system)
(include-book "characters")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc string-utilities
  :parents (kestrel-utilities)
  :short "Utilities for @(see strings).")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nonempty-stringp (x)
  :returns (yes/no booleanp)
  :parents (string-utilities)
  :short "Recognize non-empty strings."
  (not (equal (str-fix x) ""))
  ///

  (defrule stringp-when-nonempty-stringp
    (implies (nonempty-stringp x)
             (stringp x))))

(std::deflist nonempty-string-listp (x)
  (nonempty-stringp x)
  :parents (string-utilities)
  :short "Recognize @('nil')-terminated lists of nonempty strings."
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define msg-downcase-first ((msg msgp))
  :returns (new-msg msgp :hyp :guard)
  :parents (string-utilities)
  :short "Convert the first character
          of a <see topic='@(url msg)'>structured message</see>
          to lower case."
  (if (stringp msg)
      (str::downcase-first msg)
    (cons (str::downcase-first (car msg))
          (cdr msg))))

(define msg-upcase-first ((msg msgp))
  :returns (new-msg msgp :hyp :guard)
  :parents (string-utilities)
  :short "Convert the first character
          of a <see topic='@(url msg)'>structured message</see>
          to upper case."
  (if (stringp msg)
      (str::upcase-first msg)
    (cons (str::upcase-first (car msg))
          (cdr msg))))
