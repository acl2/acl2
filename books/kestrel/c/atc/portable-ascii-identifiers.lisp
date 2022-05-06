; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../language/keywords")

(include-book "kestrel/std/strings/letter-digit-uscore-chars" :dir :system)
(include-book "std/strings/decimal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-portable-ascii-identifiers
  :parents (atc-implementation)
  :short "Portable ASCII C identifiers used by ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "This notion is defined in the user documentation of ATC (see @(tsee atc)).
     Here we provide code to check whether an ACL2 string
     is a portable ASCII C identifier."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-ident-char-listp ((chs character-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of ACL2 characters is not empty,
          consists only of ASCII letters, digits, and underscores,
          and does not start with a digit."
  :long
  (xdoc::topstring-p
   "Sequences of characters satisfying these conditions
    may be portable ASCII C identifiers,
    provided they are distinct from C keywords.")
  (and (consp chs)
       (str::letter/digit/uscore-charlist-p chs)
       (not (str::dec-digit-char-p (car chs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-ident-stringp ((str stringp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 string is a portable ASCII C identifier."
  (and (atc-ident-char-listp (str::explode str))
       (not (member-equal str *ckeywords*))))
