; C Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2020 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../language/keywords")

(include-book "std/strings/coerce" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/deflist" :dir :system)

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

(define atc-letter/digit/uscore-char-p ((ch characterp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 character is an ASCII letter, digit, or underscore."
  (or (and (standard-char-p ch)
           (alpha-char-p ch))
      (and (digit-char-p ch)
           t)
      (eql ch #\_)))

;;;;;;;;;;;;;;;;;;;;

(std::deflist atc-letter/digit/uscore-char-listp (x)
  (atc-letter/digit/uscore-char-p x)
  :guard (character-listp x)
  :short "Check if a list of ACL2 characters
          only consists of ASCII letters, digits, and underscores."
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;

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
       (atc-letter/digit/uscore-char-listp chs)
       (not (digit-char-p (car chs)))))

;;;;;;;;;;;;;;;;;;;;

(define atc-ident-stringp ((str stringp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 string is a portable ASCII C identifier."
  (and (atc-ident-char-listp (str::explode str))
       (not (member-equal str *ckeywords*))))
