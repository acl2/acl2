; C Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
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
    "The grammar in [C:6.4.2.1] allows three sets of characters
     usable in C identifiers (besides the ten digits, except at the beginning):
     (i) the lowercase and uppercase ASCII letters and underscore;
     (ii) certain universal characters detailed in [C:D]; and
     (iii) other implementation-defined characters.
     The third set is not portable.
     The second set consists of non-ASCII characters.
     This leaves the first set,
     whose characters correspond to ASCII characters
     (even though the exact set of C source characters
     is implementation-defined [C:5.2.1]):
     identifiers consisting of only this set of characters plus the digits
     are both portable (i.e. implementation-independent)
     and ASCII (at least in the sense of a clear correspondence,
     although in practice many C implementations use (supersets of) ASCII
     as source characters."))
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
   "Sequences of characters satisfying these conditions may be C identifiers,
    provided they are distinct from C keywords.")
  (and (consp chs)
       (atc-letter/digit/uscore-char-listp chs)
       (not (digit-char-p (car chs)))))

;;;;;;;;;;;;;;;;;;;;

(define atc-ident-stringp ((str stringp))
  :returns (yes/no booleanp)
  :short "Check if an ACL2 string is a portable ASCII C identifier."
  :long
  (xdoc::topstring-p
   "This is as defined in the @(tsee atc) user documentation.")
  (and (atc-ident-char-listp (str::explode str))
       (not (member-equal str *ckeywords*))))
