; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "implementation-environments/top")

(include-book "std/util/defprojection" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bytes
  :parents (language)
  :short "Bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "In C, a byte consists of @('CHAR_BIT') bits (8 or more)
     [C17:5.2.4.2.1/1] [C23:5.3.5.3.2],
     whose number is captured in @(see uchar-formats) in our formalization.
     Here we provide recognizers and fixers for bytes, and lists thereof,
     parameterized by an implementation environment."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bytep (x (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Recognize a byte."
  :long
  (xdoc::topstring
   (xdoc::p
    "We model a byte as a natural number
     not exceeding the maximum value of @('unsigned char')."))
  (and (natp x)
       (<= x (ienv->uchar-max ienv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define byte-fix ((byte (bytep byte ienv)) (ienv ienvp))
  :returns (fixed-byte (bytep fixed-byte ienv)
                       :hints (("Goal" :in-theory (enable bytep))))
  :short "Fixer for @(tsee bytep)."
  (mbe :logic (if (bytep byte ienv) byte 0)
       :exec byte)

  ///

  (defrule byte-fix-when-bytep
    (implies (bytep byte ienv)
             (equal (byte-fix byte ienv)
                    byte))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist byte-listp (x ienv)
  :guard (ienvp ienv)
  :short "Recognize lists of bytes."
  (bytep x ienv)
  :true-listp t

  ///

  (fty::deffixequiv byte-listp
    :args ((ienv ienvp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection byte-list-fix (x ienv)
  :guard (and (ienvp ienv) (byte-listp x ienv))
  :returns (fixed-bytes (byte-listp fixed-bytes ienv))
  :short "Fixer for @(tsee byte-listp)."
  (byte-fix x ienv)

  ///

  (defrule byte-list-fix-when-byte-listp
    (implies (byte-listp x ienv)
             (equal (byte-list-fix x ienv)
                    x))
    :induct t)

  (fty::deffixequiv byte-list-fix
    :args ((ienv ienvp))))
