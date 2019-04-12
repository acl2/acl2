; FTY -- Standard Byte Fixtype Instances
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "defubyte")
(include-book "defsbyte")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defbyte-standard-instances
  :parents (fty-extensions specific-types defbyte)
  :short "Standard fixtypes of unsigned and signed bytes of various sizes,
          with some accompanying theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here `standard' means that these all have uniform structure and naming.
     They are unary counterparts of
     @('(unsigned-byte-p n ...)') and @('(signed-byte-p n ...)'),
     for various values of @('n').")
   (xdoc::p
    "These are all generated via @(tsee defbyte).")
   (xdoc::p
    "If standard (in the sense above) fixtypes
     of unsigned or signed bytes of a certain size
     are needed but are not among the ones defined here,
     they can be added here.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defubyte 1)
(defubyte 2)
(defubyte 3)
(defubyte 4)
(defubyte 8)
(defubyte 16)
(defubyte 32)
(defubyte 64)
(defubyte 128)
(defubyte 256)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsbyte 1)
(defsbyte 2)
(defsbyte 3)
(defsbyte 4)
(defsbyte 8)
(defsbyte 16)
(defsbyte 32)
(defsbyte 64)
(defsbyte 128)
(defsbyte 256)
