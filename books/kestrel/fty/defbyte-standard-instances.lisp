; FTY -- Standard Byte Fixtype Instances
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "ubyte1")
(include-book "ubyte2")
(include-book "ubyte3")
(include-book "ubyte4")
(include-book "ubyte8")
(include-book "ubyte11")
(include-book "ubyte16")
(include-book "ubyte32")
(include-book "ubyte64")
(include-book "ubyte128")
(include-book "ubyte256")

(include-book "sbyte1")
(include-book "sbyte2")
(include-book "sbyte3")
(include-book "sbyte4")
(include-book "sbyte8")
(include-book "sbyte16")
(include-book "sbyte32")
(include-book "sbyte64")
(include-book "sbyte128")
(include-book "sbyte256")

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
