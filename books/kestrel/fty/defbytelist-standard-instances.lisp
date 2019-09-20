; FTY -- Standard Byte List Fixtype Instances
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "ubyte1-list")
(include-book "ubyte2-list")
(include-book "ubyte3-list")
(include-book "ubyte4-list")
(include-book "ubyte8-list")
(include-book "ubyte11-list")
(include-book "ubyte16-list")
(include-book "ubyte32-list")
(include-book "ubyte64-list")
(include-book "ubyte128-list")
(include-book "ubyte256-list")

(include-book "sbyte1-list")
(include-book "sbyte2-list")
(include-book "sbyte3-list")
(include-book "sbyte4-list")
(include-book "sbyte8-list")
(include-book "sbyte16-list")
(include-book "sbyte32-list")
(include-book "sbyte64-list")
(include-book "sbyte128-list")
(include-book "sbyte256-list")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defbytelist-standard-instances
  :parents (fty-extensions specific-types defbytelist)
  :short "Standard fixtypes of
          true lists of unsigned and signed bytes of various sizes,
          with some accompanying theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here `standard' means that these all have uniform structure and naming.
     They are unary counterparts of
     @('(unsigned-byte-listp n ...)') and @('(signed-byte-listp n ...)'),
     for various values of @('n').")
   (xdoc::p
    "These are all generated via @(tsee defbytelist).")
   (xdoc::p
    "If standard (in the sense above) fixtypes
     of true lists of unsigned or signed bytes of a certain size
     are needed but are not among the ones defined here,
     they can be added here.")
   (xdoc::p
    "These fixtypes are based on "
    (xdoc::seetopic "defbyte-standard-instances"
                  "the standard fixtypes
                   of unsigned and signed bytes of various sizes")
    " that correspond to the element types of the lists.")))
