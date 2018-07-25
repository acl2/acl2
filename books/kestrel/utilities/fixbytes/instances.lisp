; Fixtypes for Unsigned and Signed Bytes -- Instances
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ubyte1")
(include-book "ubyte2")
(include-book "ubyte3")
(include-book "ubyte4")
(include-book "ubyte8")
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

; The files includes by this file use DEFBYTE
; to generate fixtypes (and theorems)
; for (lists of) unsigned and signed bytes of several common sizes.
; If fixtypes for (lists of) unsigned or signed bytes for a certain size
; are needed but are not among the ones already defined here,
; new files can be easily added for such fixtypes,
; and included in this file so they will all appear in the manual.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defbyte-instances
  :parents (defbyte)
  :short "Fixtypes for unsigned and signed bytes of several common sizes,
          and for lists thereof, with accompanying theorems."
  :long
  (xdoc::topapp
   (xdoc::p
    "These are all obtained via @(tsee defbyte).
     If fixtypes for (lists of) unsigned or signed bytes for a certain size
     are needed but are not among the ones defined here,
     they should be added here.")))
