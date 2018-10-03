; Fixtypes for (Lists of) Unsigned and Signed Bytes of Common Sizes
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ubyte1-list")
(include-book "ubyte2-list")
(include-book "ubyte3-list")
(include-book "ubyte4-list")
(include-book "ubyte8-list")
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

; The files (directly and indirectly) included by this file
; use DEFBYTE and DEFBYTELIST to generate fixtypes (and theorems)
; for (lists of) unsigned and signed bytes of several common sizes.
; If fixtypes for (lists of) unsigned or signed bytes for a certain size
; are needed but are not among the ones already defined here,
; new files can be easily added for such fixtypes,
; and included in this file so they will all appear in the manual.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defbyte-instances
  :parents (fty::defbyte)
  :short "Fixtypes for unsigned and signed bytes of several common sizes,
          with accompanying theorems."
  :long
  (xdoc::topapp
   (xdoc::p
    "These are all obtained via @(tsee fty::defbyte).
     If fixtypes for unsigned or signed bytes for a certain size
     are needed but are not among the ones defined here,
     they should be added here.")))

(defxdoc defbytelist-instances
  :parents (fty::defbytelist)
  :short "Fixtypes for true lists of
          unsigned and signed bytes of several common sizes,
          with accompanying theorems."
  :long
  (xdoc::topapp
   (xdoc::p
    "These are all obtained via @(tsee fty::defbytelist).
     If fixtypes for lists of unsigned or signed bytes for a certain size
     are needed but are not among the ones defined here,
     they should be added here.")))
