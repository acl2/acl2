; Fixtypes for Unsigned and Signed Bytes -- Instances
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defbyte")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file uses DEFBYTE to generate fixtypes (and theorems)
; for (lists of) unsigned and signed bytes of several common sizes.
; If fixtypes for (lists of) unsigned or signed bytes for a certain size
; are needed but are not among the ones defined here,
; this file can be easily extended to include such fixtypes.

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defbyte 1 :signed nil :pred ubyte1p :parents (defbyte-instances))
(defbyte 2 :signed nil :pred ubyte2p :parents (defbyte-instances))
(defbyte 3 :signed nil :pred ubyte3p :parents (defbyte-instances))
(defbyte 4 :signed nil :pred ubyte4p :parents (defbyte-instances))
(defbyte 8 :signed nil :pred ubyte8p :parents (defbyte-instances))
(defbyte 16 :signed nil :pred ubyte16p :parents (defbyte-instances))
(defbyte 32 :signed nil :pred ubyte32p :parents (defbyte-instances))
(defbyte 64 :signed nil :pred ubyte64p :parents (defbyte-instances))
(defbyte 128 :signed nil :pred ubyte128p :parents (defbyte-instances))
(defbyte 256 :signed nil :pred ubyte256p :parents (defbyte-instances))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defbyte 1 :signed t :pred sbyte1p :parents (defbyte-instances))
(defbyte 2 :signed t :pred sbyte2p :parents (defbyte-instances))
(defbyte 3 :signed t :pred sbyte3p :parents (defbyte-instances))
(defbyte 4 :signed t :pred sbyte4p :parents (defbyte-instances))
(defbyte 8 :signed t :pred sbyte8p :parents (defbyte-instances))
(defbyte 16 :signed t :pred sbyte16p :parents (defbyte-instances))
(defbyte 32 :signed t :pred sbyte32p :parents (defbyte-instances))
(defbyte 64 :signed t :pred sbyte64p :parents (defbyte-instances))
(defbyte 128 :signed t :pred sbyte128p :parents (defbyte-instances))
(defbyte 256 :signed t :pred sbyte256p :parents (defbyte-instances))
