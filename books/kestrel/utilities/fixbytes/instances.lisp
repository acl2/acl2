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

(defbyte 1 :signed nil :parents (defbyte-instances))
(defbyte 2 :signed nil :parents (defbyte-instances))
(defbyte 3 :signed nil :parents (defbyte-instances))
(defbyte 4 :signed nil :parents (defbyte-instances))
(defbyte 8 :signed nil :parents (defbyte-instances))
(defbyte 16 :signed nil :parents (defbyte-instances))
(defbyte 32 :signed nil :parents (defbyte-instances))
(defbyte 64 :signed nil :parents (defbyte-instances))
(defbyte 128 :signed nil :parents (defbyte-instances))
(defbyte 256 :signed nil :parents (defbyte-instances))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defbyte 1 :signed t :parents (defbyte-instances))
(defbyte 2 :signed t :parents (defbyte-instances))
(defbyte 3 :signed t :parents (defbyte-instances))
(defbyte 4 :signed t :parents (defbyte-instances))
(defbyte 8 :signed t :parents (defbyte-instances))
(defbyte 16 :signed t :parents (defbyte-instances))
(defbyte 32 :signed t :parents (defbyte-instances))
(defbyte 64 :signed t :parents (defbyte-instances))
(defbyte 128 :signed t :parents (defbyte-instances))
(defbyte 256 :signed t :parents (defbyte-instances))
