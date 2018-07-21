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

(defbyte 1 :signed nil)
(defbyte 2 :signed nil)
(defbyte 3 :signed nil)
(defbyte 4 :signed nil)
(defbyte 8 :signed nil)
(defbyte 16 :signed nil)
(defbyte 32 :signed nil)
(defbyte 64 :signed nil)
(defbyte 128 :signed nil)
(defbyte 256 :signed nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defbyte 1 :signed t)
(defbyte 2 :signed t)
(defbyte 3 :signed t)
(defbyte 4 :signed t)
(defbyte 8 :signed t)
(defbyte 16 :signed t)
(defbyte 32 :signed t)
(defbyte 64 :signed t)
(defbyte 128 :signed t)
(defbyte 256 :signed t)
