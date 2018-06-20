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

(defbyte 1 :unsigned)
(defbyte 2 :unsigned)
(defbyte 3 :unsigned)
(defbyte 4 :unsigned)
(defbyte 8 :unsigned)
(defbyte 16 :unsigned)
(defbyte 32 :unsigned)
(defbyte 64 :unsigned)
(defbyte 128 :unsigned)
(defbyte 256 :unsigned)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defbyte 1 :signed)
(defbyte 2 :signed)
(defbyte 3 :signed)
(defbyte 4 :signed)
(defbyte 8 :signed)
(defbyte 16 :signed)
(defbyte 32 :signed)
(defbyte 64 :signed)
(defbyte 128 :signed)
(defbyte 256 :signed)
