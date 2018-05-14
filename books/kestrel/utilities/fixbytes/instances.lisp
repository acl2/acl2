; Fixtypes for Unsigned and Signed Bytes -- Instances
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "macros")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file uses DEFUBYTE and DEFSBYTE to generate fixtypes (and theorems)
; for (lists of) unsigned and signed bytes of several common sizes.
; If fixtypes for (lists of) unsigned or signed bytes for a certain size
; are needed but are not among the ones defined here,
; this file can be easily extended to include such fixtypes.

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
