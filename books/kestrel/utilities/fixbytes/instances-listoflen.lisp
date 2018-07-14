; Fixtypes for fixed-length lists of unsigned 8-bit bytes -- Instances
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author:
; Eric McCarthy at Kestrel Institute (last name at kestrel.edu).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defbytelistoflen")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file uses DEFBYTELISTOFLEN to generate fixtypes (and theorems)
; for fixed-length lists of unsigned 8-bit bytes.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Users of defbytelistoflen might wish to create such fixtypes in their
; own packages.  E.g., ETHEREUM::B32

; Currently this is a single example.

(defbytelistoflen BYTES 20)
