; Copyright (C) 2025, Matt Kaufmann and Konrad Slind
; Written by Matt Kaufmann and Konrad Slind
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; For background, see file README.txt.

(in-package "HOL")

; (depends-on "eval_poly.defhol")

(include-book "../acl2/theories")

(zf::import-theory eval-poly :hol-name eval_poly)
