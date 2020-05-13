; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Here is a quick test that we sometimes run.  To see what it generates,
; evaluate (trans1 '(mini-proveall)).

(set-gag-mode :goals)

(mini-proveall)
