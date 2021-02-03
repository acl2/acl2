; Theorems about remove-guard-holders
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "system/remove-guard-holders-lemmas" :dir :system) ;provides most of what we need

;(include-book "tools/flag" :dir :system)
;(make-flag remove-guard-holders1) ;might want this

(defthm pseudo-termp-of-remove-guard-holders-weak
  (implies (pseudo-termp term)
           (pseudo-termp (remove-guard-holders-weak term))))

(in-theory (disable remove-guard-holders-weak))
