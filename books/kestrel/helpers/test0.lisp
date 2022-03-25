; A test of the proof helper tool
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "helper")
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)

(in-theory (disable append))

(must-fail
 ;;fails:
 (defthm consp-of-append
   (implies (consp x)
            (consp (append x y)))))

;;succeeds:
(help-with
 (defthm consp-of-append
   (implies (consp x)
            (consp (append x y)))))

(must-be-redundant
 ;; The tool finds this proof (even though APPEND is disabled, the tool tries
 ;; inducting on it:
 (defthm consp-of-append
   (implies (consp x)
            (consp (binary-append x y)))
   :hints (("Goal" :induct (binary-append x y)
            :in-theory (enable binary-append)))))
