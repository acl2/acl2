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

(in-theory (disable pos-listp nat-listp))

(must-fail
 ;;fails:
 (defthm nat-listp-when-pos-listp
   (implies (pos-listp x)
            (nat-listp x))))

;;succeeds:
(help-with
 (defthm nat-listp-when-pos-listp
   (implies (pos-listp x)
            (nat-listp x))))

;; TODO: Have the tool try to combine the 2 steps that it finds
(must-be-redundant ; todo: make a quiet version of this
 ;; The tool finds this proof:
 (defthm nat-listp-when-pos-listp-induct-1
   (implies (and (consp x)
                 (integerp (car x))
                 (< 0 (car x))
                 (nat-listp (cdr x))
                 (pos-listp (cdr x)))
            (nat-listp x))
   :hints (("Goal" :in-theory (enable (:definition nat-listp)))))
 (defthm nat-listp-when-pos-listp
   (implies (pos-listp x)
            (nat-listp x))
   :hints (("Goal" :induct (pos-listp x)
            :in-theory (enable pos-listp)))))
