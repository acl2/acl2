; Rules about IF
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/booleans/bool-fix-def" :dir :system)

;; These rules are for Axe, not ACL2, since ACL2 will split on IFs automatically.

;; to be used as an inside-out rule, we need this phrasing (with the hyp)!
(defthm if-when-not-nil
  (implies test
           (equal (if test then else)
                  then))
  :rule-classes nil)

;; to be used as an inside-out rule, we need this phrasing (with the hyp)!
(defthm if-when-nil
  (implies (not test)
           (equal (if test then else)
                  else))
  :rule-classes nil)
