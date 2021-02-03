; Rules about IF
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;to be used as an inside-out rule; we need the hyp!
(defthm if-when-not-nil
  (implies test
           (equal (if test x y)
                  x))
  :rule-classes nil)

;to be used as an inside-out rule; we need the hyp!
(defthm if-when-nil
  (implies (not test)
           (equal (if test x y)
                  y))
  :rule-classes nil)
