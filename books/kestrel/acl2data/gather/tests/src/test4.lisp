; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This test shows that for :HYP-ALIST, the untranslated hypothesis is included
; in untranslated form as the last field entry.

(in-package "ACL2")

(defthm foo
  (implies (not (equal x nil))
           (not (equal (car x) x))))
