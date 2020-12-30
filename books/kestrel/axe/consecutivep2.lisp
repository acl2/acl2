; Theorems about consecutivep and DAGs
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

;; Rules that mix consecutivep with dags

(include-book "consecutivep")
(include-book "dags")
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))

(defthm consecutivep-of-reverse-list-of-strip-cars
  (implies (pseudo-dagp-aux dag nodenum)
           (consecutivep (reverse-list (strip-cars dag))))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux strip-cars))))

(defthm consecutivep-of-reverse-list-of-strip-cars-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (consecutivep (reverse-list (strip-cars dag))))
  :hints (("Goal" :in-theory (enable pseudo-dagp))))
