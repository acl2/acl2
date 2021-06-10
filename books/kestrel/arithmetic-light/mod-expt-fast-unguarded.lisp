; A version of mod-expt-fast with a guard of t
;
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "arithmetic-3/floor-mod/mod-expt-fast" :dir :system)
(include-book "kestrel/axe/unguarded-built-ins" :dir :system) ;todo: reduce

;; This can be useful in evaluators, such as the ones used in Axe.
(defund mod-expt-fast-unguarded (a i n)
  (declare (xargs :guard t))
  (if (and (rationalp a)
           (natp i)
           (rationalp n)
           (not (equal n 0))
           (not (and (equal a 0) (equal i 0))))
      (mod-expt-fast a i n)
    (mod-unguarded (expt-unguarded a i) n)))

(defthm mod-expt-fast-unguarded-correct
  (equal (mod-expt-fast-unguarded a i n)
         (mod-expt-fast a i n))
  :hints (("Goal" :in-theory (enable mod-expt-fast-unguarded
                                     mod-expt-fast))))
