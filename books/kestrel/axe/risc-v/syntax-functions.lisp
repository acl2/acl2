; RISC-V-related syntactic tests
;
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

(include-book "portcullis") ; for the package
(include-book "../dag-arrays")
(include-book "../axe-syntax-functions")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (in-theory (disable aref1 dimensions)))

;; Stops once it finds a non-write.
(defund write-with-addr-and-size-presentp-axe (size-darg addr-darg stat-darg dag-array)
  (declare (xargs :guard (and (or (myquotep size-darg)
                                  (and (natp size-darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 size-darg))))
                              (or (myquotep addr-darg)
                                  (and (natp addr-darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 addr-darg))))
                              (or (myquotep stat-darg)
                                  (and (natp stat-darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 stat-darg)))))
                  :measure (if (consp stat-darg) ;checks for quotep
                               0
                             (+ 1 (nfix stat-darg)))
                  :guard-hints (("Goal" :in-theory (enable acl2::consp-of-cdr)))))
  (if (consp stat-darg) ; tests for quotep
      nil
    (and (mbt (natp stat-darg)) ; for termination
         (let ((expr (aref1 'dag-array dag-array stat-darg)))
           (if (and (consp expr)
                    (eq 'write (car expr)) ; (write n addr val stat)
                    (consp (cdddr (dargs expr))))
               ;; it's a write:
               (if (and (equal (darg2 expr) addr-darg) ; we check the addr first, to fail fast
                        (equal (darg1 expr) size-darg))
                   t ; found a write with the target addr and size
                 (and ; for termination:
                  (mbt (or (quotep (darg4 expr))
                           (and (natp (darg4 expr))
                                (< (darg4 expr) stat-darg))))
                  (write-with-addr-and-size-presentp-axe size-darg addr-darg (darg4 expr) dag-array)))
             ;; not a write:
             nil)))))
