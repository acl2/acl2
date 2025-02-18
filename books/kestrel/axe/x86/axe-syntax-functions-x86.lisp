; X86-related syntactic tests
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "../dag-arrays")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (in-theory (disable aref1 dimensions)))

;move?
;; Stops once it finds a non-write.
(defund write-with-addr-and-size-presentp-axe (size-darg addr-darg x86-darg dag-array)
  (declare (xargs :guard (and (or (myquotep size-darg)
                                  (and (natp size-darg)
                                       (acl2::pseudo-dag-arrayp 'dag-array dag-array (+ 1 size-darg))))
                              (or (myquotep addr-darg)
                                  (and (natp addr-darg)
                                       (acl2::pseudo-dag-arrayp 'dag-array dag-array (+ 1 addr-darg))))
                              (or (myquotep x86-darg)
                                  (and (natp x86-darg)
                                       (acl2::pseudo-dag-arrayp 'dag-array dag-array (+ 1 x86-darg)))))
                  :measure (if (consp x86-darg) ;checks for quotep
                               0
                             (+ 1 (nfix x86-darg)))))
  (if (consp x86-darg) ; tests for quotep
      nil
    (and (mbt (natp x86-darg)) ; for termination
         (let ((expr (aref1 'dag-array dag-array x86-darg)))
           (if (and (consp expr)
                    (eq 'x::write (car expr)) ; (write n addr val x86)
                    (= 4 (len (dargs expr))))
               ;; it's a write:
               (if (and (equal (darg1 expr) size-darg)
                        (equal (darg2 expr) addr-darg))
                   t
                 (and ; for termination:
                   (mbt (or (quotep (darg4 expr))
                            (and (natp (darg4 expr))
                                 (< (darg4 expr) x86-darg))))
                   (write-with-addr-and-size-presentp-axe size-darg addr-darg (darg4 expr) dag-array)))
             ;; not a write:
             nil)))))

(defund write-nest-with-inner-set-flagp-axe (x86-darg dag-array)
  (declare (xargs :guard (or (myquotep x86-darg)
                             (and (natp x86-darg)
                                  (acl2::pseudo-dag-arrayp 'dag-array dag-array (+ 1 x86-darg))))
                  :measure (if (consp x86-darg) ;checks for quotep
                               0
                             (+ 1 (nfix x86-darg)))))
  (if (consp x86-darg) ; tests for quotep
      nil
    (let ((expr (aref1 'dag-array dag-array x86-darg)))
      (if (and (consp expr)
               (eq 'x::write (car expr)) ; (write n addr val x86)
               (= 4 (len (dargs expr))))
          ;; it's a write:
          (and ; for termination:
            (mbt (and (natp x86-darg)
                      (or (quotep (darg4 expr))
                          (and (natp (darg4 expr))
                               (< (darg4 expr) x86-darg)))))
            (write-nest-with-inner-set-flagp-axe (darg4 expr) dag-array))
        (if (and (consp expr)
                 (eq 'x::set-flag (car expr)) ; (set-flag flag val x86)
                 (= 3 (len (dargs expr))))
            t
          nil)))))


;move
;;todo: should we check for nodenums of constants?
(defund acl2::dargs-equalp (darg1 darg2 dag-array)
  (declare (xargs :guard (and (or (myquotep darg1)
                                  (and (natp darg1)
                                       (acl2::pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg1))))
                              (or (myquotep darg2)
                                  (and (natp darg2)
                                       (acl2::pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg2))))))
           (ignore dag-array))
  (equal darg1 darg2))
