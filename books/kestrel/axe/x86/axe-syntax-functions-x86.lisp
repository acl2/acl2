; X86-related syntactic tests
;
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "../dag-arrays")
(include-book "../axe-syntax-functions")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (in-theory (disable aref1 dimensions)))

;; Stops once it finds a non-write.
(defund write-with-addr-and-size-presentp-axe (size-darg addr-darg x86-darg dag-array)
  (declare (xargs :guard (and (or (myquotep size-darg)
                                  (and (natp size-darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 size-darg))))
                              (or (myquotep addr-darg)
                                  (and (natp addr-darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 addr-darg))))
                              (or (myquotep x86-darg)
                                  (and (natp x86-darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 x86-darg)))))
                  :measure (if (consp x86-darg) ;checks for quotep
                               0
                             (+ 1 (nfix x86-darg)))
                  :guard-hints (("Goal" :in-theory (enable acl2::consp-of-cdr)))))
  (if (consp x86-darg) ; tests for quotep
      nil
    (and (mbt (natp x86-darg)) ; for termination
         (let ((expr (aref1 'dag-array dag-array x86-darg)))
           (if (and (consp expr)
                    (eq 'x::write (car expr)) ; (write n addr val x86)
                    (consp (cdddr (dargs expr))))
               ;; it's a write:
               (if (and (equal (darg2 expr) addr-darg) ; we check the addr first, to fail fast
                        (equal (darg1 expr) size-darg))
                   t ; found a write with the target addr and size
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
                                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 x86-darg))))
                  :measure (if (consp x86-darg) ;checks for quotep
                               0
                             (+ 1 (nfix x86-darg)))
                  :guard-hints (("Goal" :in-theory (enable acl2::consp-of-cdr)))))
  (if (consp x86-darg) ; tests for quotep
      nil
    (let ((expr (aref1 'dag-array dag-array x86-darg)))
      (if (and (consp expr)
               (eq 'x::write (car expr)) ; (write n addr val x86)
               (consp (cdddr (dargs expr)))
               )
          ;; it's a write, so continue looking:
          (and ; for termination:
           (mbt (and (natp x86-darg)
                     (or (quotep (darg4 expr))
                         (and (natp (darg4 expr))
                              (< (darg4 expr) x86-darg)))))
           (write-nest-with-inner-set-flagp-axe (darg4 expr) dag-array))
        ;; we've found the core of the write-nest, so check if it is a call of set-flag:
        (and (consp expr)
             (eq 'x::set-flag (car expr)) ; (set-flag flag val x86)
             ;; (= 3 (len (dargs expr))) ; probably no need to check the arity
             )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; darg1 and darg2 are addresses (such as in calls of write)
(defund addresses-out-of-orderp (darg1 darg2 dag-array)
  (declare (xargs :guard (and (or (myquotep darg1)
                                  (and (natp darg1)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg1))))
                              (or (myquotep darg2)
                                  (and (natp darg2)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg2)))))
                  ;:guard-hints (("Goal" :in-theory (enable len)))
                  ))
  (if (consp darg1) ;tests for quotep
      (if (consp darg2) ;tests for quotep
          ;; both are constants:
          (let ((val1 (unquote darg1))
                (val2 (unquote darg2)))
            (if (not (and (integerp val1) ; might be a negative offset (e.g., from RSP)
                          (integerp val2)))
                nil ; be tolerant, so we don't loop
              (< val2 val1) ; if val2 comes first, they are out-of-order
              ))
        ;; only darg1 is a constant:
        nil)
    (if (consp darg2) ; tests for quotep
        ;; only darg2 is a constant:
        t ; they should be switched to put the constant first
      ;; they are both nodenums:
      (let* ((expr1 (aref1 'dag-array dag-array darg1))
             (expr2 (aref1 'dag-array dag-array darg2)))
        (mv-let (offset1 base1)
          (if (not (and (consp expr1)
                        (eq 'binary-+ (ffn-symb expr1))
                        (consp (cdr (dargs expr1)))))
              (mv 0 darg1)
            (let ((maybe-offset (darg1 expr1)))
              (if (not (acl2::darg-quoted-integerp maybe-offset))
                  (mv 0 darg1)
                ;; (binary-+ '<offset> <base>):
                (mv (unquote maybe-offset)
                    (darg2 expr1)))))
          (mv-let (offset2 base2)
            (if (not (and (consp expr2)
                          (eq 'binary-+ (ffn-symb expr2))
                          (consp (cdr (dargs expr2)))))
                (mv 0 darg2)
              (let ((maybe-offset (darg1 expr2)))
                (if (not (acl2::darg-quoted-integerp maybe-offset))
                    (mv 0 darg2)
                  ;; (binary-+ '<offset> <base>):
                  (mv (unquote maybe-offset)
                      (darg2 expr2)))))
            ;; first compare the bases:
            (if (lighter-dargp base2 base1)
                t
              (if (lighter-dargp base1 base2)
                  nil
                ;; the bases are the same, so check the offsets:
                (< offset2 offset1) ; todo: add type decl
                ))))))))
