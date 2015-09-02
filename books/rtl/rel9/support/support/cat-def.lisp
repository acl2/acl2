; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

;don't include just this book unless you really mean it; this book contains no theorems about cat.  even the
;type-prescription lemma generated about binary-cat in this book is poor.

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund bits (x i j)
  (declare (xargs :guard (and (natp x)
                              (natp i)
                              (natp j))
                  :verify-guards nil))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

#|
;drop?
(defund ocat (x y n)
  (declare (xargs :guard t))
  (+ (* (expt 2 (nfix n)) (nfix x)) (nfix y)))
|#

; return 0 if m or n isn't a nat (change this bevahior?)
(defund binary-cat (x m y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp m) (< 0 m)
                              (integerp n) (< 0 n))
                  :verify-guards nil))
  (if (and (natp m) (natp n))
      (+ (* (expt 2 n) (bits x (1- m) 0))
         (bits y (1- n) 0))
    0))

;; The macro cat

(defun formal-+ (x y)
  ;;an auxiliary function that does not appear in translate-rtl output.
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

(encapsulate
 ()
 (local ; for guard proof below
  (defthm fold-constants-in-+
    (implies (and (syntaxp (quotep x))
                  (syntaxp (quotep y)))
             (equal (+ x y z)
                    (+ (+ x y) z)))))

;;X is a list of alternating data values and sizes.  CAT-SIZE returns the
;;formal sum of the sizes.  X must contain at least 1 data/size pair, but we do
;;not need to specify this in the guard, and leaving it out of that guard
;;simplifies the guard proof.

 (defun cat-size (x)
   ;;an auxiliary function that does not appear in translate-rtl output.
   (declare (xargs :guard (and (true-listp x) (evenp (length x)))))
   (if (endp (cddr x))
       (cadr x)
     (formal-+ (cadr x)
               (cat-size (cddr x))))))

;data and sizes alternate thus: (cat x xsize y ysize z zsize ...)
(defmacro cat (&rest x)
  (declare (xargs :guard (and x (true-listp x) (evenp (length x)))))
  (cond ((endp (cddr x))
         `(bits ,(car x) ,(formal-+ -1 (cadr x)) 0))
        ((endp (cddddr x))
         `(binary-cat ,@x))
        (t
         `(binary-cat ,(car x)
                      ,(cadr x)
                      (cat ,@(cddr x))
                      ,(cat-size (cddr x))))))

;Allows things like (in-theory (disable cat)) to refer to binary-cat.
(add-macro-alias cat binary-cat)

