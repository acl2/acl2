; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

; This book provides a motivating example for creation of a set-theoretic
; function (set of ordered pairs) from an ACL2 function.  See zify.lisp for a
; macro that implements that idea.

; WARNING: This book is not compatible with zify.lisp, as it defines zfib a bit
; differently.

(include-book "base")

(defun fib (n)
  (declare (xargs :guard (natp n)
                  :guard-hints (("Goal" :in-theory (enable natp)))))
  (cond ((zp n) 0)
        ((= n 1) 1)
        (t (+ (fib (- n 1)) (fib (- n 2))))))

(zsub zfib ()                       ; name, args
      p                             ; x
      (prod2 (omega) (omega))       ; s
      (equal (cdr p) (fib (car p))) ; u
      )

(defthmz relation-p-zfib
  (relation-p (zfib))
  :props (zfc prod2$prop zfib$prop)
  :hints (("Goal" :in-theory (enable relation-p))))

(defthmz funp-zfib
  (funp (zfib))
  :props (zfc prod2$prop zfib$prop)
  :hints (("Goal" :in-theory (enable funp))))

(defthmz in-domain-zfib
  (implies (natp n)
           (in n (domain (zfib))))
  :props (zfc prod2$prop zfib$prop domain$prop)
  :hints (("Goal" :restrict ((in-car-domain-alt ((p (cons n (fib n)))))))))

(defthmz zfib-is-fib
  (implies (natp n)
           (equal (apply (zfib) n)
                  (fib n)))
  :props (zfc prod2$prop zfib$prop domain$prop))

(thm (implies (and (zfc) (prod2$prop) (zfib$prop) (domain$prop))
              (equal (map (zfib) '(0 1 2 3 4 5 6 7))
                     '(0 1 1 2 3 5 8 13))))

(defun map-fib (lst)
  (declare (xargs :guard (nat-listp lst)))
  (cond ((endp lst) nil)
        (t (cons (fib (car lst))
                 (map-fib (cdr lst))))))

(defthmz map-zfib
  (implies (nat-listp lst)
           (equal (map (zfib) lst)
                  (map-fib lst)))
  :props (zfc prod2$prop zfib$prop domain$prop))
