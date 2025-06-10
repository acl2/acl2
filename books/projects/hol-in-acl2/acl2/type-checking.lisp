; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book has miscellaneous useful theorems pertaining to HOL type checks.

(in-package "ZF")

(include-book "hol")
(include-book "alist-subsetp")

(defun arrow-typep (x)
  (declare (xargs :guard t))
  (case-match x
    ((:arrow & &) t)
    (& nil)))

(defun arrow-domain (x)
  (declare (xargs :guard (arrow-typep x)))
  (cadr x))

(defun arrow-range (x)
  (declare (xargs :guard (arrow-typep x)))
  (caddr x))

(defthmz hpp-hap
  (implies (and (force (hpp f hta))
                (force (arrow-typep (hp-type f)))
                (force (hpp x hta))
                (force (equal (hp-type x) (arrow-domain (hp-type f)))))
           (hpp (hap f x) hta))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop)
  :hints (("Goal"
           :in-theory (enable hpp hap hp-type hol-valuep hol-type-eval))))

(defthmz hp-type-hap
  (implies (and (force (weak-hol-typep (hp-type f) t))
                (force (arrow-typep (hp-type f)))
                (force (equal (hp-type x) (arrow-domain (hp-type f)))))
           (equal (hp-type (hap f x))
                  (arrow-range (hp-type f))))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop)
  :hints (("Goal"
           :in-theory (enable hpp hap hp-type hol-valuep hol-type-eval))))

(defthm hol-typep-monotone-for-alist-subsetp
  (implies (and (alist-subsetp hta1 hta2)
                (hol-typep type hta1 groundp))
           (hol-typep type hta2 groundp)))

(defthmd hol-type-eval-monotone-for-alist-subsetp
; Let's keep this disabled until it's clear what form the rule could usefully
; take in general.
  (implies (and (alist-subsetp hta1 hta2)
                (hol-typep type hta1 groundp))
           (equal (hol-type-eval type hta1)
                  (hol-type-eval type hta2)))
  :hints (("Goal" :in-theory (enable hol-type-eval))))

(defthmz hpp-monotone-for-alist-subsetp
  (implies (and (alist-subsetp hta1 hta2)
                (hpp x hta1))
           (hpp x hta2))
  :hints
  (("Goal" :in-theory (enable hol-type-eval-monotone-for-alist-subsetp))))
