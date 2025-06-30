; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book has miscellaneous useful theorems for reasoning about translations
; of HOL definitions.

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

; The hypotheses were originally forced, but that cause complications for
; ../examples/eval-poly-support.lisp.

  (implies (and (hpp f hta)
                (arrow-typep (hp-type f))
                (hpp x hta)
                (equal (hp-type x) (arrow-domain (hp-type f))))
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

; The following were developed in support of
; ../examples/eval-poly-support.lisp.  Many are generally applicable.  Others
; could presumably be automatically generated based on the types we've seen.

(defthm natp-+
  (implies (and (natp x) (natp y))
           (natp (+ x y))))

(defthm natp-*
  (implies (and (natp x) (natp y))
           (natp (* x y))))

(defthm natp-expt
  (implies (and (natp x) (natp y))
           (natp (expt x y))))

(defthm hp+-reduction
  (implies (and (alist-subsetp (hta0) hta)
                (force (hpp x hta))
                (force (equal (hp-type x) :num))
                (force (hpp y hta))
                (force (equal (hp-type y) :num) ))
           (equal (hp+ x y)
                  (make-hp (+ (hp-value x) (hp-value y))
                           :num))))

(defthm hp*-reduction
  (implies (and (alist-subsetp (hta0) hta)
                (force (hpp x hta))
                (force (equal (hp-type x) :num))
                (force (hpp y hta))
                (force (equal (hp-type y) :num) ))
           (equal (hp* x y)
                  (make-hp (* (hp-value x) (hp-value y))
                           :num))))

(defthm hons-assoc-equal-num
  (implies (alist-subsetp (hta0) hta)
           (equal (hons-assoc-equal :num hta)
                  (cons :num (omega)))))

(defthmz hpp-restrict
  (implies (and (hpp x hta)
                (equal (hp-type x)
                       (list :list alpha))
                (not (equal (car x) 0)))
           (hpp (cons (restrict (car x) (+ -1 (domain (car x))))
                      (list :list alpha))
                hta))
  :hints (("Goal"
           :restrict ((subset-transitivity ((y (image (car x))))))
           :expand ((hol-type-eval (cdr x) hta))
           :in-theory (enable hpp hol-valuep hol-type-eval)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop
              finseqs$prop))

(defthmz consp-finseq-to-list

; This is really too specific to belong here instead of in the book
; ../examples/eval-poly-support.lisp where it originally appeared.  But we
; put it here to suggest that eventually it be replaced by the following
; generalization.

;     (implies (and (alist-subsetp (hta0) hta)
;                   (hpp x hta)
;                   (hol-list-typep (hp-type x))
;                   (hol-hash-typep (hol-list-element-type (hp-type x))))
;              (equal (consp (finseq-to-list (car x))) ; (car x) is (hp-value x)
;                     (not (equal x (hp-nil (hol-list-element-type (hp-type x)))))))

  (implies (and (alist-subsetp (hta0) hta)
                (hpp x hta)
                (equal (cdr x) ; (hp-type x)
                       '(:list (:hash :num :num))))
           (equal (consp (finseq-to-list (car x))) ; (car x) is (hp-value x)
                  (not (equal x (hp-nil '(:hash :num :num))))))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop
              finseqs$prop)
  :hints (("Goal"
           :in-theory (enable hpp hol-valuep hol-type-eval))))

(defthmz hpp-implies-natp
  (implies (and (alist-subsetp (hta0) hta)
                (hpp x hta)
                (equal (cdr x) :num))
           (natp (car x)))
  :hints (("Goal" :in-theory (enable hpp hol-valuep hol-type-eval)))
  :rule-classes :forward-chaining)

(defthmz hpp-natp
  (implies (and (alist-subsetp (hta0) hta)
                (force (natp x)))
           (hpp (cons x :num)
                hta))
  :hints (("Goal" :in-theory (enable hpp hol-valuep hol-type-eval))))

(defthmz hpp-funp
  (implies (and (hpp x hta)
                (equal (cdr x) (cons :list rest)))
           (and (funp (car x))
                (natp (domain (car x)))))
  :hints (("Goal"
           :in-theory (enable hpp hol-valuep hol-type-eval)
           :expand ((hol-type-eval (cdr x) hta))))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop)
  :rule-classes :forward-chaining)

; The following "type-i" (i from 1 to 6) aren't great names and might be
; renamed.  They were developed in support of hol::hol{eval_poly}1-alt in
; ../examples/eval-poly-support.lisp.

(defthmz type-1
  (implies (and (equal (cdr x)
                       '(:list (:hash :num :num)))
                (force (< 0 (domain (car x))))
                (force (hpp x hta)))
           (equal (cdr (hp-hash-car (hp-list-car x)))
                  :num))
  :hints (("Goal"
           :in-theory
           (enable hol-type-eval hp-hash-car hp-list-car)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop))

(defthmz type-2-lemma-1
  (implies (and (funp fn)
                (subset (image fn) s)
                (in i (domain fn)))
           (in (apply fn i) s))
  :props (zfc prod2$prop domain$prop inverse$prop diff$prop)
  :rule-classes nil)

(defthmz type-2-lemma
  (implies (and (funp fn)
                (posp (domain fn))
                (subset (image fn) (prod2 (omega) (omega)))
                (natp i)
                (< i (domain fn)))
           (natp (cdr (apply fn i))))
  :hints (("Goal"
           :use ((:instance type-2-lemma-1
                            (s (prod2 (omega) (omega)))))
           :in-theory (disable subset-preserves-in-2)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop diff$prop))

(defthmz type-2
  (implies (and (alist-subsetp (hta0) hta)
                (equal (cdr x)
                       '(:list (:hash :num :num)))
                (force (< 0 (domain (car x))))
                (force (hpp x hta)))
           (hpp (hp-hash-cdr (hp-list-car x))
                hta))
  :hints (("Goal"
           :in-theory
           (enable hpp hol-valuep hol-type-eval hp-hash-cdr hp-list-car)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop diff$prop))

(defthmz type-3
  (implies (and (equal (cdr x)
                       '(:list (:hash :num :num)))
                (force (< 0 (domain (car x))))
                (force (hpp x hta)))
           (equal (cdr (hp-hash-cdr (hp-list-car x)))
                  :num))
  :hints (("Goal"
           :in-theory (enable hol-type-eval hp-hash-cdr hp-list-car)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop))

(defthmz type-4-lemma
  (implies (and (funp fn)
                (posp (domain fn))
                (subset (image fn) (prod2 (omega) (omega)))
                (natp i)
                (< i (domain fn)))
           (natp (car (apply fn i))))
  :hints (("Goal"
           :use ((:instance type-2-lemma-1
                            (s (prod2 (omega) (omega)))))
           :in-theory (disable subset-preserves-in-2)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop diff$prop))

(defthmz type-4
; !! We can surely do better here, probably by splitting into two lemmas: one
; that takes the hp-list-car, and one that takes the hp-hash-car.
  (implies (and (alist-subsetp (hta0) hta)
                (equal (cdr x)
                       '(:list (:hash :num :num)))
                (force (< 0 (domain (car x))))
                (force (hpp x hta)))
           (hpp (hp-hash-car (hp-list-car x))
                hta))
  :hints (("Goal"
           :in-theory
           (enable  hpp hol-valuep hol-type-eval
                   hp-hash-car hp-list-car)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop diff$prop))

(defthmz type-5
  (implies (and (equal (car (cdr x)) :list)
                (force (hpp x hta)))
           (hpp (hp-list-cdr x)
                hta))
  :hints (("Goal"
           :expand ((hol-type-eval (cdr x) hta))
           :in-theory (enable hpp hol-valuep hol-type-eval hp-list-cdr)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop diff$prop
              restrict$prop))

(defthmz type-6
  (implies (and (equal (car (cdr x)) :list)
                (force (hpp x hta)))
           (equal (cdr (hp-list-cdr x))
                  (cdr x)))
  :hints (("Goal"
           :expand ((hol-typep (cdr x) hta t))
           :in-theory (enable hpp hol-type-eval hol-valuep hp-list-cdr)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop))

(defthmz type-7
  (implies (and (< 0 (domain (car y)))
                (equal (car (cdr y)) :list)
                (force (hpp y hta)))
           (hpp (hp-list-car y) hta))
  :hints (("Goal"
           :expand ((HOL-TYPEP (CDR Y) HTA T))
           :in-theory (enable hpp hol-valuep hol-type-eval hp-list-car)))
  :props (zfc prod2$prop inverse$prop diff$prop domain$prop finseqs$prop))

(defthmz type-8
  (implies (and (< 0 (domain (car y)))
                (equal (cdr y) '(:list (:hash :num :num)))
                (force (hpp y hta)))
           (equal (cdr (hp-list-car y))
                  '(:hash :num :num)))
  :hints (("Goal"
           :in-theory (enable hpp hol-valuep hol-type-eval hp-list-car)))
  :props (zfc prod2$prop inverse$prop diff$prop domain$prop finseqs$prop))

(defthmz hp-type-bool-cases
  (implies (and (alist-subsetp (hta0) hta)
                (hpp x hta)
                (equal (hp-type x) :bool))
           (or (equal x (hp-true))
               (equal x (hp-false))))
  :hints (("Goal" :in-theory (enable hpp hol-valuep hol-type-eval)))
  :rule-classes nil)

(defthmz type-9-lemma
  (implies (and (subset (image fn) (prod2 s1 s2))
                (funp fn)
                (in i (domain fn)))
           (consp (apply fn i)))
  :hints (("Goal"
           :use ((:instance in-apply-image
                            (x i)
                            (r fn)))
           :in-theory (disable in-apply-image in-apply-image-force)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz type-9
  (let* ((typ (cdr x)) ; :list
         (element-type (hol-list-element-type typ)))
    (implies (and (not (equal (hp-value x) 0))
                  (equal (car typ) :list)
                  (equal (car element-type) :hash)
                  (force (hpp x hta)))
             (hp-comma-p (hp-list-car x))))
  :hints (("Goal"
           :expand ((hol-typep (cdr x) hta t)
                    (HOL-TYPEP (CADDR X) HTA T))
           :in-theory (enable hpp hol-type-eval hol-valuep hp-comma-p
                              WEAK-HOL-TYPEP HP-LIST-CAR)))
  :props (zfc prod2$prop inverse$prop diff$prop domain$prop finseqs$prop))

(defthm type-10
  (implies (and (not (equal y (hp-nil '(:hash :num :num))))
                (hpp y hta)
                (equal (cdr y) '(:list (:hash :num :num))))
           (not (equal (car y) 0))))

(defthmz type-10-alt
  (implies (and (not (equal y (hp-nil '(:hash :num :num))))
                (hpp y hta)
                (equal (cdr y) '(:list (:hash :num :num))))
           (< 0 (domain (car y))))
  :hints (("Goal" :in-theory (enable HOL-TYPE-EVAL)))
  :props (zfc prod2$prop inverse$prop diff$prop domain$prop finseqs$prop))

; End of lemmas developed in support of ../examples/eval-poly-support.lisp (see
; comment above about this).
