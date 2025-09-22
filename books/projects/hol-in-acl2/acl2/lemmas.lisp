; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book has miscellaneous useful theorems for reasoning about translations
; of HOL definitions.

(in-package "ZF")

(include-book "hol")
(include-book "alist-subsetp")
(include-book "typ")

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
; ../examples/eval-poly-proof.lisp.

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
; ../examples/eval-poly-proof.lisp.  Many are generally applicable.  Others
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
; ../examples/eval-poly-proof.lisp where it originally appeared.  But we
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

(defthmz num-type-implies-natp
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

(defthmz list-type-implies-funp-with-natp-domain
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
; ../examples/eval-poly-proof.lisp.

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
           (enable hpp hol-valuep hol-type-eval hp-hash-car hp-list-car)))
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

; Here are more lemmas in support of ../examples/eval-poly-proof.lisp,
; developed during the proof of sum_polys-reduction.

(in-theory (disable hta0 (hta0)))

(defthmz subset-image-car-omega-cross-omega
  (implies (and (alist-subsetp (hta0) hta)
                (hpp x hta)
                (equal (hp-type x)
                       (typ (:list (:hash :num :num)))))
           (subset (image (car x))
                   (prod2 (omega) (omega))))
  :hints (("Goal" :in-theory (enable hpp hp-cons hol-valuep hol-type-eval)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop diff$prop))

(defthmz car-finseq-to-list-car
  (implies (and (alist-subsetp (hta0) hta)
                (hpp x hta)
                (equal (hp-type x)
                       (typ (:list (:hash :num :num)))))
           (equal (car (finseq-to-list (car x)))
                  (hp-value (hp-list-car x))))
  :hints (("Goal"
           :in-theory (enable hp-list-car)
           :expand ((finseq-to-list (car x)))))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop diff$prop
              restrict$prop))

(defthmz finseq-to-list-car-hp-list-cdr
  (implies (and (alist-subsetp (hta0) hta)
                (hpp x hta)
                (equal (hp-type x)
                       (typ (:list (:hash :num :num)))))
           (equal (finseq-to-list (car (hp-list-cdr x)))
                  (cdr (finseq-to-list (hp-value x)))))
  :hints (("Goal"
           :in-theory (enable hp-list-cdr)
           :expand ((finseq-to-list (car x)))))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop diff$prop
              restrict$prop))

(defthm car-hp-hash-car
  (equal (car (hp-hash-car v))
         (car (car v)))
  :hints (("Goal" :in-theory (enable hp-hash-car))))

(defthm car-hp-hash-cdr
  (equal (car (hp-hash-cdr v))
         (cdr (car v)))
  :hints (("Goal" :in-theory (enable hp-hash-cdr))))

(in-theory (disable hpp))

(defthmz natp-car-from-hpp
  (implies (and (hpp v hta)
                (alist-subsetp (hta0) hta)
                (equal (hp-type v) (typ :num)))
           (natp (car v)))
  :rule-classes :forward-chaining)

(defthmz natp-cdr-car-hp-list-car
  (implies (and (hpp x hta)
                (alist-subsetp (hta0) hta)
                (equal (cdr x) ; (hp-type x)
                       (typ (:list (:hash :num :num))))
                (not (equal x '(0 :list (:hash :num :num)))))
           (natp (cdr (car (hp-list-car x)))))
  :hints (("Goal" :in-theory (enable hp-list-car hpp hol-valuep hol-type-eval)))
  :rule-classes :forward-chaining
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop diff$prop))

(defthmz natp-car-car-hp-list-car
  (implies (and (hpp x hta)
                (alist-subsetp (hta0) hta)
                (equal (cdr x) ; (hp-type x)
                       (typ (:list (:hash :num :num))))
                (not (equal x '(0 :list (:hash :num :num)))))
           (natp (car (car (hp-list-car x)))))
  :hints (("Goal" :in-theory (enable hp-list-car hpp hol-valuep hol-type-eval)))
  :rule-classes :forward-chaining
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop diff$prop))

(defthm consp-hp-list-car
  (implies (force (hp-cons-p x))
           (consp (hp-list-car x)))
  :hints (("goal" :in-theory (enable hp-list-car))))

(defthmz consp-car-hp-list-car
  (implies (and (force (hpp x hta))
                (force (hp-cons-p x))
                (force (equal (hp-type x) (typ (:list (:hash :num :num))))))
           (consp (car (hp-list-car x))))
  :hints (("Goal" :in-theory (enable hp-list-car hpp hol-valuep
                                     hol-type-eval)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop diff$prop))

(in-theory (disable (:e hp-hash-car) (:e hp-hash-cdr)
                    (:e hp-cons)
                    (:e hp-list-car) (:e hp-list-cdr)))

(defthmz natp-union2
  (implies (natp n)
           (natp (union2 n (pair n n))))
  :hints (("Goal" :use n+1-as-union2)))

(defthmz image-union2-1-1
  (implies (in a (image (union2 x y)))
           (in a (union2 (image x) (image y))))
  :hints (("Goal"
           :in-theory (disable in-image-necc)
           :use ((:instance in-image-necc
                            (x a)
                            (f (union2 x y))))))
  :props (zfc domain$prop prod2$prop inverse$prop))

(defthmz image-union2-1
  (subset (image (union2 x y))
          (union2 (image x) (image y)))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc domain$prop prod2$prop inverse$prop))

(defthmz domain-monotone-1
  (implies (and (subset x y)
                (in a (domain x)))
           (in a (domain y)))
  :hints (("Goal"
           :use ((:instance in-domain-rewrite (x a) (r x)))
           :restrict ((in-car-domain-alt ((p (cons a (apply x a))))))
           :in-theory (disable in-cons-apply)))
  :props (zfc domain$prop))

(defthmz domain-monotone
  (implies (subset x y)
           (subset (domain x) (domain y)))
  :hints (("Goal" :expand ((subset (domain x) (domain y)))))
  :props (zfc domain$prop))

(defthmz inverse-monotone
  (implies (subset x y)
           (subset (inverse x) (inverse y)))
  :hints (("Goal" :expand ((subset (inverse x) (inverse y)))))
  :props (zfc domain$prop prod2$prop inverse$prop))

(defthmz image-monotone
  (implies (subset x y)
           (subset (image x) (image y)))
  :hints (("Goal" :in-theory (e/d (image) (domain-inverse))))
  :props (zfc domain$prop prod2$prop inverse$prop))

(defthmz image-union2
  (equal (image (union2 x y))
         (union2 (image x) (image y)))
  :hints (("Goal" :in-theory (enable extensionality-rewrite)))
  :props (zfc domain$prop prod2$prop inverse$prop))

(defthmz image-pair-1
  (subset (image (pair (cons x1 y1)
                       (cons x2 y2)))
          (pair y1 y2))
  :hints (("Goal"
           :expand ((subset (image (pair (cons x1 y1) (cons x2 y2)))
                            (pair y1 y2)))
           :in-theory (enable in-image-rewrite)))
  :props (zfc domain$prop prod2$prop inverse$prop))

(defthmz image-pair
  (equal (image (pair (cons x1 y1)
                      (cons x2 y2)))
         (pair y1 y2))
  :hints (("Goal" :in-theory (enable extensionality-rewrite)))
  :props (zfc domain$prop prod2$prop inverse$prop))

(encapsulate ()

(local (defthmz hpp-hp-cons-lemma
         (implies (and (equal y-typ (list :list x-typ))
                       (hol-typep x-typ hta t)
                       (in x-val (hol-type-eval x-typ hta))
                       (hol-typep y-typ hta t)
                       (in y-val (hol-type-eval y-typ hta)))
                  (in (union2 y-val
                              (pair (cons (domain y-val) x-val)
                                    (cons (domain y-val) x-val)))
                      (hol-type-eval y-typ hta)))
         :hints (("Goal"
                  :expand ((hol-type-eval (list :list x-typ) hta))))
         :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop)))

(defthmz hpp-hp-cons
  (implies (and (hpp x hta)
                (hpp y hta)
                (equal (hp-type y)
                       (list :list (hp-type x))))
           (hpp (hp-cons x y) hta))
  :hints (("Goal" :in-theory (enable hpp hp-cons hol-valuep)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop))
)

(defthmz car-hp-cons
  (equal (car (hp-cons x y))
         (insert (cons (domain (hp-value y))
                       (hp-value x))
                 (hp-value y)))
  :hints (("Goal" :in-theory (enable hp-cons))))

(defthmz cdr-hp-cons
  (equal (cdr (hp-cons x y))
         (hp-type y))
  :hints (("Goal" :in-theory (enable hp-cons))))

(defthmdz hp-list-car-open
  (implies (and (hpp x hta)
                (not (equal (hp-value x) 0))
                (equal (cdr x)
                       '(:list (:hash :num :num))))
           (equal (hp-list-car x)
                  (let ((fn (hp-value x)))
                    (make-hp (apply fn (1- (domain fn)))
                             (hol-list-element-type (hp-type x))))))
  :hints (("Goal" :in-theory (enable hp-list-car)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop))

(defthm car-hp-comma
  (equal (car (hp-comma x y))
         (cons (car x) (car y)))
  :hints (("Goal" :in-theory (enable hp-comma))))

(defthmz hpp-cons-x-bool
  (implies (alist-subsetp (hta0) hta)
           (equal (hpp (cons x :bool) hta)
                  (booleanp x)))
  :hints (("Goal" :in-theory (enable hpp hol-valuep hol-type-eval hta0))))

; Start proof of finseq-to-list-insert.

(defthmz domain-extend-by-1
  (implies (natp (domain fn))
           (equal (domain (insert (cons (domain fn) x) fn))
                  (1+ (domain fn))))
  :hints (("Goal" :in-theory (enable insert n+1-as-union2)))
  :props (zfc domain$prop))

(defthmz image-insert-cons
  (equal (image (insert (cons a b) fn))
         (insert b (image fn)))
  :hints (("Goal" :in-theory (enable insert)))
  :props (zfc inverse$prop prod2$prop domain$prop))

(defthmz subset-insert
  (equal (subset (insert a x) y)
         (and (in a y)
              (subset x y)))
  :hints (("Goal" :in-theory (enable insert))))

(defthmz insert-non-0
  (not (equal (insert a x)
              0))
  :hints (("Goal" :in-theory (enable insert))))

(defthmz funp-extend-with-domain
  (implies (and (funp fn)
                (natp (domain fn)))
           (funp (insert (cons (domain fn) x) fn)))
  :hints (("Goal" :in-theory (enable insert)))
  :props (zfc domain$prop))

(defthmz restrict-extend-with-domain-to-domain
  (implies (and (funp fn)
                (natp (domain fn)))
           (equal (restrict (insert (cons (domain fn) x) fn)
                            (domain fn))
                  fn))
  :hints (("Goal" :in-theory (enable insert)))
  :props (zfc restrict$prop domain$prop))

(in-theory (disable insert))

(defthmz finseq-to-list-insert
  (implies (and (funp fn)
                (natp (domain fn))
                (in x (prod2 (omega) (omega)))
                (subset (image fn)
                        (prod2 (omega) (omega))))
           (equal (finseq-to-list (insert (cons (domain fn) x)
                                          fn))
                  (cons x
                        (finseq-to-list fn))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((finseq-to-list (insert (cons (domain fn) x)
                                            fn)))))
    :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop diff$prop
                restrict$prop))

; Start proofs of lemmas for forcing rounds of sum_polys-reduction.

(defun hp-list-typep (typ)
  (declare (xargs :guard t))
  (and (consp typ)
       (eq (car typ) :list)))

(defthmz hpp-cons-apply-for-list
  (implies (and (hpp x hta)
                (hp-list-typep (hp-type x))
                (equal element-type (cadr (hp-type x)))
                (in n (domain (car x))))
           (hpp (cons (apply (car x) n)
                      element-type)
                hta))
  :hints (("Goal" :in-theory (enable hpp hol-valuep hol-type-eval)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop))

(defthmz nonempty-list-has-posp-domain
  (implies (and (hpp x hta)
                (hp-list-typep (hp-type x))
                (not (equal (car x) 0)))
           (natp (1- (domain (car x)))))
  :hints (("Goal"
           :expand ((hol-typep (cdr x) hta t))
           :in-theory (enable hpp hol-valuep hol-typep hol-type-eval)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop))

(defthmz hpp-hp-cons-hp-comma
  (implies (and (force (hpp x hta))
                (force (equal (hp-type x)
                              (typ (:list (:hash :num :num)))))
                (force (hpp m hta))
                (force (equal (hp-type m) :num))
                (force (hpp n hta))
                (force (equal (hp-type n) :num)))
           (hpp (hp-cons (hp-comma m n)
                         x)
                hta))
  :hints (("Goal"
           :in-theory (enable hpp hol-valuep hol-typep hol-type-eval)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop))

(defthm cdr-hp-hash-cdr-cons
  (equal (cdr (hp-hash-cdr (cons x (list :hash t1 t2))))
         t2)
  :hints (("Goal" :in-theory (enable hp-hash-cdr))))

(defthm cdr-hp-hash-car-cons
  (equal (cdr (hp-hash-car (cons x (list :hash t1 t2))))
         t1)
  :hints (("Goal" :in-theory (enable hp-hash-car))))

(defthmz hpp-hp-hash-cdr-special-case
  (implies (and (alist-subsetp (hta0) hta)
                (hpp x hta)
                (equal (cdr x)
                       '(:list (:hash :num :num)))
                (not (equal x '(0 :list (:hash :num :num)))))
           (hpp (hp-hash-cdr (cons (apply (car x) (+ -1 (domain (car x))))
                                   '(:hash :num :num)))
                hta))
  :hints (("Goal" :in-theory (enable hpp hol-valuep hol-typep hol-type-eval
                                     hp-hash-cdr)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop))

(defthmz natp-cdr-apply-for-finseq

; This is a general theorem that could be added to the end of theories.lisp.
; But it's specific to finseqs (HOL lists) whose values are pairs of numbers,
; so for other examples there could be analogous lemmas for finseqs whose
; values are of various types.  Thus, it seems best to leave this lemma here,
; as an example of an application-specific lemma that might be needed.

  (implies (and (funp fn)
                (in n (domain fn))
                (subset (image fn)
                        (prod2 (omega) (omega))))
           (natp (cdr (apply fn n))))
  :hints (("Goal"
           :use ((:instance in-apply-image
                            (x n)
                            (r fn)))
           :in-theory (disable subset-preserves-in-2
                               in-apply-image in-apply-image-force)))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz hp-cons-fold
  (implies (and (hpp y hta)
                (equal (cdr y)
                       '(:list (:hash :num :num)))
                (not (equal y '(0 :list (:hash :num :num)))))
           (equal (hp-cons (cons (apply (car y) (+ -1 (domain (car y))))
                                 '(:hash :num :num))
                           (hp-list-cdr y))
                  y))
  :hints (("Goal"
           :in-theory (enable hp-list-car-open)
           :use ((:instance hp-cons-hp-list-car-hp-list-cdr
                            (x y)))))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop diff$prop
              restrict$prop))

(defthmz list-type-is-funp
  (implies (and (hpp x hta)
                (equal (cdr x)
                       (cons :list rest)))
           (funp (car x)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop))

; End of lemmas developed in support of ../examples/eval-poly-proof.lisp (see
; comment above about this).
