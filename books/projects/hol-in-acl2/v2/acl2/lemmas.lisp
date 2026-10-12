; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book has miscellaneous useful theorems for reasoning about translations
; of HOL definitions.

(in-package "ZF")

(include-book "hol")
(include-book "alist-subsetp")
(include-book "typ")

; The following openers, together with disables that come later in the file,
; speed up ../examples/ex1-proof.lisp and ../examples/eval-poly-proof.lisp.
; The openers also speed up proofs in the present file.

(defthm hol-typep-flg-nil-open
  (implies (and (equal kwd (car x))
                (syntaxp (quotep kwd)))
           (equal (hol-typep-flg nil x hta)
                  (cond
                   ((atom x)
                    (and (keywordp x)
                         (let ((pair (assoc-hta x (or hta (hta0)))))
                           (if pair
                               (let ((val (cdr pair)))
                                 (and (consp val)
                                      (eql (cdr val) 0) ; arity 0

; We consider an hta entry to be invalid when it maps to the empty set, because
; types are supposed to be non-empty.

                                      (not (equal (car val) 0))))
                             (null hta)))))
                   ((keywordp (car x))
                    (and (let ((pair (assoc-hta (car x) (or hta (hta0)))))
                           (if pair
                               (let ((val (cdr pair)))
                                 (and (consp val)
                                      (posp (cdr val)) ; positive arity
                                      (eql (len (cdr x)) (cdr val))))
                             (and (null hta)
                                  (cdr x))))
                         (hol-typep-flg t (cdr x) hta)))
                   (t nil)))))

(defthm hol-typep-flg-t-consp
  (implies (consp x)
           (equal (hol-typep-flg t x hta)
                  (and (hol-typep-flg nil (car x) hta)
                       (hol-typep-flg t (cdr x) hta)))))

(defthm hol-typep-flg-t-nil
  (implies (atom x)
           (equal (hol-typep-flg t x hta)
                  (equal x nil))))

(defthm hol-type-eval-flg-nil-open
  (implies (and (equal kwd (car x))
                (syntaxp (quotep kwd)))
           (equal (hol-type-eval-flg nil x hta)
                  (cond
                   ((not (mbt (hol-typep x hta)))
                    0)
                   ((keywordp x)
                    (let ((pair (assoc-hta x hta)))
                      (cond
                       (pair
                        (assert$
                         (consp pair)
                         (let ((val (cdr pair)))
                           (cond
                            ((or (atom val) ; ill-formed hta
                                 (not (equal (cdr val) 0))) ; not arity 0
                             0)
                            (t (car val))))))
                       (t 0))))
                   ((and (true-listp x)
                         (consp (cdr x)) ; at least one argument
                         (keywordp (car x)))
                    (let ((pair (assoc-hta (car x) hta)))
                      (cond
                       (pair
                        (assert$
                         (consp pair)
                         (let ((val (cdr pair)))
                           (cond
                            ((and (consp val)
                                  (equal (length (cdr x)) (cdr val)))
                             (let ((vals (hol-type-eval-flg t (cdr x) hta)))
                               (if (equal vals 0)
                                   0
                                 (apply (car val) vals))))
                            (t 0)))))
                       (t 0))))
                   (t 0)))))

(defthm hol-type-eval-flg-t-consp
  (implies (consp x)
           (equal (hol-type-eval-flg t x hta)
                  (let ((fst (hol-type-eval-flg nil (car x) hta))
                        (rst (hol-type-eval-flg t (cdr x) hta)))
                    (cond ((or (equal fst 0)
                               (equal rst 0))
                           0)
                          (t (cons fst rst)))))))

(defthm hol-type-eval-flg-t-atom
  (implies (not (consp x))
           (equal (hol-type-eval-flg t x hta)
                  nil)))

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

(defthmz hol-type-eval-arrow
  (implies (and (htap hta)
                (hol-typep type hta)
                (equal (car type) :arrow))
           (equal (hol-type-eval type hta)
                  (let ((val1 (hol-type-eval (cadr type) hta))
                        (val2 (hol-type-eval (caddr type) hta)))
                    (if (or (equal val1 0)
                            (equal val2 0))
                        0
                      (fun-space val1 val2)))))
  :hints (("Goal" :in-theory (enable hol-type-eval)))
  :props (hta-prop))

(defthmz hpp-hap

; Hypothesese were originally forced, but that caused complications for
; ../examples/eval-poly-proof.lisp.

  (implies (and (htap hta)
                (hpp f hta)
                (arrow-typep (hp-type f))
                (hpp x hta)
                (equal (hp-type x) (arrow-domain (hp-type f))))
           (hpp (hap f x) hta))
  :props (hta-prop)
  :hints (("Goal" :in-theory (enable hap))))

(defthmz hp-type-hap
  (implies (and (force (weak-hol-typep (hp-type f)))
                (force (arrow-typep (hp-type f)))
                (force (equal (hp-type x) (arrow-domain (hp-type f)))))
           (equal (hp-type (hap f x))
                  (arrow-range (hp-type f))))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop)
  :hints (("Goal" :in-theory (enable hap))))

(defthmz hol-typep-flg-monotone-for-alist-subsetp
  (implies (and (alist-subsetp hta1 hta2)
                (htap hta1)
                (hol-typep-flg flg type hta1))
           (hol-typep-flg flg type hta2))
  :props (hta-prop))

(defthmz hol-typep-monotone-for-alist-subsetp
  (implies (and (alist-subsetp hta1 hta2)
                (htap hta1)
                (hol-typep type hta1))
           (hol-typep type hta2))
  :props (hta-prop))

(defthmz hol-type-eval-flg-monotone-for-alist-subsetp
  (implies (and (alist-subsetp hta1 hta2)
                (htap hta1)
                (hol-typep-flg flg type hta1))
           (equal (hol-type-eval-flg flg type hta1)
                  (hol-type-eval-flg flg type hta2)))
  :hints (("Goal" :in-theory (enable hol-type-eval-flg)))
  :props (hta-prop))

(defthmdz hol-type-eval-monotone-for-alist-subsetp
; Let's keep this disabled until it's clear what form the rule could usefully
; take in general.
  (implies (and (alist-subsetp hta1 hta2)
                (htap hta1)
                (hol-typep type hta1))
           (equal (hol-type-eval type hta1)
                  (hol-type-eval type hta2)))
  :props (hta-prop))

(defthmz hpp-monotone-for-alist-subsetp
  (implies (and (alist-subsetp hta1 hta2)
                (htap hta1)
                (hpp x hta1))
           (hpp x hta2))
  :props (hta-prop))

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
                  (cons :num (cons (omega) 0)))))

(defthmz hpp-restrict
  (implies (and (hpp x hta)
                (htap hta)
                (equal (hp-type x)
                       (list :list alpha))
                (not (equal (car x) 0)))
           (hpp (cons (restrict (car x) (+ -1 (domain (car x))))
                      (list :list alpha))
                hta))
  :props (hta-prop restrict$prop diff$prop))

(defthmz hol-type-eval-num
  (implies (alist-subsetp (hta0) hta)
           (equal (hol-type-eval :num hta)
                  (omega)))
  :hints (("Goal" :in-theory (enable hol-type-eval hol-typep)))
  :props (hta-prop))

(defthmz hol-type-eval-hash
  (implies (and (hol-typep type hta)
                (htap hta)
                (equal (car type) :hash))
           (equal (hol-type-eval type hta)
                  (prod2 (hol-type-eval (cadr type) hta)
                         (hol-type-eval (caddr type) hta))))
  :props (hta-prop))

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
                (htap1 hta)
                (hpp x hta)
                (equal (cdr x) ; (hp-type x)
                       '(:list (:hash :num :num))))
           (equal (consp (finseq-to-list (car x))) ; (car x) is (hp-value x)
                  (not (equal x (hp-nil '(:hash :num :num))))))
  :props (hta-prop restrict$prop diff$prop))

(defthmz num-type-implies-natp
  (implies (and (alist-subsetp (hta0) hta)
                (hpp x hta)
                (equal (cdr x) :num))
           (natp (car x)))
  :rule-classes :forward-chaining
  :props (hta-prop))

(defthmz hpp-natp ; relies on omega-is-not-natp
  (implies (and (alist-subsetp (hta0) hta)
                (force (natp x)))
           (hpp (cons x :num)
                hta))
  :hints (("Goal" :in-theory (enable hol-typep)))
  :props (hta-prop))

(defthmz list-type-implies-funp-with-natp-domain
  (implies (and (hpp x hta)
                (htap hta)
                (equal (cdr x) (cons :list rest)))
           (and (funp (car x))
                (natp (domain (car x)))))
  :props (hta-prop)
  :rule-classes :forward-chaining)

; The following "type-i" (i from 1 to 6) aren't great names and might be
; renamed.  They were developed in support of hol::hol{eval_poly}1-alt in
; ../examples/eval-poly-proof.lisp.

(defthmz type-1
  (implies (and (alist-subsetp (hta0) hta)
                (htap1 hta)
                (equal (cdr x)
                       '(:list (:hash :num :num)))
                (force (< 0 (domain (car x))))
                (force (hpp x hta)))
           (equal (cdr (hp-hash-car (hp-list-car x)))
                  :num))
  :hints (("Goal" :in-theory (enable hp-hash-car hp-list-car)))
  :props (hta-prop))

(local
 (defthmz type-2-lemma-1
   (implies (and (funp fn)
                 (subset (image fn) s)
                 (in i (domain fn)))
            (in (apply fn i) s))
   :props (zfc prod2$prop domain$prop inverse$prop diff$prop)
   :rule-classes nil))

(local
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
 )

(defthmz type-2
  (implies (and (htap hta)
                (equal (cdr x)
                       '(:list (:hash :num :num)))
                (force (< 0 (domain (car x))))
                (force (hpp x hta)))
           (hpp (hp-hash-cdr (hp-list-car x))
                hta))
  :hints (("Goal" :in-theory (enable hp-hash-cdr hp-list-car hol-type-eval)))
  :props (hta-prop diff$prop))

(defthmz type-3
  (implies (and (alist-subsetp (hta0) hta)
                (htap1 hta)
                (equal (cdr x)
                       '(:list (:hash :num :num)))
                (force (< 0 (domain (car x))))
                (force (hpp x hta)))
           (equal (cdr (hp-hash-cdr (hp-list-car x)))
                  :num))
  :hints (("Goal" :in-theory (enable hp-hash-cdr hp-list-car)))
  :props (hta-prop))

(local
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
   :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop diff$prop)))

(defthmz type-4a
  (implies (and (htap hta)
                (equal (car (cdr x)) :list)
                (force (< 0 (domain (car x))))
                (force (hpp x hta)))
           (hpp (hp-list-car x)
                hta))
  :hints (("Goal" :in-theory (enable hp-list-car)))
  :props (hta-prop))

(defthm type-4b
  (implies (and (htap hta)
                (equal (cdr x) :hash)
                (force (hpp x hta)))
           (hpp (hp-hash-car x)
                hta))
  :hints (("Goal" :in-theory (enable hp-hash-car))))

(defthmz type-5
  (implies (and (htap hta)
                (equal (car (cdr x)) :list)
                (force (hpp x hta)))
           (hpp (hp-list-cdr x)
                hta))
  :hints (("Goal" :in-theory (enable hp-list-cdr)))
  :props (hta-prop diff$prop restrict$prop))

(local (in-theory (disable hol-type-eval-flg-non-empty)))

(defthm type-6
  (implies (and (alist-subsetp (hta0) hta)
                (htap1 hta)
                (equal (car (cdr x)) :list)
                (force (hpp x hta)))
           (equal (cdr (hp-list-cdr x))
                  (cdr x)))
  :hints (("Goal"
           :expand ((hol-type-eval-flg nil (cdr x) hta))
           :in-theory (enable hp-list-cdr))))

(defthmz type-7
  (implies (and (htap hta)
                (< 0 (domain (car y)))
                (equal (car (cdr y)) :list)
                (force (hpp y hta)))
           (hpp (hp-list-car y) hta))
  :hints (("Goal" :in-theory (enable hp-list-car)))
  :props (hta-prop))

(defthmz type-8
  (implies (and (alist-subsetp (hta0) hta)
                (htap1 hta)
                (< 0 (domain (car y)))
                (equal (cdr y) '(:list (:hash :num :num)))
                (force (hpp y hta)))
           (equal (cdr (hp-list-car y))
                  '(:hash :num :num)))
  :hints (("Goal" :in-theory (enable hp-list-car)))
  :props (hta-prop))

(in-theory (disable (:e hol-type-eval-flg)))

(defthmz hp-type-bool-cases
; This is unused in this file (as of this wriging), but perhaps it is useful
; elsewhere.
  (implies (and (alist-subsetp (hta0) hta)
                (hpp x hta)
                (equal (hp-type x) :bool))
           (or (equal x (hp-true))
               (equal x (hp-false))))
  :rule-classes nil)

(local
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
   :props (zfc prod2$prop domain$prop inverse$prop)))

(defthmz type-9
  (let* ((typ (cdr x)) ; (:list _)
         (element-type (hol-list-element-type typ)))
    (implies (and (alist-subsetp (hta0) hta)
                  (htap1 hta)
                  (not (equal (hp-value x) 0))
                  (equal (car typ) :list)
                  (equal (car element-type) :hash)
                  (force (hpp x hta)))
             (hp-comma-p (hp-list-car x))))
  :hints (("Goal" :in-theory (enable hp-list-car)))
  :props (hta-prop))

(defthm hons-assoc-list-num
  (implies (alist-subsetp (hta0) hta)
           (equal (hons-assoc-equal :num hta)
                  (cons :num (cons (omega) 0)))))

(defthmz type-10
  (implies (and (alist-subsetp (hta0) hta)
                (htap1 hta)
                (not (equal y (hp-nil '(:hash :num :num))))
                (hpp y hta)
                (equal (cdr y) '(:list (:hash :num :num))))
           (< 0 (domain (car y))))
  :rule-classes :linear
  :props (hta-prop))

; Here are more lemmas in support of ../examples/eval-poly-proof.lisp,
; developed during the proof of sum_polys-reduction.

(defthmz subset-image-car-omega-cross-omega
  (implies (and (alist-subsetp (hta0) hta)
                (hpp x hta)
                (equal (hp-type x)
                       (typ (:list (:hash :num :num)))))
           (subset (image (car x))
                   (prod2 (omega) (omega))))
  :props (hta-prop))

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
  :props (hta-prop restrict$prop diff$prop))

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
  :props (hta-prop restrict$prop diff$prop))

(defthm car-hp-hash-car
  (equal (car (hp-hash-car v))
         (car (car v)))
  :hints (("Goal" :in-theory (enable hp-hash-car))))

(defthm car-hp-hash-cdr
  (equal (car (hp-hash-cdr v))
         (cdr (car v)))
  :hints (("Goal" :in-theory (enable hp-hash-cdr))))

(defthmz natp-car-from-hpp
  (implies (and (alist-subsetp (hta0) hta)
                (hpp v hta)
                (equal (hp-type v) (typ :num)))
           (natp (car v)))
  :rule-classes :forward-chaining
  :props (hta-prop))

(defthmz natp-cdr-car-hp-list-car
  (implies (and (alist-subsetp (hta0) hta)
                (hpp x hta)
                (equal (cdr x) ; (hp-type x)
                       (typ (:list (:hash :num :num))))
                (not (equal x '(0 :list (:hash :num :num)))))
           (natp (cdr (car (hp-list-car x)))))
  :hints (("Goal" :in-theory (enable hp-list-car)))
  :rule-classes :forward-chaining
  :props (hta-prop diff$prop))

(defthmz natp-car-car-hp-list-car
  (implies (and (alist-subsetp (hta0) hta)
                (hpp x hta)
                (equal (cdr x) ; (hp-type x)
                       (typ (:list (:hash :num :num))))
                (not (equal x '(0 :list (:hash :num :num)))))
           (natp (car (car (hp-list-car x)))))
  :hints (("Goal" :in-theory (enable hp-list-car)))
  :rule-classes :forward-chaining
  :props (hta-prop diff$prop))

(defthm consp-hp-list-car
  (implies (force (hp-cons-p x))
           (consp (hp-list-car x)))
  :hints (("goal" :in-theory (enable hp-list-car))))

(defthmz consp-car-hp-list-car
  (implies (and (alist-subsetp (hta0) hta)
                (force (hpp x hta))
                (force (hp-cons-p x))
                (force (equal (hp-type x) (typ (:list (:hash :num :num))))))
           (consp (car (hp-list-car x))))
  :hints (("Goal" :in-theory (enable hp-list-car)))
  :props (hta-prop))

(in-theory (disable (:e hp-hash-car) (:e hp-hash-cdr)
                    (:e hp-cons)
                    (:e hp-list-car) (:e hp-list-cdr)))

(defthmz natp-union2
  (implies (natp n)
           (natp (union2 n (pair n n))))
  :hints (("Goal" :use n+1-as-union2)))

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
         (implies (and (htap hta)
                       (equal y-typ (list :list x-typ))
                       (in x-val (hol-type-eval x-typ hta))
                       (in y-val (hol-type-eval y-typ hta)))
                  (in (union2 y-val
                              (pair (cons (domain y-val) x-val)
                                    (cons (domain y-val) x-val)))
                      (hol-type-eval y-typ hta)))
         :props (hta-prop)))

(defthmz hpp-hp-cons
  (implies (and (htap hta)
                (hpp x hta)
                (hpp y hta)
                (equal (hp-type y)
                       (list :list (hp-type x))))
           (hpp (hp-cons x y) hta))
  :hints (("Goal" :in-theory (enable hp-cons)))
  :props (hta-prop))
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
  (implies (and (alist-subsetp (hta0) hta)
                (hpp x hta)
                (not (equal (hp-value x) 0))
                (equal (hp-type x)
                       '(:list (:hash :num :num))))
           (equal (hp-list-car x)
                  (let ((fn (hp-value x)))
                    (make-hp (apply fn (1- (domain fn)))
                             (hol-list-element-type (hp-type x))))))
  :hints (("Goal" :in-theory (enable hp-list-car)))
  :props (hta-prop))

(defthm car-hp-comma
  (equal (car (hp-comma x y))
         (cons (car x) (car y)))
  :hints (("Goal" :in-theory (enable hp-comma))))

(defthmz hpp-cons-x-bool
  (implies (alist-subsetp (hta0) hta)
           (equal (hpp (cons x :bool) hta)
                  (booleanp x)))
  :hints (("Goal" :in-theory (enable hol-type-eval hta0))))

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
  :hints (("Goal" :expand ((finseq-to-list (insert (cons (domain fn) x)
                                                   fn)))))
    :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop diff$prop
                restrict$prop))

; Start proofs of lemmas for forcing rounds of sum_polys-reduction.

(defun hp-list-typep (typ)
  (declare (xargs :guard t))
  (and (consp typ)
       (eq (car typ) :list)))

(defthmz hpp-cons-apply-for-list
  (implies (and (htap hta)
                (hpp x hta)
                (hp-list-typep (hp-type x))
                (equal element-type (cadr (hp-type x)))
                (in n (domain (car x))))
           (hpp (cons (apply (car x) n)
                      element-type)
                hta))
  :props (hta-prop))

(defthmz nonempty-list-has-posp-domain
  (implies (and (alist-subsetp (hta0) hta)
                (htap1 hta)
                (hpp x hta)
                (hp-list-typep (hp-type x))
                (not (equal (car x) 0)))
           (natp (1- (domain (car x)))))
  :props (hta-prop))

(defthmz hpp-hp-cons-hp-comma
  (implies (and (force (alist-subsetp (hta0) hta))
                (force (hpp x hta))
                (force (equal (hp-type x)
                              (typ (:list (:hash :num :num)))))
                (force (hpp m hta))
                (force (equal (hp-type m) :num))
                (force (hpp n hta))
                (force (equal (hp-type n) :num)))
           (hpp (hp-cons (hp-comma m n)
                         x)
                hta))
  :props (hta-prop))

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
  :props (hta-prop))

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
  (implies (and (alist-subsetp (hta0) hta)
                (hpp y hta)
                (equal (cdr y)
                       '(:list (:hash :num :num)))
                (not (equal y '(0 :list (:hash :num :num)))))
           (equal (hp-cons (cons (apply (car y) (+ -1 (domain (car y))))
                                 '(:hash :num :num))
                           (hp-list-cdr y))
                  y))
  :hints (("Goal"
           :in-theory (e/d (hp-list-car-open)
                           (hp-cons-hp-list-car-hp-list-cdr))
           :use ((:instance hp-cons-hp-list-car-hp-list-cdr
                            (x y)))))
  :props (hta-prop restrict$prop diff$prop))

(defthmz list-type-is-funp
  (implies (and (alist-subsetp (hta0) hta)
                (htap1 hta)
                (hpp x hta)
                (equal (cdr x)
                       (cons :list rest)))
           (funp (car x)))
  :props (hta-prop))

; End of lemmas developed in support of ../examples/eval-poly-proof.lisp (see
; comment above about this).

; Lemmas developed while cleaning up ../examples/ex1-proof.lisp

(defthmz hol-typep-hash
  (implies (and (alist-subsetp (hta0) hta)
                (equal (car type) :hash))
           (equal (hol-typep type hta)
                  (and (true-listp type)
                       (equal (len type) 3)
                       (hol-typep (cadr type) hta)
                       (hol-typep (caddr type) hta))))
  :hints (("Goal" :expand ((hol-typep-flg nil type hta))))
  :props (hta-prop))

(defthm cdr-hp-comma
  (equal (cdr (hp-comma x y))
         (list :hash (hp-type x) (hp-type y)))
  :hints (("Goal" :in-theory (enable hp-comma))))

; End of lemmas developed while cleaning up ../examples/ex1-proof.lisp

; The following openers and disables speed up ../examples/ex1-proof.lisp and
; ../examples/eval-poly-proof.lisp.

(defthm hol-typep-flg-nil-open
  (implies (and (equal kwd (car x))
                (syntaxp (quotep kwd)))
           (equal (hol-typep-flg nil x hta)
                  (cond
                   ((atom x)
                    (and (keywordp x)
                         (let ((pair (assoc-hta x (or hta (hta0)))))
                           (if pair
                               (let ((val (cdr pair)))
                                 (and (consp val)
                                      (eql (cdr val) 0) ; arity 0

; We consider an hta entry to be invalid when it maps to the empty set, because
; types are supposed to be non-empty.

                                      (not (equal (car val) 0))))
                             (null hta)))))
                   ((keywordp (car x))
                    (and (let ((pair (assoc-hta (car x) (or hta (hta0)))))
                           (if pair
                               (let ((val (cdr pair)))
                                 (and (consp val)
                                      (posp (cdr val)) ; positive arity
                                      (eql (len (cdr x)) (cdr val))))
                             (and (null hta)
                                  (cdr x))))
                         (hol-typep-flg t (cdr x) hta)))
                   (t nil)))))

(defthm hol-typep-flg-t-consp
  (implies (consp x)
           (equal (hol-typep-flg t x hta)
                  (and (hol-typep-flg nil (car x) hta)
                       (hol-typep-flg t (cdr x) hta)))))

(defthm hol-typep-flg-t-nil
  (implies (atom x)
           (equal (hol-typep-flg t x hta)
                  (equal x nil))))

(in-theory (disable hol-typep-flg hol-type-eval-flg
                    hol-typep-flg-monotone-for-alist-subsetp
; Needed for ../examples/eval-poly-thy-alt.lisp:
                    (:e hol-type-eval-flg)

; The following set theory rules aren't needed and seem too low-level anyhow
; for the sort of reasoning we want to do.
                    relation-p-necc car-preserves-in-for-transitive
                    cdr-preserves-in-for-transitive subset-preserves-in-2
                    funp-rcompose-lemma rcompose-is-compose))

; Disabling the following sped up the key lemma, sum_polys-reduction, in
; ../examples/eval-poly-proof.lisp.
(in-theory (disable ordinal-trichotomy in-cons-apply in-domain-finseq
                    hol-type-eval-arrow
                    finseq-fold-1-1 apply-default natp-<-implies-in
; The following is needed for hol{sum_polys}1-alt in
; ../examples/eval-poly-thy-alt.lisp:
                    ; consp-hp-list-car
                    hons-assoc-equal-preserves-in-for-transitive
                    funp-hp-cons-lemma list-type-is-funp
                    in-fun-space ordinals-closure
                    <=-implies-subset-on-natps))
