
(in-package "ACL2")

(include-book "../clause-processors/sat-clause-processor" :ttags (sat sat-cl))

#|
;; An example of something that can currently be proven with
;; the SAT-based tool:

(thm
 (bv-eq 4
        (bv-and 4 (bv-not 4 x) (bv-not 4 y))
        (bv-not 4 (bv-or 4 x y)))
 :hints (("Goal" :external (sat nil $sat))))

;; Of course I can prove it form much larger bit vectors than
;; "4".

|# ;|

(include-book "bv-lib-definitions" :skip-proofs-okp t)

;; Given a bit value in the range of a
;; a n1 bit, bit vector return the corresponding
;; bit value in the range of an n2 bit, bit
;; vector.
;; n2 >= n1 > val
(defun rel-bit (n2 n1 val)
  (+ val n2 (- n1)))

(defun strip-unary-b-fn (fn x)
  (declare (xargs :guard (symbolp fn)))
  (cond
   ((atom x)
    x)
   ((and (eq fn (car x))
         (consp (cdr x)))
    (strip-unary-b-fn fn (cadr x)))
   (t
    x)))

(defun strip-unary-bv-fn (fn x)
  (declare (xargs :guard (symbolp fn)))
  (cond
   ((atom x)
    x)
   ((and (eq fn (car x))
         (consp (cdr x))
         (consp (cddr x)))
    (strip-unary-bv-fn fn (caddr x)))
   (t
    x)))

;;(deftheory pre-bv-lemma-theory
;;  (current-theory :here))

;;(i-am-here)

(skip-proofs
(encapsulate nil

;; not checked
(defthm bv-communitivity
  (and
   (implies
    (syntaxp (not (term-order (strip-unary-bv-fn 'bv-not x) (strip-unary-bv-fn 'bv-not y))))
    (bv-eq (bv-or n x y)
           (bv-or n y x)))
   (implies
    (and (syntaxp (and (not (term-order (strip-unary-bv-fn 'bv-not x) (strip-unary-bv-fn 'bv-not y)))
                       (quotep n1) (quotep n2)))
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-or n1 x (bv-or n2 y z))
           (bv-or n1 y (bv-or n1 x z))))

   (implies
    (syntaxp (not (term-order (strip-unary-bv-fn 'bv-not x) (strip-unary-bv-fn 'bv-not y))))
    (bv-eq (bv-and n x y)
           (bv-and n y x)))
   (implies
    (and (syntaxp (and (not (term-order (strip-unary-bv-fn 'bv-not x) (strip-unary-bv-fn 'bv-not y)))
                       (quotep n1) (quotep n2)))
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-and n1 x (bv-and n2 y z))
           (bv-and n1 y (bv-and n1 x z))))

   (implies
    (syntaxp (not (term-order (strip-unary-bv-fn 'bv-neg x) (strip-unary-bv-fn 'bv-neg y))))
    (bv-eq (bv-add n x y)
           (bv-add n y x)))
   (implies
    (and (syntaxp (and (not (term-order (strip-unary-bv-fn 'bv-neg x) (strip-unary-bv-fn 'bv-neg y)))
                       (quotep n1) (quotep n2)))
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-add n1 x (bv-add n2 y z))
           (bv-add n1 y (bv-add n1 x z))))

   (implies
    (syntaxp (not (term-order (strip-unary-bv-fn 'bv-neg x) (strip-unary-bv-fn 'bv-neg y))))
    (bv-eq (bv-mul n x y)
           (bv-mul n y x)))
   (implies
    (and (syntaxp (and (not (term-order (strip-unary-bv-fn 'bv-neg x) (strip-unary-bv-fn 'bv-neg y)))
                       (quotep n1) (quotep n2)))
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-mul n1 x (bv-mul n2 y z))
           (bv-mul n1 y (bv-mul n1 x z))))))

;; not checked
(defthm bv-associativity
  (implies
   (and (syntaxp (and (quotep n1) (quotep n2)))
        (natp n1) (natp n2) (< 0 n1) (<= n1 n2))
   (and
    (bv-eq (bv-or n1 (bv-or n2 x y) z)
           (bv-or n1 x (bv-or n1 y z)))

    (bv-eq (bv-and n1 (bv-and n2 x y) z)
           (bv-and n1 x (bv-and n1 y z)))

    (bv-eq (bv-add n1 (bv-add n2 x y) z)
           (bv-add n1 x (bv-add n1 y z)))

    (bv-eq (bv-mul n1 (bv-mul n2 x y) z)
           (bv-mul n1 x (bv-mul n1 y z))))))

;; not checked
(defthm bv-distributivity
  (implies
   (and (syntaxp (and (quotep n1) (quotep n2)))
        (natp n1) (natp n2)
        (< 0 n1) (<= n1 n2))
   (and
    (bv-eq (bv-and n1 x (bv-or n2 y z))
           (bv-or n1 (bv-and n1 x y) (bv-and n1 x z)))
    (bv-eq (bv-and n1 (bv-or n2 x y) z)
           (bv-or n1 (bv-and n1 x z) (bv-and n1 y z)))

    (bv-eq (bv-mul n1 x (bv-add n2 y z))
           (bv-add n1 (bv-mul n1 x y) (bv-mul n1 x z)))
    (bv-eq (bv-mul n1 x (bv-add n2 y z))
           (bv-add n1 (bv-mul n1 x y) (bv-mul n1 x z))))))

;; not checked
;; Note I may need to add some sanity implications on top to
;; make it true, but in practice the lhs and rhs of a bv-eq are
;; always equal sized and nx and ny are gt 0.
(defthm bv-eq-bv-concat-break-up
  (and
   (iff (bv-eq (bv-concat nx ny x y) z)
        (let ((z-size (bv-size z)))
          (b-if (bv-eq x (bv-ex z-size (+ z-size -1) (+ z-size (- nx)) z))
                (bv-eq y (bv-ex z-size
                                (+ z-size (- nx) -1)
                                (+ z-size (- nx) (- ny))
                                z))
                nil)))

   (iff (bv-eq z (bv-concat nx ny x y))
        (let ((z-size (bv-size z)))
          (b-if (bv-eq (bv-ex z-size (+ z-size -1) (+ z-size (- nx)) z) x)
                (bv-eq (bv-ex z-size
                              (+ z-size (- nx) -1)
                              (+ z-size (- nx) (- ny))
                              z)
                       y)
                nil)))))



;; not-checked
(defthm drive-bv-not-inwards
  (implies
   (and (syntaxp (and (quotep n1) (quotep n2)))
        (natp n1) (natp n2)
        (< 0 n1) (<= n1 n2))
   (and
    (bv-eq (bv-not n1 (bv-and n2 x y))
           (bv-or n1 (bv-not n1 x) (bv-not n1 y)))

    (bv-eq (bv-not n1 (bv-or n2 x y))
           (bv-and n1 (bv-not n1 x) (bv-not n1 y))))))

(defthm drive-b-not-inwards
  (and
   (iff (b-not (b-iff a b))
        (b-iff (b-not a) b))

   (iff (b-not (b-if a b c))
        (b-if a (b-not b) (b-not c)))

   (iff (b-not (b-not a))
        a)))

;; not-checked
(defthm bv-not-cancelation
  (and
   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-not n1 (bv-not n2 y))
           (bv-resize n1 y)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-and n1 x (bv-not n2 x))
           (fill0 n1)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-and n1 (bv-not n2 x) x)
           (fill0 n1)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2) (quotep n3)))
         (natp n1) (natp n2) (natp n3)
         (< 0 n1) (<= n1 n2) (<= n1 n3))
    (bv-eq (bv-and n1 (bv-not n2 x) (bv-and n3 x y))
           (fill0 n1)))))

;; not-checked
(defthm push-bv-neg-around
  (implies
   (and (syntaxp (and (quotep n1) (quotep n2)))
        (natp n1) (natp n2)
        (< 0 n1) (<= n1 n2))
   (and (bv-eq (bv-neg n1 (bv-add n2 x y))
               (bv-add n1 (bv-neg n1 x) (bv-neg n1 y)))

        (bv-eq (bv-mul n1 (bv-neg n2 x) y)
               (bv-neg n1 (bv-mul n1 x y)))

        (bv-eq (bv-mul n1 x (bv-neg n2 y))
               (bv-neg n1 (bv-mul n1 x y))))))

;; not-checked
(defthm bv-neg-cancelation
  (and
   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-neg n1 (bv-neg n2 x))
           (bv-resize n1 x)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-add n1 x (bv-neg n2 x))
           (fill0 n1)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2) (quotep n3)))
         (natp n1) (natp n2) (natp n3)
         (< 0 n1) (<= n1 n2) (<= n2 n3))
    (bv-eq (bv-add n1 x (bv-add n2 (bv-neg n3 x) y))
           (bv-resize n1 y)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-add n1 (bv-neg n2 x) x)
           (fill0 n1)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2) (quotep n3)))
         (natp n1) (natp n2) (natp n3)
         (< 0 n1) (<= n1 n2) (<= n1 n3))
    (bv-eq (bv-add n1 (bv-neg n2 x) (bv-add n3 x y))
           (bv-resize n1 y)))))

;; not checked
;; I'm not confident of this rule!  I'd really like to prove
;; at least part of it!!!
(defthm remove-bv-resize
  (and
   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (iff (bv-s-negp n1 (bv-resize n2 x))
         (bv-s-negp n1 x)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2) (quotep hbit) (quotep lbit)))
         (natp n1) (natp n2) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 n2))
    (bv-eq (bv-ex n1 hbit lbit (bv-resize n2 x))
           (bv-ex n1 hbit lbit x)))

   (implies
    (and (syntaxp (and (quotep nx) (quotep ny) (quotep nx2)))
         (natp nx) (natp ny) (natp nx2)
         (< 0 nx) (< 0 ny) (<= nx nx2))
    (bv-eq (bv-concat nx ny (bv-resize nx2 x) y)
           (bv-concat nx ny x y)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-not n1 (bv-resize n2 x))
           (bv-not n1 x)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-and n1 (bv-resize n2 x) y)
           (bv-and n1 x y)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-and n1 x (bv-resize n2 y))
           (bv-and n1 x y)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-or n1 (bv-resize n2 x) y)
           (bv-or n1 x y)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-or n1 x (bv-resize n2 y))
           (bv-or n1 x y)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-add n1 (bv-resize n2 x) y)
           (bv-add n1 x y)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-add n1 x (bv-resize n2 y))
           (bv-add n1 x y)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-neg n1 (bv-resize n2 x))
           (bv-neg n1 x)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-mul n1 (bv-resize n2 x) y)
           (bv-mul n1 x y)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-mul n1 x (bv-resize n2 y))
           (bv-mul n1 x y)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (iff (bv-lt n1 (bv-resize n2 x) y)
         (bv-lt n1 x y)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (iff (bv-lt n1 x (bv-resize n2 y))
         (bv-lt n1 x y)))

   (implies
    (and (syntaxp (and (quotep n1) (quotep n2)))
         (natp n1) (natp n2)
         (< 0 n1) (<= n1 n2))
    (bv-eq (bv-repeat n1 (bv-resize n2 x) j)
           (bv-repeat n1 x j)))))

;; not checked
(defthm bv-lt-x-x
  (iff (bv-lt n x x) nil))

;; not checked
(defthm bv-ex-into-bv-not
  (implies
   (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
        (natp n2) (natp n1) (natp hbit) (natp lbit)
        (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 n2))
   (bv-eq (bv-ex n1 hbit lbit (bv-not n2 x))
          (bv-not (+ hbit (- lbit) 1)
                  (bv-ex n2
                         (rel-bit n2 n1 hbit)
                         (rel-bit n2 n1 lbit)
                         x)))))

;; not checked
(defthm bv-ex-into-bv-and
  (implies
   (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
        (natp n2) (natp n1) (natp hbit) (natp lbit)
        (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 n2))
   (bv-eq (bv-ex n1 hbit lbit (bv-and n2 x y))
          (bv-and (+ hbit (- lbit) 1)
                  (bv-ex n2
                         (rel-bit n2 n1 hbit)
                         (rel-bit n2 n1 lbit)
                         x)
                  (bv-ex n2
                         (rel-bit n2 n1 hbit)
                         (rel-bit n2 n1 lbit)
                         y)))))

;; not checked
(defthm bv-ex-into-bv-or
  (implies
   (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
        (natp n2) (natp n1) (natp hbit) (natp lbit)
        (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 n2))
   (bv-eq (bv-ex n1 hbit lbit (bv-or n2 x y))
          (bv-or (+ hbit (- lbit) 1)
                 (bv-ex n2
                        (rel-bit n2 n1 hbit)
                        (rel-bit n2 n1 lbit)
                        x)
                 (bv-ex n2
                        (rel-bit n2 n1 hbit)
                        (rel-bit n2 n1 lbit)
                        y)))))

;; not checked
(defthm bv-ex-into-bv-add
  (implies
   (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
        (natp n2) (natp n1) (natp hbit) (natp lbit)
        (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 n2))
   (bv-eq (bv-ex n1 hbit lbit (bv-add n2 x y))
          (bv-resize (- (1+ hbit) lbit)
                     (bv-add (+ 1 (rel-bit n2 n1 hbit))
                             (bv-ex n2 (rel-bit n2 n1 hbit) 0 x)
                             (bv-ex n2 (rel-bit n2 n1 hbit) 0 y))))))

;; not checked
(defthm bv-ex-into-bv-mul
  (implies
   (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
        (natp n2) (natp n1) (natp hbit) (natp lbit)
        (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 n2))
   (bv-eq (bv-ex n1 hbit lbit (bv-mul n2 x y))
          (bv-resize (- (1+ hbit) lbit)
                     (bv-mul (+ 1 (rel-bit n2 n1 hbit))
                             (bv-ex n2 (rel-bit n2 n1 hbit) 0 x)
                             (bv-ex n2 (rel-bit n2 n1 hbit) 0 y))))))

;; n1=15, n2=5, j=3, hbit=10, lbit=3
;; (bv-ex 15 10 3 (bv-repeat 5 x 3)) => (bv-concat 1 7 (bv-ex 5 0 0 x)
;;                                                 (bv-concat 5 2 (bv-repeat 5 x 1)
;;                                                            (bv-ex 5 4 3 x)))

;; n1=15, n2=5, j=5, hbit=10, lbit=0
;; (bv-ex 15 10 3 (bv-repeat 5 x 3)) => (bv-concat 1 10 (bv-ex 5 0 0 x)
;;                                                 (bv-repeat 5 x 2))
;;

;; n1=21, n2=7, j=3, hbit=19, lbit=4
;; (bv-ex 21 19 4 (bv-repeat 7 x 3)) => (bv-concat 6 10 (bv-ex 7 5 0 x)
;;                                                 (bv-concat 7 3 (bv-repeat 7 x 1)
;;                                                            (bv-ex 7 6 4 x)))


(defun ex-rep-lsize (n1 n2 j lbit)
  (let* ((lbit (rel-bit (* n2 j) n1 lbit)))
    (- n2 (mod lbit n2))))

(defun ex-rep-j (n1 n2 j hbit lbit)
  (let* ((lsize (ex-rep-lsize n1 n2 j lbit)))
    (floor (- (1+ (- hbit lbit)) lsize) n2)))

(defun ex-rep-hsize (n1 n2 j hbit)
  (let* ((hbit (rel-bit (* n2 j) n1 hbit)))
    (mod (1+ hbit) n2)))

;; No split is needed if hbit and lbit fit
;; into a single repetition.
(defun ex-rep-splitp (n1 n2 j hbit lbit)
  (let ((hbit (rel-bit (* n2 j) n1 hbit))
        (lbit (rel-bit (* n2 j) n1 lbit)))
    (not (equal (floor hbit n2)
                (floor lbit n2)))))

;; not checked
(defthm bv-ex-into-bv-repeat
  (and
   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (ex-rep-splitp n1 n2 j hbit lbit)
         (not (zp (ex-rep-hsize n1 n2 j hbit)))
         (not (zp (ex-rep-lsize n1 n2 j lbit)))
         (not (zp (ex-rep-j n1 n2 j hbit lbit)))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
      (bv-concat
       (ex-rep-hsize n1 n2 j hbit)
       (+ 1 hbit (- lbit) (- (ex-rep-hsize n1 n2 j hbit)))
       (bv-ex n2 (1- (ex-rep-hsize n1 n2 j hbit)) 0 x)
       (bv-concat
        (* (ex-rep-j n1 n2 j hbit lbit) n2)
        (ex-rep-lsize n1 n2 j lbit)
        (bv-repeat n2 x (ex-rep-j n1 n2 j hbit lbit))
        (bv-ex n2 (1- n2) (- n2 (ex-rep-lsize n1 n2 j lbit)) x)))))

   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (ex-rep-splitp n1 n2 j hbit lbit)
         (not (zp (ex-rep-hsize n1 n2 j hbit)))
         (not (zp (ex-rep-lsize n1 n2 j lbit)))
         (zp (ex-rep-j n1 n2 j hbit lbit))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
      (bv-concat
       (ex-rep-hsize n1 n2 j hbit)
       (+ 1 hbit (- lbit) (- (ex-rep-hsize n1 n2 j hbit)))
       (bv-ex n2 (1- (ex-rep-hsize n1 n2 j hbit)) 0 x)
       (bv-ex n2 (1- n2) (- n2 (ex-rep-lsize n1 n2 j lbit)) x))))

   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (ex-rep-splitp n1 n2 j hbit lbit)
         (not (zp (ex-rep-hsize n1 n2 j hbit)))
         (zp (ex-rep-lsize n1 n2 j lbit))
         (not (zp (ex-rep-j n1 n2 j hbit lbit)))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-concat
      (ex-rep-hsize n1 n2 j hbit)
      (+ 1 hbit (- lbit) (- (ex-rep-hsize n1 n2 j hbit)))
      (bv-ex n2 (1- (ex-rep-hsize n1 n2 j hbit)) 0 x)
      (bv-repeat n2 x (ex-rep-j n1 n2 j hbit lbit)))))


   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (ex-rep-splitp n1 n2 j hbit lbit)
         (not (zp (ex-rep-hsize n1 n2 j hbit)))
         (zp (ex-rep-lsize n1 n2 j lbit))
         (zp (ex-rep-j n1 n2 j hbit lbit))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-ex n2 (1- (ex-rep-hsize n1 n2 j hbit)) 0 x)))

   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (ex-rep-splitp n1 n2 j hbit lbit)
         (zp (ex-rep-hsize n1 n2 j hbit))
         (not (zp (ex-rep-lsize n1 n2 j lbit)))
         (not (zp (ex-rep-j n1 n2 j hbit lbit)))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-concat
      (* (ex-rep-j n1 n2 j hbit lbit) n2)
      (ex-rep-lsize n1 n2 j lbit)
      (bv-repeat n2 x (ex-rep-j n1 n2 j hbit lbit))
      (bv-ex n2 (1- n2) (- n2 (ex-rep-lsize n1 n2 j lbit)) x))))

   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (ex-rep-splitp n1 n2 j hbit lbit)
         (zp (ex-rep-hsize n1 n2 j hbit))
         (not (zp (ex-rep-lsize n1 n2 j lbit)))
         (zp (ex-rep-j n1 n2 j hbit lbit))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-ex n2 (1- n2) (- n2 (ex-rep-lsize n1 n2 j lbit)) x)))

   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (ex-rep-splitp n1 n2 j hbit lbit)
         (zp (ex-rep-hsize n1 n2 j hbit))
         (zp (ex-rep-lsize n1 n2 j lbit))
         (not (zp (ex-rep-j n1 n2 j hbit lbit)))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-repeat n2 x (ex-rep-j n1 n2 j hbit lbit))))

   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (ex-rep-splitp n1 n2 j hbit lbit)
         (zp (ex-rep-hsize n1 n2 j hbit))
         (zp (ex-rep-lsize n1 n2 j lbit))
         (zp (ex-rep-j n1 n2 j hbit lbit))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (fill0 (+ 1 hbit (- lbit)))))


   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (not (ex-rep-splitp n1 n2 j hbit lbit))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-ex n2
            (mod (rel-bit (* n2 j) n1 hbit) n2)
            (mod (rel-bit (* n2 j) n1 lbit) n2)
            x)))
   ))


(defthm bv-concat-0A
  (bv-eq (bv-concat nx 0 x y)
         x))

(defthm bv-concat-0B
  (bv-eq (bv-concat 0 ny x y)
         y))

;; not checked
(defthm bv-ex-into-bv-ex
  (implies
   (and (syntaxp (and (quotep n1) (quotep n2)
                      (quotep hbit1) (quotep lbit1)
                      (quotep hbit2) (quotep lbit2)))
        (<= 0 lbit1) (<= lbit1 hbit1) (< hbit1 n1)
        (<= 0 lbit2) (<= lbit2 hbit2) (< hbit2 n2)
        (<= n1 (1+ (- hbit2 lbit2))))
   (bv-eq (bv-ex n1 hbit1 lbit1 (bv-ex n2 hbit2 lbit2 x))
          (bv-ex n2
                 (- hbit2 (- n1 (1+ hbit1)))
                 (+ lbit2 lbit1)
                 x))))

;; (bv-ex 10 7 3 (bv-ex 20 15 6))
;; =
;; (bv-ex 20 13 9)

;; (bv-ex 20 (- 15 (- 10 (1+ 7))) (+ 6 3))

;; (bv-ex 20 (+ 15 (- 10 7)

;; n1=2, hbit1=1, lbit1=1, n2=3, hbit2=1, lbit2=0
;; (bv-ex 2 1 1 (bv-ex 3 1 0 x))
;; =
;; (bv-ex 3 (- 1 (- 2 (1+ 1))) (- 0 (- 2 (1+ 1))) x)
;; =
;; (bv-ex 3 1 0 x)

;;(bv-ex 32 30 0 (bv-concat 24 8 x y))
;;=
;;(bv-concat 23 8 (bv-ex 24 22 0 x) y)

;;(bv-ex 32 30 3 (bv-concat 24 8 x y))
;;=
;;(bv-concat 23 5 (bv-ex 24 22 0 x) y)

;;(bv-ex 32 7 3 (bv-concat 24 8 x y))
;;=
;;(bv-ex 8 7 3 y)

;;(bv-ex 32 30 10 (bv-concat 24 8 x y))
;;=
;;(bv-ex 24 22 2 x)

;;(bv-ex 10 7 2 (bv-concat 7 3 x y))
;;=
;;(bv-concat 5 1 (bv-ex 7 4 0 x) (bv-ex 3 2 2 y))

;; partially-checked
(defthm bv-ex-into-bv-concat
  (and
   (implies
    (and (syntaxp (and (quotep n) (quotep nx) (quotep ny) (quotep hbit) (quotep lbit)))
         (natp n) (natp nx) (natp ny) (natp hbit) (natp lbit)
         (< 0 ny) (<= ny (rel-bit (+ nx ny) n lbit))
         (< lbit hbit) (< hbit n) (<= n (+ nx ny)))
    (bv-eq (bv-ex n hbit lbit (bv-concat nx ny x y))
           (bv-ex nx (- nx (- n hbit)) (- nx (- n lbit)) x)))

   (implies
    (and (syntaxp (and (quotep n) (quotep nx) (quotep ny) (quotep hbit) (quotep lbit)))
         (natp n) (natp nx) (natp ny) (natp hbit) (natp lbit)
         (<= 0 lbit)
         (< (rel-bit (+ nx ny) n lbit) ny)
         (< (rel-bit (+ nx ny) n hbit) ny)
         (< lbit hbit) (< hbit n) (<= n (+ nx ny)))
    (bv-eq (bv-ex n hbit lbit (bv-concat nx ny x y))
           (bv-ex ny (rel-bit (+ nx ny) n hbit) (rel-bit (+ nx ny) n lbit)
                  y)))

   (implies
    (and (syntaxp (and (quotep n) (quotep nx) (quotep ny) (quotep hbit) (quotep lbit)))
         (natp n) (natp nx) (natp ny) (natp hbit) (natp lbit)
         (<= 0 lbit)
         (< (rel-bit (+ nx ny) n lbit) ny)
         (<= ny (rel-bit (+ nx ny) n hbit))
         (< hbit n) (<= n (+ nx ny)))
    (bv-eq (bv-ex n hbit lbit (bv-concat nx ny x y))
           (bv-concat (+ 1 (rel-bit nx n hbit))
                      (+ (- n lbit) (- nx))
                      (bv-ex nx
                             (rel-bit nx n hbit)
                             0
                             x)
                      y)))))

;; (bv-ex 13 7 1 (bv-concat 10 7 x y))
;; =
;; (bv-concat 5 2 (bv-ex 10 4 0 x) y)

(defthm cancel-equal-+-*
  (and (iff (bv-eq (bv-add n x y) x)
            (bv-eq y nil))
       (iff (bv-eq (bv-add n y x) x)
            (bv-eq y nil))
       ;; Case split!!!
       (iff (bv-eq (bv-mul n x y) x)
            (or (bv-eq x nil) (bv-eq y (bv-const n 1))))
       ;; Case split!!!
       (iff (bv-eq (bv-mul n x y) y)
            (or (bv-eq y nil) (bv-eq x (bv-const n 1))))))

(defthm normalize-equal-0
  (and
   (implies
    (and (syntaxp (quotep zero))
         (bv-eq zero nil))
    (iff (bv-eq (bv-neg n x) zero)
         (bv-eq x nil)))
   (implies
    (and (syntaxp (quotep zero))
         (bv-eq zero nil))
    (iff (bv-eq (bv-add n x y) zero)
         (bv-eq x (bv-neg n y))))
   (implies
    (and (syntaxp (quotep zero))
         (bv-eq zero nil))
    ;; Case split!!!
    (iff (bv-eq (bv-mul n x y) zero)
         (or (bv-eq x zero)
             (bv-eq y nil))))))

(defthm normalize-<-minus
  (and (implies
        (and (syntaxp (quotep zero))
             (bv-eq zero nil))
        (iff (bv-lt n (bv-neg n x) zero)
             (bv-lt n nil x)))
       (implies
        (and (syntaxp (quotep zero))
             (bv-eq zero nil))
        (iff (bv-lt n zero (bv-neg n x))
             (bv-lt n x nil)))
        (iff (bv-lt n (bv-neg n x) (bv-neg n y))
             (bv-lt n x y))))

))


;; -----------------------------------------------------------
;; Logical primitives

(defthm b-not-b-not
  (iff (b-not (b-not a))
       a)
  :hints (("Goal" :in-theory (enable b-not b-not-raw))))

(skip-proofs
(defthm bv-equiv-symmetry
  (and
   (implies
    (syntaxp (not (term-order (strip-unary-b-fn 'b-not a) (strip-unary-b-fn 'b-not b))))
    (iff (b-iff a b)
         (b-iff b a)))

   (implies
    (syntaxp (term-order (strip-unary-b-fn 'b-not a) (strip-unary-b-fn 'b-not b)))
    (iff (b-iff (b-not a) b)
         (b-iff a (b-not b))))

   (implies
    (syntaxp (not (term-order (strip-unary-bv-fn 'bv-not a) (strip-unary-bv-fn 'bv-not b))))
    (iff (bv-eq a b)
         (bv-eq b a)))

   ;; There should probably be a check that b's size is n...
   (implies
    (syntaxp (term-order (strip-unary-bv-fn 'bv-not a) (strip-unary-bv-fn 'bv-not b)))
    (iff (bv-eq (bv-not n a) b)
         (bv-eq a (bv-not n b))))))
)

(defthm b-if-simplifications
  (and
   (iff (b-if (b-not a) b c)
        (b-if a c b))

   (equal (b-if a x x)
          x)
   (iff (b-if a t nil)
        a)
   (equal (b-if a nil t)
          (b-not a))
   (implies
    a
    (equal (b-if a x y)
           x))
   (implies
    (b-not a)
    (equal (b-if a x y)
           y)))
  :hints (("Goal" :in-theory (enable b-if b-if-raw))))

(skip-proofs
(defthm bv-if-simplifications
  (and
   (bv-eq (bv-if n (b-not a) x y)
          (bv-if n a y x))

   (bv-eq (bv-if n a x x)
          (bv-resize n x))

   (implies
    a
    (bv-eq (bv-if n a x y)
           (bv-resize n x)))

   (implies
    (not a)
    (bv-eq (bv-if n a x y)
           (bv-resize n y)))))
)

(mutual-recursion
(defun b-if-meta1-list (test-term posp term-list changed acc)
  (declare (xargs :guard (and (pseudo-termp test-term)
                              (pseudo-term-listp term-list)
                              (booleanp changed)
                              (true-listp acc))
                  :verify-guards nil))
  (cond
   ((endp term-list)
    (mv changed (revappend acc term-list)))
   (t
    (mv-let
     (car-changed new-car-term)
     (b-if-meta1 test-term posp (car term-list) changed)
     (b-if-meta1-list test-term posp (cdr term-list) (or car-changed changed)
                      (cons new-car-term acc))))))

;; Simplifies (b-if a (... (b-if a b c) ...) (...))
;; to (b-if a (... b ...) (...))
;; and returns whether any changes were made (so that
;; we don't create a new term if we don't have to).

(defun b-if-meta1 (test-term posp term changed)
  (declare (xargs :guard (and (pseudo-termp test-term)
                              (booleanp posp)
                              (pseudo-termp term))
                  :verify-guards nil))
  (cond
   ((or (atom term) (quotep term))
    (mv changed term))
   ((equal test-term term)
    (mv t (if posp `(d-known-truth ,test-term) nil)))
   ((and (equal (car term) 'not)
         (equal (cadr term) test-term))
    (mv t (if posp nil `(d-known-truth ,test-term))))
   ((and (equal (car term) 'b-if)
         (equal (length term) 4))
    (let ((i-test-term (cadr term))
          (true-br (caddr term))
          (false-br (cadddr term)))
      (cond
       ((equal i-test-term test-term)
        (b-if-meta1 test-term posp (if posp true-br false-br) t))
       (t
        (mv-let
         (args-changed new-args)
         (b-if-meta1-list test-term posp (cdr term) nil nil)
         (mv (or changed args-changed)
             (if args-changed `(b-if . ,new-args) term)))))))

   ((and (equal (car term) 'bv-if)
         (equal (length term) 5))
    (let (;;(size (cadr term))
          (i-test-term (caddr term))
          (true-br (cadddr term))
          (false-br (cadr (cdddr term))))
      (cond
       ((equal i-test-term test-term)
        (b-if-meta1 test-term posp (if posp true-br false-br) t))
       (t
        (mv-let
         (args-changed new-args)
         (b-if-meta1-list test-term posp (cdr term) nil nil)
         (mv (or changed args-changed)
             (if args-changed `(bv-if . ,new-args) term)))))))
   (t
    (mv-let
     (args-changed new-args)
     (b-if-meta1-list test-term posp (cdr term) nil nil)
     (mv (or changed args-changed)
         (if args-changed `(,(car term) . ,new-args) term))))))
)

(skip-proofs (verify-guards b-if-meta1))

(defun b-not-callp (x)
  (declare (xargs :guard t))
  (and (consp x) (eq 'b-not (car x))))

(defun b-if-meta (term)
  (declare (xargs :guard (pseudo-termp term)))
  (cond
   ((and (consp term)
         (equal (car term) 'b-if)
         (equal (length term) 4)
         (not (b-not-callp (cadr term))))
    (let ((condition (cadr term))
          (true-br (caddr term))
          (false-br (cadr (cddr term))))
      (mv-let
       (true-br-changed new-true-br)
       (b-if-meta1 condition t true-br nil)
       (mv-let
        (false-br-changed new-false-br)
        (b-if-meta1 condition nil false-br nil)
        (cond
         ((or true-br-changed false-br-changed)
          `(b-if ,condition ,new-true-br ,new-false-br))
         (t
          term))))))

   ((and (consp term)
         (equal (car term) 'bv-if)
         (equal (length term) 5)
         (not (b-not-callp (caddr term))))
    (let ((size (cadr term))
          (condition (caddr term))
          (true-br (cadddr term))
          (false-br (cadr (cdddr term))))
      (mv-let
       (true-br-changed new-true-br)
       (b-if-meta1 condition t true-br nil)
       (mv-let
        (false-br-changed new-false-br)
        (b-if-meta1 condition nil false-br nil)
        (cond
         ((or true-br-changed false-br-changed)
          `(bv-if ,size ,condition ,new-true-br ,new-false-br))
         (t
          term))))))

   (t
    term)))

;; I can't define the meta theorem I want because I don't
;; have all the functions I need to evaluate.  So instead
;; I'm using a macro that the user can call once all the
;; functions are known

(defmacro def-b-if-meta (fn-lst)
  `(skip-proofs
    (encapsulate
     nil
     (defevaluator bv-eval bv-eval-list ,fn-lst)

     (defthm b-if-meta-lemma
       (equal (bv-eval term a)
              (bv-eval (b-if-meta term) a))
       :rule-classes ((:meta :trigger-fns (b-if bv-if)))))))

#|
;; A little proof to help justify removing bv-resize

(defthm rem-extra-bits-raw-help
  (implies
   (not (zp n))
   (equal (car (rem-extra-bits-raw n x))
          (car x)))
  :hints (("Goal" :expand (rem-extra-bits-raw n x))))

(thm
 (implies
  (and (natp n1) (natp n2)
       (< 0 n1) (<= n1 n2))
  (iff (bv-s-negp n1 (bv-resize n2 x))
       (bv-s-negp n1 x)))
 :hints (("Goal" :in-theory (enable bv-s-negp bv-resize bv-s-negp-raw
                                    rem-extra-bits-raw))))
|# ;|


#|

;; I'm using the SAT engine to check my rewrite rules,
;; though I'm just using bv-eq instead of equal.
;; Note that bv-eq is really what I want anyway.

(include-book "../clause-processors/sat-clause-processor")

(deftheory raw-bv-only-theory
  (union-theories ;;(theory 'pre-bv-lemma-theory)
   (current-theory :here)
   '(B-KNOWN-TRUTH B-CONC B-HYP B-NOT
                   B-IFF BV-IF B-IF BV-RESIZE BV-REPEAT
                   BV-S-LT BV-LT BV-MUL BV-NEG BV-ADD BV-OR
                   BV-AND BV-NOT BV-CONCAT BV-EX BV-S-NEGP
                   BV-CONST FILL1 FILL0 BV-TO-NUM BV-EQ)))

(defun sat-when-stable (stable-under-simplificationp)
  (if stable-under-simplificationp
      `(:external (sat nil $sat))
    nil))

(thm
 (let ((n 13)
       (hbit 1)
       (lbit 0)
       (nx 10)
       (ny 7)
       (x (make-bv 10 x0))
       (y (make-bv 7 y0)))
   (and
    (implies
     (and (syntaxp (and (quotep n) (quotep nx) (quotep ny) (quotep hbit) (quotep lbit)))
          (natp n) (natp nx) (natp ny) (natp hbit) (natp lbit)
          (< 0 ny) (<= ny (rel-bit (+ nx ny) n lbit))
          (< lbit hbit) (< hbit n) (<= n (+ nx ny)))
     (bv-eq (bv-ex n hbit lbit (bv-concat nx ny x y))
            (bv-ex nx (- nx (- n hbit)) (- nx (- n lbit)) x)))

    (implies
     (and (syntaxp (and (quotep n) (quotep nx) (quotep ny) (quotep hbit) (quotep lbit)))
          (natp n) (natp nx) (natp ny) (natp hbit) (natp lbit)
          (<= 0 lbit)
          (< (rel-bit (+ nx ny) n lbit) ny)
          (< (rel-bit (+ nx ny) n hbit) ny)
          (< lbit hbit) (< hbit n) (<= n (+ nx ny)))
     (bv-eq (bv-ex n hbit lbit (bv-concat nx ny x y))
            (bv-ex ny (rel-bit (+ nx ny) n hbit) (rel-bit (+ nx ny) n lbit)
                   y)))

    (implies
     (and (syntaxp (and (quotep n) (quotep nx) (quotep ny) (quotep hbit) (quotep lbit)))
          (natp n) (natp nx) (natp ny) (natp hbit) (natp lbit)
          (<= 0 lbit)
          (< (rel-bit (+ nx ny) n lbit) ny)
          (<= ny (rel-bit (+ nx ny) n hbit))
          (< hbit n) (<= n (+ nx ny)))
     (bv-eq (bv-ex n hbit lbit (bv-concat nx ny x y))
            (bv-concat (+ 1 (rel-bit nx n hbit))
                       (+ (- n lbit) (- nx))
                       (bv-ex nx
                              (rel-bit nx n hbit)
                              0
                              x)
                       y)))))
 :hints (("Goal" :in-theory (theory 'raw-bv-only-theory))
         (sat-when-stable stable-under-simplificationp)))

(thm
 (bv-eq (bv-ex 7 5 2 (bv-ex 10 8 2 (make-bv 10 x)))
        (bv-ex 10
               (- 8 (- 7 (1+ 5)))
               (+ 2 2)
               (make-bv 10 x)))
 :hints (("Goal" :in-theory (theory 'raw-bv-only-theory))
         (sat-when-stable stable-under-simplificationp)))

(thm
 (iff (bv-eq (bv-concat 6 4 (make-bv 6 x0) (make-bv 4 y0)) (make-bv 10 z0))
      (let ((z-size (bv-size (make-bv 10 z0))))
        (b-if (bv-eq (make-bv 6 x0) (bv-ex z-size (+ z-size -1) (+ z-size (- 6)) (make-bv 10 z0)))
              (bv-eq (make-bv 4 y0) (bv-ex z-size
                              (+ z-size (- 6) -1)
                              (+ z-size (- 6) (- 4))
                              (make-bv 10 z0)))
              nil)))
 :hints (("Goal" :in-theory (theory 'raw-bv-only-theory))
         (sat-when-stable stable-under-simplificationp)))

(thm
 (iff (bv-eq (make-bv 10 z0) (bv-concat 6 4 (make-bv 6 x0) (make-bv 4 y0)))
      (let ((z-size (bv-size (make-bv 10 z0))))
        (b-if (bv-eq (bv-ex z-size
                            (+ z-size -1)
                            (+ z-size (- 6))
                            (make-bv 10 z0))
                     (make-bv 6 x0))
              (bv-eq (bv-ex z-size
                            (+ z-size (- 6) -1)
                            (+ z-size (- 6) (- 4))
                            (make-bv 10 z0))
                     (make-bv 4 y0))
              nil)))
   :hints (("Goal" :in-theory (theory 'raw-bv-only-theory))
           (sat-when-stable stable-under-simplificationp)))

;; n1=10, n2=12, hbit=7, lbit=3
(thm
 (bv-eq 5
        (bv-ex 10 7 3 (bv-add 12 x y))
        (bv-add (+ 1 (rel-bit 12 10 7))
                (bv-ex 12 (rel-bit 12 10 7) 0 x)
                (bv-ex 12 (rel-bit 12 10 7) 0 y)))
  :hints (("Goal" :external (sat nil $sat))))

;; n1=10, n2=12, hbit=7, lbit=3
(thm
 (bv-eq 5
        (bv-ex 10 7 3 (bv-mul 12 x y))
        (bv-mul (+ 1 (rel-bit 12 10 7))
                (bv-ex 12 (rel-bit 12 10 7) 0 x)
                (bv-ex 12 (rel-bit 12 10 7) 0 y)))
 :hints (("Goal" :external (sat nil $sat))))

(thm
 (bv-eq 5 (bv-mul 5 x y) (bv-mul 5 y x))
 :hints (("Goal" :external (sat nil $sat))))

(thm
 (bv-eq 5
        (bv-ex 10 7 3 (bv-mul 12 x (bv-ex 12 11 0 y)))
        (bv-mul 10
                (bv-ex 12 9 0 x)
                (bv-ex 12 9 0 y)))
 :hints (("Goal" :external (sat nil $sat))))



;; n=15, nx=8, ny=7, hbit=10, lbit=2
(thm
 (bv-eq 6
        (bv-ex 15 10 5 (bv-concat 8 7 a b))
        (bv-concat (+ 1 (rel-bit (+ 8 7) 15 10) (- 7))
                   (+ 1 (rel-bit (+ 8 7) 15 5))
                   (bv-ex 8
                          (+ (rel-bit (+ 8 7) 15 10) (- 7))
                          0
                          a)
                   b))
 :hints (("Goal" :external (sat nil $sat))))

;; n=13, nx=8, ny=7, hbit=10, lbit=2
(thm
 (bv-eq 6
        (bv-ex 13 10 2 (bv-concat 8 7 a b))
        (bv-concat (+ 1 (rel-bit (+ 8 7) 13 10) (- 7))
                   (+ 1 (rel-bit (+ 8 7) 13 2))
                   (bv-ex 8
                          (+ (rel-bit (+ 8 7) 13 10) (- 7))
                          0
                          a)
                   b))
 :hints (("Goal" :external (sat nil $sat))))

;; nx=8, ny=20, n=25, hbit=10, lbit=5
(thm
 (bv-eq 6
        (bv-ex 25 10 5 (bv-concat 8 20 a b))
        (bv-ex 20 (rel-bit (+ 8 20) 25 10) (rel-bit (+ 8 20) 25 5)
               b))
  :hints (("Goal" :external (sat nil $sat))))

;; nx=20, ny=8, n=25, hbit=12, lbit=7
(thm ;;bv-ex-into-bv-concat-3
 (bv-eq 6
        (bv-ex 25 12 7 (bv-concat 20 8 x y))
        (bv-ex 20 (+ 20 (- 25 12)) (+ 20 (- 25 7)) x))
  :hints (("Goal" :external (sat nil $sat))))

;; nx=20, ny=8, n=28, hbit=12, lbit=7
(thm ;;bv-ex-into-bv-concat-3
 (bv-eq 6
        (bv-ex 25 12 7 (bv-concat 20 8 x y))
        (bv-ex 20 (- 20 (- 25 12)) (- 20 (- 25 7)) x))
  :hints (("Goal" :external (sat nil $sat))))

;; n2=20, n1=11, hbit2=15, lbit2=5, hbit1=9,lbit1=5
(thm ;;bv-ex-into-bv-ex
 (bv-eq (bv-ex 11 9 5 (bv-ex 20 15 5 x))
        (bv-ex 20
               (- 15 (- 11 (1+ 9)))
               (- 5 (- 11 (1+ 5)))
               x))
  :hints (("Goal" :external (sat nil $sat))))

(thm
 (bv-eq 8 (bv-rotate-left 8 x 3)
         (bv-concat (- 8 3) 3 (bv-ex 8 (+ 8 (- 3) (- 1)) 0 x) x))
  :hints (("Goal" :external (sat nil $sat))))

(thm
 (bv-eq 10
        (bv-rotate-right 10 x 4)
        (bv-concat 4 (- 10 4) (bv-ex 10 3 0 x) x))
  :hints (("Goal" :external (sat nil $sat))))

;; n2=10, n1=8, hbit=6, lbit=2
(thm ;;bv-ex-into-bv-not
 (bv-eq 5
        (bv-ex 8 6 2 (bv-not 10 x))
        (bv-not (+ 6 (- 2) 1)
                (bv-ex 10
                       (rel-bit 10 8 6)
                       (rel-bit 10 8 2)
                       x)))
  :hints (("Goal" :external (sat nil $sat))))

;; n2=10, n1=8, hbit=6, lbit=2
(thm ;;bv-ex-into-bv-and
 (bv-eq 5
        (bv-ex 8 6 2 (bv-and 10 x y))
        (bv-and (+ 6 (- 2) 1)
                (bv-ex 10
                       (rel-bit 10 8 6)
                       (rel-bit 10 8 2)
                       x)
                (bv-ex 10
                       (rel-bit 10 8 6)
                       (rel-bit 10 8 2)
                       y)))
  :hints (("Goal" :external (sat nil $sat))))

;; n2=10, n1=8, hbit=4, lbit=0
(thm ;;bv-ex-into-bv-or
 (bv-eq 5
        (bv-ex 8 4 0 (bv-or 10 x y))
        (bv-or (+ 4 (- 0) 1)
               (bv-ex 10
                      (rel-bit 10 8 4)
                      (rel-bit 10 8 0)
                      x)
               (bv-ex 10
                      (rel-bit 10 8 4)
                      (rel-bit 10 8 0)
                      y)))
 :hints (("Goal" :external (sat nil $sat))))

;; n1=21, n2=7, j=5, hbit=18, lbit=2
(thm
 (bv-eq 17
  (bv-ex 21 18 2 (bv-repeat 7 x 5))
  (bv-concat
   (ex-rep-hsize 21 7 5 18)
   (+ 1 18 (- 2) (- (ex-rep-hsize 21 7 5 18)))
   (bv-ex 7 (1- (ex-rep-hsize 21 7 5 18)) 0 x)
   (bv-concat
    (* (ex-rep-j 21 7 5 18 2) 7)
    (ex-rep-lsize 21 7 5 2)
    (bv-repeat 7 x (ex-rep-j 21 7 5 18 2))
    (bv-ex 7 (1- 7) (- 7 (ex-rep-lsize 21 7 5 2)) x))))
 :hints ((sat-when-stable stable-under-simplificationp)))

(thm ;;bv-ex-into-bv-repeat
 (implies
  (and (equal n1 28)
       (equal n2 7)
       (equal j 4)
       (equal hbit 3)
       (equal lbit 3))
  (and
   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (not (zp (ex-rep-hsize n1 n2 j hbit)))
         (not (zp (ex-rep-lsize n1 n2 j lbit)))
         (not (zp (ex-rep-j n1 n2 j hbit lbit)))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq (+ 1 hbit (- lbit))
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-concat
      (ex-rep-hsize n1 n2 j hbit)
      (+ 1 hbit (- lbit) (- (ex-rep-hsize n1 n2 j hbit)))
      (bv-ex n2 (1- (ex-rep-hsize n1 n2 j hbit)) 0 x)
      (bv-concat
       (* (ex-rep-j n1 n2 j hbit lbit) n2)
       (ex-rep-lsize n1 n2 j lbit)
       (bv-repeat n2 x (ex-rep-j n1 n2 j hbit lbit))
       (bv-ex n2 (1- n2) (- n2 (ex-rep-lsize n1 n2 j lbit)) x)))))

   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (not (zp (ex-rep-hsize n1 n2 j hbit)))
         (not (zp (ex-rep-lsize n1 n2 j lbit)))
         (zp (ex-rep-j n1 n2 j hbit lbit))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq (+ 1 hbit (- lbit))
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-concat
      (ex-rep-hsize n1 n2 j hbit)
      (+ 1 hbit (- lbit) (- (ex-rep-hsize n1 n2 j hbit)))
      (bv-ex n2 (1- (ex-rep-hsize n1 n2 j hbit)) 0 x)
      (bv-ex n2 (1- n2) (- n2 (ex-rep-lsize n1 n2 j lbit)) x))))

   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (not (zp (ex-rep-hsize n1 n2 j hbit)))
         (zp (ex-rep-lsize n1 n2 j lbit))
         (not (zp (ex-rep-j n1 n2 j hbit lbit)))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq (+ 1 hbit (- lbit))
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-concat
      (ex-rep-hsize n1 n2 j hbit)
      (+ 1 hbit (- lbit) (- (ex-rep-hsize n1 n2 j hbit)))
      (bv-ex n2 (1- (ex-rep-hsize n1 n2 j hbit)) 0 x)
      (bv-repeat n2 x (ex-rep-j n1 n2 j hbit lbit)))))


   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (not (zp (ex-rep-hsize n1 n2 j hbit)))
         (zp (ex-rep-lsize n1 n2 j lbit))
         (zp (ex-rep-j n1 n2 j hbit lbit))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq (+ 1 hbit (- lbit))
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-ex n2 (1- (ex-rep-hsize n1 n2 j hbit)) 0 x)))

   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (zp (ex-rep-hsize n1 n2 j hbit))
         (not (zp (ex-rep-lsize n1 n2 j lbit)))
         (not (zp (ex-rep-j n1 n2 j hbit lbit)))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq (+ 1 hbit (- lbit))
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-concat
      (* (ex-rep-j n1 n2 j hbit lbit) n2)
      (ex-rep-lsize n1 n2 j lbit)
      (bv-repeat n2 x (ex-rep-j n1 n2 j hbit lbit))
      (bv-ex n2 (1- n2) (- n2 (ex-rep-lsize n1 n2 j lbit)) x))))

   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (zp (ex-rep-hsize n1 n2 j hbit))
         (not (zp (ex-rep-lsize n1 n2 j lbit)))
         (zp (ex-rep-j n1 n2 j hbit lbit))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq (+ 1 hbit (- lbit))
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-ex n2 (1- n2) (- n2 (ex-rep-lsize n1 n2 j lbit)) x)))

   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (zp (ex-rep-hsize n1 n2 j hbit))
         (zp (ex-rep-lsize n1 n2 j lbit))
         (not (zp (ex-rep-j n1 n2 j hbit lbit)))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq (+ 1 hbit (- lbit))
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-repeat n2 x (ex-rep-j n1 n2 j hbit lbit))))

   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (zp (ex-rep-hsize n1 n2 j hbit))
         (zp (ex-rep-lsize n1 n2 j lbit))
         (zp (ex-rep-j n1 n2 j hbit lbit))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq (+ 1 hbit (- lbit))
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (fill0 (+ 1 hbit (- lbit)))))
   ))
  :hints ((sat-when-stable stable-under-simplificationp)))

(thm ;;bv-ex-into-bv-repeat
 (implies
  (and (equal n1 40)
       (equal n2 7)
       (equal j 6)
       (equal hbit 38)
       (equal lbit 3))
  (and
   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (ex-rep-splitp n1 n2 j hbit lbit)
         (not (zp (ex-rep-hsize n1 n2 j hbit)))
         (not (zp (ex-rep-lsize n1 n2 j lbit)))
         (not (zp (ex-rep-j n1 n2 j hbit lbit)))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq (+ 1 hbit (- lbit))
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-concat
      (ex-rep-hsize n1 n2 j hbit)
      (+ 1 hbit (- lbit) (- (ex-rep-hsize n1 n2 j hbit)))
      (bv-ex n2 (1- (ex-rep-hsize n1 n2 j hbit)) 0 x)
      (bv-concat
       (* (ex-rep-j n1 n2 j hbit lbit) n2)
       (ex-rep-lsize n1 n2 j lbit)
       (bv-repeat n2 x (ex-rep-j n1 n2 j hbit lbit))
       (bv-ex n2 (1- n2) (- n2 (ex-rep-lsize n1 n2 j lbit)) x)))))

   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (ex-rep-splitp n1 n2 j hbit lbit)
         (not (zp (ex-rep-hsize n1 n2 j hbit)))
         (not (zp (ex-rep-lsize n1 n2 j lbit)))
         (zp (ex-rep-j n1 n2 j hbit lbit))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq (+ 1 hbit (- lbit))
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-concat
      (ex-rep-hsize n1 n2 j hbit)
      (+ 1 hbit (- lbit) (- (ex-rep-hsize n1 n2 j hbit)))
      (bv-ex n2 (1- (ex-rep-hsize n1 n2 j hbit)) 0 x)
      (bv-ex n2 (1- n2) (- n2 (ex-rep-lsize n1 n2 j lbit)) x))))

   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (ex-rep-splitp n1 n2 j hbit lbit)
         (not (zp (ex-rep-hsize n1 n2 j hbit)))
         (zp (ex-rep-lsize n1 n2 j lbit))
         (not (zp (ex-rep-j n1 n2 j hbit lbit)))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq (+ 1 hbit (- lbit))
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-concat
      (ex-rep-hsize n1 n2 j hbit)
      (+ 1 hbit (- lbit) (- (ex-rep-hsize n1 n2 j hbit)))
      (bv-ex n2 (1- (ex-rep-hsize n1 n2 j hbit)) 0 x)
      (bv-repeat n2 x (ex-rep-j n1 n2 j hbit lbit)))))


   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (ex-rep-splitp n1 n2 j hbit lbit)
         (not (zp (ex-rep-hsize n1 n2 j hbit)))
         (zp (ex-rep-lsize n1 n2 j lbit))
         (zp (ex-rep-j n1 n2 j hbit lbit))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq (+ 1 hbit (- lbit))
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-ex n2 (1- (ex-rep-hsize n1 n2 j hbit)) 0 x)))

   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (ex-rep-splitp n1 n2 j hbit lbit)
         (zp (ex-rep-hsize n1 n2 j hbit))
         (not (zp (ex-rep-lsize n1 n2 j lbit)))
         (not (zp (ex-rep-j n1 n2 j hbit lbit)))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq (+ 1 hbit (- lbit))
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-concat
      (* (ex-rep-j n1 n2 j hbit lbit) n2)
      (ex-rep-lsize n1 n2 j lbit)
      (bv-repeat n2 x (ex-rep-j n1 n2 j hbit lbit))
      (bv-ex n2 (1- n2) (- n2 (ex-rep-lsize n1 n2 j lbit)) x))))

   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (ex-rep-splitp n1 n2 j hbit lbit)
         (zp (ex-rep-hsize n1 n2 j hbit))
         (not (zp (ex-rep-lsize n1 n2 j lbit)))
         (zp (ex-rep-j n1 n2 j hbit lbit))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq (+ 1 hbit (- lbit))
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-ex n2 (1- n2) (- n2 (ex-rep-lsize n1 n2 j lbit)) x)))

   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (ex-rep-splitp n1 n2 j hbit lbit)
         (zp (ex-rep-hsize n1 n2 j hbit))
         (zp (ex-rep-lsize n1 n2 j lbit))
         (not (zp (ex-rep-j n1 n2 j hbit lbit)))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq (+ 1 hbit (- lbit))
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-repeat n2 x (ex-rep-j n1 n2 j hbit lbit))))

   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (ex-rep-splitp n1 n2 j hbit lbit)
         (zp (ex-rep-hsize n1 n2 j hbit))
         (zp (ex-rep-lsize n1 n2 j lbit))
         (zp (ex-rep-j n1 n2 j hbit lbit))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq (+ 1 hbit (- lbit))
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (fill0 (+ 1 hbit (- lbit)))))


   (implies
    (and (syntaxp (and (quotep n2) (quotep n1) (quotep hbit) (quotep lbit)))
         (not (ex-rep-splitp n1 n2 j hbit lbit))
         (natp n2) (natp n1) (natp hbit) (natp lbit)
         (<= 0 lbit) (<= lbit hbit) (< hbit n1) (<= n1 (* n2 j)))
    (bv-eq (+ 1 hbit (- lbit))
     (bv-ex n1 hbit lbit (bv-repeat n2 x j))
     (bv-ex n2
            (mod (rel-bit (* n2 j) n1 hbit) n2)
            (mod (rel-bit (* n2 j) n1 lbit) n2)
            x)))
   ))
 :hints ((sat-when-stable stable-under-simplificationp)))



;; (thm ;;remove-unnecessary-functions
;;  (implies
;;   (and (equal n 8)
;;        (equal j 7))
;;   (and
;;    (bv-eq n (shift-left0 n x j)
;;           (bv-concat (- n j) j
;;                      (bv-ex n (+ n (- j) -1) 0 x)
;;                      (fill0 j)))

;;    (bv-eq n (shift-left1 n x j)
;;           (bv-concat (- n j) j
;;                      (bv-ex n (+ n (- j) -1) 0 x)
;;                      (fill1 j)))

;;    (bv-eq n (shift-right0 n x j)
;;           (bv-concat j n (fill0 j) x))

;;    (bv-eq n (shift-right1 n x j)
;;           (bv-concat j n (fill1 j) x))

;;    (bv-eq n (sign-extend n x j)
;;           (bv-concat j n (bv-repeat 1 x j) x))

;;    (bv-eq n (bv-rotate-left n x j)
;;           (bv-concat (- n j) j (bv-ex n (+ n (- j) (- 1)) 0 x) x))

;;    (bv-eq n (bv-rotate-right n x j)
;;           (bv-concat j (- n j) (bv-ex n (1- j) 0 x) x))))
;;  :hints ((sat-when-stable stable-under-simplificationp)))

|# ;|

;; Rules I think I should have:
;; drive bv-extract downward
;; bv-extract-of-bv-extract
;; (bv-eq n x x) = t.
;; Resize removal.

;; communitivity of bv-add and bv-mul
;; Use term-order, but ignore negation
;; drive bv-neg into bv-add and bv-mul

;; communitivity of bv-or and bv-and
;; Use term-order, but ignore not
;; drive bv-not into bv-or and bv-and

;; Do something to help less-than and equality
;;  left-to-right or right-to-left for most functions?

;; Look at arithmetic book for help normalizing + and *.
;; Look at ihs/logops-lemmas.lisp for help with and, or, not, etc.



