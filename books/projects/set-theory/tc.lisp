; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book defines tc as the transitive closure of a set s, proves that it is
; transitive (tc-is-transitive), contains s (subset-tc), is a subset of every
; transitive set containing s (tc-is-least).

(in-package "ZF")

(include-book "set-algebra") ; provides union-monotone for tc-contains-union

(defun tc-n (n s)
; This us the n-fold iteration of union on s.
  (declare (xargs :guard (natp n)))
  (if (zp n)
      s
    (union (tc-n (1- n) s))))

; We want to define the function (tc-fn s) such that for all naturals n,
; (apply (tc-fn s) n) = (tc-n n s).
; Our version of the Replacement Scheme gives us:
; (forall x \in (omega)) (exists y) (equal y (tc-n x s))
; =>
; (exists tc-fn) (forall n \in (omega))
;   (let ((y (apply tc-fn n)))
;     (equal y (tc-n n s)))
; The call of zfn just below implements that observation.
; The extra EQUAL call below is to make the $CHOOSES theorem a useful rewrite
; rule.
(zfn tc-fn (s)                      ; name, args
     n y                            ; x, y
     (omega)                        ; bound for x
     (equal (equal y (tc-n n s)) t) ; u
     )

(encapsulate
  ()

  (local (defthmz tc-n$domain-lemma
           (subset (omega) (domain (tc-fn s)))
           :props (zfc tc-fn$prop domain$prop)
           :hints (("Goal"
                    :expand ((subset (omega) (domain (tc-fn s))))
                    :restrict ((tc-fn$domain-2
                                ((y (tc-n (subset-witness (omega)
                                                          (domain (tc-fn s)))
                                          s)))))))))

  (defthmz tc-n$domain
    (equal (domain (tc-fn s)) (omega))
    :props (zfc tc-fn$prop domain$prop)
    :hints (("Goal" :in-theory (enable extensionality)))))

(defun tc (s)
  (declare (xargs :guard t))
  (union (codomain (tc-fn s))))

; Start proof of subset-tc.

(defthmz tc-fn-maps-n-to-tc-n
  (implies (natp n)
           (in (cons n (tc-n n s))
               (tc-fn s)))
  :props (zfc tc-fn$prop domain$prop)
  :hints (("Goal"
           :in-theory (disable tc-fn$chooses)
           :use ((:instance tc-fn$chooses
                            (y (apply (tc-fn s) n)))))))

(defthmz subset-tc-n-tc
  (implies (force (natp m))
           (subset (tc-n m s) (tc s)))
  :props (zfc tc-fn$prop domain$prop prod2$prop inverse$prop)
  :hints (("Goal"
           :restrict ((in-codomain-suff ((p (cons m (tc-n m s)))))))))

; A key theorem:
(defthmz subset-tc
  (subset s (tc s))
  :hints (("Goal" :use ((:instance subset-tc-n-tc (m 0)))))
  :props (zfc tc-fn$prop domain$prop prod2$prop inverse$prop))

(encapsulate ; Proof of tc-transitive.
  ()

  (local
   (encapsulate ; tc-is-transitive-1
     ()

     (local (defthmz tc-is-transitive-1-1
              (implies (in z (codomain (tc-fn s)))
                       (equal z (tc-n (apply (inverse (tc-fn s)) z)
                                      s)))
              :rule-classes nil
              :props (zfc tc-fn$prop domain$prop prod2$prop inverse$prop)))

     (local
      (encapsulate ; tc-is-transitive-1-2
        ()

        (local (defthmz tc-is-transitive-1-2-1-1
                 (implies (and (natp n)
                               (in x y)
                               (in y (tc-n n s)))
                          (in x (tc-n (1+ n) s)))))

        (local (defthmz tc-is-transitive-1-2-1
                 (implies (and (natp n)
                               (in x y)
                               (in y (tc-n n s)))
                          (in x (union (codomain (tc-fn s)))))
                 :hints (("Goal"
                          :restrict ((in-codomain-suff
                                      ((p (cons (+ 1 n) (tc-n (+ 1 n) s)))))
                                     (in-in-suff
                                      ((y (tc-n (1+ n) s)))))
                          :in-theory (disable tc-n)))
                 :props (zfc tc-fn$prop domain$prop prod2$prop inverse$prop)))

        (defthmz tc-is-transitive-1-2
          (let* ((n (apply (inverse (tc-fn s)) z))
                 (z (tc-n n s)))
            (implies (and (natp n)
                          (in x y)
                          (in y z))
                     (in x (union (codomain (tc-fn s))))))
          :rule-classes nil
          :props (zfc tc-fn$prop domain$prop prod2$prop inverse$prop))))

     (local
      (encapsulate ; tc-is-transitive-1-3
        ()

        (local (defthmz tc-is-transitive-1-3-1
                 (implies (in z (codomain (tc-fn s)))
                          (in (apply (inverse (tc-fn s)) z)
                              (omega)))
                 :hints (("Goal" :in-theory (enable in-codomain-rewrite)))
                 :rule-classes nil
                 :props (zfc tc-fn$prop domain$prop prod2$prop inverse$prop)))

        (defthmz tc-is-transitive-1-3
          (implies (in z (codomain (tc-fn s)))
                   (natp (apply (inverse (tc-fn s)) z)))
          :hints (("Goal"
                   :in-theory '(infinity)
                   :use tc-is-transitive-1-3-1))
          :rule-classes nil
          :props (zfc tc-fn$prop domain$prop prod2$prop inverse$prop))))

     (defthmz tc-is-transitive-1
       (implies (and (in x y)
                     (in y z)
                     (in z (codomain (tc-fn s))))
                (in x (union (codomain (tc-fn s)))))
       :hints (("Goal"
                :in-theory (theory 'minimal-theory)
                :use (tc-is-transitive-1-1
                      tc-is-transitive-1-2
                      tc-is-transitive-1-3)))
       :props (zfc tc-fn$prop domain$prop prod2$prop inverse$prop))))

; A key theorem:
  (defthmz tc-is-transitive
    (transitive (tc s))
    :hints (("Goal" :in-theory (enable transitive in-in subset)))
    :props (zfc tc-fn$prop domain$prop prod2$prop inverse$prop)))

(defun transitive-alt (x)
; This might be a better definition of transitive, since it doesn't involve
; quantifiers.  But it's not the one I thought of and used first.  Better late
; than never... and they're proved equivalent in the encapsulate just below
; (transitive-is-transitive-alt).
  (declare (xargs :guard t))
  (subset (union x) x))

(encapsulate
  ()

  (local (defthmz transitive-implies-transitive-alt
           (implies (transitive x)
                    (transitive-alt x))
           :hints (("Goal" :in-theory (enable subset in-in)))
           :rule-classes nil))

  (local (defthmz transitive-alt-implies-transitive
           (implies (transitive-alt x)
                    (transitive x))
           :hints (("Goal"
                    :expand ((subset (transitive-witness x) x))
                    :in-theory (enable transitive)))
           :rule-classes nil))

  (defthmz transitive-is-transitive-alt
    (equal (transitive x)
           (transitive-alt x))
    :hints (("Goal" :use (transitive-implies-transitive-alt
                          transitive-alt-implies-transitive)))))

(defthmz union-preserves-subset-for-transitive
  (implies (and (subset s tr)
                (transitive tr))
           (subset (union s) tr))
  :hints (("Goal"
           :cases ((subset (union s) (union tr)))
           :restrict ((subset-transitivity ((y (union tr))))))))

(in-theory (disable transitive-is-transitive-alt))

(defthmz tc-n-preserves-subset-for-transitive
  (implies (and (subset s tr)
                (transitive tr))
           (subset (tc-n n s) tr)))

(defthm tc-n-of-non-natp
  (implies (not (natp n))
           (equal (tc-n n s)
                  (tc-n 0 s))))

(defthmz in-tc-0-codomain-tc-fn ; lemma for in-codomain-tc-fn
  (in (tc-n 0 s) (codomain (tc-fn s)))
  :hints (("Goal"
           :restrict ((in-codomain-suff
                       ((p (cons 0 (tc-n 0 s))))))
           :in-theory (disable tc-n)))
  :otf-flg t
  :props (zfc tc-fn$prop domain$prop prod2$prop inverse$prop))

(defthmz in-tc-n-codomain-tc-fn ; lemma for in-codomain-tc-fn
  (in (tc-n n s) (codomain (tc-fn s)))
  :hints (("Goal"
           :restrict ((in-codomain-suff
                       ((p (cons n (tc-n n s))))))
           :in-theory (disable tc-n)
           :cases ((natp n))))
  :otf-flg t
  :props (zfc tc-fn$prop domain$prop prod2$prop inverse$prop))

(defthmz in-codomain-tc-fn ; rewrite version of tc-is-transitive-1-1
  (equal (in z (codomain (tc-fn s)))
         (equal z (tc-n (apply (inverse (tc-fn s)) z)
                        s)))
  :otf-flg t
  :props (zfc tc-fn$prop domain$prop prod2$prop inverse$prop))

; A key theorem:
(defthmz tc-is-least
  (implies (and (subset s tr)
                (transitive tr))
           (subset (tc s) tr))
  :hints (("Goal"
           :in-theory (enable in-in)
           :expand ((subset (union (codomain (tc-fn s))) tr))))
  :props (zfc tc-fn$prop domain$prop prod2$prop inverse$prop))

(in-theory (disable tc))
