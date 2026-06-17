; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "prelims")

; We define the subspace topology, and prove that the subspace topology on a
; closed set is compact.

(zsub subspace-fn (s tp)               ; name, args
      p                                ; x
      (prod2 (powerset s) tp)          ; s
      (equal (car p) (int2 (cdr p) s)) ; u
      )

(defun subspace (s tp)
  (domain (subspace-fn s tp)))

(defun subspace-wit (s2 s tp)
; For s2 \subset s, this chooses w \in tp such that, if possible s = (int2 s
; w).
  (let ((wit (apply (subspace-fn s tp) s2)))
    (if (equal s2 (int2 wit s))
        wit
      0)))

(defthmdz in-subspace-suff
  (implies (and (equal s2 (int2 w s))
                (in w tp))
           (in s2 (subspace s tp)))
  :hints (("Goal" :restrict ((in-car-domain-alt ((p (cons (int2 w s) w)))))))
  :props (zfc subspace-fn$prop domain$prop prod2$prop diff$prop))

(local
 (defthmz in-0-domain-subspace-fn
   (implies (in 0 tp)
            (in 0 (domain (subspace-fn s tp))))
   :hints (("Goal" :restrict ((in-car-domain-alt ((p (cons 0 0)))))))
   :props (zfc domain$prop subspace-fn$prop prod2$prop diff$prop)))

(defthmdz in-subspace-suff-alt
  (implies (and (equal s2
                       (int2 (subspace-wit s2 s tp)
                             s))
                (in 0 tp))
           (in s2 (subspace s tp)))
  :hints (("Goal"
           :use ((:instance
                  in-car-domain-alt
                  (p (cons s2 (apply (subspace-fn s tp) s2)))
                  (x s2)
                  (r (subspace-fn s tp))))
           :in-theory (disable in-car-domain in-car-domain-alt)))
  :props (zfc subspace-fn$prop domain$prop prod2$prop diff$prop))

(defthmdz in-subspace-necc
  (implies (in s2 (subspace s tp))
           (equal (int2 (subspace-wit s2 s tp)
                        s)
                  s2))
  :hints (("Goal" :in-theory (enable domain$comprehension)))
  :props (zfc subspace-fn$prop domain$prop prod2$prop))

(defthmdz in-subspace
  (implies (force (in 0 tp)) ; or more generally, (tpp tp)
           (equal (in s2 (subspace s tp))
                  (equal s2
                         (int2 (subspace-wit s2 s tp)
                               s))))
  :hints (("Goal" :use (in-subspace-suff-alt in-subspace-necc)))
  :props (zfc subspace-fn$prop domain$prop prod2$prop diff$prop))

(in-theory (disable subspace subspace-wit))

; Start proof of tpp-subspace

(encapsulate
  ()

  (local (defthmz in-apply-subspace-fn-0-tp-1
           (implies (in 0 tp)
                    (in (cons 0 0)
                        (subspace-fn s tp)))
           :props (zfc subspace-fn$prop prod2$prop diff$prop)
           :rule-classes nil))

  (local (defthmz in-apply-subspace-fn-0-tp-2
           (implies (in 0 tp)
                    (in (cons 0 (apply (subspace-fn s tp) 0))
                        (subspace-fn s tp)))
           :hints (("Goal"
                    :use in-apply-subspace-fn-0-tp-1
                    :in-theory (disable subspace-fn$comprehension)))
           :props (zfc subspace-fn$prop prod2$prop diff$prop)
           :rule-classes nil))

  (local (defthmz in-apply-subspace-fn-0-tp-3
           (implies (in (cons x y) (subspace-fn s tp))
                    (in y tp))
           :props (zfc subspace-fn$prop prod2$prop)))

  (defthmz in-apply-subspace-fn-0-tp
    (implies (in 0 tp)
             (in (apply (subspace-fn s tp) 0) tp))
    :hints (("Goal"
             :use (in-apply-subspace-fn-0-tp-2)
             :in-theory '(in-apply-subspace-fn-0-tp-3)))
    :props (zfc subspace-fn$prop prod2$prop diff$prop)))

(defthmz in-subspace-wit-tp
    (implies (in 0 tp)
             (in (subspace-wit w1 s tp) tp))
    :hints (("Goal" 
             :in-theory (enable subspace-wit)))
    :props (zfc subspace-fn$prop prod2$prop diff$prop))

(defthmz tpp-int2-subspace-1
  (implies (and (tpp tp)
                (subset s (union tp))
                (in w1 (subspace s tp))
                (in w2 (subspace s tp)))
           (in (int2 w1 w2)
               (subspace s tp)))
  :hints (("Goal"
           :use ((:instance in-subspace (s2 w1))
                 (:instance in-subspace (s2 w2)))
           :in-theory (enable in-subspace-suff)
           :restrict ((in-subspace-suff
                       ((w (int2 (subspace-wit w1 s tp)
                                 (subspace-wit w2 s tp))))))))
  :props (zfc subspace-fn$prop domain$prop prod2$prop diff$prop))

(defthmz tpp-int2-subspace
  (implies (and (tpp tp)
                (subset s (union tp)))
           (tpp-int2 (subspace s tp)))
  :hints (("Goal" :in-theory (enable tpp-int2)))
  :props (zfc subspace-fn$prop domain$prop prod2$prop diff$prop))

; Start proof of tpp-union-subspace-1 (for tpp-union-subspace).

(defthmz tpp-union-subspace-1-1-1-1
  (subset (domain (subspace-fn s tp))
          (powerset s))
  :hints (("Goal"
           :use ((:instance domain-preserves-subset
                            (r1 (subspace-fn s tp))
                            (r2 (prod2 (powerset s) tp))))
           :in-theory (disable domain-preserves-subset)))
  :props (zfc subspace-fn$prop domain$prop prod2$prop))

(defthmz in-in-powerset-1
  (implies (in-in x (powerset s))
           (in x s))
  :hints (("Goal" :in-theory (enable in-in))))

(defthmz in-in-powerset-2
  (implies (in x s)
           (in-in x (powerset s))))

(defthmz in-in-powerset
  (iff (in-in x (powerset s))
       (in x s)))

(defthmz union-powerset
  (equal (union (powerset s))
         s)
  :hints (("Goal" :in-theory (enable extensionality-rewrite subset))))

(defthmz tpp-union-subspace-1-1-1
  (subset (union (domain (subspace-fn s tp)))
          s)
  :hints (("Goal"
           :use ((:instance union-preserves-subset
                            (x (domain (subspace-fn s tp)))
                            (y (powerset s))))
           :in-theory (disable union-preserves-subset)))
  :props (zfc subspace-fn$prop domain$prop prod2$prop))

(defthmz tpp-union-subspace-1-1-2
  (implies (and (subset w d)
                (subset (union d) s))
           (subset (union w) s))
  :hints (("Goal"
           :use ((:instance union-preserves-subset
                            (x w) (y d)))
           :in-theory (disable union-preserves-subset union-monotone))))

(defthmz tpp-union-subspace-1-1
  (implies (subset wit (domain (subspace-fn s tp)))
           (subset (union wit) s))
  :props (zfc subspace-fn$prop domain$prop prod2$prop))

(local
 (defthmz tpp-union-subspace-1-2-1-1-1
   (implies (and (tpp tp)
                 (subset wit (domain (subspace-fn s tp)))
                 (subset s (union tp))
                 (in x s)
                 (in x s1)
                 (in s1 (image (restrict (subspace-fn s tp) wit))))
            (in-in x wit))
   :hints (("Goal"
            :restrict
            ((in-in-suff
              ((y (apply (inverse (restrict (subspace-fn s tp) wit))
                         s1)))))
            :in-theory (enable in-image-rewrite)))
   :props (zfc subspace-fn$prop domain$prop prod2$prop diff$prop restrict$prop
               inverse$prop)))

(local
 (defthmz tpp-union-subspace-1-2-1-1
   (implies (and (tpp tp)
                 (subset wit (domain (subspace-fn s tp)))
                 (subset s (union tp))
                 (in x (int2 (union (image (restrict (subspace-fn s tp) wit)))
                             s)))
            (in x (union wit)))
   :hints (("Goal"
            :expand ((in-in x
                            (image (restrict (subspace-fn s tp) wit))))))
   :props (zfc subspace-fn$prop domain$prop prod2$prop diff$prop restrict$prop
               inverse$prop)))

(local
 (defthmz tpp-union-subspace-1-2-1

; Informal proof.  Recall that (subspace-fn s tp) maps each open s0 in subspace
; s to w in tp such that s0 = (int2 w s).  So (restrict (subspace-fn s tp) wit)
; contains pairs <s0,s1> such that s0 \in wit, s0 = (int2 s s1), and s1 \in tp.
; Thus (image (restrict (subspace-fn s tp) wit)) is the set of all such s1.

; Suppose x is in the given intersection -- so x \in s and also, x \in s1 for
; some s1 as above.  Thus there is <s0,s1> such that s0 \in wit, s0 = (int2 s
; s1), and s1 \in tp.  Since x \in s and x \in s1, then x \in s0.  So x \in s0
; \in wit, and hence x in (union wit).

   (implies (and (tpp tp)
                 (subset s (union tp))
                 (subset wit (domain (subspace-fn s tp))))
            (subset (int2 (union (image (restrict (subspace-fn s tp) wit)))
                          s)
                    (union wit)))
   :hints (("Goal"
            :expand
            ((subset (int2 (union (image (restrict (subspace-fn s tp) wit)))
                           s)
                     (union wit)))
            :in-theory (disable in-int2 in-union)))
   :props (zfc subspace-fn$prop domain$prop prod2$prop diff$prop restrict$prop
               inverse$prop)))

; Start proof of tpp-union-subspace-1-2-2-1.  Here is the informal proof.

; Suppose (in-in x wit).

; Choose s0 such that x \in s0 \in wit.

; Since s0 \in wit \subset (domain (subspace-fn s tp)), then s0 \in (domain
; (subspace-fn s tp)), so choose s1 such that <s0,s1> \in (subspace-fn s tp),
; e.g., s1 can be (apply (subspace-fn s tp) s0).

; By definition of subspace-fn, s0 = (int2 s1 s).

; Since x \in s0, then x \in s1.

; Then since s1 \in (image (restrict (subspace-fn s tp) wit)), by virtue of
; <s0,s1> \in (subspace-fn s tp), we are done.

(local
 (defthmz tpp-union-subspace-1-2-2-1-1-1
   (implies (and (subset wit (domain (subspace-fn s tp)))
                 (in s0 wit))
            (in (cons s0 (apply (subspace-fn s tp) s0))
                (subspace-fn s tp)))
   :props (zfc domain$prop)
   :hints (("Goal"
            :use ((:instance subspace-fn$comprehension
                             (p (cons s0 (apply (subspace-fn s tp) s0)))
                             (s s)
                             (tp tp)))
            :in-theory (disable subspace-fn$comprehension)))
   :rule-classes nil))

(local
 (defthmz tpp-union-subspace-1-2-2-1-1-2
   (implies (and (subset wit (domain (subspace-fn s tp)))
                 (in x s0)
                 (in s0 wit)
                 (in (cons s0 s1) (subspace-fn s tp)))
            (in-in x
                   (image (restrict (subspace-fn s tp) wit))))
   :hints (("Goal"
            :restrict ((in-image-suff
                        ((p (cons (int2 s1 s) s1))))
                       (in-in-suff
                        ((y s1))))))
   :props (zfc subspace-fn$prop domain$prop prod2$prop diff$prop restrict$prop
               inverse$prop)
   :rule-classes nil))

(local
 (defthmz tpp-union-subspace-1-2-2-1-1
   (implies (and (subset wit (domain (subspace-fn s tp)))
                 (in x s0)
                 (in s0 wit))
            (in-in x
                   (image (restrict (subspace-fn s tp) wit))))
   :hints (("Goal"
            :expand ((in-in x wit))
            :use (tpp-union-subspace-1-2-2-1-1-1
                  (:instance tpp-union-subspace-1-2-2-1-1-2
                             (s1 (apply (subspace-fn s tp) s0))))))
   :props (zfc subspace-fn$prop domain$prop prod2$prop diff$prop restrict$prop
               inverse$prop)))

(local
 (defthmz tpp-union-subspace-1-2-2-1

; See "Start proof of tpp-union-subspace-1-2-2-1" above for informal proof.

   (implies (and (subset wit (domain (subspace-fn s tp)))
                 (in-in x wit))
            (in-in x
                   (image (restrict (subspace-fn s tp) wit))))
   :hints (("Goal" :expand ((in-in x wit))))
   :props (zfc subspace-fn$prop domain$prop prod2$prop diff$prop restrict$prop
               inverse$prop)))

(local
 (defthmz tpp-union-subspace-1-2-2
   (implies (subset wit (domain (subspace-fn s tp)))
; Note that tpp-union-subspace-1-1 takes care of the conclusion
; (subset (union wit) s).
            (subset (union wit)
                    (union (image (restrict (subspace-fn s tp) wit)))))
   :hints (("Goal"
            :expand
            ((subset (union wit)
                     (union (image (restrict (subspace-fn s tp) wit)))))))
   :props (zfc subspace-fn$prop domain$prop prod2$prop diff$prop restrict$prop
               inverse$prop)))

(local
 (defthmz tpp-union-subspace-1-2
   (implies (and (tpp tp)
                 (subset s (union tp))
                 (subset wit (domain (subspace-fn s tp))))
            (equal (int2 (union (image (restrict (subspace-fn s tp) wit)))
                         s)
                   (union wit)))
   :hints (("Goal" :in-theory (e/d (extensionality-rewrite)
                                   (subset-x-0))))
   :props (zfc subspace-fn$prop domain$prop prod2$prop diff$prop restrict$prop
               inverse$prop)))

(local
 (defthmz tpp-union-subspace-1-3-1-1
   (implies (in s0 (image (restrict (subspace-fn s tp) wit)))
            (in s0 tp))
   :hints (("Goal" :in-theory (enable in-image-rewrite)))
   :props (zfc subspace-fn$prop domain$prop prod2$prop restrict$prop
               inverse$prop)))

(local
 (defthmz tpp-union-subspace-1-3-1
   (subset (image (restrict (subspace-fn s tp) wit))
           tp)
   :hints (("Goal"
            :expand ((subset (image (restrict (subspace-fn s tp) wit))
                             tp))))
   :props (zfc subspace-fn$prop domain$prop prod2$prop restrict$prop
               inverse$prop)))

(local
 (defthmz tpp-union-subspace-1-3
   (implies (and (tpp tp)
                 (subset wit (domain (subspace-fn s tp))))
            (in (union (image (restrict (subspace-fn s tp) wit)))
                tp))
   :props (zfc subspace-fn$prop domain$prop prod2$prop restrict$prop
               inverse$prop)))

(defthmz tpp-union-subspace-1
  (implies (and (tpp tp)
                (subset s (union tp))
                (subset wit (domain (subspace-fn s tp))))
           (in (union wit)
               (domain (subspace-fn s tp))))
  :hints
  (("Goal"
    :in-theory (disable in-car-domain-alt)
    :use
    ((:instance
      in-car-domain-alt
      (x (union wit))
      (r (subspace-fn s tp))
      (p (cons (union wit)
               (union (image (restrict (subspace-fn s tp) wit)))))))))
  :props (zfc subspace-fn$prop domain$prop prod2$prop diff$prop restrict$prop 
              inverse$prop))

(defthmz tpp-union-subspace

;;; PLAN: we have a relation R from the subspace sets to corresponding open
;;; sets of tp.  Let s0 \subset s.  The union of (image (restrict r s0)) is a
;;; witness to (union s0), i.e., (int2 (image (restrict r s0)) (union s)) =
;;; (union s0).

  (implies (and (tpp tp)
                (subset s (union tp)))
           (tpp-union (subspace s tp)))
  :hints
  (("Goal"
    :in-theory (e/d (tpp-union subspace)
                    (in-car-domain-alt))
    :use
    ((:instance
      in-car-domain-alt
      (x (union wit))
      (r (subspace-fn s tp))
      (p (cons (union wit)
               (union (image (restrict (subspace-fn s tp) wit)))))))))
  :props (zfc subspace-fn$prop domain$prop prod2$prop diff$prop restrict$prop
              inverse$prop))

(defthmz tpp-subspace
  (implies (and (tpp tp)
                (subset s (union tp)))
           (tpp (subspace s tp)))
  :hints (("Goal" :expand ((tpp (subspace s tp)))))
  :props (zfc subspace-fn$prop domain$prop prod2$prop diff$prop restrict$prop
              inverse$prop))
