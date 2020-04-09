; Copyright (C) 2020, Rob Sumners
; Written by Rob Sumners
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "bake-models")
(include-book "wfo-thry")
(local (include-book "gl-setup"))

;; now we setup memory and satlink settings for GL through a macro

(local (gl::init-gl-params))
(local (set-slow-alist-action nil))

(fty::defprod bake-tr-sh
  ((tr bake-tr-p)
   (sh bake-sh-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Starting bake-rank-msr proofs..
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *bake-rank-a-dom*
  (nodes-from-graph *bake-rank-reach*))

(define bake-rank-a-dom ()
  :returns (r arcs-p)
  *bake-rank-a-dom*)

;; Given this definition of map-e, we need to prove that all
;; reachable nodes have a mapping in a-dom, which we prove
;; below..

(define bake-rank-map-e (x)
  ;; x is a cons of a (bake-tr . bake-sh)
  :returns (r node-p)
  (if (bake-tr-sh-p x)
      (b* ((a (bake-rank-map (bake-tr-sh->tr x))))
        (if (in-p a (bake-rank-a-dom)) a 
          (first (bake-rank-a-dom))))
    (first (bake-rank-a-dom))))

(defthm bake-rank-map-e-in-a-dom
  (in-p (bake-rank-map-e x)
        (bake-rank-a-dom))
  :hints (("Goal" :in-theory (enable bake-rank-map-e
                                     bake-rank-a-dom
                                     (bake-rank-a-dom)))))

(define bake-rank-nexts ((a node-p))
  :returns (r arcs-p)
  (cdr (graph-get a *bake-rank-reach*)))

(defthm bake-rank-nexts-subset-bake-rank-a-dom
  (subset-p (bake-rank-nexts a) (bake-rank-a-dom))
  :hints (("Goal" :in-theory (enable bake-rank-nexts graph-get))))

(define bake-rank-rel-p (x y)
  (and (bake-tr-sh-p x)
       (bake-tr-sh-p y)
       (b* (((bake-tr-sh x) x)
            ((bake-tr-sh y) y))
         (and (not (bake-tr-done x.tr))
              (in-p (bake-rank-map x.tr) (bake-rank-a-dom))
              (equal y.tr (bake-tr-next x.tr x.sh))))))

(define bake-rank-o-bnd () 0)

(define bake-rank-map-o (x (o ord-p))
  :returns (r (bplp r (bake-rank-o-bnd))
              :hints (("Goal" :in-theory (enable bplp))))
  (if (bake-tr-sh-p x) (1+ (bake-rank-ord (bake-tr-sh->tr x) o)) 1))

(define bake-rank-chk-ord-arc ((a node-p) (b node-p) (o ord-p))
  :returns (r ord-tag-p)
  (and (member-eq o '(loop runs))
       (chk-bake-rank-ord-arc a b o)))

;;;; GL theorems proving that mapping membership in a-dom is invariant..

(def-gl-thm bake-rank-map-init-gl-inv
  :hyp (and (gl::shape-spec-obj-in-range (n-shp) n)
            (gl::shape-spec-obj-in-range (r-shp) r))
  :concl (in-p (bake-rank-map (bake-tr-init n r))
               (bake-rank-a-dom))
  :g-bindings (get-var-shps '(n r))
  :cov-theory-add (enable n-shp r-shp)
  :rule-classes nil)

(def-gl-thm bake-rank-map-next-gl-inv
  :hyp (and (gl::shape-spec-obj-in-range (a-shp) a)
            (gl::shape-spec-obj-in-range (sh-shp) sh))
  :concl (implies (and (in-p (bake-rank-map a) (bake-rank-a-dom))
                       (not (bake-tr-done a)))
                  (in-p (bake-rank-map (bake-tr-next a sh))
                        (bake-rank-a-dom)))
  :g-bindings (get-var-shps '(a sh))
  :cov-theory-add (enable a-shp sh-shp)
  :rule-classes nil)

;;;; GL theorems leading to big required properties for bake-rank

(def-gl-thm bake-rank-map-e-nexts-gl-prep
  :hyp (and (gl::shape-spec-obj-in-range (a-shp) a)
            (gl::shape-spec-obj-in-range (sh-shp) sh))
  :concl (implies (and (in-p (bake-rank-map a) (bake-rank-a-dom))
                       (not (bake-tr-done a)))
                  (in-p (bake-rank-map (bake-tr-next a sh))
                        (bake-rank-nexts (bake-rank-map a))))
  :g-bindings (get-var-shps '(a sh))
  :cov-theory-add (enable a-shp sh-shp)
  :rule-classes nil)

(def-gl-thm bake-rank-map-o-decr-strict-gl-prep-runs
  :hyp (and (gl::shape-spec-obj-in-range (a-shp) a)
            (gl::shape-spec-obj-in-range (sh-shp) sh))
  :concl (implies (and (in-p (bake-rank-map a) (bake-rank-a-dom))
                       (not (bake-tr-done a))
                       (equal (bake-rank-chk-ord-arc (bake-rank-map a)
                                                     (bake-rank-map
                                                      (bake-tr-next a sh))
                                                     'runs)
                              :<<))
                  (< (bake-rank-ord (bake-tr-next a sh) 'runs)
                     (bake-rank-ord a 'runs)))
  :g-bindings (get-var-shps '(a sh))
  :cov-theory-add (enable a-shp sh-shp)
  :rule-classes nil)

(def-gl-thm bake-rank-map-o-decr-strict-gl-prep-loop
  :hyp (and (gl::shape-spec-obj-in-range (a-shp) a)
            (gl::shape-spec-obj-in-range (sh-shp) sh))
  :concl (implies (and (in-p (bake-rank-map a) (bake-rank-a-dom))
                       (not (bake-tr-done a))
                       (equal (bake-rank-chk-ord-arc (bake-rank-map a)
                                                     (bake-rank-map
                                                      (bake-tr-next a sh))
                                                     'loop)
                              :<<))
                  (< (bake-rank-ord (bake-tr-next a sh) 'loop)
                     (bake-rank-ord a 'loop)))
  :g-bindings (get-var-shps '(a sh))
  :cov-theory-add (enable a-shp sh-shp)
  :rule-classes nil)

(def-gl-thm bake-rank-map-o-decr-non-strict-gl-prep-runs
  :hyp (and (gl::shape-spec-obj-in-range (a-shp) a)
            (gl::shape-spec-obj-in-range (sh-shp) sh))
  :concl (implies (and (in-p (bake-rank-map a) (bake-rank-a-dom))
                       (not (bake-tr-done a))
                       (equal (bake-rank-chk-ord-arc (bake-rank-map a)
                                                     (bake-rank-map
                                                      (bake-tr-next a sh))
                                                     'runs)
                              t))
                  (<= (bake-rank-ord (bake-tr-next a sh) 'runs)
                      (bake-rank-ord a 'runs)))
  :g-bindings (get-var-shps '(a sh))
  :cov-theory-add (enable a-shp sh-shp)
  :rule-classes nil)

(def-gl-thm bake-rank-map-o-decr-non-strict-gl-prep-loop
  :hyp (and (gl::shape-spec-obj-in-range (a-shp) a)
            (gl::shape-spec-obj-in-range (sh-shp) sh))
  :concl (implies (and (in-p (bake-rank-map a) (bake-rank-a-dom))
                       (not (bake-tr-done a))
                       (equal (bake-rank-chk-ord-arc (bake-rank-map a)
                                                     (bake-rank-map
                                                      (bake-tr-next a sh))
                                                     'loop)
                              t))
                  (<= (bake-rank-ord (bake-tr-next a sh) 'loop)
                      (bake-rank-ord a 'loop)))
  :g-bindings (get-var-shps '(a sh))
  :cov-theory-add (enable a-shp sh-shp)
  :rule-classes nil)

(defthm bake-rank-chk-ord-arc-on-non-ord
  (implies (and (not (equal o 'loop))
                (not (equal o 'runs)))
           (equal (bake-rank-chk-ord-arc a b o) nil))
  :hints (("Goal" :in-theory (enable chk-bake-rank-ord-arc
                                     bake-rank-chk-ord-arc))))

;;;; big required properties

(in-theory (disable (bake-rank-a-dom) bake-rank-a-dom))

(defthm bake-rank-map-e-member-nexts
  (implies (bake-rank-rel-p x y)
           (in-p (bake-rank-map-e y)
                 (bake-rank-nexts (bake-rank-map-e x))))
  :hints (("Goal"
           :in-theory (e/d (bake-rank-rel-p bake-rank-map-e)
                           (a-shp sh-shp (a-shp) (sh-shp)))
           :use ((:instance bake-rank-map-e-nexts-gl-prep
                            (a (bake-tr-sh->tr x))
                            (sh (bake-tr-sh->sh x)))
                 (:instance in-p-subset-p-transfer
                            (e (bake-rank-map (bake-tr-sh->tr y)))
                            (x (bake-rank-nexts (bake-rank-map (bake-tr-sh->tr x))))
                            (y (bake-rank-a-dom)))))))

(defthm bake-rank-map-o-decrement-strict
  (implies (and (bake-rank-rel-p x y)
                (equal (bake-rank-chk-ord-arc (bake-rank-map-e x)
                                              (bake-rank-map-e y)
                                              o)
                       :<<))
           (bnl< (bake-rank-map-o y o)
                 (bake-rank-map-o x o)
                 (bake-rank-o-bnd)))
  :hints (("Goal"
           :in-theory (e/d (bake-rank-rel-p bake-rank-map-e bake-rank-map-o)
                           (a-shp sh-shp (a-shp) (sh-shp)))
           :cases ((equal o 'loop) (equal o 'runs))
           :use ((:instance bake-rank-map-o-decr-strict-gl-prep-runs
                            (a (bake-tr-sh->tr x))
                            (sh (bake-tr-sh->sh x)))
                 (:instance bake-rank-map-o-decr-strict-gl-prep-loop
                            (a (bake-tr-sh->tr x))
                            (sh (bake-tr-sh->sh x)))
                 (:instance bake-rank-map-e-nexts-gl-prep
                            (a (bake-tr-sh->tr x))
                            (sh (bake-tr-sh->sh x)))
                 (:instance in-p-subset-p-transfer
                            (e (bake-rank-map (bake-tr-sh->tr y)))
                            (x (bake-rank-nexts (bake-rank-map (bake-tr-sh->tr x))))
                            (y (bake-rank-a-dom)))))))

(defthm bake-rank-map-o-decrement-non-strict
  (implies (and (bake-rank-rel-p x y)
                (equal (bake-rank-chk-ord-arc (bake-rank-map-e x)
                                              (bake-rank-map-e y)
                                              o)
                       t))
           (bnl<= (bake-rank-map-o y o)
                  (bake-rank-map-o x o)
                  (bake-rank-o-bnd)))
  :hints (("Goal"
           :in-theory (e/d (bake-rank-rel-p bake-rank-map-e bake-rank-map-o)
                           (a-shp sh-shp (a-shp) (sh-shp)))
           :cases ((equal o 'loop) (equal o 'runs))
           :use ((:instance bake-rank-map-o-decr-non-strict-gl-prep-runs
                            (a (bake-tr-sh->tr x))
                            (sh (bake-tr-sh->sh x)))
                 (:instance bake-rank-map-o-decr-non-strict-gl-prep-loop
                            (a (bake-tr-sh->tr x))
                            (sh (bake-tr-sh->sh x)))
                 (:instance bake-rank-map-e-nexts-gl-prep
                            (a (bake-tr-sh->tr x))
                            (sh (bake-tr-sh->sh x)))
                 (:instance in-p-subset-p-transfer
                            (e (bake-rank-map (bake-tr-sh->tr y)))
                            (x (bake-rank-nexts (bake-rank-map (bake-tr-sh->tr x))))
                            (y (bake-rank-a-dom)))))))

(def-valid-wf-corr-assumption bake-rank)

(in-theory (disable (bake-rank-o-bnd) bake-rank-o-bnd
                    (:type-prescription bake-rank-o-bnd)))

(def-valid-wf-corr-conclusion bake-rank)

;; we prove that our generated omap is valid and get a bpl measure

(define bake-rank->bpl (x)
  (bake-rank-mk-bpl x (w-ord-rslt->order-rslt *bake-rank-word*)))

(define bake-rank->bnd ()
  (bake-rank-bpl-bnd (w-ord-rslt->order-rslt *bake-rank-word*)))

(in-theory (e/d (bake-rank->bpl bake-rank->bnd)
                (bake-rank-mk-bpl bake-rank-bpl-bnd
                 (bake-rank->bnd) (bake-rank-bpl-bnd))))

(defthm bake-rank->bpl-is-bplp
  (bplp (bake-rank->bpl x) (bake-rank->bnd)))

(defthm bake-rank->bpl-bnl<
  (implies (bake-rank-rel-p x y)
           (bnl< (bake-rank->bpl y) (bake-rank->bpl x) (bake-rank->bnd))))

(in-theory (disable bake-rank->bpl bake-rank->bnd))

;; finally we prove that our generated omap is valid and prove that
;; bake-rank-rel-p is well-founded:

(define bake-rank-wf-msr (x)
  (bake-rank-msr x (w-ord-rslt->order-rslt *bake-rank-word*)))

(in-theory (e/d (bake-rank-wf-msr) (bake-rank-msr)))

(defthm bake-rank-wf-msr-is-o-p
  (o-p (bake-rank-wf-msr x)))

(defthm bake-rank-wf-msr-well-founded
  (implies (bake-rank-rel-p x y)
           (o< (bake-rank-wf-msr y)
               (bake-rank-wf-msr x))))

(in-theory (disable bake-rank-wf-msr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End bake-rank-msr proofs..
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Starting bake-rank auxiliary proofs..
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bake-rank-map-init-inv
  (implies (and (bake-ndx-p n)
                (bake-runs-p r))
           (in-p (bake-rank-map (bake-tr-init n r))
                 (bake-rank-a-dom)))
  :hints (("Goal" :in-theory (enable bake-ndx-p bake-runs-p)
           :use (:instance bake-rank-map-init-gl-inv))))

(defthm bake-rank-map-next-inv
  (implies (and (bake-tr-p a)
                (bake-sh-p sh)
                (in-p (bake-rank-map a) (bake-rank-a-dom))
                (not (bake-tr-done a)))
           (in-p (bake-rank-map (bake-tr-next a sh))
                 (bake-rank-a-dom)))
  :hints (("Goal" :in-theory (disable a-shp (a-shp) sh-shp (sh-shp))
           :use (:instance bake-rank-map-next-gl-inv))))

;;;; some theorems needed to show that bake-rank->bpl does not
;;;; care about the shared state:

(local
(defthm bake-rank-map-o-sh-irrel
  (equal (equal (bake-rank-map-o (bake-tr-sh x sh1) o)
                (bake-rank-map-o (bake-tr-sh x sh2) o))
         t)
  :hints (("Goal" :in-theory (enable bake-rank-map-o)))))

(local
(defthm bake-rank-build-bpll-sh-irrel
  (equal (equal (bake-rank-build-bpll w (bake-tr-sh x sh1))
                (bake-rank-build-bpll w (bake-tr-sh x sh2)))
         t)
  :hints (("Goal" :in-theory (enable bake-rank-build-bpll)))))

(local
(defthm bake-rank-map-e-sh-irrel
  (equal (bake-rank-map-e (bake-tr-sh x sh1))
         (bake-rank-map-e (bake-tr-sh x sh2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable bake-rank-map-e)))))

(local
(defthm bake-rank-mk-bpll-sh-irrel
  (equal (equal (bake-rank-mk-bpll (bake-tr-sh x sh1) m)
                (bake-rank-mk-bpll (bake-tr-sh x sh2) m))
         t)
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (bake-rank-mk-bpll) ())
           :use (:instance bake-rank-map-e-sh-irrel)))))

(local
(defthm bake-rank-mk-bpl-sh-irrel
  (equal (equal (bake-rank-mk-bpl (bake-tr-sh x sh1) m)
                (bake-rank-mk-bpl (bake-tr-sh x sh2) m))
         t)
  :hints (("Goal" :in-theory (e/d (bake-rank-mk-bpl) (bake-rank-mk-bpll))
           :use (:instance bake-rank-mk-bpll-sh-irrel)))))
           
(defthm bake-rank->bpl-sh-irrel
  (equal (bake-rank->bpl (bake-tr-sh x sh1))
         (bake-rank->bpl (bake-tr-sh x sh2)))
  :hints (("Goal" :in-theory (enable bake-rank->bpl)))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End bake-rank auxiliary proofs..
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Starting bake-nlock-msr proofs..
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *bake-nlock-a-dom*
  (nodes-from-graph *bake-nlock-blok*))

(define bake-nlock-a-dom ()
  :returns (r arcs-p)
  *bake-nlock-a-dom*)

(define bake-nlock-map-e (x)
  ;; x is a cons of a (bake-tr . bake-sh)
  :returns (r node-p)
  (if (bake-tr-sh-p x)
      (b* ((a (bake-nlock-map (bake-tr-sh->tr x)
                              (bake-tr-sh->sh x))))
        (if (in-p a (bake-nlock-a-dom)) a 
          (first (bake-nlock-a-dom))))
    (first (bake-nlock-a-dom))))

(defthm bake-nlock-map-e-in-a-dom
  (in-p (bake-nlock-map-e x)
        (bake-nlock-a-dom))
  :hints (("Goal" :in-theory (enable bake-nlock-map-e
                                     bake-nlock-a-dom
                                     (bake-nlock-a-dom)))))

(define bake-nlock-nexts ((a node-p))
  :returns (r arcs-p)
  (cdr (graph-get a *bake-nlock-blok*)))

(define bake-nlock-rel-p (x y)
  (and (bake-tr-sh-p x)
       (bake-tr-sh-p y)
       (b* (((bake-tr-sh x) x)
            ((bake-tr-sh y) y))
         (and (in-p (bake-nlock-map x.tr x.sh) (bake-nlock-a-dom))
              (in-p (bake-nlock-map y.tr y.sh) (bake-nlock-a-dom))
              (equal x.sh y.sh)
              (bake-tr-blok x.tr y.tr)))))

(define bake-nlock-o-bnd () 0)

(define bake-nlock-map-o (x (o ord-p))
  :returns (r (bplp r (bake-nlock-o-bnd))
              :hints (("Goal" :in-theory (enable bplp))))
  (if (bake-tr-sh-p x) (1+ (bake-nlock-ord (bake-tr-sh->tr x) o)) 1))

(define bake-nlock-chk-ord-arc ((a node-p) (b node-p) (o ord-p))
  :returns (r ord-tag-p)
  (and (member-eq o '(ndx pos))
       (chk-bake-nlock-ord-arc a b o)))

;;;; GL theorems proving that mapping membership in a-dom is invariant..

(def-gl-thm bake-nlock-map-init-gl-inv
  :hyp (and (gl::shape-spec-obj-in-range (n-shp) n)
            (gl::shape-spec-obj-in-range (r-shp) r))
  :concl (in-p (bake-nlock-map (bake-tr-init n r)
                               (bake-sh-init))
               (bake-nlock-a-dom))
  :g-bindings (get-var-shps '(n r))
  :cov-theory-add (enable n-shp r-shp)
  :rule-classes nil)

(def-gl-thm bake-nlock-map-next-gl-inv
  :hyp (and (gl::shape-spec-obj-in-range (a-shp) a)
            (gl::shape-spec-obj-in-range (sh-shp) sh))
  :concl (implies (and (in-p (bake-nlock-map a sh) (bake-nlock-a-dom))
                       (not (bake-tr-done a)))
                  (in-p (bake-nlock-map (bake-tr-next a sh)
                                        (bake-sh-next sh a))
                        (bake-nlock-a-dom)))
  :g-bindings (get-var-shps '(a sh))
  :cov-theory-add (enable a-shp sh-shp)
  :rule-classes nil)

(def-gl-thm bake-nlock-map-next-gl-hold
  :hyp (and (gl::shape-spec-obj-in-range (a-shp) a)
            (gl::shape-spec-obj-in-range (b-shp) b)
            (gl::shape-spec-obj-in-range (sh-shp) sh))
  :concl (implies (and (in-p (bake-nlock-map a sh) (bake-nlock-a-dom))
                       (in-p (bake-nlock-map b sh) (bake-nlock-a-dom))
                       (not (bake-tr-done a)))
                  (in-p (bake-nlock-map b (bake-sh-next sh a))
                        (bake-nlock-a-dom)))
  :g-bindings (get-var-shps '(a b sh))
  :cov-theory-add (enable a-shp b-shp sh-shp)
  :rule-classes nil)

;;;; GL theorems leading to big required properties for bake-nlock..

(def-gl-thm bake-nlock-map-e-nexts-gl-prep
  :hyp (and (gl::shape-spec-obj-in-range (a-shp) a)
            (gl::shape-spec-obj-in-range (b-shp) b)
            (gl::shape-spec-obj-in-range (sh-shp) sh))
  :concl (implies (and (in-p (bake-nlock-map a sh) (bake-nlock-a-dom))
                       (in-p (bake-nlock-map b sh) (bake-nlock-a-dom))
                       (bake-tr-blok a b))
                  (in-p (bake-nlock-map b sh)
                        (bake-nlock-nexts (bake-nlock-map a sh))))
  :g-bindings (get-var-shps '(a b sh))
  :cov-theory-add (enable a-shp b-shp sh-shp)
  :rule-classes nil)

(def-gl-thm bake-nlock-map-o-decr-strict-gl-prep-pos
  :hyp (and (gl::shape-spec-obj-in-range (a-shp) a)
            (gl::shape-spec-obj-in-range (b-shp) b)
            (gl::shape-spec-obj-in-range (sh-shp) sh))
  :concl (implies (and (in-p (bake-nlock-map a sh) (bake-nlock-a-dom))
                       (in-p (bake-nlock-map b sh) (bake-nlock-a-dom))
                       (bake-tr-blok a b)
                       (equal (bake-nlock-chk-ord-arc (bake-nlock-map a sh)
                                                      (bake-nlock-map b sh)
                                                      'pos)
                              :<<))
                  (< (bake-nlock-ord b 'pos)
                     (bake-nlock-ord a 'pos)))
  :g-bindings (get-var-shps '(a b sh))
  :cov-theory-add (enable a-shp b-shp sh-shp)
  :rule-classes nil)

(def-gl-thm bake-nlock-map-o-decr-strict-gl-prep-ndx
  :hyp (and (gl::shape-spec-obj-in-range (a-shp) a)
            (gl::shape-spec-obj-in-range (b-shp) b)
            (gl::shape-spec-obj-in-range (sh-shp) sh))
  :concl (implies (and (in-p (bake-nlock-map a sh) (bake-nlock-a-dom))
                       (in-p (bake-nlock-map b sh) (bake-nlock-a-dom))
                       (bake-tr-blok a b)
                       (equal (bake-nlock-chk-ord-arc (bake-nlock-map a sh)
                                                      (bake-nlock-map b sh)
                                                      'ndx)
                              :<<))
                  (< (bake-nlock-ord b 'ndx)
                     (bake-nlock-ord a 'ndx)))
  :g-bindings (get-var-shps '(a b sh))
  :cov-theory-add (enable a-shp b-shp sh-shp)
  :rule-classes nil)

(def-gl-thm bake-nlock-map-o-decr-non-strict-gl-prep-pos
  :hyp (and (gl::shape-spec-obj-in-range (a-shp) a)
            (gl::shape-spec-obj-in-range (b-shp) b)
            (gl::shape-spec-obj-in-range (sh-shp) sh))
  :concl (implies (and (in-p (bake-nlock-map a sh) (bake-nlock-a-dom))
                       (in-p (bake-nlock-map b sh) (bake-nlock-a-dom))
                       (bake-tr-blok a b)
                       (equal (bake-nlock-chk-ord-arc (bake-nlock-map a sh)
                                                      (bake-nlock-map b sh)
                                                      'pos)
                              t))
                  (<= (bake-nlock-ord b 'pos)
                      (bake-nlock-ord a 'pos)))
  :g-bindings (get-var-shps '(a b sh))
  :cov-theory-add (enable a-shp b-shp sh-shp)
  :rule-classes nil)

(def-gl-thm bake-nlock-map-o-decr-non-strict-gl-prep-ndx
  :hyp (and (gl::shape-spec-obj-in-range (a-shp) a)
            (gl::shape-spec-obj-in-range (b-shp) b)
            (gl::shape-spec-obj-in-range (sh-shp) sh))
  :concl (implies (and (in-p (bake-nlock-map a sh) (bake-nlock-a-dom))
                       (in-p (bake-nlock-map b sh) (bake-nlock-a-dom))
                       (bake-tr-blok a b)
                       (equal (bake-nlock-chk-ord-arc (bake-nlock-map a sh)
                                                      (bake-nlock-map b sh)
                                                      'ndx)
                              t))
                  (<= (bake-nlock-ord b 'ndx)
                      (bake-nlock-ord a 'ndx)))
  :g-bindings (get-var-shps '(a b sh))
  :cov-theory-add (enable a-shp b-shp sh-shp)
  :rule-classes nil)

(defthm bake-nlock-chk-ord-arc-on-non-ord
  (implies (and (not (equal o 'ndx))
                (not (equal o 'pos)))
           (equal (bake-nlock-chk-ord-arc a b o) nil))
  :hints (("Goal" :in-theory (enable chk-bake-nlock-ord-arc
                                     bake-nlock-chk-ord-arc))))

;;;; big required properties

(in-theory (disable (bake-nlock-a-dom) bake-nlock-a-dom))

(defthm bake-nlock-map-e-member-nexts
  (implies (bake-nlock-rel-p x y)
           (in-p (bake-nlock-map-e y)
                 (bake-nlock-nexts (bake-nlock-map-e x))))
  :hints (("Goal"
           :in-theory (e/d (bake-nlock-rel-p bake-nlock-map-e)
                           (a-shp b-shp sh-shp (a-shp) (b-shp) (sh-shp)))
           :use ((:instance bake-nlock-map-e-nexts-gl-prep
                            (a (bake-tr-sh->tr x))
                            (b (bake-tr-sh->tr y))
                            (sh (bake-tr-sh->sh x)))))))

(defthm bake-nlock-map-o-decrement-strict
  (implies (and (bake-nlock-rel-p x y)
                (equal (bake-nlock-chk-ord-arc (bake-nlock-map-e x)
                                               (bake-nlock-map-e y)
                                               o)
                       :<<))
           (bnl< (bake-nlock-map-o y o)
                 (bake-nlock-map-o x o)
                 (bake-nlock-o-bnd)))
  :hints (("Goal"
           :in-theory (e/d (bake-nlock-rel-p bake-nlock-map-e bake-nlock-map-o)
                           (a-shp b-shp sh-shp (a-shp) (b-shp) (sh-shp)))
           :cases ((equal o 'pos) (equal o 'ndx))
           :use ((:instance bake-nlock-map-o-decr-strict-gl-prep-pos
                            (a (bake-tr-sh->tr x))
                            (b (bake-tr-sh->tr y))
                            (sh (bake-tr-sh->sh x)))
                 (:instance bake-nlock-map-o-decr-strict-gl-prep-ndx
                            (a (bake-tr-sh->tr x))
                            (b (bake-tr-sh->tr y))
                            (sh (bake-tr-sh->sh x)))))))

(defthm bake-nlock-map-o-decrement-non-strict
  (implies (and (bake-nlock-rel-p x y)
                (equal (bake-nlock-chk-ord-arc (bake-nlock-map-e x)
                                               (bake-nlock-map-e y)
                                               o)
                       t))
           (bnl<= (bake-nlock-map-o y o)
                  (bake-nlock-map-o x o)
                  (bake-nlock-o-bnd)))
  :hints (("Goal"
           :in-theory (e/d (bake-nlock-rel-p bake-nlock-map-e bake-nlock-map-o)
                           (a-shp b-shp sh-shp (a-shp) (b-shp) (sh-shp)))
           :cases ((equal o 'pos) (equal o 'ndx))
           :use ((:instance bake-nlock-map-o-decr-non-strict-gl-prep-pos
                            (a (bake-tr-sh->tr x))
                            (b (bake-tr-sh->tr y))
                            (sh (bake-tr-sh->sh x)))
                 (:instance bake-nlock-map-o-decr-non-strict-gl-prep-ndx
                            (a (bake-tr-sh->tr x))
                            (b (bake-tr-sh->tr y))
                            (sh (bake-tr-sh->sh x)))))))

(def-valid-wf-corr-assumption bake-nlock)

(in-theory (disable (bake-nlock-o-bnd) bake-nlock-o-bnd
                    (:type-prescription bake-nlock-o-bnd)))

(def-valid-wf-corr-conclusion bake-nlock)

;; we prove that our generated omap is valid and get a bpl measure

(define bake-nlock->bpl (x)
  (bake-nlock-mk-bpl x (w-ord-rslt->order-rslt *bake-nlock-word*)))

(define bake-nlock->bnd ()
  (bake-nlock-bpl-bnd (w-ord-rslt->order-rslt *bake-nlock-word*)))

(in-theory (e/d (bake-nlock->bpl bake-nlock->bnd)
                (bake-nlock-mk-bpl bake-nlock-bpl-bnd
                 (bake-nlock->bnd) (bake-nlock-bpl-bnd))))

(defthm bake-nlock->bpl-is-bplp
  (bplp (bake-nlock->bpl x) (bake-nlock->bnd)))

(defthm bake-nlock->bpl-bnl<
  (implies (bake-nlock-rel-p x y)
           (bnl< (bake-nlock->bpl y) (bake-nlock->bpl x) (bake-nlock->bnd))))

(in-theory (disable bake-nlock->bpl bake-nlock->bnd))

;; finally we prove that our generated omap is valid and prove that
;; bake-nlock-rel-p is well-founded:

(define bake-nlock-wf-msr (x)
  :enabled t
  (bake-nlock-msr x (w-ord-rslt->order-rslt *bake-nlock-word*)))

(in-theory (disable bake-nlock-msr))

(defthm bake-nlock-wf-msr-is-o-p
  (o-p (bake-nlock-wf-msr x)))

(defthm bake-nlock-wf-msr-well-founded
  (implies (bake-nlock-rel-p x y)
           (o< (bake-nlock-wf-msr y)
               (bake-nlock-wf-msr x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End bake-nlock-msr proofs..
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Starting bake-nlock auxiliary proofs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; we also use the bake-rank-a-dom invariant to show that if a
;; bakery is done then it cannot block:

(def-gl-thm bake-tr-done-cannot-blok-gl-prep
  :hyp (and (gl::shape-spec-obj-in-range (a-shp) a)
            (gl::shape-spec-obj-in-range (b-shp) b)
            (gl::shape-spec-obj-in-range (sh-shp) sh))
  :concl (implies (and (in-p (bake-nlock-map a sh) (bake-nlock-a-dom))
                       (in-p (bake-nlock-map b sh) (bake-nlock-a-dom))
                       (bake-tr-done b))
                  (not (bake-tr-blok a b)))
  :g-bindings (get-var-shps '(a b sh))
  :cov-theory-add (enable a-shp b-shp sh-shp)
  :rule-classes nil)

(defthm bake-tr-done-cannot-blok
  (implies (and (bake-tr-p a) (bake-tr-p b) (bake-sh-p sh)
                (in-p (bake-nlock-map a sh) (bake-nlock-a-dom))
                (in-p (bake-nlock-map b sh) (bake-nlock-a-dom))
                (bake-tr-done b))
           (not (bake-tr-blok a b)))
  :hints (("Goal"
           :use ((:instance bake-tr-done-cannot-blok-gl-prep))
           :in-theory (disable a-shp b-shp sh-shp (a-shp) (b-shp) (sh-shp)))))

;; and tidy up some invariant proofs

(defthm bake-nlock-map-init-inv
  (implies (and (bake-ndx-p n)
                (bake-runs-p r))
           (in-p (bake-nlock-map (bake-tr-init n r)
                                 (bake-sh-init))
                 (bake-nlock-a-dom)))
  :hints (("Goal" :in-theory (enable bake-ndx-p bake-runs-p)
           :use (:instance bake-nlock-map-init-gl-inv))))

(defthm bake-nlock-map-next-inv
  (implies (and (bake-tr-p a)
                (bake-sh-p sh)
                (in-p (bake-nlock-map a sh) (bake-nlock-a-dom))
                (not (bake-tr-done a)))
           (in-p (bake-nlock-map (bake-tr-next a sh)
                                 (bake-sh-next sh a))
                 (bake-nlock-a-dom)))
  :hints (("Goal" :in-theory (disable a-shp (a-shp) sh-shp (sh-shp))
           :use (:instance bake-nlock-map-next-gl-inv))))

(defthm bake-nlock-map-next-hold
  (implies (and (bake-tr-p a)
                (bake-tr-p b)
                (bake-sh-p sh)
                (in-p (bake-nlock-map a sh) (bake-nlock-a-dom))
                (in-p (bake-nlock-map b sh) (bake-nlock-a-dom))
                (not (bake-tr-done a)))
           (in-p (bake-nlock-map b (bake-sh-next sh a))
                 (bake-nlock-a-dom)))
  :hints (("Goal" :in-theory (disable a-shp (a-shp) b-shp (b-shp) sh-shp (sh-shp))
           :use (:instance bake-nlock-map-next-gl-hold))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; End bake-nlock auxiliary proofs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
