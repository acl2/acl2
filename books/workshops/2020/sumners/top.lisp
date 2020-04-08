; Copyright (C) 2020, Rob Sumners
; Written by Rob Sumners
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")
(include-book "bake-proofs")

;; we compose the well-founded-ness of the bake-rank and bake-nlock relations
;; to prove the termination of a simplified composition of bakery states..

;; building the top-level bakery routines:

(encapsulate (((bake-init-runs *) => *))
  (local (define bake-init-runs (n) :enabled t (declare (ignore n)) 1))
  (defthm bake-init-runs-bake-runs-p
    (bake-runs-p (bake-init-runs n))))

(define legal-ndx-p (x)
  :enabled t
  (and (bake-ndx-p x) (>= x 0)))

(define bake-init-trs ((n bake-ndx-p))
  :guard (>= n 0)
  :guard-hints (("Goal" :in-theory (enable bake-ndx-p)))
  :returns (r bake-tr-lst-p :hyp :guard
              :hints (("Goal" :in-theory (enable bake-ndx-p))))
  (if (zp n) ()
    (cons (bake-tr-init (1- n) (bake-init-runs (1- n)))
          (bake-init-trs (1- n))))
  ///
  (defthm bake-init-trs-len
    (implies (natp n)
             (equal (len (bake-init-trs n)) n))))
                         
(define bake-init ((max-n bake-ndx-p))
  :guard (>= max-n 0)
  :returns (r bake-st-p :hyp :guard)
  (make-bake-st :sh (bake-sh-init) :trs (bake-init-trs max-n))
  ///
  (defthm bake-init-len-trs
    (implies (legal-ndx-p max-n) ;;(and (bake-ndx-p max-n) (>= max-n 0))
             (equal (len (bake-st->trs (bake-init max-n)))
                    max-n))))

(define all-rank-a-dom ((l bake-tr-lst-p))
  (or (endp l)
      (and (in-p (bake-rank-map (first l)) (bake-rank-a-dom))
           (all-rank-a-dom (rest l)))))

(define all-nlock-a-dom ((l bake-tr-lst-p) (sh bake-sh-p))
  (or (endp l)
      (and (in-p (bake-nlock-map (first l) sh) (bake-nlock-a-dom))
           (all-nlock-a-dom (rest l) sh))))

(define good-st-p (x max-n)
  :enabled t
  (and (bake-st-p x)
       (equal (len (bake-st->trs x)) max-n)
       (all-rank-a-dom (bake-st->trs x))
       (all-nlock-a-dom (bake-st->trs x) (bake-st->sh x))))

(defthm all-rank-a-dom-bake-init
  (implies (legal-ndx-p max-n)  ;; (and (bake-ndx-p max-n) (>= max-n 0))
           (all-rank-a-dom (bake-init-trs max-n)))
  :hints (("Goal" :in-theory (enable bake-rank-map bake-tr-init bake-rank-a-dom
                                     bake-ndx-p all-rank-a-dom bake-init-trs))))

(defthm all-nlock-a-dom-bake-init
  (implies (legal-ndx-p max-n)  ;; (and (bake-ndx-p max-n) (>= max-n 0))
           (all-nlock-a-dom (bake-init-trs max-n) (bake-sh-init)))
  :hints (("Goal" :in-theory (enable bake-nlock-map bake-tr-init bake-nlock-a-dom
                                     bake-ndx-p all-nlock-a-dom bake-init-trs))))

(defthm bake-init-is-good-st-p
  (implies (legal-ndx-p max-n)  ;; (and (bake-ndx-p max-n) (>= max-n 0))
           (good-st-p (bake-init max-n) max-n))
  :hints (("Goal" :in-theory (e/d (bake-init) (bake-sh-init (bake-sh-init))))))

;;;;;;;;;;;

(define bake-rank-bpll ((l bake-tr-lst-p) (sh bake-sh-p))
  :returns (r (bpllp r (bake-rank->bnd)))
  :verify-guards nil
  (if (endp l) ()
    (cons (bake-rank->bpl (make-bake-tr-sh :tr (first l) :sh sh))
          (bake-rank-bpll (rest l) sh))))

(verify-guards bake-rank-bpll)

(define bake-all-done ((l bake-tr-lst-p))
  (or (endp l)
      (and (bake-tr-done (first l))
           (bake-all-done (rest l)))))

(define find-undone ((l bake-tr-lst-p))
  :returns (r natp)
  (cond ((endp l) 0)
        ((not (bake-tr-done (first l))) 0)
        (t (1+ (find-undone (rest l)))))
  ///
  (defthm find-undone-<=-len
    (<= (find-undone l) (len l))
    :rule-classes (:rewrite :linear))

  (defthm find-undone-is-not-done
    (implies (not (bake-all-done l))
             (not (bake-tr-done (nth (find-undone l) l))))
    :hints (("Goal" :in-theory (enable bake-all-done))))

  (defthm find-undone-nth-is-in-bounds
    (implies (not (bake-all-done l))
             (< (find-undone l) (len l)))
    :rule-classes (:linear :rewrite)
    :hints (("Goal" :in-theory (enable bake-all-done)))))

;;;;

(define bake-blok ((a bake-tr-p) (l bake-tr-lst-p))
  (and (consp l)
       (or (bake-tr-blok a (first l))
           (bake-blok a (rest l)))))

(define pick-blok ((a bake-tr-p) (l bake-tr-lst-p))
  :returns (r natp)
  (cond ((endp l) 0)
        ((bake-tr-blok a (first l)) 0)
        (t (1+ (pick-blok a (rest l)))))
  ///
  (defthm pick-blok-<=-len
    (<= (pick-blok a l) (len l))
    :rule-classes (:rewrite :linear))
  
  (defthm pick-blok-is-blocking
    (implies (bake-blok a l)
             (bake-tr-blok a (nth (pick-blok a l) l)))
    :hints (("Goal" :in-theory (enable bake-blok))))
  
  (defthm pick-blok-nth-is-in-bounds
    (implies (bake-blok a l)
             (< (pick-blok a l) (len l)))
    :rule-classes (:linear :rewrite)
    :hints (("Goal" :in-theory (enable bake-blok)))))

;;;;

(defthm all-rank-a-dom-update-nth
  (implies (and (natp n)
                (< n (len l))
                (all-rank-a-dom l)
                (in-p (bake-rank-map e) (bake-rank-a-dom)))
           (all-rank-a-dom (update-nth n e l)))
  :hints (("Goal" :induct (nth n l)
           :in-theory (enable all-rank-a-dom))))

(defthm all-rank-a-dom-nth
  (implies (and (natp n)
                (< n (len l))
                (all-rank-a-dom l))
           (in-p (bake-rank-map (nth n l))
                 (bake-rank-a-dom)))
  :hints (("Goal" :induct (nth n l)
           :in-theory (enable all-rank-a-dom))))

(defthm all-nlock-a-dom-update-nth
  (implies (and (natp n)
                (< n (len l))
                (all-nlock-a-dom l sh)
                (in-p (bake-nlock-map e sh) (bake-nlock-a-dom)))
           (all-nlock-a-dom (update-nth n e l) sh))
  :hints (("Goal" :induct (nth n l)
           :in-theory (enable all-nlock-a-dom))))

(defthm all-nlock-a-dom-nth
  (implies (and (natp n)
                (< n (len l))
                (all-nlock-a-dom l sh))
           (in-p (bake-nlock-map (nth n l) sh)
                 (bake-nlock-a-dom)))
  :hints (("Goal" :induct (nth n l)
           :in-theory (enable all-nlock-a-dom))))

(defthm all-nlock-a-dom-car
  (implies (and (consp l)
                (all-nlock-a-dom l sh))
           (in-p (bake-nlock-map (car l) sh)
                 (bake-nlock-a-dom)))
  :hints (("Goal" :in-theory (enable all-nlock-a-dom))))

(defthm all-nlock-a-dom-transfer
  (implies (and (natp n)
                (< n (len l))
                (bake-tr-lst-p l)
                (bake-sh-p sh)
                (not (bake-tr-done (nth n l)))
                (all-nlock-a-dom l sh))
           (all-nlock-a-dom l (bake-sh-next sh (nth n l))))
    :hints (("Goal" :induct (nth n l)
             :in-theory (enable all-nlock-a-dom))))

;;;;

(define find-unblok ((n natp) (l bake-tr-lst-p) (sh bake-sh-p))
  :measure (bake-nlock-wf-msr (make-bake-tr-sh :tr (nth n l) :sh sh))
  :hints (("Goal" :do-not-induct t
           :use ((:instance bake-nlock-wf-msr-well-founded
                            (y (bake-tr-sh (nth (pick-blok (nth n l) l) l) sh))
                            (x (bake-tr-sh (nth n l) sh))))
           :in-theory (e/d (bake-nlock-rel-p)
                           (bake-nlock-wf-msr-well-founded bake-nlock-wf-msr))))
  :guard (and (< n (len l))
              (all-nlock-a-dom l sh))
  :returns (r natp :hyp (natp n))
  (if (and (mbe :logic (and (natp n)
                            (< n (len l))
                            (bake-tr-lst-p l)
                            (bake-sh-p sh)
                            (all-nlock-a-dom l sh))
                :exec t)
           (bake-blok (nth n l) l))
      (find-unblok (pick-blok (nth n l) l) l sh)
    n))

(defthm find-unblok-is-in-bounds
  (implies (and (natp n)
                (< n (len l))
                (all-nlock-a-dom l sh)
                (bake-tr-lst-p l))
           (< (find-unblok n l sh) (len l)))
  :hints (("Goal" :in-theory (enable find-unblok)))
  :rule-classes (:rewrite :linear))

(defthm find-unblok-is-not-blocked
  (implies (and (natp n)
                (< n (len l))
                (all-nlock-a-dom l sh)
                (bake-sh-p sh)
                (bake-tr-lst-p l))
           (not (bake-blok (nth (find-unblok n l sh) l) l)))
  :hints (("Goal" :in-theory (enable find-unblok))))

(defthm find-unblok-is-not-done
  (implies (and (natp n)
                (< n (len l))
                (all-nlock-a-dom l sh)
                (not (bake-tr-done (nth n l)))
                (bake-sh-p sh)
                (bake-tr-lst-p l))
           (not (bake-tr-done (nth (find-unblok n l sh) l))))
  :hints (("Goal" :in-theory (enable find-unblok))
          ("Subgoal *1/3" :in-theory (disable bake-tr-done-cannot-blok)
           :use ((:instance bake-tr-done-cannot-blok
                            (a (nth n l))
                            (b (nth (pick-blok (nth n l) l) l)))))))

(encapsulate
  (((choose-ready * * *) => *)
   ((next-oracle *) => *)
   ((init-oracle) => *))

  (local
   (defun choose-ready (l sh o)
     (declare (ignore o))
     (find-unblok (find-undone l) l sh)))

  (local
   (defun next-oracle (o)
     (cons o o)))

  (local 
   (defun init-oracle ()
     (cons 1 2)))
   
  (defthm choose-ready-is-natp
    (natp (choose-ready l sh o))
    :rule-classes (:type-prescription :rewrite))
  
  (defthm choose-ready-is-in-bounds
    (implies (and (not (bake-all-done l))
                  (all-nlock-a-dom l sh)
                  (bake-tr-lst-p l))
             (< (choose-ready l sh o) (len l)))
    :rule-classes (:rewrite :linear))

  (defthm choose-ready-is-not-blocked
    (implies (and (not (bake-all-done l))
                  (all-nlock-a-dom l sh)
                  (bake-sh-p sh)
                  (bake-tr-lst-p l))
             (not (bake-blok (nth (choose-ready l sh o) l) l))))

  (defthm choose-ready-is-not-done
    (implies (and (not (bake-all-done l))
                  (all-nlock-a-dom l sh)
                  (bake-sh-p sh)
                  (bake-tr-lst-p l))
             (not (bake-tr-done (nth (choose-ready l sh o) l))))))

;; not sure why I need the following the
(local (defthm stupid1
         (implies (all-rank-a-dom l)
                  (all-rank-a-dom (cdr l)))
         :hints (("Goal" :in-theory (enable all-rank-a-dom)))))

(defthm bnll<-irreflexive ;; this should be in bounded-ords somehow..
  (not (bnll< a a l))
  :hints (("Goal" :in-theory (enable bnll<))))

(local
(defthm bake-rank-bpll-cons-expand
  (implies (and (syntaxp (and (consp l) (eq (car l) 'cons)))
                (consp l))
           (equal (bake-rank-bpll l sh)
                  (cons (bake-rank->bpl (bake-tr-sh (first l) sh))
                        (bake-rank-bpll (rest l) sh))))
  :hints (("Goal" :in-theory (enable bake-rank-bpll)))))

(local
(defthm bake-rank->bpl-sh-irrel-rewrite
  (equal (equal (bake-rank->bpl (bake-tr-sh x sh1))
                (bake-rank->bpl (bake-tr-sh x sh2)))
         t)
  :hints (("Goal" :use (:instance bake-rank->bpl-sh-irrel)))))

(defthm update-nth-not-bake-tr-done-bnll<
  (implies (and (natp n)
                (bake-tr-lst-p l)
                (bake-sh-p sh)
                (all-rank-a-dom l)
                (< n (len l))
                (not (bake-tr-done (nth n l))))
           (bnll< (bake-rank-bpll (update-nth n (bake-tr-next (nth n l) sh) l)
                                  (bake-sh-next sh (nth n l)))
                  (bake-rank-bpll l sh)
                  (bake-rank->bnd)))
  :hints (("Goal" :in-theory (enable bnll< bake-rank-bpll all-rank-a-dom)
           :induct (nth n l))
          ("Subgoal *1/3" :in-theory (e/d (bake-rank-rel-p)
                                          (bake-rank->bpl-bnl<))
           :expand ((bake-rank-bpll l sh)
                    (all-rank-a-dom l))
           :use ((:instance bake-rank->bpl-bnl<
                            (x (make-bake-tr-sh :tr (car l) :sh sh))
                            (y (make-bake-tr-sh :tr (bake-tr-next (car l) sh)
                                                :sh (bake-sh-next sh (car l)))))))
          ("Subgoal *1/2" :in-theory (e/d (bake-rank-rel-p)
                                          (bake-rank->bpl-bnl<))
           :expand ((bake-rank-bpll l sh)
                    (all-rank-a-dom l))
           :use ((:instance bake-rank->bpl-bnl<
                            (x (make-bake-tr-sh :tr (car l) :sh sh))
                            (y (make-bake-tr-sh :tr (bake-tr-next (car l) sh)
                                                :sh (bake-sh-next sh (car l))))))))
  :rule-classes nil)

(local
 (defthm len-of-update-nth-backchain
   (implies (and (natp n) (< n (len l)))
            (equal (len (update-nth n e l))
                   (len l)))))

(local
 (defthm len-of-bake-rank-bpll
   (equal (len (bake-rank-bpll l sh))
          (len l))
   :hints (("Goal" :in-theory (enable bake-rank-bpll)))))

(local
 (defthm bake-run-msr-proof
   (implies
    (and (not (bake-all-done l))
         (not (bake-tr-done (nth n l)))
         (bake-tr-lst-p l)
         (bake-sh-p sh)
         (natp n)
         (< n (len l))
         (all-rank-a-dom l))
    (o< (bnll->o (len l)
                 (bake-rank-bpll (update-nth n (bake-tr-next (nth n l) sh) l)
                                 (bake-sh-next sh (nth n l)))
                 (bake-rank->bnd))
        (bnll->o (len l)
                 (bake-rank-bpll l sh)
                 (bake-rank->bnd))))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable bake-rank-bpll bnll<-implies-o<-bnll->o)           
            :use ((:instance update-nth-not-bake-tr-done-bnll<)
                  (:instance bnll<-implies-o<-bnll->o
                             (b (bake-rank->bnd))
                             (n (len l))
                             (x (bake-rank-bpll (update-nth n (bake-tr-next (nth n l) sh) l)
                                                (bake-sh-next sh (nth n l))))
                             (y (bake-rank-bpll l sh))))))
   :rule-classes nil))

(define final-st-p ((st bake-st-p) max-n)
  :enabled t
  (and (good-st-p st max-n)
       (bake-all-done (bake-st->trs st))))

(define bake-run (st max-n oracle)
  :guard (and (legal-ndx-p max-n)
              (good-st-p st max-n))
  :measure (bnll->o (len (bake-st->trs st))
                    (bake-rank-bpll (bake-st->trs st)
                                    (bake-st->sh st))
                    (bake-rank->bnd))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (bake-st-p)
                           (bake-rank-bpll bake-rank-bpll-cons-expand
                                           bnll->o o-finp o<))
           :use (:instance bake-run-msr-proof
                           (n (choose-ready (bake-st->trs st)
                                            (bake-st->sh st)
                                            oracle))
                           (l (bake-st->trs st))
                           (sh (bake-st->sh st)))))
  :returns (r (final-st-p r max-n) :hyp :guard)
  (b* (((bake-st st) st))
    (cond
     ((bake-all-done st.trs) st)
     ((mbe :logic (and (good-st-p st max-n)
                       (legal-ndx-p max-n))
           :exec t)
      (b* ((n   (choose-ready st.trs st.sh oracle))
           (a   (nth n st.trs))
           (trs (update-nth n (bake-tr-next a st.sh) st.trs))
           (sh  (bake-sh-next st.sh a)))
        (bake-run (make-bake-st :trs trs :sh sh) max-n
                  (next-oracle oracle))))
     (t st))))

(define bake-go ((max-n legal-ndx-p))
  :guard-hints (("Goal" :in-theory (disable good-st-p)))
  :returns (r (final-st-p r max-n) :hyp :guard
              :hints (("Goal" :in-theory (disable final-st-p good-st-p legal-ndx-p))))
  (bake-run (bake-init max-n) max-n (init-oracle)))

#|
Well-founded relations in ACL2:

(encapsulate (((r * *) => *) ((m *) => *))
  (local (defun r (x y) (declare (ignore x y)) nil))
  (local (defun m (x)   (declare (ignore x))   1))  

  (defthm m-is-an-ordinal (o-p (m x)))
  (defthm m-is-o<-when-r  (implies (r x y) (o< (m y) (m x)))))

(defchoose chz-r (y) (x) (r x y))

(defun seq-r (x)  ;; any seq. of objects related by R must be finite!
  (declare (xargs :measure (m x)))
  (if (r x (chz-r x)) (seq-r (chz-r x)) x))
|#

#|
Computed measure in the case bake-rank-map:

;;                (<abstract node -- reachable bake-rank-map>) . (<measure-descriptor>)
;;                ---------------------------------------------------------------------
((((:LOC 0)  (:DONE NIL) (:LOOP=0 T)   (:RUNS=0 NIL) (:INV T)) . (4 RUNS 11 0))
 (((:LOC 1)  (:DONE NIL) (:LOOP=0 T)   (:RUNS=0 NIL) (:INV T)) . (4 RUNS 10 0))
 (((:LOC 2)  (:DONE NIL) (:LOOP=0 T)   (:RUNS=0 NIL) (:INV T)) . (4 RUNS 9  0))
 (((:LOC 3)  (:DONE NIL) (:LOOP=0 NIL) (:RUNS=0 NIL) (:INV T)) . (4 RUNS 8  LOOP 2 0))
 (((:LOC 4)  (:DONE NIL) (:LOOP=0 NIL) (:RUNS=0 NIL) (:INV T)) . (4 RUNS 8  LOOP 1 0))
 (((:LOC 5)  (:DONE NIL) (:LOOP=0 NIL) (:RUNS=0 NIL) (:INV T)) . (4 RUNS 8  LOOP 3 0))
 (((:LOC 5)  (:DONE NIL) (:LOOP=0 T)   (:RUNS=0 NIL) (:INV T)) . (4 RUNS 7  0))
 (((:LOC 6)  (:DONE NIL) (:LOOP=0 T)   (:RUNS=0 NIL) (:INV T)) . (4 RUNS 6  0))
 (((:LOC 7)  (:DONE NIL) (:LOOP=0 T)   (:RUNS=0 NIL) (:INV T)) . (4 RUNS 5  0))
 (((:LOC 8)  (:DONE NIL) (:LOOP=0 NIL) (:RUNS=0 NIL) (:INV T)) . (4 RUNS 4  LOOP 4 0))
 (((:LOC 9)  (:DONE NIL) (:LOOP=0 NIL) (:RUNS=0 NIL) (:INV T)) . (4 RUNS 4  LOOP 3 0))
 (((:LOC 10) (:DONE NIL) (:LOOP=0 NIL) (:RUNS=0 NIL) (:INV T)) . (4 RUNS 4  LOOP 2 0))
 (((:LOC 11) (:DONE NIL) (:LOOP=0 NIL) (:RUNS=0 NIL) (:INV T)) . (4 RUNS 4  LOOP 1 0))
 (((:LOC 12) (:DONE NIL) (:LOOP=0 NIL) (:RUNS=0 NIL) (:INV T)) . (4 RUNS 4  LOOP 5 0))
 (((:LOC 12) (:DONE NIL) (:LOOP=0 T)   (:RUNS=0 NIL) (:INV T)) . (4 RUNS 3  0))
 (((:LOC 13) (:DONE NIL) (:LOOP=0 T)   (:RUNS=0 NIL) (:INV T)) . (4 RUNS 2  0))
 (((:LOC 14) (:DONE NIL) (:LOOP=0 T)   (:RUNS=0 NIL) (:INV T)) . (4 RUNS 1  0))
 (((:LOC 15) (:DONE NIL) (:LOOP=0 T)   (:RUNS=0 NIL) (:INV T)) . (4 RUNS 12 0))
 (((:LOC 15) (:DONE NIL) (:LOOP=0 T)   (:RUNS=0 T)   (:INV T)) . (3 0))
 (((:LOC 16) (:DONE NIL) (:LOOP=0 T)   (:RUNS=0 T)   (:INV T)) . (2 0))
 (((:LOC 17) (:DONE T)   (:LOOP=0 T)   (:RUNS=0 T)   (:INV T)) . (1 0)))
|#
