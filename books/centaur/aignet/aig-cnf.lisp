; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

;; mechanism for transforming AIG -> AIGNET -> CNF and showing them
;; equisatisfiable

(in-package "AIGNET")

(include-book "aignet-cnf")
(include-book "aignet-from-aig")
(include-book "aignet-refcounts")
(include-book "centaur/aig/accumulate-nodes-vars" :dir :system)
(local (include-book "centaur/satlink/cnf-basics" :dir :system))

(local (in-theory (e/d (aiglist-to-aignet)
                       (create-sat-lits
                        (create-sat-lits)
                        resize-aignet->sat
                        nth update-nth
                        acl2::make-list-ac-redef
                        make-list-ac
                        aignet-count-refs
                        acl2::nth-with-large-index
                        (aignet-clear)))))


(defun aignet-one-lit->cnf (lit sat-lits aignet)
  (declare (xargs :stobjs (aignet sat-lits)
                  :guard (and (aignet-well-formedp aignet)
                              (aignet-litp lit aignet))))
  (b* (((local-stobjs aignet-refcounts)
        (mv cnf sat-lits aignet-refcounts))
       (sat-lits (sat-lits-empty (num-nodes aignet) sat-lits))
       (aignet-refcounts (resize-u32 (num-nodes aignet) aignet-refcounts))
       (aignet-refcounts (aignet-count-refs 0 aignet-refcounts aignet))
       ((mv sat-lits cnf)
        (aignet-lit->cnf lit t aignet-refcounts sat-lits aignet nil))
       (sat-lit (aignet-lit->sat-lit lit sat-lits)))
    (mv (list* (list sat-lit) ;; lit is true
               (list 1)       ;; constant-0 is false
               cnf)
        sat-lits aignet-refcounts)))

(defthm lit-list-listp-of-aignet-one-lit->cnf
  (satlink::lit-list-listp (mv-nth 0 (aignet-one-lit->cnf lit sat-lits aignet))))

(defthm sat-lits-wfp-of-aignet-one-lit->cnf
  (implies (aignet-well-formedp aignet)
           (sat-lits-wfp (mv-nth 1 (aignet-one-lit->cnf lit sat-lits aignet))
                         aignet))
  :hints(("Goal" :in-theory (enable aignet-one-lit->cnf))))

(defthm aignet-one-lit->cnf-normalize-sat-lits
  (implies (syntaxp (not (equal sat-lits ''nil)))
           (equal (aignet-one-lit->cnf lit sat-lits aignet)
                  (aignet-one-lit->cnf lit nil aignet))))

(defthm satlink::eval-lit-1
  (equal (satlink::eval-lit 1 cnf-eval)
         (b-not (satlink::eval-var 0 cnf-eval)))
  :hints(("Goal" :in-theory (enable satlink::eval-lit))))

(defthm 0-value-of-aignet->cnf-eval
  (implies (and (aignet-well-formedp aignet)
                (sat-lits-wfp sat-lits aignet))
           (equal (satlink::eval-var 0 (aignet->cnf-eval 0 in-vals reg-vals sat-lits
                                                    cnf-eval aignet))
                  0))
  :hints (("goal" :in-theory (e/d (satlink::eval-lit)
                                  (lookup-in-aignet->cnf-eval))
           :use ((:instance lookup-in-aignet->cnf-eval
                  (m 0) (n 0))))))

(local (in-theory (e/d (satlink-eval-lit-of-make-lit-of-lit-var)
                       (satlink::eval-lit-of-make-lit))))

(defthm aignet-satisfying-assign-induces-cnf-satisfying-assign
  (b* (((mv cnf sat-lits) (aignet-one-lit->cnf lit sat-lits aignet))
       (cnf-eval (aignet->cnf-eval 0 in-vals reg-vals sat-lits cnf-eval aignet)))
    (implies (and (aignet-well-formedp aignet)
                  (aignet-litp lit aignet)
                  (sat-lits-wfp sat-lits aignet)
                  (equal (lit-eval lit in-vals reg-vals aignet) 1))
             (equal (satlink::eval-formula cnf cnf-eval) 1))))


(defun cnf-eval->aignet-vals (n cnf-eval aignet-vals sat-lits aignet)
  (declare (xargs :stobjs (cnf-eval aignet-vals sat-lits aignet)
                  :guard (and (aignet-well-formedp aignet)
                              (sat-lits-wfp sat-lits aignet)
                              (natp n)
                              (<= n (sat-next-var sat-lits))
                              (bitarr-sizedp aignet-vals aignet))
                  :measure (nfix (- (nfix (sat-next-var sat-lits))
                                    (nfix n)))
                  :guard-hints (("goal" :in-theory (enable sat-varp))))
           (ignorable aignet))
  (b* (((when (mbe :logic (zp (- (nfix (sat-next-var sat-lits))
                                 (nfix n)))
                   :exec (int= (sat-next-var sat-lits) n)))
        aignet-vals)
       (nvar (satlink::make-var n))
       (val (satlink::eval-var nvar cnf-eval))
       (lit (sat-var->aignet-lit nvar sat-lits))
       (val (b-xor val (lit-neg lit)))
       (aignet-vals (set-id->bit (lit-id lit) val aignet-vals)))
    (cnf-eval->aignet-vals (1+ (lnfix n)) cnf-eval aignet-vals sat-lits
                           aignet)))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (in-theory (disable acl2::nth-with-large-index
                           (:definition cnf-eval->aignet-vals)
                           sat-lits-wfp-implies-when-not-aignet-idp)))

;; (local (in-theory (enable satlink::eval-var)))

;; (local (DEFTHM SAT-LITS-WFP-IMPLIES-LOOKUP-SAT-VAR-part
;;                 (IMPLIES
;;                  (AND
;;                    (SAT-LITS-WFP SAT-LITS AIGNET)
;;                    (BIND-FREE (MATCH-EQUIV-OR-REFINEMENT
;;                                    'ID-EQUIV
;;                                    'ID
;;                                    '(LIT-ID (SAT-VAR->AIGNET-LIT N SAT-LITS))
;;                                    MFC STATE)
;;                               (N))
;;                    (ID-EQUIV ID
;;                              (LIT-ID (SAT-VAR->AIGNET-LIT N SAT-LITS)))
;;                    (SAT-VARP N SAT-LITS))
;;                  (AIGNET-ID-HAS-SAT-VAR ID SAT-LITS))))

;; (local (in-theory (disable SAT-LITS-WFP-IMPLIES-LOOKUP-SAT-VAR)))

(local (in-theory (disable aignet-id->sat-lit-var-index-bound)))
; (local (in-theory (disable SAT-LITS-WFP-IMPLIES-LOOKUP-AIGNET-ID)))
(defthm lookup-in-cnf-eval->aignet-vals
  (implies (and (aignet-well-formedp aignet)
                (sat-lits-wfp sat-lits aignet))
           (acl2::bit-equiv
            (nth m (cnf-eval->aignet-vals
                    n cnf-eval aignet-vals sat-lits aignet))
            (let ((sat-lit (aignet-id->sat-lit (to-id m) sat-lits)))
              (if (or (not (aignet-id-has-sat-var (to-id m) sat-lits))
                      (< (satlink::var->index (satlink::lit->var sat-lit)) (nfix n))
                      (<= (nfix (sat-next-var sat-lits)) (satlink::var->index (satlink::lit->var sat-lit))))
                  (nth m aignet-vals)
                (satlink::eval-lit sat-lit cnf-eval)))))
  :hints ((acl2::just-induct-and-expand
           (cnf-eval->aignet-vals
            n cnf-eval aignet-vals sat-lits aignet))
          (and stable-under-simplificationp
               '(:in-theory (e/d (satlink::eval-lit
                                  satlink::eval-var))))
          ))


(local (defthm sat-next-var-gte-0-when-sat-lits-wfp
         (mv-let (sat-lits cnf)
           (aignet-lit->cnf x use-muxes refcounts sat-lits aignet cnf)
           (declare (ignore cnf))
           (implies (sat-lits-wfp sat-lits aignet)
                    (<= 0 (nth *sat-next-var* sat-lits))))))

;; (defun aignet-one-lit-cnf-eval->aignet-vals (cnf-eval lit aignet)
;;   (declare (xargs :stobjs (cnf-eval aignet)
;;                   :guard (and (aignet-well-formedp aignet)
;;                               (aignet-litp lit aignet))
;;                   :guard-debug t))
;;   (b* (((local-stobjs sat-lits aignet-refcounts aignet-vals)
;;         (mv avals sat-lits aignet-refcounts aignet-vals))
;;        (aignet-refcounts (resize-u32 (num-nodes aignet) aignet-refcounts))
;;        (aignet-refcounts (aignet-count-refs 0 aignet-refcounts aignet))
;;        (sat-lits (resize-aignet->sat (num-nodes aignet) sat-lits))
;;        ((mv sat-lits ?cnf)
;;         (aignet-lit->cnf lit t aignet-refcounts sat-lits aignet
;;                               nil))
;;        (aignet-vals (resize-bits (num-nodes aignet) aignet-vals))
;;        (aignet-vals (cnf-eval->aignet-vals 0 cnf-eval aignet-vals sat-lits aignet))
;;        (aignetvals (non-exec aignet-vals)))
;;     (mv aignetvals
;;         sat-lits aignet-refcounts aignet-vals)))



(defcong bits-equiv equal
  (cnf/aignet-evals-agree n in-vals reg-vals sat-lits cnf-eval aignet) 2
  :hints((acl2::just-induct-and-expand
          (cnf/aignet-evals-agree n in-vals reg-vals sat-lits cnf-eval
                                  aignet))))

(defcong bits-equiv equal
  (cnf/aignet-evals-agree n in-vals reg-vals sat-lits cnf-eval aignet) 3
  :hints((acl2::just-induct-and-expand
          (cnf/aignet-evals-agree n in-vals reg-vals sat-lits cnf-eval aignet))))

(defthm nth-of-aignet-vals-in-vals-ext
  (implies (and (aignet-well-formedp aignet)
                (<= (nfix m) (num-ins aignet)))
           (acl2::bit-equiv
            (nth n (aignet-vals-in-vals-iter m in-vals aignet-vals aignet))
            (if (< (nfix n) (nfix m))
                (nth (id-val (innum->id n aignet))
                     aignet-vals)
              (nth n in-vals))))
    :hints ((acl2::just-induct-and-expand (aignet-vals-in-vals-iter m in-vals aignet-vals aignet))))

(defthm lookup-in-aignet-vals-in-vals-iter-of-cnf-eval->aignet-vals
  (implies (and (aignet-well-formedp aignet)
                (sat-lits-wfp sat-lits aignet)
                (bits-equiv aignet-vals nil))
           (acl2::bit-equiv
            (nth i (aignet-vals-in-vals-iter
                    (nth *num-ins* aignet)
                    nil
                    (cnf-eval->aignet-vals 0 cnf-eval aignet-vals sat-lits
                                           aignet)
                    aignet))
            (nth i (cnf->aignet-in-vals 0 nil sat-lits cnf-eval aignet))))
  :hints (("goal" :use
           ((:instance SAT-LITS-WFP-IMPLIES-SAT-VARP-OF-LOOKUP-AIGNET-ID
             (n (NTH-ID I (NTH *INSI* AIGNET)))))
           :in-theory (e/d (sat-varp)
                           (sat-lits-wfp-implies-sat-varp-of-lookup-aignet-id)))))

(defthm bits-equiv-of-aignet-vals-in-vals-iter-of-cnf-eval->aignet-vals
  (implies (and (aignet-well-formedp aignet)
                (sat-lits-wfp sat-lits aignet)
                (double-rewrite (bits-equiv aignet-vals nil)))
           (acl2::bits-equiv
            (aignet-vals-in-vals-iter
             (nth *num-ins* aignet)
             nil
             (cnf-eval->aignet-vals 0 cnf-eval aignet-vals sat-lits
                                    aignet)
             aignet)
            (cnf->aignet-in-vals 0 nil sat-lits cnf-eval aignet)))
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defthm nth-of-aignet-vals-reg-vals-ext
  (implies (and (aignet-well-formedp aignet)
                (<= (nfix m) (num-regs aignet)))
           (acl2::bit-equiv
            (nth n (aignet-vals-reg-vals-iter m reg-vals aignet-vals aignet))
            (if (< (nfix n) (nfix m))
                (nth (id-val (regnum->ro n aignet))
                     aignet-vals)
              (nth n reg-vals))))
    :hints ((acl2::just-induct-and-expand (aignet-vals-reg-vals-iter m reg-vals
                                                                    aignet-vals
                                                                    aignet))))

(defthm lookup-in-aignet-vals-reg-vals-iter-of-cnf-eval->aignet-vals
  (implies (and (aignet-well-formedp aignet)
                (sat-lits-wfp sat-lits aignet)
                (bits-equiv aignet-vals nil))
           (acl2::bit-equiv
            (nth i (aignet-vals-reg-vals-iter
                    (nth *num-regs* aignet)
                    nil
                    (cnf-eval->aignet-vals 0 cnf-eval aignet-vals sat-lits
                                           aignet)
                    aignet))
            (nth i (cnf->aignet-reg-vals 0 nil sat-lits cnf-eval aignet))))
  :hints (("goal" :use
           ((:instance SAT-LITS-WFP-IMPLIES-SAT-VARP-OF-LOOKUP-AIGNET-ID
             (n (regnum->ro I aignet))))
           :in-theory (e/d (sat-varp)
                           (sat-lits-wfp-implies-sat-varp-of-lookup-aignet-id)))))

(defthm bits-equiv-of-aignet-vals-reg-vals-iter-of-cnf-eval->aignet-vals
  (implies (and (aignet-well-formedp aignet)
                (sat-lits-wfp sat-lits aignet)
                (double-rewrite (bits-equiv aignet-vals nil)))
           (acl2::bits-equiv
            (aignet-vals-reg-vals-iter
             (nth *num-regs* aignet)
             nil
             (cnf-eval->aignet-vals 0 cnf-eval aignet-vals sat-lits
                                    aignet)
             aignet)
            (cnf->aignet-reg-vals 0 nil sat-lits cnf-eval aignet)))
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause)))))))


(defcong bits-equiv bits-equiv (cons a b) 2
  :hints(("Goal" :expand ((:free (c d)
                           (bits-equiv (cons a b) (cons c d)))
                          (:free (n a b)
                           (nth n (cons a b)))))))

(defcong bit-equiv bits-equiv (cons a b) 1
  :hints(("Goal" :expand ((:free (c d)
                           (bits-equiv (cons a b) (cons c d)))
                          (:free (n a b)
                           (nth n (cons a b)))))))

(defthm make-list-ac-bit-equiv
  (implies (bits-equiv acc nil)
           (bits-equiv (make-list-ac n 0 acc)
                       nil))
  :hints (("goal" :induct (make-list-ac n 0 acc)
           :in-theory (enable acl2::make-list-ac-redef))
          (and stable-under-simplificationp
               '(:expand ((bits-equiv '(0) nil)
                          (:free (n a b)
                           (nth n (cons a b)))))))
  :otf-flg t)


(local (defthm b-and-equals-1
         (implies (acl2::rewriting-negative-literal
                   `(equal (acl2::b-and$inline ,a ,b) '1))
                  (equal (equal (b-and a b) 1)
                         (and (equal a 1)
                              (equal b 1))))
         :hints(("Goal" :in-theory (enable b-and)))))

(local (defthm b-ior-0
         (equal (b-ior x 0)
                (bfix x))
         :hints(("Goal" :in-theory (enable b-ior)))))



(encapsulate
  nil
  (local (in-theory (disable cnf/aignet-evals-agree-implies
                             cnf/aignet-evals-agree
                             aignet-count-refs
                             acl2::zp-open
                             acl2::make-list-ac-redef
                             make-list-ac)))
  (defthm cnf-satisfying-assign-induces-aignet-satisfying-assign
    (b* (((mv cnf sat-lits) (aignet-one-lit->cnf lit sat-lits aignet))
         (aignet-vals (resize-bits (num-nodes aignet) (acl2::create-bitarr)))
         (aignet-vals (cnf-eval->aignet-vals 0 cnf-eval aignet-vals sat-lits aignet)))
      (implies (and (aignet-well-formedp aignet)
                    (aignet-litp lit aignet)
                    (equal (satlink::eval-formula cnf cnf-eval) 1))
               (equal (lit-eval lit
                                (aignet-vals-in-vals nil aignet-vals aignet)
                                (aignet-vals-reg-vals nil aignet-vals aignet)
                                aignet)
                      1)))
    :hints(("Goal" :in-theory (disable b-and b-ior b-xor b-not)
            :use ((:instance cnf/aignet-evals-agree-implies
                   (in-vals
                    (b* (((mv ?cnf sat-lits) (aignet-one-lit->cnf lit sat-lits aignet))
                         (aignet-vals (resize-bits (num-nodes aignet) (acl2::create-bitarr)))
                         (aignet-vals (cnf-eval->aignet-vals 0 cnf-eval aignet-vals sat-lits aignet)))
                      (aignet-vals-in-vals nil aignet-vals aignet)))
                   (reg-vals
                    (b* (((mv ?cnf sat-lits) (aignet-one-lit->cnf lit sat-lits aignet))
                         (aignet-vals (resize-bits (num-nodes aignet) (acl2::create-bitarr)))
                         (aignet-vals (cnf-eval->aignet-vals 0 cnf-eval aignet-vals sat-lits aignet)))
                      (aignet-vals-reg-vals nil aignet-vals aignet)))
                   (sat-lits
                    (b* (((mv ?cnf sat-lits) (aignet-one-lit->cnf lit sat-lits aignet)))
                      sat-lits))
                   (m (lit-id lit))
                   (n 0))))
           (and stable-under-simplificationp
                '(:in-theory (e/d (b-xor)))))))






(in-theory (disable aignet-one-lit->cnf))


(defthm good-varmap-p-of-nil
  (good-varmap-p nil x)
  :hints(("Goal" :in-theory (enable good-varmap-p))))

(defun aig->cnf (aig sat-lits aignet)
  (declare (xargs :stobjs (aignet sat-lits)))
  (b* (((local-stobjs strash)
        (mv cnf lit vars sat-lits aignet strash))
       (aiglist (list aig))
       (vars (acl2::aig-vars-unordered-list aiglist))
       (aignet (aignet-clear aignet))
       ((mv varmap aignet) (make-varmap vars nil nil aignet))
       (strash (strashtab-init 100 nil nil strash))
       ((mv lits strash aignet)
        (aiglist-to-aignet-top aiglist varmap strash
                               (mk-gatesimp 4 t) aignet))
       (aignet-lit (car lits))
       ((mv cnf sat-lits)
        (aignet-one-lit->cnf aignet-lit sat-lits aignet)))
    (mv cnf aignet-lit vars sat-lits aignet strash)))

(defthm lit-list-listp-of-aig->cnf
  (satlink::lit-list-listp (mv-nth 0 (aig->cnf aig sat-lits aignet))))

;; (defun reverse-varmap (varmap)
;;   (b* (((when (atom varmap))
;;         nil)
;;        ((when (atom (car varmap)))
;;         (reverse-varmap (cdr varmap)))
;;        ((cons aig-node lit) (car varmap))
;;        ((when (consp aig-node))
;;         (reverse-varmap (cdr varmap))))
;;     (cons (cons (lit-id lit) aig-node)
;;           (reverse-varmap (cdr varmap)))))

(defun env-to-in-vals (vars env)
  (declare (xargs :guard t))
  (if (atom vars)
      nil
    (cons (if (acl2::aig-env-lookup (car vars) env) 1 0)
          (env-to-in-vals (cdr vars) env))))

(defun satisfying-assign-for-env (env vars sat-lits aignet cnf-eval)
  (declare (xargs :stobjs (sat-lits aignet cnf-eval)
                  :guard (and (aignet-well-formedp aignet)
                              (sat-lits-wfp sat-lits aignet))))
  (b* ((in-vals (env-to-in-vals vars env))
       (cnf-eval (resize-bits 0 cnf-eval))
       (cnf-eval (resize-bits (sat-next-var sat-lits) cnf-eval))
       (cnf-eval (aignet->cnf-eval 0 in-vals nil sat-lits cnf-eval aignet)))
    cnf-eval))

;; (defun aig-aignet-lit-in-vals (env aig)
;;   (declare (xargs :guard t))
;;   (b* (((local-stobjs aignet strash)
;;         (mv anet lit in-vals aignet strash))
;;        (aiglist (list aig))
;;        (vars (acl2::aig-vars-unordered-list aiglist))
;;        (aignet (resize-nodes (max 100 (* 2 (len vars))) aignet))
;;        (aignet (aignet-clear aignet))
;;        ((mv varmap aignet) (make-varmap vars nil nil aignet))
;;        (strash (strashtab-init 100 nil nil strash))
;;        ((mv lits strash aignet)
;;         (aiglist-to-aignet-top aiglist varmap strash
;;                                (mk-gatesimp 4 t) aignet))
;;        (aignet-lit (car lits))
;;        (in-vals (env-to-in-vals vars env)))
;;     (mv (non-exec aignet) aignet-lit in-vals aignet strash)))

(defthm lookup-in-make-varmap-iff
  (iff (hons-assoc-equal v (mv-nth 0 (make-varmap vars nil varmap0 aignet0)))
       (or (member v vars)
           (hons-assoc-equal v varmap0)))
  :hints(("Goal" :in-theory (enable make-varmap))))



(defun lst-position (x lst)
  (cond ((endp lst) nil)
        ((equal x (car lst)) 0)
        (t (let ((rst (lst-position x (cdr lst))))
             (and rst (+ 1 rst))))))

(defthm lst-position-iff-member
  (iff (lst-position x lst)
       (member x lst)))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(defthm lookup-in-make-varmap
  (implies (and (no-duplicatesp vars)
                (not (intersectp-equal vars (alist-keys varmap0)))
                (aignet-well-formedp aignet0))
           (equal (cdr (hons-assoc-equal v (mv-nth 0 (make-varmap vars nil varmap0
                                                                  aignet0))))
                  (if (member v vars)
                      (mk-lit (to-id (+ (lst-position v vars)
                                        (num-nodes aignet0)))
                              0)
                    (cdr (hons-assoc-equal v varmap0)))))
  :hints(("Goal" :in-theory (enable make-varmap
                                    intersectp-equal
                                    alist-keys)
          :induct (make-varmap vars nil varmap0 aignet0))))

(in-theory (enable (:induction make-varmap)))
(def-aignet-preservation-thms make-varmap)

(defthm num-ins-of-make-varmap
  (implies (aignet-well-formedp aignet)
           (equal (nth *num-ins* (mv-nth 1 (make-varmap vars nil acc aignet)))
                  (+ (nth *num-ins* aignet)
                     (len vars))))
  :hints(("Goal" :in-theory (enable make-varmap))))

(defthm num-regs-of-make-varmap
  (implies (aignet-well-formedp aignet)
           (equal (nth *num-regs* (mv-nth 1 (make-varmap vars nil acc aignet)))
                  (nth *num-regs* aignet)))
  :hints(("Goal" :in-theory (enable* make-varmap aignet-frame-thms))))


(encapsulate nil
  (local
   (defthm aignet-idp-in-make-varmap
     (implies (and (aignet-well-formedp aignet0)
                   (idp id)
                   (force (< (id-val id) (+ (num-nodes aignet0)
                                            (len vars)))))
              (aignet-idp id (mv-nth 1 (make-varmap vars regp varmap0 aignet0))))
     :hints(("Goal" :in-theory (enable make-varmap)
             :induct (make-varmap vars regp varmap0 aignet0))
            (and stable-under-simplificationp
                 '(:in-theory (enable aignet-idp))))))

  (local
   (defthm aignet-idp-of-aignet-add-reg
     (implies (and (aignet-well-formedp aignet)
                   (idp id)
                   (<= (id-val id) (num-nodes aignet)))
              (aignet-idp id (mv-nth 1 (Aignet-add-reg aignet))))
     :hints(("Goal" :in-theory (enable aignet-add-reg
                                       aignet-idp)))))

  (local
   (defthm aignet-idp-of-aignet-add-in
     (implies (and (aignet-well-formedp aignet)
                   (idp id)
                   (<= (id-val id) (num-nodes aignet)))
              (aignet-idp id (mv-nth 1 (Aignet-add-in aignet))))
     :hints(("Goal" :in-theory (enable aignet-add-in
                                       aignet-idp)))))

  (local
   (defthm node-type-in-make-varmap
     (implies (and (aignet-well-formedp aignet0)
                   (idp id)
                   (<= (num-nodes aignet0) (id-val id))
                   (force (< (id-val id) (+ (num-nodes aignet0)
                                            (len vars)))))
              (let ((node (nth-node
                           id
                           (nth *nodesi*
                                (mv-nth 1 (make-varmap vars regp varmap0
                                                       aignet0))))))
                (and (equal (node->type node) (in-type))
                     (equal (node->regp node) (if regp 1 0)))))
     :hints(("Goal" :in-theory (enable make-varmap)
             :induct (make-varmap vars regp varmap0 aignet0))
            (and stable-under-simplificationp
                 '(:in-theory (enable aignet-add-reg
                                      aignet-add-in
                                      mk-in-node
                                      mk-reg-node))))))

  (defthm id-eval-of-make-varmap-input
    (implies (and (aignet-well-formedp aignet0)
                  (idp id)
                  (<= (num-nodes aignet0) (id-val id))
                  (< (id-val id) (+ (num-nodes aignet0)
                                    (len vars))))
             (equal (id-eval id in-vals reg-vals
                             (mv-nth 1 (make-varmap vars nil varmap0 aignet0)))
                    (bfix (nth (+ (id-val id)
                                  (- (num-nodes aignet0))
                                  (num-ins aignet0))
                               in-vals))))
    :hints(("Goal" :in-theory (enable make-varmap)
            :induct (make-varmap vars nil varmap0 aignet0))
           (and stable-under-simplificationp
                '(:expand ((:free (aignet)
                            (id-eval id in-vals reg-vals aignet)))))))

  (defthm lit-eval-of-make-varmap-input
    (implies (and (aignet-well-formedp aignet0)
                  (<= (num-nodes aignet0)
                      (id-val (lit-id lit)))
                  (< (id-val (lit-id lit))
                     (+ (num-nodes aignet0)
                        (len vars))))
             (equal (lit-eval lit in-vals reg-vals
                              (mv-nth 1 (make-varmap vars nil varmap0
                                                     aignet0)))
                    (b-xor (lit-neg lit)
                           (nth (+ (id-val (lit-id lit))
                                   (- (num-nodes aignet0))
                                   (num-ins aignet0))
                                in-vals))))
    :hints(("Goal"
            :expand ((:free (aignet)
                      (lit-eval lit in-vals reg-vals aignet)))
            :in-theory (disable id-eval-in-terms-of-lit-eval)
            :do-not-induct t))))






(local (defthm intersectp-equal-of-switch
         (implies (and (no-duplicatesp a)
                       (not (intersectp-equal a b)))
                  (not (intersectp-equal (cdr a)
                                          (cons (car a) b))))
         :hints(("Goal" :in-theory (enable intersectp-equal)))))


(defthm id-eval-of-aignet-add-in
  (equal (id-eval (to-id (nth *num-nodes* aignet))
                  in-vals reg-vals
                  (mv-nth 1 (aignet-add-in aignet)))
         (bfix (nth (num-ins aignet) in-vals)))
  :hints(("Goal" :in-theory (enable id-eval))))

(defthm id-eval-of-aignet-add-reg
  (equal (id-eval (to-id (nth *num-nodes* aignet))
                  in-vals reg-vals
                  (mv-nth 1 (aignet-add-reg aignet)))
         (bfix (nth (num-regs aignet) reg-vals)))
  :hints(("Goal" :in-theory (enable id-eval))))

(defthm lit-eval-of-aignet-add-in
  (implies (equal (id-val (lit-id lit))
                  (nfix (num-nodes aignet)))
           (equal (lit-eval lit in-vals reg-vals
                            (mv-nth 1 (aignet-add-in aignet)))
                  (b-xor (lit-neg lit)
                         (nth (num-ins aignet) in-vals))))
  :hints(("Goal" :in-theory (e/d (lit-eval)
                                 (id-eval-in-terms-of-lit-eval
                                  id-eval-of-aignet-add-in))
          :use ((:instance id-eval-of-aignet-add-in)))))

(defthm lit-eval-of-aignet-add-reg
  (implies (equal (id-val (lit-id lit))
                  (nfix (num-nodes aignet)))
           (equal (lit-eval lit in-vals reg-vals
                            (mv-nth 1 (aignet-add-reg aignet)))
                  (b-xor (lit-neg lit)
                         (nth (num-regs aignet) reg-vals))))
  :hints(("Goal" :in-theory (e/d (lit-eval)
                                 (id-eval-in-terms-of-lit-eval
                                  id-eval-of-aignet-add-reg))
          :use ((:instance id-eval-of-aignet-add-reg)))))


;; (defthm position-equal-car
;;   (implies (consp x)
;;            (equal (position (car x) x) 0))
;;   :hints(("Goal" :in-theory (enable position))))

(defthm aig-env-lookup-of-aignet-eval-to-env-of-make-varmap
  (implies (and (aignet-well-formedp aignet0)
                (member v vars)
                (equal (len (alist-keys varmap0))
                       (num-ins aignet0))
                (no-duplicatesp-equal vars)
                (not (intersectp-equal vars (alist-keys varmap0))))
           (mv-let (varmap aignet)
             (make-varmap vars nil varmap0 aignet0)
             (equal (acl2::aig-env-lookup
                     v (aignet-eval-to-env
                        varmap
                        in-vals reg-vals aignet))
                    (equal (nth (+ (num-ins aignet0)
                                   (lst-position v vars))
                                in-vals)
                           1))))
  :hints (("goal" :induct (make-varmap vars nil varmap0 aignet0)
           :in-theory (e/d (make-varmap
                            aignet-eval-to-env
                            alist-keys)
                           (acl2::aig-env-lookup)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (make-varmap
                                  aignet-eval-to-env
                                  alist-keys))))))



(defthm nth-in-env-to-in-vals
  (implies (< (nfix n) (len vars))
           (equal (nth n (env-to-in-vals vars env))
                  (if (acl2::aig-env-lookup (nth n vars) env) 1 0)))
  :hints(("Goal" :in-theory (enable nth env-to-in-vals))))

(defthm lst-position-less-when-member
  (implies (member v vars)
           (< (lst-position v vars) (len vars))))

(defthm nth-lst-position
  (implies (member v vars)
           (equal (nth (lst-position v vars) vars) v))
  :hints(("Goal" :in-theory (enable nth))))

(defthm lst-position-type-when-member
  (implies (member v vars)
           (natp (lst-position v vars)))
  :rule-classes :type-prescription)

;; (defthm aig-env-lookup-of-aignet-eval-to-env-of-make-varmap-env-to-in-vals
;;   (implies (and (aignet-well-formedp aignet0)
;;                 (member v vars)
;;                 (equal (len (alist-keys varmap0))
;;                        (num-ins aignet0))
;;                 (no-duplicatesp-equal vars)
;;                 (not (intersectp-equal vars (alist-keys varmap0))))
;;            (mv-let (varmap aignet)
;;              (make-varmap vars nil varmap0 aignet0)
;;              (equal (acl2::aig-env-lookup
;;                      v (aignet-eval-to-env
;;                         varmap
;;                         (env-to-in-vals
;;                          (revappend (alist-keys varmap0) vars)
;;                          env)
;;                         nil
;;                         aignet))
;;                     (and (acl2::aig-env-lookup v env) t))))
;;   :hints (("goal" :do-not-induct t
;;            :in-theory (disable acl2::aig-env-lookup))))

(defthm aig-eval-of-aignet-eval-to-env-of-make-varmap
  (implies (and (aignet-well-formedp aignet0)
                (subsetp-equal (aig-vars aig) vars)
                (equal (len (alist-keys varmap0))
                       (num-ins aignet0))
                (no-duplicatesp-equal vars)
                (not (intersectp-equal vars (alist-keys varmap0))))
           (mv-let (varmap aignet)
             (make-varmap vars nil varmap0 aignet0)
             (equal (aig-eval aig
                              (aignet-eval-to-env
                               varmap
                               (env-to-in-vals
                                (revappend (alist-keys varmap0) vars)
                                env)
                               nil
                               aignet))
                    (aig-eval aig env))))
  :hints(("Goal" :in-theory (e/d (aig-eval)
                                 (lookup-in-aignet-eval-to-env
                                  acl2::aig-env-lookup
                                  acl2::revappend-removal))
          :induct (aig-eval aig env))))

(defthm aig-eval-of-aignet-eval-to-env-of-make-varmap-init
  (implies (and (aignet-well-formedp aignet0)
                (double-rewrite
                 (subsetp-equal (aig-vars aig) vars))
                (no-duplicatesp-equal vars)
                (equal (num-ins aignet0) 0))
           (mv-let (varmap aignet)
             (make-varmap vars nil nil aignet0)
             (equal (aig-eval aig
                              (aignet-eval-to-env
                               varmap
                               (env-to-in-vals vars env)
                               nil
                               aignet))
                    (aig-eval aig env))))
  :hints(("Goal" :in-theory (e/d (aig-eval)
                                 (lookup-in-aignet-eval-to-env
                                  acl2::aig-env-lookup
                                  acl2::revappend-removal
                                  aig-eval-of-aignet-eval-to-env-of-make-varmap))
          :use ((:instance aig-eval-of-aignet-eval-to-env-of-make-varmap
                 (varmap0 nil))))))



(defthm aig-satisfying-assign-induces-aig->cnf-satisfying-assign
  (b* (((mv cnf ?lit vars sat-lits aignet) (aig->cnf aig sat-lits aignet))
       (cnf-eval (satisfying-assign-for-env env vars sat-lits aignet cnf-eval)))
    (implies (aig-eval aig env)
             (equal (satlink::eval-formula cnf cnf-eval) 1)))
  :hints (("goal" :use ((:instance
                         aignet-satisfying-assign-induces-cnf-satisfying-assign
                         (aignet (mv-nth 4 (aig->cnf aig sat-lits aignet)))
                         (lit (mv-nth 1 (aig->cnf aig sat-lits aignet)))
                         (in-vals (env-to-in-vals
                                   (mv-nth 2 (aig->cnf aig sat-lits aignet))
                                   env))
                         (reg-vals nil)
                         (cnf-eval (resize-bits (sat-next-var
                                                 (mv-nth 3 (aig->cnf aig sat-lits aignet)))
                                                nil))))
           :in-theory (disable
                       aignet-satisfying-assign-induces-cnf-satisfying-assign))))

(defthm aignet-well-formedp-of-aig->cnf
  (aignet-well-formedp (mv-nth 4 (aig->cnf aig sat-lits aignet))))

(defthm sat-lits-wfp-of-aig->cnf
  (sat-lits-wfp (mv-nth 3 (aig->cnf aig sat-lits aignet))
                (mv-nth 4 (aig->cnf aig sat-lits aignet))))


(local (defthm len-equal-0
         (equal (equal (len x) 0)
                (atom x))))

(defun aignet-vals-make-env (vars innum aignet-vals aignet)
  (Declare (xargs :stobjs (aignet-vals aignet)
                  :guard (and (aignet-well-formedp aignet)
                              (bitarr-sizedp aignet-vals aignet)
                              (natp innum)
                              (<= (+ (len vars) innum) (num-ins aignet)))
                  :guard-hints (("goal" :use ((:instance
                                               id-in-bounds-when-memo-tablep
                                               (arr aignet-vals)
                                               (n (innum->id innum aignet))))
                                 :in-theory (disable id-in-bounds-when-memo-tablep)))))
  (if (atom vars)
      nil
    (cons (cons (car vars)
                (equal 1 (get-id->bit (innum->id innum aignet) aignet-vals)))
          (aignet-vals-make-env (cdr vars) (1+ (lnfix innum)) aignet-vals aignet))))


;; (defthm lookup-in-aignet-vals-make-env
;;   (equal (hons-assoc-equal k (aignet-vals-make-env vars innum aignet-vals
;;                                                    aignet))
;;          (if (member k vars)



(defthm memo-tablep-cnf-eval->aignet-vals
  (implies (memo-tablep aignet-vals aignet)
           (memo-tablep
            (cnf-eval->aignet-vals n cnf-eval aignet-vals sat-lits aignet)
            aignet))
  :hints(("Goal" :in-theory (enable cnf-eval->aignet-vals))))


(defun aig-cnf-eval->env (cnf-eval vars sat-lits aignet)
  (declare (xargs :stobjs (cnf-eval sat-lits aignet)
                  :guard (and (aignet-well-formedp aignet)
                              (sat-lits-wfp sat-lits aignet)
                              (<= (len vars) (num-ins aignet)))))
  (b* (((local-stobjs aignet-vals)
        (mv env aignet-vals))
       (aignet-vals (resize-bits (num-nodes aignet) aignet-vals))
       (aignet-vals (cnf-eval->aignet-vals 0 cnf-eval aignet-vals sat-lits
                                           aignet))
       (env (aignet-vals-make-env vars 0 aignet-vals aignet)))
    (mv env aignet-vals)))


(defthm lookup-in-aignet-vals-make-env
  (equal (acl2::aig-env-lookup v (aignet-vals-make-env vars innum aignet-vals
                                                       aignet))
         (or (not (member v vars))
             (equal 1 (get-id->bit (innum->id (+ (nfix innum)
                                                 (lst-position v vars))
                                              aignet)
                                   aignet-vals))))
  :hints(("Goal" :in-theory (enable acl2::aig-env-lookup))))

(defthm aignet-vals-make-env-of-extension
  (implies (and (aignet-extension-binding)
                (aignet-extension-p new-aignet orig-aignet)
                (<= (+ (nfix innum) (len vars)) (num-ins orig-aignet))
                (aignet-well-formedp orig-aignet)
                (aignet-well-formedp new-aignet))
           (equal (aignet-vals-make-env vars innum aignet-vals new-aignet)
                  (aignet-vals-make-env vars innum aignet-vals orig-aignet))))

(defthm aignet-vals-in-vals-iter-of-extension
  (implies (and (aignet-extension-binding)
                (aignet-extension-p new-aignet orig-aignet)
                (<= (nfix innum) (num-ins orig-aignet))
                (aignet-well-formedp orig-aignet)
                (aignet-well-formedp new-aignet))
           (equal (aignet-vals-in-vals-iter innum in-vals aignet-vals new-aignet)
                  (aignet-vals-in-vals-iter innum in-vals aignet-vals
                                            orig-aignet)))
  :hints(("Goal" :in-theory (enable aignet-vals-in-vals-iter))))

(defthm aignet-vals-reg-vals-iter-of-extension
  (implies (and (aignet-extension-binding)
                (aignet-extension-p new-aignet orig-aignet)
                (<= (nfix innum) (num-regs orig-aignet))
                (aignet-well-formedp orig-aignet)
                (aignet-well-formedp new-aignet))
           (equal (aignet-vals-reg-vals-iter innum reg-vals aignet-vals new-aignet)
                  (aignet-vals-reg-vals-iter innum reg-vals aignet-vals
                                            orig-aignet)))
  :hints(("Goal" :in-theory (enable aignet-vals-reg-vals-iter))))

(local (defthmd equal-1-rewrite-under-congruence
         (implies (and (equal y (double-rewrite (bfix x)))
                       (syntaxp ;(prog2$ (cw "x: ~x0~%y: ~x1~%" x y)
                        (and (not (equal x y))
                             (not (equal y `(acl2::bfix$inline ,x))))))
                  (equal (equal x 1)
                         (equal y 1)))))
(defthm aignet-eval-to-env-of-extension
  (implies (and (aignet-extension-binding)
                (aignet-extension-p new-aignet orig-aignet)
                (good-varmap-p varmap orig-aignet))
           (equal (aignet-eval-to-env varmap in-vals reg-vals new-aignet)
                  (aignet-eval-to-env varmap in-vals reg-vals orig-aignet)))
  :hints(("Goal" :in-theory (enable good-varmap-p))))

(encapsulate nil
  (local (in-theory (disable aignet-vals-make-env
                             no-duplicatesp-equal
                             subsetp-equal
                             make-varmap acl2::aig-env-lookup
                             aignet-eval-to-env
                             aignet-vals-in-vals-iter
                             aignet-vals-reg-vals-iter)))
  (defthm aig-eval-of-aignet-vals-make-env
    (implies (and (aignet-well-formedp aignet)
                  (equal (num-ins aignet) 0)
                  (no-duplicatesp-equal vars)
                  (double-rewrite (subsetp-equal (aig-vars aig) vars)))
             (mv-let (varmap new-aignet)
               (make-varmap vars nil nil aignet)
               (equal (aig-eval aig
                                (aignet-vals-make-env
                                 vars 0 aignet-vals new-aignet))
                      (aig-eval aig
                                (aignet-eval-to-env
                                 varmap
                                 (aignet-vals-in-vals nil aignet-vals new-aignet)
                                 (aignet-vals-reg-vals nil aignet-vals new-aignet)
                                 new-aignet)))))
    :hints(("Goal" :in-theory (e/d (aig-eval
                                    equal-1-rewrite-under-congruence))
            :induct t))))

(local (in-theory (enable (:induction aig-to-aignet))))


(defthm cnf-satisfying-assign-induces-aig-satisfying-assign
    (b* (((mv cnf ?lit vars sat-lits aignet)
          (aig->cnf aig sat-lits aignet))
         (env (aig-cnf-eval->env cnf-eval vars sat-lits aignet)))
      (implies (equal (satlink::eval-formula cnf cnf-eval) 1)
               (aig-eval aig env)))
    :hints(("Goal" :in-theory (e/d (nth-aignet-of-aig-to-aignet)
                                   (cnf-satisfying-assign-induces-aignet-satisfying-assign
                                    b-and b-ior b-xor b-not))
            :use ((:instance
                   cnf-satisfying-assign-induces-aignet-satisfying-assign
                   (lit (mv-nth 1 (aig->cnf aig sat-lits aignet)))
                   (aignet (mv-nth 4 (aig->cnf aig sat-lits aignet)))))
            :do-not-induct t)))

(defthm len-vars-of-aig->cnf
  (equal (len (mv-nth 2 (aig->cnf aig sat-lits aignet)))
         (nth *num-ins* (mv-nth 4 (aig->cnf aig sat-lits aignet))))
  :hints(("Goal" :in-theory (enable* aig->cnf
                                     aignet-frame-thms))))

(in-theory (disable aig->cnf
                    aig-cnf-eval->env
                    satisfying-assign-for-env))
