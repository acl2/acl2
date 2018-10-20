;; extra.lisp
;;
;; A book for doing some quick checks using the exs$ exsim setup..

(in-package "EXSIM")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; BOZOs
;; 1. ???
;;
;; TODOs
;; 1. ??? 
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "exsim")
(include-book "std/strings/isubstrp" :dir :system)

(define find-str-pat ((x stringp) (pat stringp) (no-pat stringp))
  (and (str::isubstrp pat x) (not (str::isubstrp no-pat x))))

(define find-sub-pat (x (pat stringp) (no-pat stringp))
  (cond ((stringp x) (find-str-pat x pat no-pat))
        ((symbolp x) (find-str-pat (symbol-name x) pat no-pat))))

(define find-name-pat (name (pat stringp) (no-pat stringp))
  (if (atom name) (find-sub-pat name pat no-pat)
    (or (find-sub-pat (car name) pat no-pat)
        (find-name-pat (cdr name) pat no-pat))))

(define collect-state-ndxs ((vars var->ndx-map-p) &key ((rslt var->ndx-map-p) 'nil))
  :returns (rslt var->ndx-map-p)
  (cond ((endp vars) (var->ndx-map-fix rslt))
        ((find-name-pat (sv::svar->name (caar vars)) "State" "StateNxt")
         (collect-state-ndxs (rest vars) :rslt (cons (first vars) rslt)))
        (t (collect-state-ndxs (rest vars) :rslt rslt))))

(define each-neg-pairs ((lits lit-listp) (lit litp) (rslt lit-list-listp))
  :returns (rslt lit-list-listp)
  (if (endp lits) (lit-list-list-fix rslt)
    (each-neg-pairs (rest lits) lit
                    (cons (list (lit-negate (first lits))
                                (lit-negate lit))
                          rslt))))

(define all-neg-pairs ((lits lit-listp) &key ((rslt lit-list-listp) 'nil))
  :returns (rslt lit-list-listp)
  (if (endp lits) (lit-list-list-fix rslt)
    (all-neg-pairs (rest lits)
                   :rslt (each-neg-pairs (rest lits) (first lits) rslt))))

(define assume-onehot ((lits lit-listp) total)
  :returns (rslt lit-list-listp)
  (if (endp lits) ()
    (revapp! (and total (list (lit-list-fix lits))) 
             (all-neg-pairs lits))))

(define mk-not-onehot ((all lit-listp) (lit litp)
                       &key ((rslt lit-listp) 'nil))
  :returns (rslt lit-listp)
  (if (endp all) (lit-list-fix rslt)
    (mk-not-onehot (rest all) lit
                   :rslt
                   (cons (if (eql (first all) lit)
                             (lit-negate lit)
                           (first all))
                         rslt))))

(define check-not-onehot ((lits lit-listp) (all lit-listp) 
                          &key ((rslt lit-list-listp) 'nil))
  :returns (rslt lit-list-listp)
  (if (endp lits) (lit-list-list-fix rslt)
    (check-not-onehot (rest lits) all
                      :rslt (cons (mk-not-onehot all (first lits)) rslt))))

(define pull-ndx-lits ((ndxs ndx-list-p) (map ndx-map-p)
                       &key ((rslt lit-listp) 'nil))
  :returns (rslt lit-listp)
  (if (endp ndxs) (lit-list-fix rslt)
    (pull-ndx-lits (rest ndxs) map
                   :rslt ;; BOZO -- slightly bogus here for in-lits, we should probably
                         ;; throw an error if we don't find a sat var? all state
                         ;; bits should be depended upon.. because otherwise our onehot
                         ;; assumption is wrong.. too strong.
                   (b* ((look (hons-get (first ndxs) map)))
                     (if (not look) rslt (cons (cdr look) rslt))))))

(define assume-onehots ((all var->ndx-map-p) (map ndx-map-p)
                        &key ((rslt lit-list-listp) 'nil))
  :returns (rslt lit-list-listp)
  (if (endp all) (lit-list-list-fix rslt)
    (b* ((lits (pull-ndx-lits (cdar all) map))
         (total (eql (len lits) (len (cdar all)))))
      (assume-onehots (rest all) map
                      :rslt (revapp! (assume-onehot lits total) rslt)))))

(define exs-fsm-just-status ((var sv::svar-p) status exs$)
  (update-exs$-fchk-rslt 
   (hons-acons var (make-fchk-rslt :status (list status)
                                   :ins nil
                                   :outs nil)
               (exs$-fchk-rslt exs$))
   exs$))

(define exs-fsm-sat-result ((var sv::svar-p) (ins exs-vmap-p) (outs exs-vmap-p) exs$)
  (update-exs$-fchk-rslt 
   (hons-acons var (make-fchk-rslt :status (list :sat)
                                   :ins ins
                                   :outs outs)
               (exs$-fchk-rslt exs$))
   exs$))

(define exs-mk-rslt-vmap ((map ndx-map-p) 
                          &key 
                          ((rslt exs-vmap-p) 'nil) 
                          (exs$ 'exs$) 
                          (env$ 'env$))
  :returns (rslt exs-vmap-p)
  (if (endp map) (exs-vmap-fix (fast-alist-clean rslt))
    (b* ((ndx  (caar map))
         (val  (cdar map))
         (val  (if (bitp val) val (eval-lit val env$)))
         (rslt (exs-add-ndx-lit->vmap ndx 0 val rslt)))
      (exs-mk-rslt-vmap (rest map) :rslt rslt))))

(define exs-check-fsm ((var sv::svar-p) (ndxs ndx-list-p) (all var->ndx-map-p)
                       &key (exs$ 'exs$))
  (b* (((local-stobjs in-lvals env$) (mv in-lvals env$ exs$))
       (- (cw "******** check-fsm for: ~x0~%" var))
       (num-ndxs (exs-num-ndxs))
       (in-lvals (exs-init-cnl-lvals num-ndxs :lvals in-lvals)))
    (stobj-let ((ipasir (exs$-solver exs$)) 
                (aignet (exs$-aignet exs$)))
               (cnf in-map out-map next-base ipasir)
               (b* (((mv cnf in-map out-map - - next-base - ipasir)
                     (backward-expand ndxs in-lvals ()
                                      :base 2
                                      :use-ipasir nil
                                      :ipasir ipasir)))
                 (mv cnf in-map out-map next-base ipasir))
               (b* ((in-map (make-fast-alist in-map))
                    (out-map (make-fast-alist out-map))
                    (out-lits (pull-ndx-lits ndxs out-map))
                    (cnf (revapp! (assume-onehots all in-map) cnf))
                    (cnf (revapp! (check-not-onehot out-lits out-lits) cnf))
                    ((mv status env$) (satlink::sat cnf env$))
                    ((when (not (eq status :sat)))
                     (b* ((exs$ (exs-fsm-just-status var status exs$)))
                       (mv in-lvals env$ exs$)))
                    (ins  (exs-mk-rslt-vmap in-map))
                    (outs (exs-mk-rslt-vmap out-map))
                    (exs$ (exs-fsm-sat-result var ins outs exs$)))
                 (mv in-lvals env$ exs$)))))
                     
(define exs-check-fsms ((vars var->ndx-map-p) (all var->ndx-map-p) &key (exs$ 'exs$))
  (if (endp vars) exs$
    (b* ((exs$ (exs-check-fsm (caar vars) (cdar vars) all)))
      (exs-check-fsms (rest vars) all))))

(define exs-count-fchk ((fchk fchk-rslt-map-p) (mtch symbolp) 
                        &key ((rslt natp) '0))
  :returns (rslt natp)
  (if (endp fchk) (lnfix rslt)
    (exs-count-fchk (rest fchk) mtch
                    :rslt (if (eq (first (fchk-rslt->status (cdar fchk))) mtch)
                              (1+ rslt)
                            rslt))))

(define prune-fchk ((fchk fchk-rslt-map-p) &key (rslt 'nil))
  (if (endp fchk) rslt
    (prune-fchk (rest fchk) 
                :rslt (cons (cons (caar fchk) (fchk-rslt->status (cdar fchk))) rslt))))

(define inst= (x y)
  (cond ((natp x) (natp y))
        ((atom x) (equal x y))
        ((atom y) nil)
        (t (and (inst= (car x) (car y))
                (inst= (cdr x) (cdr y))))))


(define mtch-inst ((var sv::svar-p) (fchk fchk-rslt-map-p))
  (and (consp fchk)
       (or (inst= var (caar fchk))
           (mtch-inst var (rest fchk)))))


(define pull-insts ((fchk fchk-rslt-map-p) &key ((rslt fchk-rslt-map-p) 'nil))
  :returns (rslt fchk-rslt-map-p)
  (if (endp fchk) (fchk-rslt-map-fix rslt)
    (pull-insts (rest fchk)
                :rslt (if (mtch-inst (caar fchk) rslt) rslt
                        (cons (car fchk) rslt)))))


(define flatten-insts ((fchk fchk-rslt-map-p) &key (rslt 'nil))
  (if (endp fchk) rslt
    (flatten-insts (rest fchk)
                   :rslt
                   (acl2::rev$! (list "===============" (caar fchk) "===============")
                                (acl2::rev$! (cons "++++++++++++++++++++++" (fchk-rslt->ins (cdar fchk)))
                                             (acl2::rev$! (cons "++++++++++++++++++++++" (fchk-rslt->outs (cdar fchk)))
                                                          rslt))))))

(define exs-report-fsm-checks (&key (exs$ 'exs$) (state 'state))
  (b* ((rslt (exs$-fchk-rslt exs$))
       (state (exs-write-objs-file (cons (list (list "sat-count:"    (exs-count-fchk rslt :sat))
                                               (list "unsat-count:"  (exs-count-fchk rslt :unsat))
                                               (list "failed-count:" (exs-count-fchk rslt :failed)))
                                         (prune-fchk rslt))
                                   "onehot_rpt.lsp"))
       (state (exs-write-objs-file (flatten-insts (pull-insts rslt)) "onehot_fails.lsp")))
    state))

(define exs-fsm-checks (&key (exs$ 'exs$) (state 'state))
  (b* ((-        (acl2::tshell-ensure))
       (st-vars  (collect-state-ndxs (exs$-var->ndx exs$)))
       (exs$     (exs-check-fsms st-vars st-vars))
       (state    (exs-report-fsm-checks)))
    (mv exs$ state)))


;;;;;;;;;;;;;;;;;;;
;; functions for extracting AIGs..
;;;;;;;;;;;;;;;;;;;

(define true-list-fix ((x true-listp))
  :inline t
  :returns (rslt true-listp)
  (mbe :logic (if (true-listp x) x nil)
       :exec x))

(define atom-list-fix ((x atom-listp))
  :inline t
  :returns (rslt atom-listp)
  (mbe :logic (if (atom-listp x) x nil)
       :exec x))

(define get-ndxs-aigs ((ndxs ndx-list-p)
                       (out-aigs ndx->aig-p)
                       (next-aigs ndx->aig-p)
                       &key
                       ((rslt true-listp) 'nil))
  :returns (rslt true-listp)
  (if (endp ndxs) (rev! rslt)
    (b* ((ndx     (first ndxs))
         (look    (hons-get ndx out-aigs))
         (look2   (and (not look)
                       (hons-get ndx next-aigs)))
         ((when (and (not look)
                     (or (not look2)
                         ;; only use next-aigs to get
                         ;; constant aigs..
                         (not (booleanp (cdr look))))))
          (raise "internal error: did not find aig! ~x0~%"
                 (list ndx look2))))
      (get-ndxs-aigs (rest ndxs) out-aigs next-aigs
                     :rslt (cons (or (cdr look)
                                     (cdr look2))
                                 rslt)))))

(define my-aig-vars (aig)
  :enabled t
  :verify-guards nil
  :returns (rslt atom-listp)
  (cond ((or (eq aig t) (eq aig nil)) ())
        ((atom aig) (mbe :logic (set::insert aig nil)
                         :exec (list aig)))
        (t (set::union (my-aig-vars (car aig))
                       (my-aig-vars (cdr aig))))))

(defthm setp-my-aig-vars
  (set::setp (my-aig-vars x)))

(verify-guards my-aig-vars
  :hints(("Goal" :in-theory (enable* (:ruleset set::primitive-rules)))))

(memoize 'my-aig-vars :condition '(and (consp aig) (cdr aig)))

(define collect-aig-vars ((aigs true-listp)
                          &key
                          ((rslt atom-listp) 'nil))
  :returns (new-rslt atom-listp :hyp (atom-listp rslt))
  (if (endp aigs) (atom-list-fix rslt)
    (collect-aig-vars (rest aigs)
                      :rslt (acl2::hons-alphorder-merge (my-aig-vars (first aigs)) rslt))))

(define compose-aigs-list ((aigs true-listp) tbl
                           &key ((rslt true-listp) 'nil))
  :returns (rslt true-listp)
  (if (endp aigs) (rev! rslt)
    (compose-aigs-list (rest aigs) tbl
                       :rslt (cons (acl2::aig-compose (first aigs) tbl) rslt))))

(define inv-look-ndx->aig ((var natp) (in-aigs ndx->aig-p))
  :returns (rslt natp :hyp :guard)
  (cond ((endp in-aigs)
         (prog2$ (raise "internal error: did not find aig var.:~x0~%" var) 0))
        ((eql var (cdar in-aigs))
         (caar in-aigs))
        (t (inv-look-ndx->aig var (cdr in-aigs)))))

(define aig-vars->ndxs ((vars true-listp) (in-aigs ndx->aig-p)
                        (lkup styp-lkup-p)
                        &key
                        ((rslt ndx-list-p)  'nil)
                        ((ovs  true-listp)  'nil)
                        ((frees true-listp) 'nil)
                        ((free-aigs ndx->aig-p) 'nil))
  :returns (mv (rslt ndx-list-p)
               (ovs true-listp)
               (frees true-listp)
               (free-aigs ndx->aig-p))
  (if (endp vars) (mv (ndx-list-fix rslt)
                      (true-list-fix ovs)
                      (true-list-fix frees)
                      (ndx->aig-fix free-aigs))
    (b* ((var (first vars))
         ((when (not (natp var)))
          (mv (raise "internal error: aig var. not natural:~x0~%"
                     var) () () ()))
         (ndx (inv-look-ndx->aig var in-aigs))
         (free (eq (cdr (hons-get ndx lkup)) :free)))
      (aig-vars->ndxs (rest vars) in-aigs lkup
                      :rslt  (if free rslt (cons ndx rslt))
                      :ovs   (if free ovs (cons var ovs))
                      :frees (if free (cons var frees) frees)
                      :free-aigs (if free (acons! ndx var free-aigs) free-aigs)))))

(defthm cyc->ndx->aig-alistp
  (implies (cyc->ndx->aig-p x) (alistp x))
  :hints (("Goal" :in-theory (enable cyc->ndx->aig-p))))

(defthm cyc->ndx->aig-assoc-equal
  (implies (cyc->ndx->aig-p x)
           (ndx->aig-p (cdr (assoc-equal a x))))
  :hints (("Goal" :in-theory (enable cyc->ndx->aig-p))))

(defthm assoc-equal-consp-cdr-alistp
  (implies (and (alistp x) (assoc-equal a x))
           (consp (assoc-equal a x))))

(define exs-get-aigs-ndxs ((ndxs ndx-list-p) 
                           (cyc natp) 
                           (next-aigs ndx->aig-p)
                           &key (exs$ 'exs$))
  ;; use the aigs computed during exsim and stored in the exs$ to compute the
  ;; output svar (with delay defining cycle) as a function.. if it passes (i.e.
  ;; if the output is a function of the inputs vars), then we return an aiglist
  ;; for the bits in out and an alist associating vars in ins to aig-vars in
  ;; the aiglist returned.. this can then be used to build a mapping from
  ;; variable values for the vars in ins to an env for evaluating the
  ;; aiglists. 
  :returns (mv (aigs true-listp) (rslt cyc->ndx->aig-p))
  :measure (nfix cyc)
  :verify-guards nil
  (if (or (zp cyc) (endp ndxs)) (mv () ())
    (b* ((in-aigs   (cdr (hons-get cyc (exs$-in-aig-ctbl exs$))))
         (out-aigs  (cdr (hons-get cyc (exs$-out-aig-ctbl exs$))))
         (ndxs-aigs (get-ndxs-aigs ndxs out-aigs next-aigs))
         (vars      (collect-aig-vars ndxs-aigs))
         ((mv ndxs vars frees free-aigs)
          (aig-vars->ndxs vars in-aigs (exs$-styp-lkup exs$)))
         ((mv prev rslt) 
          (exs-get-aigs-ndxs ndxs (1- cyc) nil))
         (tbl  (make-fast-alist (append (pairlis$ vars prev)
                                        (pairlis$ frees frees))))
         (aigs (compose-aigs-list ndxs-aigs tbl))
         (rslt (acons! cyc free-aigs rslt))
         (-    (fast-alist-clean tbl)))
      (mv aigs rslt))))

(verify-guards exs-get-aigs-ndxs-fn)

(fty::defalist off->aig
               :key-type natp
               :true-listp t)

(fty::defalist var->off->aig
               :key-type sv::svar-p
               :val-type off->aig-p
               :true-listp t)

(define upd-var-frees ((rslt var->off->aig-p) (var sv::svar-p) (off natp) aig)
  :returns (rslt var->off->aig-p :hyp :guard)
  (cond ((endp rslt)
         (acons! var (acons! off aig nil) nil))
        ((hons-equal (caar rslt) var)
         (acons! var (acons! off aig (cdar rslt)) (cdr rslt)))
        (t (cons (car rslt) (upd-var-frees (cdr rslt) var off aig)))))
         
(define map-cyc-frees ((nmap ndx->aig-p) (cyc natp)
                       &key
                       ((rslt var->off->aig-p) 'nil)
                       (exs$ 'exs$))
  :returns (rslt var->off->aig-p)
  (if (endp nmap) (var->off->aig-fix rslt)
    (b* ((ndx (caar nmap))
         (aig (cdar nmap))
         (look (hons-get ndx (exs$-ndx->var exs$)))
         ((when (not look))
          (raise "intenral error: ndx not found:~x0~%" ndx))
         (var (ndx->var-elem->var (cdr look)))
         (off (ndx->var-elem->off (cdr look))))
      (map-cyc-frees (rest nmap) cyc
                     :rslt (upd-var-frees rslt (exsim-mk-svar var cyc) off aig)))))

(define map-ins-frees ((ins cyc->ndx->aig-p)
                       &key
                       ((rslt var->off->aig-p) 'nil)
                       (exs$ 'exs$))
  :returns (rslt var->off->aig-p)
  (if (endp ins) (var->off->aig-fix rslt)
    (map-ins-frees (rest ins)
                   :rslt (map-cyc-frees (cdar ins) (caar ins) :rslt rslt))))

(define insert-ins ((rslt off->aig-p) (off natp) aig)
  :returns (rslt off->aig-p :hyp :guard)
  (cond ((endp rslt) (acons! off aig ()))
        ((< off (caar rslt)) (acons! off aig rslt))
        ((eql off (caar rslt)) (raise "bad insert!:~x0~%" off))
        (t (cons (first rslt) (insert-ins (rest rslt) off aig)))))

(define sort-ins ((ins off->aig-p) &key ((rslt off->aig-p) 'nil))
  :returns (rslt off->aig-p)
  (if (endp ins) (off->aig-fix rslt)
    (sort-ins (rest ins) :rslt (insert-ins rslt (caar ins) (cdar ins)))))

(define pull-out-ins ((in-vars sv::svarlist-p)
                      (frees var->off->aig-p))
  :returns (rslt var->aigs-p)
  (if (endp in-vars) ()
    (b* ((var (first in-vars))
         (look (hons-get var frees))
         ((when (not look))
          (raise "did not find var in free support:~x0~%" var)))
      (acons! (sv::svar-fix var)
              (strip-cdrs (sort-ins (cdr look)))
              (pull-out-ins (rest in-vars) frees)))))

(define hons-in! (e (x true-listp))
  (and (not (endp x))
       (or (hons-equal e (first x))
           (hons-in! e (rest x)))))

(define off-aig-isect-p ((x off->aig-p) (y true-listp))
  (and (not (endp x))
       (or (hons-in! (cdar x) y)
           (off-aig-isect-p (rest x) y))))

(define chk-out-ins ((frees var->off->aig-p)
                     (in-vars sv::svarlist-p))
  (or (endp frees)
      (and (or (hons-in! (caar frees) in-vars)
               (raise "found var outside spec:~x0~%" (caar frees)))
           (chk-out-ins (rest frees) in-vars))))
  
(define pull-out-ins-chk ((frees var->off->aig-p)
                          (in-vars sv::svarlist-p))
  :returns (rslt var->aigs-p)
  (and (chk-out-ins frees in-vars)
       (pull-out-ins in-vars frees)))

(define prune-frees ((frees var->off->aig-p)
                     (aig-supp true-listp)
                     &key ((rslt var->off->aig-p) 'nil))
  :returns (rslt var->off->aig-p)
  (if (endp frees) (var->off->aig-fix rslt)
    (prune-frees (rest frees) aig-supp
                 :rslt (if (off-aig-isect-p (cdar frees) aig-supp)
                           (cons (first frees) rslt)
                         rslt))))

(define ndxs-val-mk-map ((ndxs ndx-list-p) (val natp)
                         &key ((rslt ndx-map-p) 'nil))
  :returns (rslt ndx-map-p)
  (if (endp ndxs) (ndx-map-fix rslt)
    (ndxs-val-mk-map (rest ndxs) (logcdr val)
                     :rslt (acons! (first ndxs) (logcar val) rslt))))

(define exs-get-aigs ((out-var sv::svar-p) (in-vars sv::svarlist-p)
                      &key (exs$ 'exs$))
  :returns (mv (out-aigs true-listp) (in-aigs var->aigs-p) exs$)
  (b* ((cyc  (sv::svar->delay out-var))
       (nvar (exsim-mk-svar out-var 0))
       (look (hons-get nvar (exs$-var->ndx exs$)))
       ((when (not look))
        (mv (raise "internal error: did not find var:~x0~%" nvar) () exs$))
       (next-aigs (cdr (hons-get (1+ cyc) (exs$-in-aig-ctbl exs$))))
       ((mv out-aigs ins)
        (exs-get-aigs-ndxs (cdr look) cyc next-aigs))
       (aig-supp (collect-aig-vars out-aigs))
       (frees (make-fast-alist (prune-frees (map-ins-frees ins) aig-supp)))
       (in-aigs (pull-out-ins-chk frees in-vars))
       (- (fast-alist-free frees))
       (exs$ (update-exs$-get-aigs-ins  in-vars exs$))
       (exs$ (update-exs$-get-aigs-outs (list out-var) exs$)))
    (mv out-aigs in-aigs exs$)))

;;(i-am-here)

;(define ndxs-in-bounds ((x ndx->aig-p) lvals)
;  (or (endp x)
;      (and (<= (caar x) (lits-length lvals))
;           (ndxs-in-bounds (cdr x) lvals))))


(define map-raw-aig-in (styp aig-base (val natp) aig ndx)
  (cond ((eq styp :free) aig-base)
        ((or (eq styp :wave) (eq styp :rand))
         (cond ((eql val 0) nil)
               ((eql val 1) t)
               (t (raise "internal error: no val:~x0~%" 
                         (list ndx val)))))
        (t aig)))

(define install-raw-ins ((curr ndx->aig-p) (aig-base natp) (lkup styp-lkup-p)
                         &key 
                         ((rslt ndx->aig-p) 'nil) (lvals 'lvals) 
                         (aigarr 'aigarr) (aignet 'aignet))
  :guard (and (<= (num-nodes aignet) (aigs-length aigarr))
              (<= (num-ins aignet) (lits-length lvals)))
  :returns (mv (next-base natp) (rslt ndx->aig-p) aigarr)
  (if (endp curr) (mv (lnfix aig-base) (ndx->aig-fix rslt) aigarr)
    (b* ((ndx  (caar curr))
         (aig  (cdar curr))
         (look (hons-get ndx lkup))
         ((when (not (< ndx (num-ins aignet))))
          (prog2$ (raise "internal error: ndx o-o-b:~x0~%" 
                         (list ndx (num-ins aignet)))
                  (mv 0 () aigarr)))
         (val    (get-lit ndx lvals))
         (styp   (cdr look))
         (in-aig (map-raw-aig-in styp aig-base val aig ndx))
         (id     (ndx->in-id ndx aignet))
         (aigarr (set-aig id in-aig aigarr))
         (next-base (if (eql in-aig aig-base) (1+ aig-base) aig-base)))
      (install-raw-ins (cdr curr) next-base lkup
                       :rslt (if (eql in-aig aig-base)
                                 (acons! ndx aig-base rslt)
                               rslt)))))

(define extract-raw-outs ((curr ndx->aig-p)
                          &key 
                          ((rslt ndx->aig-p) 'nil) (lvals 'lvals) 
                          (aigarr 'aigarr) (aignet 'aignet))
  :guard (and (<= (num-nodes aignet) (aigs-length aigarr))
              (<= (num-outs aignet) (lits-length lvals)))
  :returns (next ndx->aig-p)
  (if (endp curr) (ndx->aig-fix rslt)
    (b* ((ndx (caar curr))
         ((when (not (< ndx (num-outs aignet))))
          (raise "internal error: ndx o-o-b:~x0~%" 
                 (list ndx (num-outs aignet))))
         (lit (outnum->fanin ndx aignet))
         (aig (get-aig (lit->var lit) aigarr))
         (aig (if (eql (lit->neg lit) 1) (aig-not aig) aig)))
      (extract-raw-outs (cdr curr) :rslt (acons! ndx aig rslt)))))

(defthm install-raw-ins-len-aigarr
  (implies (<= (num-nodes aignet) (aigs-length aigarr))
           (equal (len (mv-nth 2 (install-raw-ins curr aig-base lkup :rslt rslt)))
                  (len aigarr)))
  :hints (("Goal" :in-theory (enable install-raw-ins))))

(define exs-raw-aigs-step ((curr ndx->aig-p) (aig-base natp) (lkup styp-lkup-p)
                           &key (lvals 'lvals) (aignet 'aignet))
  :returns (mv (next ndx->aig-p) (next-base natp) (ins ndx->aig-p)) 
  (b* (((local-stobjs aigarr)     (mv next next-base ins aigarr))
       ((when (not (and (<= (num-outs aignet) (lits-length lvals))
                        (<= (num-ins aignet) (lits-length lvals)))))
        (mv (raise "internal error: bad array state:~x0~%"
                   (list (num-outs aignet) (num-ins aignet) (lits-length lvals)))
            0 () aigarr))
       (aigarr (resize-aigs       (num-nodes aignet) aigarr))
       ((mv next-base ins aigarr) (install-raw-ins curr aig-base lkup))
       (aigarr                    (aignet->aig-loop aigarr aignet))
       (next                      (extract-raw-outs curr)))
    (mv next next-base ins aigarr)))

(define exs-raw-aigs-loop ((curr ndx->aig-p) (tgt natp)
                           &key 
                           ((cyc natp) '0) 
                           ((ins cyc->ndx->aig-p) 'nil)
                           ((outs cyc->ndx->aig-p) 'nil)
                           ((aig-base natp) '4) (exs$ 'exs$))
  :guard (and (<= cyc tgt) (< tgt (exs$-cnl-map-length exs$)))
  :measure (nfix (- tgt cyc))
  :returns (mv (outs cyc->ndx->aig-p) (ins cyc->ndx->aig-p))
  (if (zp (- tgt cyc)) 
      (mv (cyc->ndx->aig-fix outs) (cyc->ndx->aig-fix ins))
    (b* ((lkup (exs$-styp-lkup exs$)))
      (stobj-let ((aignet (exs$-aignet exs$))
                  (lvals  (exs$-cnl-mapi cyc exs$)))
                 (next next-base curr-ins)
                 (exs-raw-aigs-step curr aig-base lkup)
                 (exs-raw-aigs-loop next tgt :aig-base next-base :cyc (1+ cyc)
                                    :outs (acons! (1+ cyc) (make-fast-alist next) outs)
                                    :ins  (acons! cyc curr-ins ins))))))

(define pull-raw-aigs (&key ((ndx natp) '0) (lvals 'lvals)
                            ((rslt ndx->aig-p) 'nil))     
  :guard (<= ndx (lits-length lvals))
  :measure (nfix (- (lits-length lvals) ndx))
  :returns (rslt ndx->aig-p)
  (if (zp (- (lits-length lvals) ndx)) (ndx->aig-fix rslt)
    (b* ((val (get-lit ndx lvals))
         (aig (cond ((eql val 0) nil)
                    ((eql val 1) t)
                    (t (raise "internal error: no initial value?:~x0~%" 
                              (list ndx val))))))
      (pull-raw-aigs :ndx (1+ ndx) :rslt (acons! ndx aig rslt)))))

(define map-ndx-aigs ((ndxs ndx-list-p) (outs ndx->aig-p))
  :returns (rslt true-listp)
  (if (endp ndxs) ()
    (b* ((look (hons-get (first ndxs) outs))
         ((when (not look))
          (raise "internal error: did not find ndx:~x0~%" (first ndxs))))
      (cons (cdr look) (map-ndx-aigs (rest ndxs) outs)))))

(define map-vars-aigs ((vars sv::svarlist-p) (outs cyc->ndx->aig-p) 
                       &key ((rslt var->aigs-p) 'nil) (exs$ 'exs$))
  :returns (rslt var->aigs-p)
  (if (endp vars) (var->aigs-fix rslt)
    (b* ((var  (first vars))
         (cyc  (sv::svar->delay var))
         (nvar (exsim-mk-svar var 0))
         (look (hons-get nvar (exs$-var->ndx exs$)))
         ((when (not look)) 
          (raise "internal error: did not find var:~x0~%" nvar))
         (ndxs (cdr look))
         (look (hons-get cyc outs))
         ((when (not look))
          (raise "internal error: did not find cycle:~x0~%" cyc))
         (ndx-aigs (cdr look))
         (aigs (map-ndx-aigs ndxs ndx-aigs)))
      (map-vars-aigs (rest vars) outs :rslt (acons! var aigs rslt)))))

(define collect-out-vars ((outs var->aigs-p) &key ((rslt atom-listp) 'nil))
  :returns (new-rslt atom-listp :hyp (atom-listp rslt))
  (if (endp outs) rslt
    (collect-out-vars (rest outs)
                      :rslt (collect-aig-vars (cdar outs) :rslt rslt))))

(define get-svars-tgt ((vars sv::svarlist-p) &key ((tgt natp) '0))
  :returns (rslt natp)
  (if (endp vars) (lnfix tgt)
    (b* ((cyc (sv::svar->delay (first vars))))
      (get-svars-tgt (rest vars) :tgt (if (> cyc tgt) cyc tgt)))))

(define free-up-sub-alists ((outs cyc->ndx->aig-p))
  (if (endp outs) nil
    (b* ((- (fast-alist-free (cdar outs))))
      (free-up-sub-alists (cdr outs)))))

(define exs-raw-aigs ((out-vars sv::svarlist-p) (in-vars sv::svarlist-p)
                      &key (exs$ 'exs$))
  :returns (mv (out-aigs var->aigs-p) (in-aigs var->aigs-p) exs$)
  (b* (;; Setup the call to raw-aigs-loop which does most of the work: 
       (tgt     (1+ (get-svars-tgt out-vars)))
       ((when (not (and (<= 1 tgt) (< tgt (exs$-cnl-map-length exs$)))))
        (prog2$ (raise "internal error: bad tgt provided!")
                (mv () () exs$)))
       (init    (stobj-let ((lvals (exs$-cnl-mapi 0 exs$)))
                           (aigs) (pull-raw-aigs) aigs))
       ;; Call raw-aigs-loop which will iterate to construct the aigs:
       ((mv outs ins) (exs-raw-aigs-loop init tgt))
       ;; Pull out the aigs for outs and ins and build the final return:
       (outs     (make-fast-alist outs))
       (out-aigs (map-vars-aigs out-vars outs))
       (aig-supp (collect-out-vars out-aigs))
       (frees    (make-fast-alist (prune-frees (map-ins-frees ins) aig-supp)))
       (in-aigs  (pull-out-ins-chk frees in-vars))
       (-        (free-up-sub-alists outs))
       (-        (fast-alist-free outs)) 
       (-        (fast-alist-free frees))
       (exs$     (update-exs$-get-aigs-ins  in-vars exs$))
       (exs$     (update-exs$-get-aigs-outs out-vars exs$)))
    (mv out-aigs in-aigs exs$)))

(fty::defalist var->val
               :key-type sv::svar-p
               :val-type natp
               :true-listp t)

(define exs-load-reduce-vals ((vals var->val-p) &key (exs$ 'exs$))
  :guard (exs-solver-rdy exs$)
  :returns (exs$ (exs-solver-rdy exs$) :hyp (exs-solver-rdy exs$))
  (if (endp vals) exs$
    (b* ((var (caar vals))
         (cyc (sv::svar->delay var))
         ((when (not (and (<= cyc (exs$-hi exs$))
                          (< (exs$-hi exs$) (exs$-cnl-map-length exs$)))))
          (prog2$ (raise "internal error: bad cyc or insufficient cnl-map size!")
                  exs$))
         (nvar (exsim-mk-svar var 0))
         (look (hons-get nvar (exs$-var->ndx exs$)))
         ((when (not look))
          (prog2$ (raise "did not find ndxs for var:~x0~%" nvar) exs$))
         (ndx-map (ndxs-val-mk-map (cdr look) (cdar vals)))
         ((mv - exs$) (exs-forward-reduce-loop ndx-map cyc 
                                               :override-merge t
                                               :force-forward t)))
      (exs-load-reduce-vals (rest vals)))))

(define exs-witness-vcd ((vals var->val-p) &key (instance-id 'nil) (exs$ 'exs$) (state 'state))
  ;; Some explanation for this function: we assume that the GL processing was
  ;; performed with exs-get-aigs with a single signal at a single time being
  ;; the source of all relevant free variables in the design. The input and
  ;; output svar (signal name and clock cycle) are stored into the exs$
  ;; structure when the AIGs were created using exs-get-aigs above.. We then
  ;; take the captured ndx-ctbl from when the exs-get-aigs was called and
  ;; map the var. to have the value passed in and recompute all signals and
  ;; then generate VCD output.
  :guard (exs-solver-rdy exs$)
  :returns (mv (exs$ (exs-solver-rdy exs$) :hyp (exs-solver-rdy exs$)) state)
  (b* (((when (not vals)) ;; nothing to generate in this case..
        (mv exs$ state))
       (exs$ (exs-load-reduce-vals vals))
       (id (acl2::strap "GL_WITNESS_" (or instance-id "0")))
       (ctbl (exs-collect-ndx-ctbl-bits))
       (exs$ (update-exs$-out-ctbls (acons! id (list ctbl) nil) exs$))
       ((mv exs$ state) (exsim-report-results)))
    (mv exs$ state)))

