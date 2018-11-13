;; extypes.lisp
;;
;; Book defining FTY types and some related constants for the
;; types used in the exbase, exloop, svcnf, and exsim books.

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

(include-book "support")
(include-book "nxtypes")
(include-book "vcdtypes")
(include-book "centaur/satlink/litp" :dir :system)

;; just pushing these into exsim package without having to change the package itself:
(defmacro strap! (&rest x) (cons 'acl2::strap! x))
(defmacro acons! (&rest x) (cons 'acl2::acons! x))
(defmacro hons=  (&rest x) (cons 'acl2::hons= x))
(defmacro in-hons=        (&rest x) (cons 'acl2::in-hons= x))
(defmacro set-diff-hons=  (&rest x) (cons 'acl2::set-diff-hons= x))
(defmacro set-union-hons= (&rest x) (cons 'acl2::set-union-hons= x))

(defconst *upd-rewrite-fixp-max* 10)

;;;;;
;; BOZO -- need to remove some of the old types I don't use anymore
;;;;;

;;;;;
;; BOZO -- Rob, Why the heck is this here?
;;;;;
(define my-svex-rewrite-fixp ((expr sv::svex-p) (count natp))
  :returns (rslt sv::svex-p :hyp :guard)
  :measure (nfix count)
  (b* (((when (zp count)) expr)
       (nexp (sv::svex-rewrite-top expr))
       ((when (hons-equal expr nexp)) expr))
    (my-svex-rewrite-fixp nexp (1- count))))

(fty::defprod env-descr
              ((env-type symbolp)
               env-path))

(fty::defprod nxt-tbl-alist-elem
              ((nxts nxt-tbl-p)
               (insts string-listp)))

(fty::defalist nxt-tbl-alist
               :key-type stringp
               :val-type nxt-tbl-alist-elem-p)

(fty::defalist var-size-map
               :key-type sv::svar-p
               :val-type natp)

(fty::defalist mod-int-var-map
               :key-type stringp
               :val-type stringp)

(fty::defalist rtl-int-var-map
               :key-type stringp
               :val-type mod-int-var-map-p)

(fty::defprod des-params
              ((env          env-descr-p)
               (int-vars     rtl-int-var-map-p)
               (wave-pref    stringp)
               (valu-name    stringp)
               (fail-name    stringp)
               (mode-name    stringp)
               (free-name    stringp)))

(fty::defprod des-vars
              ((env        env-descr-p)
               (vsize-map  var-size-map-p)
               (free-vars  sv::svarlist-p)
               (mode-vars  sv::svarlist-p)
               (fail-vars  sv::svarlist-p)
               (valu-vars  sv::svarlist-p)))

(fty::defprod des-tbl-el
              ((insts      string-listp)
               (clk        sv::svar-p)
               (reset      sv::svar-p)
               (valid      sv::svar-p)
               (nxts       nxt-tbl-p)
               (vars       des-vars-p)))

(fty::defalist des-tbl
               :key-type stringp
               :val-type des-tbl-el-p)

(fty::defalist exs-vmap
               :key-type sv::svar
               :val-type sv::4vec)

(fty::defalist out-vmaps
               :key-type stringp
               :val-type exs-vmap-p
               :true-listp t)

(fty::deflist exs-vmaplist
              :elt-type exs-vmap
              :true-listp t)

(fty::defprod exs-tbl-elem
              ((value   natp)
               (mask    natp)
               (lits    satlink::lit-list)))
;               (in-ids  id-list-p)
;               (out-ids id-list-p)))

(fty::defalist exs-tbl
               :key-type sv::svar
               :val-type exs-tbl-elem-p)

(fty::defalist exs-svex-memo
               :key-type sv::svex
               :val-type sv::svex)

(fty::defalist root-tbl
               :key-type stringp ;; module name
               :val-type sv::svarlist-p) ;; list of instances

(fty::defalist inst-mods
               :key-type stringp
               :val-type stringp)

(fty::defprod exs-part-elem
              ((parent sv::svar-p)
               (ndx natp)
               (size natp)))

(fty::defalist exs-part-map
               :key-type sv::svar-p
               :val-type exs-part-elem-p)

(fty::defprod aig-var-elem 
              ((base natp)
               (size natp)))

(fty::defalist aig-var-tbl
               :key-type sv::svar
               :val-type aig-var-elem-p
               :true-listp t)

(fty::defalist lits-alist
               :key-type sv::svar
               :val-type lit-listp
               :true-listp t)

(fty::deflist ndx-list
              :elt-type natp
              :true-listp t)

(fty::defalist ndx-map
               :key-type natp
               :val-type litp
               :true-listp t)

(fty::defalist ndx-ctbl
               :key-type natp
               :val-type ndx-map-p
               :true-listp t)

(fty::deflist ndx-ctbls
              :elt-type ndx-ctbl
              :true-listp t)

(fty::defalist out-ctbls
               :key-type stringp
               :val-type ndx-ctbls-p
               :true-listp t)

(fty::defalist var->ndx-map
               :key-type sv::svar-p
               :val-type ndx-list-p
               :true-listp t)

(fty::defprod ndx->var-elem
              ((var sv::svar-p)
               (off natp)))

(fty::defalist ndx->var-map
               :key-type litp
               :val-type ndx->var-elem-p
               :true-listp t)

(fty::defalist var->port-map
               :key-type sv::svar-p
               :val-type symbolp
               :true-listp t)

(fty::defalist styp-lkup
               :key-type litp
               :val-type symbolp
               :true-listp t)

(fty::defalist lit-model
               :key-type litp
               :val-type litp
               :true-listp t)

(fty::defprod exs-mod-el
              ((next  sv::svex-p)
               (size  natp)
               (reset sv::4vec)
               (port  symbolp)))

(fty::defalist exs-mod-tbl
               :key-type sv::svar-p
               :val-type exs-mod-el-p
               :true-listp t)

(fty::defalist var->supp-map
               :key-type sv::svar-p
               :val-type sv::svarlist-p
               :true-listp t)

(fty::deflist svar-lists
              :elt-type sv::svarlist-p
              :true-listp t)

(fty::defalist ndx->aig
               :key-type natp
               :true-listp t)

(fty::defalist var->aig
               :key-type sv::svar-p
               :true-listp t)

(fty::defalist var->aigs
               :key-type sv::svar-p
               :val-type true-listp
               :true-listp t)

(fty::defalist cyc->ndx->aig
               :key-type natp
               :val-type ndx->aig
               :true-listp t)

(fty::defprod fchk-rslt
              ((status true-listp)
               (ins    exs-vmap-p)
               (outs   exs-vmap-p)))

(fty::defalist fchk-rslt-map
               :key-type sv::svar-p
               :val-type fchk-rslt-p
               :true-listp t)

(defmacro ndx-p (x) `(natp ,x))

(defconst *null-svar* (sv::make-svar :name :null :delay 0 :nonblocking nil))
(defconst *self-svar* (sv::make-svar :name :self :delay 0 :nonblocking nil))
(defconst *null-svex* (sv::svex-var *null-svar*))
(defconst *self-svex* (sv::svex-var *self-svar*))

(fty::defprod vcd-restor
              ((comments   string-listp)
               (date       string-listp)
               (version    string-listp)
               (timescale  string-listp)
               (timestamps string-listp)
               (parent-map acl2::vcd-parent-map-p)
               (child-map  acl2::vcd-child-map-p)
               (var-map    acl2::vcd-var-map-p)))

(defconst *def-vcd-restor*
  (make-vcd-restor :comments ()
                   :date ()
                   :version ()
                   :timescale ()
                   :timestamps ()
                   :parent-map ()
                   :child-map ()))

(fty::defprod sim-params
              ((waves        stringp)
               (use-satlink  symbolp)
               (verbose      symbolp)
               (release-sat  symbolp)
               (enable-fraig symbolp)
               ;;
               (styp-fn     symbolp)
               (fix-fn      symbolp)
               (vl-conf-fn  symbolp)
               ;;
               reset-type
               (root-time   stringp)
               ;;
               (mode-vmap   exs-vmap-p)
               vcd-prefix
               fail-tgt
               random-seed
               tst-module
               max-cycle
               ;;
               free-var-focus
               ;;
               num-fails-gen
               ;;
               use-ipasir-stats
               ;;
               save-nxt-tbl
               save-mod-tbl
               include-upds
               unsat-out-disable
               ;;
               (max-wave-var-depth natp)
               ;;
               (rew-iterations posp)
               ;;
               (gain-factor natp)
               (repeat-weight natp)
               (clean-interval natp)
               (min-diff natp)
               (min-vars natp)
               (min-clauses natp)
               (max-diff natp)
               (max-vars natp)
               (max-clauses natp)
               (mid-diff natp)
               (mid-vars natp)
               (mid-clauses natp)))

(fty::defprod choice-vars
              (sat-result
               (var-count   natp)
               (cls-count   natp)
               (lo          natp)
               (mid         natp)
               (hi          natp)
               (max-cycle   natp)
               (last-clean  natp)
               (num-steps   natp)
               (prev-choice true-listp)
               (rand-value  natp)))

(defconst *def-sim-params*
  (make-sim-params :waves         "vcs"
                   :use-satlink   t
                   :verbose       t
                   :release-sat   t
                   :enable-fraig  nil
                   ;;
                   :styp-fn       'comp-styp
                   :fix-fn        'comp-fix
                   :vl-conf-fn    'comp-vl-conf
                   ;;
                   :reset-type    nil
                   :root-time     "1ns"
                   ;;
                   :mode-vmap     ()
                   ;; BOZO NOTE :: assume top-level module named "top"?
                   :vcd-prefix    (list "top") 
                   :fail-tgt      :null
                   :random-seed   nil
                   :tst-module    nil
                   :max-cycle     nil
                   ;;
                   :free-var-focus nil
                   ;;
                   :num-fails-gen nil
                   ;;
                   :use-ipasir-stats nil
                   ;;
                   :save-nxt-tbl t
                   :save-mod-tbl t
                   :include-upds t
                   :unsat-out-disable nil
                   ;;
                   :max-wave-var-depth 3
                   ;;
                   :rew-iterations 5
                   ;;
                   :gain-factor    50 ;; 0-100
                   :repeat-weight  2
                   :clean-interval 5000
                   :min-diff       2
                   :mid-diff       10
                   :max-diff       40
                   :min-vars       20
                   :mid-vars       50
                   :max-vars       100
                   :min-clauses    100
                   :mid-clauses    500
                   :max-clauses    1000))

