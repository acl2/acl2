;; /Users/sumners/acl2/acl2-7.3/books/centaur/sv/tutorial
;;
;; rtl2chks.lisp
;;
;; Take VL design, build SV hierarchical and SV compiled definitions,
;;   and then compute the ARCH definition from this and user supplied
;;   function for providing "typing" for flopped state variables and 
;;   inputs in design.
;;
;; 

(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "misc/random" :dir :system)
(include-book "centaur/sv/mods/compile" :dir :system)
(include-book "std/io/read-file-lines" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "std/strings/strprefixp" :dir :system)
(include-book "support")
(include-book "nxtypes")

(define find-match-mod-hier (name (modinsts sv::modinstlist-p))
  :returns (rslt (iff (sv::modname-p rslt) rslt))
  (and (consp modinsts)
       (or (and (equal name (sv::modinst->instname (first modinsts)))
                (sv::modinst->modname (first modinsts)))
           (find-match-mod-hier name (rest modinsts)))))

(define find-var-hier-wire (name (mod sv::module-p) (alst sv::modalist-p))
  :returns (rslt (iff (sv::wire-p rslt) rslt))
  (if (atom name)
      (and (sv::name-p name)
           (sv::wirelist-find name (sv::module->wires mod)))
    (b* ((nextmodname (find-match-mod-hier (car name)
                                           (sv::module->insts mod)))
         ((unless nextmodname)
          (raise "Unable to find next module name: ~x0~%" (car name)))
         (nextmod (sv::modalist-lookup nextmodname alst))
         ((unless nextmod)
          (raise "Unable to find next module: ~x0~%" nextmodname)))
      (find-var-hier-wire (cdr name) nextmod alst))))

(define is-rtl-struct-p (name)
  (and (consp name) (eq (car name) :vl-struct)))

(define is-reg-pat (name)
  (if (atom name)
      (or (equal name "sq")
          (equal name "q"))
    (and (or (equal (car name) "rg")
             (equal (car name) "r0"))
         (equal (cdr name) "sq"))))

(define parse-lhrange ((lhr sv::lhrange-p))
  (b* ((w (sv::lhrange->w lhr))
       (atm (sv::lhrange->atom lhr))
       ((when (eq (sv::lhatom-kind atm) :z))
        (mv (raise "illegal lhrange-z encountered! ~x0~%" lhr) 0 1))
       (name (sv::lhatom-var->name atm))
       (rsh  (sv::lhatom-var->rsh atm)))
    (mv name w rsh)))

(define parse-lhs-pair ((lhs sv::lhs-p) (rhs sv::lhs-p))
  (if (not (and (consp lhs) (consp rhs)
                (atom (cdr lhs)) (atom (cdr rhs))))
      (mv (raise "bad lhs pair encountered in struct: ~x0 ~x1~%"
                 lhs rhs)
          0 1)
    (b* (((mv lf -  -)  (parse-lhrange (car lhs)))
         ((mv rf rw rr) (parse-lhrange (car rhs))))
      (if (not (and (eq rf :self) (stringp lf))) (mv () 0 1) (mv lf rr rw)))))

(define get-var-mod-subs (name
                          (mod sv::module-p)
                          (alst sv::modalist-p)
                          &key
                          ((apairs sv::lhspairs-p) 'nil)
                          ((c-d natp) '1000))
  :measure (make-ord (1+ (nfix c-d)) (1+ (len apairs)) 0)
  :returns (rslt alistp)
  (cond ((zp c-d)
         (raise "Exceeded maximum call-depth!"))
        (name
         (b* ((str-name (find-match-mod-hier name (sv::module->insts mod)))
              ((unless str-name) nil)
              ((unless (is-rtl-struct-p str-name)) nil)
              (nmod (sv::modalist-lookup str-name alst))
              ((unless nmod) (raise "Unable to find module: ~x0~%" name)))
           (get-var-mod-subs nil mod alst
                             :c-d (1- c-d)
                             :apairs (sv::module->aliaspairs nmod))))
        ((atom apairs) ())
        (t (b* (((mv fld lsb width)
                 (parse-lhs-pair (caar apairs) (cdar apairs))))
             (if (null fld)
                 (get-var-mod-subs nil mod alst
                                   :apairs (cdr apairs)
                                   :c-d c-d)
               (cons (list* fld lsb width
                            (get-var-mod-subs fld mod alst
                                              :apairs nil
                                              :c-d (1- c-d)))
                     (get-var-mod-subs nil mod alst
                                       :apairs (cdr apairs)
                                       :c-d c-d)))))))

(define find-bind-in-pair ((lhs sv::lhs-p) (rhs sv::lhs-p) (var sv::svar-p))
  (and (consp lhs) (consp rhs)
       (atom (cdr lhs)) (atom (cdr rhs))
       (b* (((mv lf - -) (parse-lhrange (car lhs)))
            ((mv rf - -) (parse-lhrange (car rhs))))
         ;; BOZO -- should we check that the sizes are for the full port size?
         ;;         I think so, but that may be overkill here.. not sure.
         (and (equal lf var) rf))))

(define find-bind-in-pairs ((apairs sv::lhspairs-p)
                            (var sv::svar-p))
  (and (consp apairs)
       (or (find-bind-in-pair (caar apairs) (cdar apairs) var)
           (find-bind-in-pairs (cdr apairs) var))))

(define get-q-bind (name (mod sv::module-p))
  (b* ((svar (sv::make-svar :name (cons name "q") :delay 0 :nonblocking nil)))
    (find-bind-in-pairs (sv::module->aliaspairs mod) svar)))

(define find-var-hier-subs (name (mod sv::module-p) (alst sv::modalist-p))
  :returns (rslt alistp)
  (if (atom name)
      (get-var-mod-subs name mod alst)
    (b* ((nextmodname (find-match-mod-hier (car name)
                                           (sv::module->insts mod)))
         ((unless nextmodname)
          (raise "Unable to find next module name: ~x0~%" (car name))))
      (if (and (stringp nextmodname)
               (str::strprefixp "rreg" nextmodname)
               (is-reg-pat (cdr name)))
          (b* ((q-bind (get-q-bind (car name) mod)))
            (and q-bind
                 (get-var-mod-subs q-bind mod alst)))
        (b* ((nextmod (sv::modalist-lookup nextmodname alst))
             ((unless nextmod)
              (raise "Unable to find next module: ~x0~%" nextmodname)))
          (find-var-hier-subs (cdr name) nextmod alst))))))

(define svex-rewrite-fixp ((expr sv::svex-p)
                           (max-iter natp))
  :returns (rslt sv::svex-p)
  :measure (nfix max-iter)
  (if (zp max-iter) (sv::svex-fix expr)
    (b* ((next (sv::svex-rewrite-top expr)))
      (if (hons-equal-lite next expr) expr
        (svex-rewrite-fixp next (1- max-iter))))))

(define dly-var ((var sv::svar-p) (dly natp))
  :returns (rslt sv::svar-p)
  (sv::change-svar var :delay dly))

(define add-phase-subst ((var sv::svar-p)
                         (fixp var-fix-p)
                         (phase symbolp)
                         (rslt sv::svex-alist-p))
  :returns (rslt sv::svex-alist-p)
  :guard-hints (("Goal" :in-theory (enable var-fix-p)))
  (b* ((var  (sv::svar-fix var))
       (rslt (sv::svex-alist-fix rslt)))
    (cond ((or (null fixp) (eq fixp :out))
           (sv::svex-alist-fix rslt))
          ((not (symbolp fixp)) 
           (acons var (sv::svex-quote fixp) rslt))
          (t           
           (cond ((eq phase :neg-step)
                  (cond ((eq fixp :reset)
                         (acons var (sv::svex-quote 0) rslt))
                        ((eq fixp :clock)
                         (acons (dly-var var 0) (sv::svex-quote 0)
                                (acons (dly-var var 1) (sv::svex-quote 1)
                                       rslt)))
                        (t rslt)))
                 ((eq phase :pos-step)
                  (cond ((eq fixp :reset)
                         (acons var (sv::svex-quote 0) rslt))
                        ((eq fixp :clock)
                         (acons (dly-var var 0) (sv::svex-quote 1)
                                (acons (dly-var var 1) (sv::svex-quote 0)
                                       rslt)))
                        (t rslt)))
                 ((eq phase :neg-reset)
                  (cond ((eq fixp :reset)
                         (acons var (sv::svex-quote 1) rslt))
                        ((eq fixp :clock)
                         (acons (dly-var var 0) (sv::svex-quote 0)
                                (acons (dly-var var 1) (sv::svex-quote 1)
                                       rslt)))
                        (t rslt)))
                 (t
                  (cond ((eq fixp :reset)
                         (acons var (sv::svex-quote 1) rslt))
                        ((eq fixp :clock)
                         (acons (dly-var var 0) (sv::svex-quote 1)
                                (acons (dly-var var 1) (sv::svex-quote 0)
                                       rslt)))
                        (t rslt))))))))

(define mk-phase-subst ((vars svar-fix-map-p)
                        (phase symbolp)
                        &key
                        ((rslt sv::svex-alist-p) 'nil))
  :returns (rslt sv::svex-alist-p)
  (if (atom vars) (sv::svex-alist-fix rslt)
    (mk-phase-subst (rest vars) phase
                    :rslt (add-phase-subst (caar vars) (cdar vars) phase rslt))))

(define make-phase-sub ((vars svar-fix-map-p)
                        (phase symbolp))
  :returns (rslt sv::svex-alist-p)
  (make-fast-alist (mk-phase-subst vars phase)))

(define mk-phase-svex ((expr sv::svex-p)
                       (vars svar-fix-map-p)
                       (phase symbolp))
  :returns (rslt sv::svex-p)
  :guard-debug t
  ;(svex-rewrite-fixp (sv::svex-subst-memo expr (mk-phase-subst vars phase ())) 1))
  (b* ((- (mk-phase-subst vars phase)))
    (svex-rewrite-fixp expr 0)))

(encapsulate 
 (((compute-var-fix *) => * 
   :formals (var) 
   :guard (sv::svar-p var)))
 
 (local (defun compute-var-fix (var)
          (declare (xargs :guard (sv::svar-p var))
                   (ignore var))
          nil))
 
 (defthm compute-var-fix-returns-var-fix-p
   (var-fix-p (compute-var-fix var))))

(define compute-var-fix-inst ((var sv::svar-p))
  :returns (rslt var-fix-p)
  (let ((name (sv::svar->name var)))
    (cond ((equal name "reset")  :reset)
          ((equal name "clk")    :clock)
          (t                     :out))))

(defattach compute-var-fix compute-var-fix-inst)

(define compute-var-fixs ((vars sv::svarlist-p)
                          &key
                          ((rslt svar-fix-map-p) ':compute-var-fixs))
  :returns (rslt svar-fix-map-p)
  (if (atom vars) (svar-fix-map-fix rslt)
    (compute-var-fixs (rest vars)
                      :rslt (b* ((var (first vars))
                                 (vfix (compute-var-fix var)))
                              (if (not vfix) (svar-fix-map-fix rslt)
                                (cons (cons var vfix) rslt))))))

(define find-svar-des-wire ((svar sv::svar-p)
                            (des  sv::design-p))
  :returns (wire (iff (sv::wire-p wire) wire))
  (b* ((name    (sv::svar->name svar))
       (modalst (sv::design->modalist des))
       (top     (sv::design->top des))
       (mod     (sv::modalist-lookup top modalst))
       ((unless mod)
        (raise "Unable to find module: ~x0~%" top))
       (wire (find-var-hier-wire name mod modalst))
       ((unless wire)
        (raise "Unable to find wire: ~x0~%" name)))
    wire))

(define find-svar-des-subs ((svar sv::svar-p)
                            (des  sv::design-p))
  :returns (rslt alistp)
  (b* ((name    (sv::svar->name svar))
       (modalst (sv::design->modalist des))
       (top     (sv::design->top des))
       (mod     (sv::modalist-lookup top modalst))
       ((unless mod)
        (raise "Unable to find module: ~x0~%" top)))
    (find-var-hier-subs name mod modalst)))

(define var-fix-port (fix)
  :returns (rslt port-typ-p)
  (cond ((eq fix :in)  :input)
        ((eq fix :out) :output)
        (t             :state)))

(define compute-phase-tbl ((nexts  sv::svex-alist-p)
                           (des    sv::design-p)
                           (rslt   phase-tbl-p)
                           &key
                           ((count  natp) '0))
  :returns (rslt phase-tbl-p)
  (if (atom nexts) (phase-tbl-fix rslt)
    (b* ((svar      (caar nexts))
         (expr      (cdar nexts))
         (wire      (find-svar-des-wire svar des))
         ((unless wire) nil)
         (vars      (sv::svex-vars expr))
         (port      (var-fix-port (compute-var-fix svar)))
         (var-fixs  (compute-var-fixs vars))
         (neg-step  (mk-phase-svex expr var-fixs :neg-step))
         (pos-step  (mk-phase-svex expr var-fixs :pos-step))
         (neg-reset (mk-phase-svex expr var-fixs :neg-reset))
         (pos-reset (mk-phase-svex expr var-fixs :pos-reset))
         (- (and (eql (mod count *prog-tbl-count*) 0)
                 (cw "**PROGRESS BAR** (compute-phase-tbl : ~x0)~%" count))))
      (compute-phase-tbl (rest nexts) des
                         (hons-acons svar
                                     (make-phase-tbl-elem :wire wire
                                                          :supp vars
                                                          :port port
                                                          :neg-step neg-step
                                                          :pos-step pos-step
                                                          :neg-reset neg-reset
                                                          :pos-reset pos-reset)
                                     rslt)
                         :count (1+ count)))))

(define mk-pre-step-alst ((supp sv::svarlist-p)
                          (tbl phase-tbl-p)
                          (typ symbolp)
                          (rslt sv::svex-alist-p))
  :returns (rslt sv::svex-alist-p)
  (if (atom supp) (sv::svex-alist-fix rslt)
    (mk-pre-step-alst (rest supp) tbl typ    
                      (b* ((var (first supp))
                           (look (hons-get var tbl))
                           ((unless look) rslt)
                           ((phase-tbl-elem el) (cdr look)))
                        (cons (cons (first supp)
                                    (if (eq typ :step) el.neg-step el.neg-reset))
                              rslt)))))

(define compute-nxt-step ((expr sv::svex-p)
                          (supp sv::svarlist-p)
                          (tbl  phase-tbl-p)
                          (typ  symbolp))
  :returns (rslt sv::svex-p)
  (svex-rewrite-fixp (sv::svex-subst-memo expr (mk-pre-step-alst supp tbl typ ())) 2))

(defthm fast-alist-fork-nxt-tbl-p
  (implies (and (nxt-tbl-p x) (nxt-tbl-p y))
           (nxt-tbl-p (fast-alist-fork x y)))
  :hints (("Goal" :in-theory (enable nxt-tbl-p))))

(defthm nxt-tbl-p-cdr-last
  (implies (nxt-tbl-p x)
           (nxt-tbl-p (cdr (last x)))))

(define compute-tmp-tbl ((nxt-vars   sv::svarlist-p)
                         (step-exprs sv::svexlist-p)
                         (reset-vals sv::4veclist-p)
                         (des        sv::design-p)
                         &key
                         ((rslt nxt-tbl-p) ':compute-tmp-tbl))
  :returns (rslt nxt-tbl-p)
  (if (atom nxt-vars)
      (nxt-tbl-fix (fast-alist-clean (make-fast-alist rslt)))
    (b* ((var  (first nxt-vars))
         (wire (find-svar-des-wire var des))
         (step (first step-exprs))
         (rval (first reset-vals))
         (subs (find-svar-des-subs var des))
         ((unless wire) (raise "Unexpected null wire: ~x0~%" var))
         ((unless step) (raise "Unexpected null step: ~x0~%" var))
         ((unless rval) (raise "Unexpected null rval: ~x0~%" var))
         (port :state)
         ;; We use the "slower" svex-vars here instead of svex-collect-vars because
         ;; svex-vars is memoized (svex-collect-vars uses a "seen" hash-table to
         ;; efficiently avoid revisiting earlier nodes.. but that makes it useless
         ;; to memoize). svex-vars is not particularly efficient but its definition
         ;; makes it easier to memoize which is most relevant for this usage here:
         (supp (sv::svex-vars step))
         (elem (make-nxt-tbl-elem :wire  wire
                                  :port  port
                                  :supp  supp
                                  :step  step
                                  :reset rval
                                  :subs  subs)))
      (compute-tmp-tbl (rest nxt-vars) (rest step-exprs) (rest reset-vals) des
                       :rslt (cons (cons var elem) rslt)))))

(define compute-nxt-tbl ((vars     sv::svarlist-p)
                         (tmp-tbl  nxt-tbl-p)
                         (des      sv::design-p)
                         &key
                         ((rslt nxt-tbl-p) ':compute-nxt-tbl))
  :returns (rslt nxt-tbl-p)
  (if (atom vars)
      (nxt-tbl-fix (fast-alist-clean (make-fast-alist rslt)))
    (b* ((var  (first vars))
         (look (hons-get var tmp-tbl))
         (wire (find-svar-des-wire var des))
         ((unless wire) (raise "Unexpected null wire:~x0~%" var))
         (elem (if (not look)
                   (make-nxt-tbl-elem :wire  wire
                                      :port  :input
                                      :supp  ()
                                      :step  (sv::svex-var var)
                                      :reset (sv::4vec-x))
                 (cdr look))))
        (compute-nxt-tbl (rest vars) tmp-tbl des
                         :rslt (cons (cons var elem) rslt)))))

(define add-supp-nxts-tbl ((vars sv::svarlist-p)
                           (tbl nxt-tbl-p)
                           (rslt nxt-tbl-p))
  :returns (rslt nxt-tbl-p)
  (if (atom vars) (nxt-tbl-fix rslt)
    (add-supp-nxts-tbl (rest vars) tbl
                       (b* ((look (hons-get (first vars) tbl))
                            ((unless look) rslt))
                         (hons-acons (first vars) (cdr look) rslt)))))

(define compute-true-nxts ((alst nxt-tbl-p)
                           (top  nxt-tbl-p)
                           (rslt nxt-tbl-p)
                           &key
                           ((count natp) '0))
  :returns (rslt nxt-tbl-p)
  (if (atom alst) (nxt-tbl-fix rslt)
    (b* (((nxt-tbl-elem el) (cdar alst))
         (rslt (if (eq el.port :output)
                   (hons-acons (caar alst) el rslt)
                 rslt))
         (- (and (eql (mod count *prog-tbl-count*) 0)
                 (cw "**PROGRESS BAR** (compute-true-nxts : ~x0)~%" count))))
      (compute-true-nxts (rest alst) top
                         (add-supp-nxts-tbl (nxt-tbl-elem->supp (cdar alst))
                                            top rslt)
                         :count (1+ count)))))

(define member-hons= (e x)
  (and (consp x)
       (or (hons-equal-lite e (first x))
           (member-hons= e (rest x)))))

(define add-to-input-set ((vars sv::svarlist-p)
                          (top  nxt-tbl-p)
                          (rslt sv::svarlist-p))
  :returns (rslt sv::svarlist-p)
  (if (atom vars) (sv::svarlist-fix rslt)
    (add-to-input-set (rest vars) top
                      (if (or (hons-get (first vars) top)
                              (member-hons= (first vars) rslt))
                          rslt
                        (cons (first vars) rslt)))))

(define compute-input-set ((alst nxt-tbl-p)
                           (top  nxt-tbl-p)
                           (rslt sv::svarlist-p))
  :returns (rslt sv::svarlist-p)
  (if (atom alst) (sv::svarlist-fix rslt)
    (b* (((nxt-tbl-elem el) (cdar alst)))
      (compute-input-set (rest alst) top
                         (add-to-input-set el.supp top rslt)))))

(define add-inpts-nxt-tbl ((inpts sv::svarlist-p)
                           (des   sv::design-p)
                           (rslt  nxt-tbl-p))
  :returns (rslt nxt-tbl-p)
  (if (atom inpts) (nxt-tbl-fix rslt)
    (b* ((svar (first inpts))
         (wire (find-svar-des-wire svar des))
         ((unless wire) nil))
      (add-inpts-nxt-tbl (rest inpts) des
                         (hons-acons svar
                                     (make-nxt-tbl-elem :wire  wire
                                                        :port  :input
                                                        :supp  ()
                                                        :step  (sv::svex-var svar)
                                                        :reset (sv::4vec-x))
                                     rslt)))))

(define default-phase/nxt-tbl-size (sz) sz)

(define add-output-vars ((var-fixs svar-fix-map-p)
                         (fin-vars sv::svarlist-p))
  :returns (fin-vars sv::svarlist-p)
  (if (atom var-fixs) (sv::svarlist-fix fin-vars)
    (add-output-vars (rest var-fixs)
                     (b* (((cons var fix) (first var-fixs)))
                       (if (eq fix :out) (cons var fin-vars) fin-vars)))))

(local (defthm unite!*-svarlist-p
         (implies (and (sv::svarlist-p x) (sv::svarlist-p y))
                  (sv::svarlist-p (unite!* x y)))
         :hints (("Goal" :in-theory (enable unite!* add! sv::svarlist-p)))))

(local (defthm unite!-svarlist-p
         (implies (and (sv::svarlist-p x) (sv::svarlist-p y))
                  (sv::svarlist-p (unite! x y)))
         :hints (("Goal" :in-theory (enable unite! sv::svarlist-p)))))

;; Finally, we go ahead and offer a normalization of the delays in the variables in
;; the nxt-tbl (it isn't really needed for the semantics of the nxt-tbl), but the delays
;; might get reused in downstream tools (namely exsim reuses the svar delay field as
;; a clock cycle..)
;;;; NOTE-- need to remap variables to all 0 delay variables, do it as an early processing
;;;; step on the nxt-tbl that we have brought in..

(define nxt-norm-var ((var sv::svar-p))
  :returns (rslt sv::svar-p)
  (sv::svar-fix 
   (if (eql (sv::svar->delay var) 0) var
     (sv::change-svar var :delay 0))))

(define nxt-norm-vars ((vars sv::svarlist-p) &key ((rslt sv::svarlist-p) 'nil))
  :returns (rslt sv::svarlist-p)
  (if (endp vars) (sv::svarlist-fix rslt)
    (nxt-norm-vars (rest vars) 
                   :rslt (cons (nxt-norm-var (first vars)) rslt))))

(defines nxt-norm-svex
  (define nxt-norm-svex ((x sv::svex-p))
    :verify-guards nil
    :returns (rslt sv::svex-p :hyp :guard)
    :measure (sv::svex-count x)
    (sv::svex-case x
        :var   (sv::svex-var (nxt-norm-var x.name))
        :quote (sv::svex-fix x)
        :call  (sv::svex-call* x.fn
                               (nxt-norm-svexlist x.args))))

  (define nxt-norm-svexlist ((x sv::svexlist-p))
    :returns (rslt sv::svexlist-p :hyp :guard)
    :measure (sv::svexlist-count x)
    (if (endp x) ()
      (cons (nxt-norm-svex (first x)) 
            (nxt-norm-svexlist (rest x))))))

(verify-guards nxt-norm-svex)

(memoize 'nxt-norm-svex :condition '(eq (sv::svex-kind x) :call))

(define norm-vars-nxt-tbl ((nxt-tbl nxt-tbl-p)
                           &key ((rslt nxt-tbl-p) ':norm-vars-nxt-tbl))
  :returns (rslt nxt-tbl-p)
  (if (atom nxt-tbl) (nxt-tbl-fix (fast-alist-clean rslt))
    (b* ((var               (caar nxt-tbl))
         (n-var         (nxt-norm-var var))
         ((nxt-tbl-elem el) (cdar nxt-tbl))
         (look       (hons-get n-var rslt))
         (action
          (cond ((not look) :update)
                ((eq el.port :input) :update)
                ((eq (nxt-tbl-elem->port (cdr look)) :input) :drop)
                (t (raise "encountered aliasing in final nxt-tbl:~x0~%"
                          var)))))
      (norm-vars-nxt-tbl 
       (rest nxt-tbl)
       :rslt (if (eq action :drop) rslt
               (hons-acons n-var 
                           (acl2::change-nxt-tbl-elem el
                                                      :step (nxt-norm-svex el.step)
                                                      :supp (nxt-norm-vars el.supp))
                           rslt))))))

(defthm append$!-svexlist-p
  (implies (and (sv::svexlist-p x) (sv::svexlist-p y))
           (sv::svexlist-p (append$! x y)))
  :hints (("Goal" :in-theory (enable append$! sv::svexlist-p))))

(defthm append$!-svarlist-p
  (implies (and (sv::svarlist-p x) (sv::svarlist-p y))
           (sv::svarlist-p (append$! x y)))
  :hints (("Goal" :in-theory (enable append$! sv::svarlist-p))))

(defthm append$!-svex-alist-p
  (implies (and (sv::svex-alist-p x) (sv::svex-alist-p y))
           (sv::svex-alist-p (append$! x y)))
  :hints (("Goal" :in-theory (enable append$! sv::svex-alist-p))))

(define re-pair ((x sv::svarlist-p) (y sv::svexlist-p)
                 &key ((rslt sv::svex-alist-p) 'nil))
  :returns (rslt sv::svex-alist-p)
  (cond ((and (endp x) (endp y)) (sv::svex-alist-fix rslt))
        ((or (endp x) (endp y))
         (raise "vars and exps should have matched len:~x0~%"
                (list x y)))
        (t (re-pair (cdr x) (cdr y)
                    :rslt (cons (cons (car x) (car y)) rslt)))))

(define sv-comps->nxt-tbl ((sv-design  sv::design-p)
                           (sv-nexts   sv::svex-alist-p)
                           (sv-upds    sv::svex-alist-p)
                           (rew-iterations posp))
  :short "Take a VL design, build SV hierarchical and compiled design, and then build and return ARCH"
  :returns (rslt nxt-tbl-p)
  ;;
  ;; 2. Compute the "types" of the variables in sv-nexts from sv-designs
  ;;    and store that in a hash-table along with the update term.
  ;; 3. Compute the set of inputs and store them in a seperate table also
  ;;    with type information.
  ;; 4. read in all clocks, resets, constants, etc. as definitions in some
  ;;    structure.
  ;; 5. go through and rewrite every term based on clock setting and
  ;;    resets,constants to get low-phase and high-phase terms.
  ;;    -- constants are held at their values
  ;;    -- inputs are stable on each phase
  ;;
  ;; NOTE -- we do all of steps 2.-5. as part of computing the phase-tbl:
  ;;
  ;; 6. Replace each variable in high-phase terms with low-phase term and
  ;;    compute nxt-tbl's for step and reset.       
  ;; 7. Compute set of true-nexts that are in the right-hand sides
  ;;    (excluding inputs).
  ;; 8. Prune the table and rebuild the hash table with the rewritten and
  ;;    simplified terms.
  ;; 9. Do same thing for reset sequence to get reset final term for each
  ;;    true flop.
  ;;    -- this will require several steps potentially but shouldn't blow
  ;;       up term wise since all inputs should be held to "reset" values
  ;;       for the inputs... (maybe all 0's)
  ;; 10. Compute the final set of inputs:
  ;;
  ;; NOTE -- we do all of steps 6.-10. in computing the reset 4vec and step
  ;;         nxt-tbls, we then use these to define the subsequent
  ;;         structures and eventually the arch def that we return..
  ;; NOTE -- for now, we simplify reset handling to be single reset pulse,
  ;;         we can handle longer reset sequence needs as assumptions
  ;;         (checked in simulation), or computed as short eval. seq.
  ;;
  (b* ((sv-nexts   (append! sv-upds sv-nexts))
       (nxt-vars   (cwtime (sv::svex-alist-keys sv-nexts)                  :mintime 0))
       (nxt-exps   (cwtime (sv::svex-alist-vals sv-nexts)                  :mintime 0))
;;       (upd-vars   (cwtime (sv::svex-alist-keys sv-upds)                   :mintime 0))
;;       (upd-exps   (cwtime (sv::svex-alist-vals sv-upds)                   :mintime 0))
       (all-vars   (cwtime (sv::svexlist-collect-vars nxt-exps)            :mintime 0))
       (all-vars   (cwtime (unite! nxt-vars all-vars)                      :mintime 0))
;;       (all-vars   (cwtime (unite! upd-vars all-vars)                      :mintime 0))
       (var-fixs   (cwtime (compute-var-fixs all-vars)                     :mintime 0))
       (var-fixs   (cwtime (make-fast-alist var-fixs)                      :mintime 0))
       ;; first only consider upds on neg-edge
;;       (neg-sub    (cwtime (make-phase-sub var-fixs :neg-step)             :mintime 0))
;;       (upd-exps   (cwtime (sv::svexlist-compose* upd-exps neg-sub)        :mintime 0))
;;       (-          (fast-alist-free neg-sub))
;;       (nxt-vars   (append! upd-vars nxt-vars))
;;       (nxt-exps   (append! upd-exps nxt-exps))
       ;; first compute the step-exps:
       (neg-sub    (cwtime (make-phase-sub var-fixs :neg-step)             :mintime 0))
       (neg-exps   (cwtime (sv::svexlist-compose* nxt-exps neg-sub)        :mintime 0))
       (-          (fast-alist-free neg-sub))
       (neg-exps   (cwtime (sv::svexlist-rewrite-top neg-exps :verbosep t) :mintime 0))
       (neg-alst   (cwtime (make-fast-alist (re-pair nxt-vars neg-exps))   :mintime 0))
       (pos-sub    (cwtime (make-phase-sub var-fixs :pos-step)             :mintime 0))
       (pos-exps   (cwtime (sv::svexlist-compose* nxt-exps pos-sub)        :mintime 0))
       (-          (fast-alist-free pos-sub))
       (pos-exps   (cwtime (sv::svexlist-rewrite-top pos-exps :verbosep t) :mintime 0))
       (step-exprs (cwtime (sv::svexlist-compose* pos-exps neg-alst)       :mintime 0))
       (-          (fast-alist-free neg-alst))
       (step-exprs (cwtime (sv::svexlist-rewrite-fixpoint 
                            step-exprs :count rew-iterations :verbosep t)  :mintime 0))
       ;; now compute the reset-vals:
       (neg-sub    (cwtime (make-phase-sub var-fixs :neg-reset)            :mintime 0))
       (neg-exps   (cwtime (sv::svexlist-compose* nxt-exps neg-sub)        :mintime 0))
       (-          (fast-alist-free neg-sub))
       (neg-exps   (cwtime (sv::svexlist-rewrite-top neg-exps :verbosep t) :mintime 0))
       (neg-alst   (cwtime (make-fast-alist (re-pair nxt-vars neg-exps))   :mintime 0))
       (pos-sub    (cwtime (make-phase-sub var-fixs :pos-reset)            :mintime 0))
       (pos-exps   (cwtime (sv::svexlist-compose* nxt-exps pos-sub)        :mintime 0))
       (-          (fast-alist-free pos-sub))
       (pos-exps   (cwtime (sv::svexlist-rewrite-top pos-exps :verbosep t) :mintime 0))
       (reset-exps (cwtime (sv::svexlist-compose* pos-exps neg-alst)       :mintime 0))
       (-          (fast-alist-free neg-alst))
       (reset-vals (cwtime (sv::svexlist-eval reset-exps ())               :mintime 0))
       ;; now recompute the support as the set of variables:
       (fin-vars   (cwtime (sv::svexlist-collect-vars step-exprs)          :mintime 0))
       (fin-vars   (cwtime (add-output-vars var-fixs fin-vars)             :mintime 0))
       ;; now compute the initial through final nxt-tbls:
       (temp-tbl   (cwtime (compute-tmp-tbl nxt-vars step-exprs 
                                            reset-vals sv-design)          :mintime 0))
       (tmp2-tbl   (cwtime (compute-nxt-tbl fin-vars temp-tbl sv-design)   :mintime 0))
       (-          (fast-alist-free temp-tbl))
       (nxt-tbl    (cwtime (norm-vars-nxt-tbl tmp2-tbl)                    :mintime 0))
       (-          (fast-alist-free tmp2-tbl))
       (-          (fast-alist-free var-fixs)))
     nxt-tbl))

#|
(define rtl->sv->nxt-tbl ((in-des     sv::design-p)
                          (fix-fn     symbolp)
                          &key
                          (state      'state))
  :short "Take a VL design, build SV hierarchical and compiled design, and then build and return ARCH"
  :returns (rslt nxt-tbl-p)
  (b* (((mv sv-design sv-nexts) (vl->sv-comps in-des))
       ((unless sv-design) nil))
    (sv-comps->nxt-tbl sv-design sv-nexts fix-fn)))
|#

;;(dfc arch-rtl-tbl nxt-tbl-p  (rtl->sv->nxt-tbl *vl-design* "processor" 'arch-fix-fn))x
;; NOTE -- we assume that the *nxt-tbl* constant built during model.lisp processing (which produces
;;         an xmv_acl2 executable image) is the nxt-tbl that we want (built as per defined in
;;         this file but loaded differently).. Need to work out the details on splitting these up.
;IFDEF?
;;(dfc arch-rtl-tbl nxt-tbl-p  *nxt-tbl*)
