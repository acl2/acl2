;; exbase.lisp
;;
;; Book primarily defining the exs$ stobj. Book begins with special macro
;; for defining the stobj which generates all of the field definitions and
;; and theorems, etc. Book also includes a bunch of wrapper definitions at
;; the exs$ level which transition to the nested stobjs in the exs$ stobj.

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

(include-book "centaur/ipasir/ipasir-logic" :dir :system)
(include-book "centaur/ipasir/ipasir-tools" :dir :system)
(include-book "centaur/misc/seed-random" :dir :system)
(include-book "centaur/aignet/top" :dir :system)
(include-book "misc/file-io" :dir :system)
(include-book "misc/random" :dir :system)
(include-book "support")
(include-book "extypes")

(defsection exsim-base-types-and-structures
  :parents (exsim)
  :short "definition of the exs$ stobj and associated macros and operations on
  nested stobjs"
  :autodoc nil
  :long " <p> This book defines the exs$ stobj which is at the core of exsim
along with a selection of functions which perform operations on the nested
stobjs inside the exs$ stobj. The book begins with a define-stobj macro which
generates a bunch of macros and theorems which assist in reducing basic
terms related to the exs$ stobj functions. Then the definiton of the exs$ stobj
and finally some wrapper functions for operations on nested stobjs
(incremental sat state, random number generator, an aignet containing the
compiled design, and an array of stobj arrays of literals) </p> ")

(defstobj-clone lvals     aignet::litarr :prefix "LVALS-")
(defstobj-clone in-lvals  aignet::litarr :prefix "IN-LVALS-")
(defstobj-clone out-lvals aignet::litarr :prefix "OUT-LVALS-")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;; some simple early stuff
;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; a few trivial def.s and theorems as well that we need..

;; just make this some big big number..
(defconst *rand-seed-upper-limit* 100000000001)

(defthm integerp-is-4vecp
  (implies (integerp x) (sv::4vec-p x))
  :hints (("Goal" :in-theory (enable sv::4vec-p))))

(defthm random$-returns-natp
  (natp (mv-nth 0 (random$ x state)))
  :hints (("Goal" :in-theory (enable random$)))
  :rule-classes (:type-prescription))

;; properties of append on lit lists.. lists

(defthm append-lit-listp
  (implies (and (lit-listp x) (lit-listp y))
           (lit-listp (acl2::append$! x y)))
  :hints (("Goal" :in-theory (enable acl2::append$!))))

(defthm append-lit-list-listp
  (implies (and (lit-list-listp x) (lit-list-listp y))
           (lit-list-listp (acl2::append$! x y)))
  :hints (("Goal" :in-theory (enable acl2::append$!))))

(define nth! ((ndx natp) lst)
  (cond ((atom lst) nil)
        ((zp ndx) (first lst))
        ((atom (rest lst)) (first lst))
        (t (nth! (1- ndx) (rest lst)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;; exs$ stobj definition ...
;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *nested-stobjs* '((exs$   . exs$p)
                            (ipasir . ipasirp)
                            (rand   . randp)
                            (lvals  . lvalsp)
                            (aignet . aignetp)))

(in-theory (disable ipasirp randp lvalsp aignetp))

(define fld-listp (x)
  (or (null x)
      (and (consp x)
           (consp (car x))
           (consp (cdar x))
           (null  (cddar x))
           (symbolp (caar x))
           (or (symbolp (cadar x))
               (and (consp (cadar x))
                    (null (cdadar x))
                    (symbolp (caadar x))))
           (fld-listp (cdr x)))))

(defmacro snip (&rest lst)
  `(intern-in-package-of-symbol (symbol-name (snap ,@lst)) 'EXSIM::foo))

(defconst *def-env-descr*
  (make-env-descr :env-type nil :env-path ()))

(define ftyp->stobj-type ((ftyp symbolp))  
  (cond ((assoc ftyp *nested-stobjs*) ftyp)
        ((eq ftyp 'natp)              '(integer 0 *))
        ((eq ftyp 'symbolp)           'symbol)
        ((eq ftyp 'stringp)           'string)
        (t                            (list 'satisfies ftyp))))

(define ftyp->stobj-init ((ftyp symbolp))
  (cond ((assoc ftyp *nested-stobjs*) nil)
        ((eq ftyp 'natp)         0)
        ((eq ftyp 'symbolp)      nil)
        ((eq ftyp 'stringp)      "")
        ((eq ftyp 'sv::svar-p)   :bad)
        ((eq ftyp 'env-descr-p)  *def-env-descr*)
        ((eq ftyp 'sim-params-p) *def-sim-params*)
        ((eq ftyp 'vcd-restor-p) *def-vcd-restor*)
        (t                       nil)))

(define make-stobj-fld ((name symbolp) (ftyp symbolp) is-array)
  (b* ((st-type (ftyp->stobj-type ftyp))
       (st-init (ftyp->stobj-init ftyp))
       (st-type (if is-array (list 'array st-type (list 10)) st-type)))
    (append (list name :type st-type) 
            (and st-init  (list :initially st-init))
            (and is-array (list :resizable t)))))

(in-theory (enable fld-listp))

(define make-stobj-flds (flds)
  :guard (fld-listp flds)
  (if (endp flds) ()
    (let* ((name (caar flds))
           (ftyp (if (consp (cadar flds)) (caadar flds) (cadar flds)))
           (is-array (consp (cadar flds))))
      (cons (make-stobj-fld name ftyp is-array)
            (make-stobj-flds (cdr flds))))))

(define make-fld-thms ((fnam symbolp) (ftyp symbolp) is-array (name symbolp) (n natp))
  (let* ((etyp (and is-array
                    (if (assoc ftyp *nested-stobjs*)
                        (cdr (assoc ftyp *nested-stobjs*))
                      ftyp)))
         (ftyp (cond (is-array (snip fnam 'p))
                     ((assoc ftyp *nested-stobjs*)
                      (cdr (assoc ftyp *nested-stobjs*)))
                     (t ftyp))))
    (append (list `(defthm ,(snip fnam '- ftyp)
                     (implies (,(snip name 'p) ,name)
                              (,ftyp (nth ,n ,name))))
                  `(defthm ,(snip 'update- fnam '- name 'p)
                     (implies (and (,(snip name 'p) ,name) (,ftyp val))
                              (,(snip name 'p) (update-nth ,n val ,name)))))
            (and is-array
                 (list `(defthm ,(snip fnam '- etyp)
                          (implies (and (,ftyp x) (< i (len x)))
                                   (,etyp (nth i x)))
                          :hints (("Goal" :in-theory (enable nth len))))
                       `(defthm ,(snip 'update- fnam '- etyp)
                          (implies (and (,ftyp x) (,etyp val))
                                   (,ftyp (update-nth i val x)))
                          :hints (("Goal" :in-theory (enable update-nth))))))
            (and (not is-array)
                 (member-eq ftyp '(symbolp natp))
                 (list `(defthm ,(snip fnam '- ftyp '-fc)
                          (implies (,(snip name 'p) ,name)
                                   (,ftyp (nth ,n ,name)))
                          :rule-classes :forward-chaining))))))

(define make-flds-thms (flds (name symbolp) &key ((n natp) '0))
  :guard (fld-listp flds)
  (if (endp flds) ()
    (let* ((fnam (caar flds))
           (ftyp (if (consp (cadar flds)) (caadar flds) (cadar flds)))
           (is-array (consp (cadar flds))))
      (append! (make-fld-thms fnam ftyp is-array name n)
               (make-flds-thms (cdr flds) name :n (1+ n))))))

(defmacro define-stobj (name &rest flds)
  (declare (xargs :guard (and (symbolp name) (fld-listp flds))))
  `(progn (defstobj ,name ,@(make-stobj-flds flds) :inline t)
          (in-theory (enable length))
          (in-theory (disable nth update-nth))
          (defthm ,(snip 'create- name '- name 'p)
            (,(snip name 'p) (,(snip 'create- name))))
          ,@(make-flds-thms flds name)
          (in-theory (disable length
                              ,(snip name 'p)
                              ,(snip 'create- name)))))

(define-stobj exs$
  ;; nested stobjs under exs$:
  (exs$-solver      ipasir)      ;; ipasir isat stobj
  (exs$-random      rand)        ;; random state stobj
  (exs$-aignet      aignet)      ;; aignet storing compiled design
  (exs$-cnl-map     (lvals))     ;; 2D array map: (CYCLE -> (NDX -> LIT))
  ;; design related maps loaded with compilation to aignet:
  (exs$-ndx->var    ndx->var-map-p)
  (exs$-var->ndx    var->ndx-map-p)
  (exs$-var->port   var->port-map-p)
  (exs$-var->supp   var->supp-map-p)
  ;; cycle indexes satisfying: 0 <= lo <= mid <= hi <= max-cycle
  (exs$-lo          natp)        ;; [lo,mid,hi] define the window of..
  (exs$-mid         natp)        ;; ..symbolic evaluation that progresses
  (exs$-hi          natp)        ;; 
  (exs$-max-cycle   natp)        ;; max-cycle search bound from input waves
  (exs$-next-base   natp)        ;; the next base sat literal to use
  (exs$-curr-cnf    lit-list-listp) ;; accumulated set of clauses (SATLINK only)
  (exs$-fail-ndxs   ndx-list-p)  ;; List of ndxs (outs) we are checking for failure.
  (exs$-free-ndxs   ndx-list-p)  ;; List of ndxs (ins) we bind to free variables.
  (exs$-rand-ndxs   ndx-list-p)  ;; List of ndxs (ins) we bind to random values.
  (exs$-styp-lkup   styp-lkup-p) ;; fast-alist looking up if ndx is free, rand, etc.
  (exs$-return-vmap exs-vmap-p)
  (exs$-reset-vmap  exs-vmap-p)
  (exs$-var-count   natp)
  (exs$-cls-count   natp)
  (exs$-sat-result  symbolp)
  (exs$-use-satlink symbolp)    ;; should be boolean
  (exs$-verbose     symbolp)    ;; should be boolean
  (exs$-out-ctbls   out-ctbls-p)
  (exs$-out-aig-ctbl cyc->ndx->aig-p)
  (exs$-in-aig-ctbl  cyc->ndx->aig-p)
  ;;
  (exs$-compute-aigs symbolp)   ;; should be boolean
  (exs$-next-aig-base natp)        ;; the next base sat literal to use
  (exs$-get-aigs-ins  sv::svarlist-p)
  (exs$-get-aigs-outs sv::svarlist-p)
  ;;
  (exs$-last-clean  natp)
  (exs$-num-steps   natp)
  (exs$-prev-choice true-listp)
  ;;
  (exs$-mod-name    stringp)
  (exs$-top-mod     stringp)
  (exs$-vcd-restor  vcd-restor-p)
  (exs$-release-sat symbolp)    ;; should be boolean
  (exs$-vcd-prefix  true-listp)
  (exs$-sim-params  sim-params-p)
  ;;
  (exs$-fchk-rslt   fchk-rslt-map-p)
  ;;
  (exs$-nxt-tbl     nxt-tbl-p)
  (exs$-mod-tbl     exs-mod-tbl-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;; nested ipasir routines...
;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solver-rdy (ipasir)
  (and (not (eq (ipasir-get-status ipasir) :undef))
       (ipasir-empty-new-clause ipasir)))

(define solver-sat (ipasir)
  (eq (ipasir-get-status ipasir) :sat))

(define solver-unsat (ipasir)
  :enabled t
  (eq (ipasir-get-status ipasir) :unsat))

(define solver-is-assume ((lit litp) ipasir)
  :enabled t
  (and (not (eq (ipasir-get-status ipasir) :undef))
       (if (eq (ipasir-get-status ipasir) :unsat)
           (member-equal lit (ipasir::ipasir-solved-assumption ipasir))
         (member-equal lit (ipasir::ipasir-get-assumption ipasir)))))

(define solver-are-assumes ((lits lit-listp) ipasir)
  :enabled t
  (or (atom lits)
      (and (solver-is-assume (first lits) ipasir)
           (solver-are-assumes (rest lits) ipasir))))

(define solver-undf (ipasir)
  (eq (ipasir-get-status ipasir) :undef))

(in-theory (enable solver-sat solver-rdy solver-undf)) ;; we want these enabled.

(define exs-ipasir-assume-cube ((cube lit-listp) ipasir)
  :guard (solver-rdy ipasir)
  :returns (new-ipasir solver-rdy :hyp (solver-rdy ipasir))
  (if (endp cube) ipasir
    (b* ((ipasir (ipasir::ipasir-assume ipasir (first cube))))
      (exs-ipasir-assume-cube (rest cube) ipasir))))

(defthm exs-ipasir-assume-cube-status
  (implies (not (equal (ipasir$a->status ipasir) :undef))
           (not (equal (ipasir$a->status (exs-ipasir-assume-cube cube ipasir)) :undef)))
  :hints (("Goal" :in-theory (enable exs-ipasir-assume-cube))))

(defthm exs-ipasir-assume-cube-new-clause
  (equal (ipasir$a->new-clause (exs-ipasir-assume-cube cube ipasir))
         (ipasir$a->new-clause ipasir))
  :hints (("Goal" :in-theory (enable exs-ipasir-assume-cube))))

(define compute-ipasir-lit ((lit litp) &key (ipasir 'ipasir))
  :guard (solver-sat ipasir)
  :returns (rslt litp)
  (if (bitp lit) (lit-fix lit)
    (b* ((val (ipasir-val ipasir lit)))
      (if (not val) (lit-fix lit) val))))

(define compute-ipasir-nmap ((nmap ndx-map-p)
                             (lkup styp-lkup-p)
                             &key 
                             ((model lit-model-p) 'nil)
                             ((frees lit-listp) 'nil)
                             ((fails lit-listp) 'nil)
                             (ipasir 'ipasir))
  :guard (solver-sat ipasir)
  :returns (mv (model lit-model-p) (frees lit-listp) (fails lit-listp))
  (if (endp nmap)
      (mv (lit-model-fix model) (lit-list-fix frees) (lit-list-fix fails))
    (b* ((ndx  (caar nmap))
         (styp (cdr (hons-get ndx lkup)))
         (lit  (cdar nmap))
         (val  (compute-ipasir-lit lit))
         (vlit (and (bitp val)
                    (if (eql val 0) (lit-negate lit) lit))))
;         (- (and (eq styp :fail)
;                 (cw "ipasir fail:~x0~%"
;                     (list ndx styp lit val vlit)))))
      (compute-ipasir-nmap (rest nmap) lkup
                           :model (if vlit
                                      (acons! lit val model)
                                    model)
                           :fails (if (and (eq styp :fail) (eql val 1))
                                      (cons lit fails)
                                    fails)
                           :frees (if (and (eq styp :free) vlit)
                                      (cons vlit frees)
                                    frees)))))

(define compute-ipasir-result ((ctbl ndx-ctbl-p)
                               (lkup styp-lkup-p)
                               &key
                               ((model lit-model-p) 'nil)
                               ((frees lit-listp) 'nil)
                               ((fails lit-listp) 'nil)
                               (ipasir 'ipasir))
  :guard (solver-sat ipasir)
  :returns (mv (model lit-model-p) (frees lit-listp) (fails lit-listp))
  (if (endp ctbl)
      (mv (lit-model-fix (make-fast-alist model))
          (lit-list-fix frees) (lit-list-fix fails))
    (b* (((mv model frees fails)
          (compute-ipasir-nmap (cdar ctbl) lkup
                               :model model :frees frees :fails fails)))
      (compute-ipasir-result (rest ctbl) lkup
                             :model model :fails fails :frees frees))))

(define negate-lits ((lits lit-listp) &key ((rslt lit-listp) 'nil))
  :returns (rslt lit-listp)
  (if (endp lits) (lit-list-fix rslt)
    (negate-lits (rest lits) :rslt (cons (lit-negate (first lits)) rslt))))

(define exs-find-lits-to-drop ((lits lit-listp)
                               &key
                               ((rslt lit-listp) 'nil)
                               (ipasir 'ipasir))
  :guard (and (solver-unsat ipasir)
              (solver-are-assumes lits ipasir))
  :returns (rslt lit-listp)
  (if (endp lits) (lit-list-fix rslt)
    (exs-find-lits-to-drop (rest lits)
                           :rslt
                           (if (eql (ipasir::ipasir-failed
                                     ipasir (first lits))
                                    0)
                               (cons (first lits) rslt)
                             rslt))))

(define exs-drop-from-model ((dropped lit-listp) (model lit-model-p))
  :returns (model lit-model-p)
  (if (endp dropped) (lit-model-fix model)
    (exs-drop-from-model (rest dropped)
                         (hons-acons (first dropped) 2
                                     (hons-acons (lit-negate (first dropped)) 2 model)))))

(define exs-build-rslt-nmap ((nmap ndx-map-p) (model lit-model-p)
                             &key ((rslt ndx-map-p) 'nil))
  :returns (rslt ndx-map-p)
  (if (endp nmap) (ndx-map-fix rslt)
    (exs-build-rslt-nmap (rest nmap) model
                         :rslt
                         (b* ((lit (cdar nmap))
                              (val (cdr (hons-get lit model))))
                           (if (bitp val)
                               (acons! (caar nmap) val rslt)
                             rslt)))))

(define exs-build-rslt-ctbl ((ctbl ndx-ctbl-p) (model lit-model-p)
                             &key ((rslt ndx-ctbl-p) 'nil))
  :returns (rslt ndx-ctbl-p)
  (if (endp ctbl) (ndx-ctbl-fix rslt)
    (exs-build-rslt-ctbl (rest ctbl) model
                         :rslt
                         (acons! (caar ctbl)
                                 (exs-build-rslt-nmap (cdar ctbl) model)
                                 rslt))))

(defthm solver-are-assumes-solve
  (implies (and (not (equal (ipasir-get-status ip) :unsat))
                (not (equal (ipasir-get-status ip) :undef))
                (equal (mv-nth 0 (ipasir::ipasir-solve$a ip)) :unsat))
           (equal (solver-are-assumes lits (mv-nth 1 (ipasir::ipasir-solve$a ip)))
                  (solver-are-assumes lits ip))))

(defthm solver-are-assumes-assume-1
  (implies (and (not (equal (ipasir-get-status ip) :unsat))
                (solver-are-assumes lits ip))
           (solver-are-assumes lits (ipasir::ipasir-assume$a ip a))))

(defthm solver-are-assumes-assume-cube-1
  (implies (and (not (equal (ipasir-get-status ip) :unsat))
                (not (equal (ipasir-get-status ip) :undef))
                (solver-are-assumes lits ip))
           (solver-are-assumes lits (exs-ipasir-assume-cube frees ip)))
  :hints (("Goal" :in-theory (enable exs-ipasir-assume-cube))))

(defthm solver-are-assumes-assume-cube-2
  (equal (ipasir$a->status (exs-ipasir-assume-cube frees ip))
         (if (consp frees) :input (ipasir$a->status ip)))
  :hints (("Goal" :in-theory (enable exs-ipasir-assume-cube))))

(defthm member-assume-cube
  (implies (and (not (equal (ipasir-get-status ip) :unsat))
                (not (equal (ipasir-get-status ip) :undef))
                (member-equal a (ipasir::ipasir$a->assumption ip)))
           (member-equal a (ipasir::ipasir$a->assumption
                            (exs-ipasir-assume-cube x ip))))
  :hints (("Goal" :in-theory (enable exs-ipasir-assume-cube))))

(defthm member-ipasir-assume
  (implies (litp a)
           (member-equal a (ipasir::ipasir$a->assumption (ipasir::ipasir-assume$a ip a)))))

(defthm solver-are-assumes-assume-cube-3
  (implies (and (not (equal (ipasir-get-status ip) :unsat))
                (not (equal (ipasir-get-status ip) :undef))
                (lit-listp lits)
                (consp lits))
           (solver-are-assumes lits (exs-ipasir-assume-cube lits ip)))
  :hints (("Goal" :in-theory (enable exs-ipasir-assume-cube))))

(define exsim-ipasir-solve-load ((ctbl ndx-ctbl-p) (lkup styp-lkup-p) ipasir)
  :guard (solver-rdy ipasir)
  :returns (mv status (rslt ndx-ctbl-p) (new-ipasir solver-rdy))
  (b* (((mv status ipasir)          (ipasir-solve ipasir))
       ((unless (eq status :sat))   (mv status nil ipasir))
       ((mv model frees fails)      (compute-ipasir-result ctbl lkup))
;       (-  (cw "fails:~x0~%" fails))
;       (-  (cw "frees:~x0~%" frees))
       ((when (atom frees))         (mv :sat (raise "should have some free bits!") ipasir))
       ((when (atom fails))         (mv :sat (raise "should have some fail bits!") ipasir))
       (ipasir                      (exs-ipasir-assume-cube (negate-lits fails) ipasir))
       (ipasir                      (exs-ipasir-assume-cube frees ipasir))
       ((mv status ipasir)          (ipasir-solve ipasir))
       ((unless (eq status :unsat)) (mv :sat (raise "expected UNSAT!:~x0~%" status) ipasir))
       ((when (not (solver-are-assumes frees ipasir)))
        (mv :sat (raise "BOZO -- stupid check.. need guard proof!") ipasir))
       (dropped-frees               (exs-find-lits-to-drop frees))
       (model                       (exs-drop-from-model dropped-frees model))
       (rslt                        (exs-build-rslt-ctbl ctbl model)))
    (mv :sat rslt ipasir)))

(define exsim-ipasir-reset-solver (ipasir)
  :guard   (solver-rdy ipasir)
  :returns (new-ipasir solver-rdy)
  (b* ((ipasir (ipasir::ipasir-release ipasir)))
    (ipasir::ipasir-reinit ipasir)))

(define exsim-ipasir-init-solver (ipasir state)
  :guard   (solver-undf ipasir)
  :returns (mv (new-ipasir solver-rdy) state)
  (ipasir::ipasir-init ipasir state))

;;; our main exs$ ipasir interface functions with stobj-lets to operate on nested ipasir.

(define exs-solver-rdy (exs$) 
  (or (exs$-use-satlink exs$)
      (stobj-let ((ipasir (exs$-solver exs$))) (rslt) (solver-rdy ipasir) rslt)))

(define exs-solver-undf (exs$) 
  (or (exs$-use-satlink exs$)
      (stobj-let ((ipasir (exs$-solver exs$))) (rslt) (solver-undf ipasir) rslt)))

(in-theory (enable exs-solver-rdy exs-solver-undf)) ;; we want these enabled as well for now..

(defthm solver-rdy-update-nth
  (implies (and (natp i) (not (equal i *EXS$-SOLVER*))
                (not (equal i *EXS$-USE-SATLINK*)))
           (equal (exs-solver-rdy (update-nth i v exs$))
                  (exs-solver-rdy exs$))))

(defthm solver-undf-update-nth
  (implies (and (natp i) (not (equal i *EXS$-SOLVER*))
                (not (equal i *EXS$-USE-SATLINK*)))
           (equal (exs-solver-undf (update-nth i v exs$))
                  (exs-solver-undf exs$))))

(defthm create-exs$-undf
  (exs-solver-undf (create-exs$))
  :hints (("Goal" :in-theory (enable solver-undf create-exs$))))

(define exsim-load-cnf ((cnf lit-list-listp) &key (exs$ 'exs$))
  :guard   (exs-solver-rdy exs$)
  :returns (new-exs$ exs-solver-rdy)
  (if (exs$-use-satlink exs$) exs$
    (b* ((exs$ (update-exs$-cls-count (+ (length cnf) (exs$-cls-count exs$)) exs$)))
      (stobj-let ((ipasir (exs$-solver exs$)))
                 (ipasir) (ipasir-add-clauses ipasir cnf) 
                 exs$))))

(define exsim-release-isat (&key (exs$ 'exs$))
  :guard   (exs-solver-rdy exs$)
  :returns (new-exs$ exs-solver-undf)
  (if (exs$-use-satlink exs$) exs$
    (b* ((exs$ (update-exs$-cls-count 0 exs$)))
      (stobj-let ((ipasir (exs$-solver exs$)))
                 (ipasir) (ipasir-release ipasir)
                 exs$))))

(in-theory (disable solver-rdy solver-undf solver-sat))

(define exsim-assume-cube ((cube lit-listp) &key (exs$ 'exs$))
  :guard   (exs-solver-rdy exs$)
  :returns (new-exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (if (exs$-use-satlink exs$) exs$
    (stobj-let ((ipasir (exs$-solver exs$)))
               (ipasir) (exs-ipasir-assume-cube cube ipasir)
               exs$)))

(local (include-book "arithmetic-5/top" :dir :system))

(define exsim-solve-cnf ((ctbl ndx-ctbl-p) &key (exs$ 'exs$))
  :guard   (exs-solver-rdy exs$)
  :returns (mv status (rslt ndx-ctbl-p) (new-exs$ exs-solver-rdy))
  (if (exs$-use-satlink exs$) 
      (prog2$ (raise "internal error: should not call solve-cnf in satlink mode!")
              (mv nil nil exs$))
    ;; BOZO NOTE -- the following is "grossly" approximate. Unfortunately, to
    ;; get an accurate clause count from IPASIR, we need to add a function to
    ;; its interface to return the number of active clauses in the
    ;; database. When we "solve", we are resolving and propagating information
    ;; about the current set of clauses (along with the fact that many of them
    ;; will not be relevant to subsequent solves.. so we crudely just take this
    ;; count in half.. the "real" solution is to add the extension to the
    ;; ipasir interface and get an accurate count from there).
    (b* ((lkup (exs$-styp-lkup exs$))
         (exs$ (update-exs$-cls-count (floor (exs$-cls-count exs$) 2) exs$)))
      (stobj-let ((ipasir (exs$-solver exs$)))
                 (status binds ipasir) (exsim-ipasir-solve-load ctbl lkup ipasir) 
                 (mv status binds exs$)))))

(define exsim-reset-isat (&key (exs$ 'exs$))
  :guard   (exs-solver-rdy exs$)
  :returns (new-exs$ exs-solver-rdy)
  (if (exs$-use-satlink exs$) exs$
    (b* ((exs$ (update-exs$-cls-count 0 exs$)))
      (stobj-let ((ipasir (exs$-solver exs$)))
                 (ipasir) (exsim-ipasir-reset-solver ipasir)
                 exs$))))

(define exsim-init-isat (&key (exs$ 'exs$) (state 'state))
  :guard   (exs-solver-undf exs$)
  :returns (mv (new-exs$ exs-solver-rdy) state)
  (if (exs$-use-satlink exs$) (mv exs$ state)
    (b* ((exs$ (update-exs$-cls-count 0 exs$)))
      (stobj-let ((ipasir (exs$-solver exs$)))
                 (ipasir state) (exsim-ipasir-init-solver ipasir state)
                 (mv exs$ state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;; nested random routines...
;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exs-init-random (seed &key (exs$ 'exs$))
  :returns (new-exs$ exs-solver-undf :hyp (exs-solver-undf exs$))
  (if (not (natp seed)) exs$
    (stobj-let ((rand (exs$-random exs$)))
               (rand) (update-seed seed rand)
               exs$)))

(define exs-next-random ((max posp) &key (exs$ 'exs$))
  :returns (mv rslt (new-exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  (stobj-let ((rand (exs$-random exs$)))
             (rslt rand) (genrandom max rand)
             (mv rslt exs$)))

(define revapp! ((x true-listp) y)
  (if (endp x) y (revapp! (cdr x) (cons (car x) y))))

(defthm lit-list-listp-implies-true-listp
  (implies (lit-list-listp x) (true-listp x)))

(defthm lit-list-listp-revapp!
  (implies (and (lit-list-listp x) (lit-list-listp y))
           (lit-list-listp (revapp! x y)))
  :hints (("Goal" :in-theory (enable revapp!))))

(in-theory (disable exs-solver-rdy exs-solver-undf)) ;; now we disable these..
