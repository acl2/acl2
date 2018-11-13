;; exloop.lisp
;;
;; This book defines the main search loop (exsim-main-loop) and the function
;; used to initialize the exs$ stobj for the main-loop: exsim-init-loop. These
;; two functions are the primary exports of this book.

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
(include-book "misc/file-io" :dir :system)
(include-book "misc/random" :dir :system)
(include-book "exbase")
(include-book "svcnf")

(defsection exsim-main-search-loop-and-init
  :parents (exsim)
  :short "Book defining exsim main search loop and initialization"
  :autodoc nil
  :long "
<p> This book defines the @({ (exsim-main-loop) }) which performs the main
  search loop for exsim. During each step of the loop, either a step-fail, a
  step-free, a check-fails, or a cleanup or completion step is performed. The
  step-fail step add CNF clauses for the next fail bits to be considered. The
  step-free step takes the oldest free variables and binds them to
  literals. The check-fails checks the current CNF clause database for
  satisfiability of any of the fails currently unresolved. The function @({
  (exsim-init-loop) }) initializes the exs$ stobj to perform the main search
  loop. </p> ")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;; exsim-step-free
;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exs-add-equiv-lits ((a litp) (b litp) &key (exs$ 'exs$))
  :guard   (exs-solver-rdy exs$)
  :returns (new-exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  ;; equiv is: (a -> b) && (!a -> !b) .. or (!a || b) && (a || !b)
  (b* ((clauses (list (list (lit-negate a) b) (list a (lit-negate b)))))
    (if (exs$-use-satlink exs$)
        (update-exs$-curr-cnf (append clauses (exs$-curr-cnf exs$)) exs$)
      (exsim-load-cnf clauses))))

(define exs-add-ground-lit ((a litp) &key (exs$ 'exs$))
  :guard (exs-solver-rdy exs$)
  :returns (new-exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (if (exs$-use-satlink exs$)
      (update-exs$-curr-cnf (cons (list a) (exs$-curr-cnf exs$)) exs$)
    (exsim-load-cnf (list (list a)))))

(define exs-add-ground-lits ((lits lit-listp) &key (exs$ 'exs$))
  :guard (exs-solver-rdy exs$)
  :returns (new-exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (if (endp lits) exs$
    (b* ((exs$ (exs-add-ground-lit (first lits))))
      (exs-add-ground-lits (rest lits)))))

(define merge-new-val ((ndx natp) (lit litp) override 
                       lvals (rslt lit-listp))
  :returns (mv (rslt lit-listp :hyp :guard) lvals)
  (if (>= ndx (lits-length lvals))
      (mv (raise "oob lvals ndx:~x0~%" ndx) lvals)
    (b* ((curr  (get-lit ndx lvals))
         (lvals (cond ((or (not (bitp curr)) override)
                       (set-lit ndx lit lvals))
                      ((not (bitp lit)) lvals)
                      ((eql lit curr)   lvals)
                      (t (prog2$ (raise "internal error: encountered mismatch:~x0~%"
                                        (list ndx lit))
                                 lvals)))))
      (mv (cond ((btm-or-bit curr) rslt)
                ((eql lit 0) (cons (lit-negate curr) rslt))
                ((eql lit 1) (cons curr rslt))
                (t rslt))
          lvals))))

(define merge-new-vals* ((vals ndx-map-p) lvals override
                         &key ((rslt lit-listp) 'nil))
  :returns (mv (rslt lit-listp) lvals)
  (if (endp vals) (mv (lit-list-fix rslt) lvals)
    (b* (((mv rslt lvals)
          (merge-new-val (caar vals) (cdar vals) override lvals rslt)))
      (merge-new-vals* (rest vals) lvals override :rslt rslt))))

(define merge-new-vals ((vals ndx-map-p) (cyc natp) override
                        &key (exs$ 'exs$))
  :returns (mv (lits lit-listp)
               (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  (if (>= cyc (exs$-cnl-map-length exs$))
      (mv (raise "oob cnl-tbl index:~x0~%" cyc) exs$)
    (stobj-let ((lvals (exs$-cnl-mapi cyc exs$)))
               (lits lvals) (merge-new-vals* vals lvals override)
               (mv lits exs$))))

(define exs-rand-free-choose ((ndxs ndx-list-p) 
                              &key ((rslt ndx-map-p) 'nil) (exs$ 'exs$))
  :guard-hints (("Goal" :in-theory (enable exs-next-random mv-nth litp)))
  :returns (mv (rslt ndx-map-p)
               (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  (if (endp ndxs) (mv (ndx-map-fix rslt) exs$)
    (b* ((ndx (first ndxs))
         ((mv bit exs$) (exs-next-random 2)))
      (exs-rand-free-choose (rest ndxs) :rslt (acons! ndx bit rslt)))))

(define filter-out-styps ((map ndx-map-p) 
                          (lkup styp-lkup-p) 
                          (styps symbol-listp)
                          &key ((rslt ndx-map-p) 'nil))
  :returns (rslt ndx-map-p)
  (if (endp map) (ndx-map-fix rslt)
    (filter-out-styps (rest map) lkup styps
                      :rslt 
                      (if (member-eq (cdr (hons-get (caar map) lkup)) styps)
                          rslt
                        (cons (first map) rslt)))))

(define exsim-increment-lo (&key (exs$ 'exs$))
  :returns (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (b* ((lo (exs$-lo exs$))
       (exs$ (update-exs$-lo (1+ lo) exs$)))
    (if (eql (exs$-mid exs$) lo) (update-exs$-mid (1+ lo) exs$) exs$)))

;;
(progn
(defthm ndx-map-fast-alist-fork
  (implies (and (ndx-map-p x) (ndx-map-p y))
           (ndx-map-p (fast-alist-fork x y))))
(defthm ndx-map-last
  (implies (ndx-map-p x) (ndx-map-p (last x))))
(defthm ndx-ctbl-fast-alist-fork
  (implies (and (ndx-ctbl-p x) (ndx-ctbl-p y))
           (ndx-ctbl-p (fast-alist-fork x y))))
(defthm ndx-ctbl-last
  (implies (ndx-ctbl-p x) (ndx-ctbl-p (last x))))
)
;;

(defthm exs$-hi-merge-new-vals
  (equal (nth *EXS$-HI* (mv-nth 1 (merge-new-vals vals cyc override)))
         (nth *EXS$-HI* exs$))
  :hints (("Goal" :in-theory (enable merge-new-vals))))

(defthm exs$-styp-lkup-merge-new-vals
  (equal (nth *EXS$-STYP-LKUP* (mv-nth 1 (merge-new-vals vals cyc override)))
         (nth *EXS$-STYP-LKUP* exs$))
  :hints (("Goal" :in-theory (enable merge-new-vals))))

(defthm exs$-cnl-map-merge-new-vals
  (implies (and (natp cyc) (< cyc (len (nth *EXS$-CNL-MAPI* exs$))))
           (equal (len (nth *EXS$-CNL-MAPI* (mv-nth 1 (merge-new-vals vals cyc override))))
                  (len (nth *EXS$-CNL-MAPI* exs$))))
  :hints (("Goal" :in-theory (enable merge-new-vals))))

(defthm exs$-hi-add-ground-lits
  (equal (nth *EXS$-HI* (exs-add-ground-lits lits))
         (nth *EXS$-HI* exs$))
  :hints (("Goal" :in-theory (enable exs-add-ground-lits 
                                     exsim-load-cnf
                                     exs-add-ground-lit))))

(defthm exs$-lo-add-ground-lits
  (equal (nth *EXS$-LO* (exs-add-ground-lits lits))
         (nth *EXS$-LO* exs$))
  :hints (("Goal" :in-theory (enable exs-add-ground-lits 
                                     exsim-load-cnf
                                     exs-add-ground-lit))))

(defthm exs$-lkup-add-ground-lits
  (equal (nth *EXS$-STYP-LKUP* (exs-add-ground-lits lits))
         (nth *EXS$-STYP-LKUP* exs$))
  :hints (("Goal" :in-theory (enable exs-add-ground-lits 
                                     exsim-load-cnf
                                     exs-add-ground-lit))))

(defthm exs$-cnl-map-add-ground-lits
  (equal (nth *EXS$-CNL-MAPI* (exs-add-ground-lits lits))
         (nth *EXS$-CNL-MAPI* exs$))
  :hints (("Goal" :in-theory (enable exs-add-ground-lits 
                                     exsim-load-cnf
                                     exs-add-ground-lit))))
;;

(define exs-forward-reduce-loop ((new-vals ndx-map-p) (cyc natp)
                                 &key 
                                 (force-forward 'nil) (override-merge 'nil)
                                 ((rslt natp) '0) (exs$ 'exs$))
  :guard (and (<= cyc (exs$-hi exs$))
              (< (exs$-hi exs$) (exs$-cnl-map-length exs$))
              (exs-solver-rdy exs$))
  :measure (nfix (- (exs$-hi exs$) cyc))
  :returns (mv (rslt natp)
               (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  (b* (((mv lits exs$) (merge-new-vals new-vals cyc override-merge))
       (exs$ (exs-add-ground-lits lits))
       (rslt (+ (len lits) rslt)))
    (if (or (and (endp new-vals) (not force-forward))
            (mbe :logic (zp (- (exs$-hi exs$) cyc))
                 :exec  (eql cyc (exs$-hi exs$))))
        (mv (lnfix rslt) exs$)
      (b* ((newv (exs-forward-reduce (1+ cyc)))
           (n-nv (filter-out-styps newv (exs$-styp-lkup exs$) 
                                   '(:free :rand :wave))))
        (exs-forward-reduce-loop n-nv (1+ cyc)
                                 :override-merge override-merge
                                 :force-forward force-forward
                                 :rslt rslt)))))

(define exs-check-bits-lvals ((lkup styp-lkup-p)
                              &key ((ndx natp) '(lits-length lvals)) (lvals 'lvals))
  :guard (<= ndx (lits-length lvals))
  (if (zp ndx) nil
    (b* ((ndx (1- ndx))
         (lit (get-lit ndx lvals))
         ((when (and (not (bitp lit)) 
                     (not (member-eq (cdr (hons-get ndx lkup))
                                     '(:free :rand :wave)))))
          (list ndx lit)))
      (exs-check-bits-lvals lkup :ndx ndx))))

(define exs-check-all-bits ((cyc natp) &key (exs$ 'exs$))
  (if (not (< cyc (exs$-cnl-map-length exs$)))
      (raise "internal error: cyc out of bounds!:~x0~%"
             (list cyc (exs$-cnl-map-length exs$)))
    (b* ((lkup (exs$-styp-lkup exs$)))
      (stobj-let ((lvals (exs$-cnl-mapi cyc exs$)))
                 (failed) (exs-check-bits-lvals lkup)
                 (and failed 
                      (raise "Encountered signal which did not reduce to 0/1:~x0~%"
                             failed))))))

(define exs-decr-var-count ((adj natp) &key (exs$ 'exs$))
  :returns (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (b* ((count (exs$-var-count exs$))
       ((when (< count adj))
        ;; (prog2$ (raise "Active lit count going negative.. should not happen!")
        ;;        exs$)))
        (update-exs$-var-count 0 exs$)))
    (update-exs$-var-count (- count adj) exs$)))

(defthm exs$-lo-exs-rand-free-choose
  (equal (nth *EXS$-LO* (mv-nth 1 (exs-rand-free-choose ndxs :rslt rslt)))
         (nth *EXS$-LO* exs$))
  :hints (("Goal" :in-theory (enable exs-rand-free-choose exs-next-random))))

(defthm exs$-hi-exs-rand-free-choose
  (equal (nth *EXS$-HI* (mv-nth 1 (exs-rand-free-choose ndxs :rslt rslt)))
         (nth *EXS$-HI* exs$))
  :hints (("Goal" :in-theory (enable exs-rand-free-choose exs-next-random))))

(define exsim-step-free (&key (exs$ 'exs$))
  :guard (and (<= (exs$-lo exs$) (exs$-hi exs$))
              (exs-solver-rdy exs$))
  :returns (mv rslt (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  (b* (((mv in-vals exs$) (exs-rand-free-choose (exs$-free-ndxs exs$)))
       ((when (not (< (exs$-hi exs$) (exs$-cnl-map-length exs$))))
        (mv (raise "internal error: insufficient cnl-map size!") exs$))
       (cyc (exs$-lo exs$))
       ((mv diff exs$) (exs-forward-reduce-loop in-vals cyc))
       (exs$ (exs-decr-var-count diff))
       (-    (exs-check-all-bits cyc))
       (exs$ (exsim-increment-lo)))
    (mv nil exs$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;; exsim-step-fail
;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define resolve-ndx-map* ((n-map ndx-map-p)
                          (styp-lkup styp-lkup-p)
                          &key
                          ((ndxs ndx-list-p) 'nil)
                          ((eqvs ndx-map-p) 'nil)
                          (lvals 'lvals))
  :returns (mv (ndxs ndx-list-p) (eqvs ndx-map-p) lvals)
  (if (endp n-map)
      (mv (ndx-list-fix ndxs) (ndx-map-fix eqvs) lvals)
    (b* ((var   (caar n-map))
         (lit-n (cdar n-map))
         ((when (not (< var (lits-length lvals))))
          (mv (raise "internal error: illegal ndx out of bounds for lvals!")
              () lvals))
         (lit-p (get-lit var lvals))
         ;; (- (cw "resolve:~x0~%" (list var lit-n lit-p)))
         )
      (cond
       ;; NOTE - I like having the following check, but it could be removed
       ;; and/or proven to be impossible..
       ((or (bitp lit-p) (bitp lit-n))
        (mv (raise "unexpected bit lit encountered!") () lvals))
       ((btm-litp lit-p)
        (b* ((lvals (set-lit var lit-n lvals)))
          (resolve-ndx-map* (rest n-map) styp-lkup :eqvs eqvs
                            ;; NOTE -- for free variables, we do not add
                            ;;         it to outgoing indexes.
                            :ndxs (if (eq (cdr (hons-get var styp-lkup)) :free)
                                      ndxs
                                    (cons var ndxs)))))
       (t
        (resolve-ndx-map* (rest n-map) styp-lkup :ndxs ndxs
                          :eqvs (acons! lit-n lit-p eqvs)))))))

(define exs-add-eqvs ((eqvs ndx-map-p) exs$)
  :guard (exs-solver-rdy exs$)
  :returns (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (if (endp eqvs) exs$
    (b* ((exs$ (exs-add-equiv-lits (caar eqvs) (cdar eqvs))))
      (exs-add-eqvs (rest eqvs) exs$))))

(define resolve-ndx-maps ((n-map ndx-map-p)
                          (cyc natp)
                          &key
                          (exs$ 'exs$))
  :guard (exs-solver-rdy exs$)
  :returns (mv (ndxs ndx-list-p)
               (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  (b* ((lkup (exs$-styp-lkup exs$))
       ((when (not (< cyc (exs$-cnl-map-length exs$))))
        (mv (raise "internal error: insufficient cnl-map length!") exs$)))
    (stobj-let ((lvals (exs$-cnl-mapi cyc exs$)))
               (ndxs eqvs lvals) (resolve-ndx-map* n-map lkup)
               (b* ((exs$ (exs-add-eqvs eqvs exs$)))
                 (mv ndxs exs$)))))

(define exsim-increment-hi (&key (exs$ 'exs$))
  :returns (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (update-exs$-hi (1+ (exs$-hi exs$)) exs$))

(defthm exs$-lo-exs-add-eqvs
  (equal (nth *EXS$-LO* (exs-add-eqvs eqvs exs$))
         (nth *EXS$-LO* exs$))
  :hints (("Goal" :in-theory (enable exs-add-equiv-lits
                                     exs-add-eqvs
                                     exsim-load-cnf))))

(defthm exs$-lo-resolve-ndx-maps
  (equal (nth *EXS$-LO* (mv-nth 1 (resolve-ndx-maps n-map cyc)))
         (nth *EXS$-LO* exs$))
  :hints (("Goal" :in-theory (enable resolve-ndx-maps))))

(defthm exs$-lo-exs-backward-expand
  (equal (nth *EXS$-LO* (mv-nth 2 (exs-backward-expand out-ndxs in-vals)))
         (nth *EXS$-LO* exs$))
  :hints (("Goal" :in-theory (enable exs-backward-expand))))

(define exs-backward-expand-loop ((ndxs ndx-list-p) (cyc natp) 
                                  &key ((rslt natp) '0) (exs$ 'exs$))
  :guard (and (>= cyc (exs$-lo exs$))
              (exs-solver-rdy exs$))
  :measure (nfix (- cyc (exs$-lo exs$)))
  :returns (mv (rslt natp)
               (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  (b* ((rslt (+ (len ndxs) rslt)))
    (if (or (endp ndxs)
            (mbe :logic (zp (- cyc (exs$-lo exs$)))
                 :exec  (eql cyc (exs$-lo exs$))))
        (b* ((- (or (endp ndxs)
                    (raise "internal error: lo cycle should have no backward expansion"))))
          (mv (lnfix rslt) exs$))
      (b* (((mv in-m out-m exs$) (exs-backward-expand ndxs cyc))
           ((mv -     exs$)      (resolve-ndx-maps out-m cyc))
           ((mv pndxs exs$)      (resolve-ndx-maps in-m (1- cyc))))
        (exs-backward-expand-loop pndxs (1- cyc) :rslt rslt)))))

(define exs-prune-ndxs ((ndxs ndx-list-p) lvals
                        &key ((rslt ndx-list-p) 'nil))
  :returns (rslt ndx-list-p)
  (if (endp ndxs) (ndx-list-fix rslt)
    (exs-prune-ndxs (rest ndxs) lvals
                    :rslt
                    (b* ((ndx (first ndxs))
                         ((when (not (< ndx (lits-length lvals))))
                          (raise "ndx out-of-bounds for lvals!:~x0~%"
                                 (list ndx (lits-length lvals)))))
                      ;; BOZO -- should we check that it should be BTM or 0/1?
                      (if (not (btm-litp (get-lit ndx lvals))) rslt
                        (cons ndx rslt))))))

(define exs-load-map-lvals ((map ndx-map-p) &key (preserve-bits 'nil) (lvals 'lvals))
  (if (endp map) lvals
    (b* ((ndx (caar map))
         ((when (not (< ndx (lits-length lvals))))
          (prog2$ (raise "internal error: out-of-bounds init ndx:~x0~%"
                         (list ndx (lits-length lvals)))
                  lvals))
         (lvals (if (and preserve-bits (bitp (get-lit ndx lvals))) lvals
                    (set-lit ndx (cdar map) lvals))))
      (exs-load-map-lvals (rest map) :preserve-bits preserve-bits))))

(defthm mv-nth-0-genrandom-car-stupid-rule
  (equal (mv-nth 0 (genrandom x y))
         (car (genrandom x y)))
  :hints (("Goal" :in-theory (enable mv-nth))))

(define add-rand-vals ((ndxs ndx-list-p) (nmap ndx-map-p) &key (exs$ 'exs$))
  :guard-hints (("Goal" :in-theory (enable exs-next-random)))
  :returns (mv (rslt ndx-map-p) 
               (new-exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  (if (endp ndxs) (mv (ndx-map-fix nmap) exs$)
    (b* (((mv bit exs$) (exs-next-random 2)))
      (add-rand-vals (rest ndxs) (acons! (first ndxs) bit nmap)))))

(defthm exs$-cnl-map-exs-next-random
  (equal (nth *EXS$-CNL-MAPI* (mv-nth 1 (exs-next-random max)))
         (nth *EXS$-CNL-MAPI* exs$))
  :hints (("Goal" :in-theory (enable exs-next-random))))

(defthm exs$-cnl-map-add-rand-vals
  (equal (nth *EXS$-CNL-MAPI* (mv-nth 1 (add-rand-vals ndxs nmap)))
         (nth *EXS$-CNL-MAPI* exs$))
  :hints (("Goal" :in-theory (enable add-rand-vals))))

(defthm exs$-hi-add-rand-vals
  (equal (nth *EXS$-HI* (mv-nth 1 (add-rand-vals ndxs map)))
         (nth *EXS$-HI* exs$))
  :hints (("Goal" :in-theory (enable exs-next-random add-rand-vals))))

(defthm exs$-lo-add-rand-vals
  (equal (nth *EXS$-LO* (mv-nth 1 (add-rand-vals ndxs map)))
         (nth *EXS$-LO* exs$))
  :hints (("Goal" :in-theory (enable exs-next-random add-rand-vals))))

(defthm exs$-next-base-add-rand-vals
  (equal (nth *EXS$-NEXT-BASE* (mv-nth 1 (add-rand-vals ndxs map)))
         (nth *EXS$-NEXT-BASE* exs$))
  :hints (("Goal" :in-theory (enable exs-next-random add-rand-vals))))

(defthm exs$-fail-ndxs-add-rand-vals
  (equal (nth *EXS$-FAIL-NDXS* (mv-nth 1 (add-rand-vals ndxs map)))
         (nth *EXS$-FAIL-NDXS* exs$))
  :hints (("Goal" :in-theory (enable exs-next-random add-rand-vals))))


(define exs-push-hi (&key (exs$ 'exs$))
  :returns (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (b* ((cyc  (exs$-hi exs$))
       (nmap (exs-forward-reduce cyc))
       ((when (not (< cyc (exs$-cnl-map-length exs$))))
        (prog2$ (raise "hi index exceeds cnl-map-length:~x0~%"
                       (list cyc (exs$-cnl-map-length exs$)))
                exs$))
       (nmap (filter-out-styps nmap (exs$-styp-lkup exs$)
                               ;; we allow :wave vars to be processed here
                               ;; since we will filter out any bits already
                               ;; set below.
                               '(:free :rand))) 
       ((mv nmap exs$) (add-rand-vals (exs$-rand-ndxs exs$) nmap))
       (exs$ (stobj-let ((lvals (exs$-cnl-mapi cyc exs$)))
                        ;; NOTE -- any bits already in the lvals for push-hi
                        ;; are bits set as part of reading in the waves and
                        ;; should not be overwritten here:
                        (lvals) (exs-load-map-lvals nmap :preserve-bits t)
                        exs$)))
    exs$))

(defthm exs$-hi-exs-push-hi
  (equal (nth *EXS$-HI* (exs-push-hi))
         (nth *EXS$-HI* exs$))
  :hints (("Goal" :in-theory (enable exs-push-hi))))

(defthm exs$-lo-exs-push-hi
  (equal (nth *EXS$-LO* (exs-push-hi))
         (nth *EXS$-LO* exs$))
  :hints (("Goal" :in-theory (enable exs-push-hi))))

(defthm exs$-next-base-exs-push-hi
  (equal (nth *EXS$-NEXT-BASE* (exs-push-hi))
         (nth *EXS$-NEXT-BASE* exs$))
  :hints (("Goal" :in-theory (enable exs-push-hi))))

(defthm exs$-fail-ndxs-exs-push-hi
  (equal (nth *EXS$-FAIL-NDXS* (exs-push-hi))
         (nth *EXS$-FAIL-NDXS* exs$))
  :hints (("Goal" :in-theory (enable exs-push-hi))))

(define exs-incr-var-count ((adj natp) &key (exs$ 'exs$))
  :returns (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (update-exs$-var-count (+ (exs$-var-count exs$) adj) exs$))

(define exsim-step-fail (&key (exs$ 'exs$))
  :guard (and (exs-solver-rdy exs$)
              (<= (exs$-lo exs$) (exs$-hi exs$)))
  :guard-hints (("Goal" :in-theory (enable exsim-increment-hi)))
  :returns (mv rslt (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  (b* ((exs$ (exsim-increment-hi))
       (exs$ (exs-push-hi))
       (cyc  (exs$-hi exs$))
       (ndxs (exs$-fail-ndxs exs$))
       ((when (not (< cyc (exs$-cnl-map-length exs$))))
        (mv (raise "internal error: cnl-map too small:~x0~%" cyc) exs$))
       (ndxs (stobj-let ((lvals (exs$-cnl-mapi cyc exs$)))
                        (ndxs) (exs-prune-ndxs ndxs lvals)
                        ndxs))
       ((mv diff exs$) (exs-backward-expand-loop ndxs cyc))
       (exs$ (exs-incr-var-count diff)))
    (mv nil exs$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;; exsim-check-fails
;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exs-ndxs-all-0 ((ndxs ndx-list-p) &key ((rslt ndx-map-p) 'nil))
  :returns (rslt ndx-map-p)
  (if (endp ndxs) (ndx-map-fix rslt)
    (exs-ndxs-all-0 (rest ndxs) :rslt (cons (cons (first ndxs) 0) rslt))))

(define exs-clear-fails-ctbl-lo-mid (&key ((cyc natp) '(exs$-lo exs$)) 
                                          ((rslt ndx-ctbl-p) 'nil)
                                          (exs$ 'exs$))
  :guard (<= cyc (exs$-mid exs$))
  :measure (nfix (- (exs$-mid exs$) cyc))
  :returns (rslt ndx-ctbl-p :hyp :guard)
  (b* ((all0 (cons cyc (exs-ndxs-all-0 (exs$-fail-ndxs exs$)))))
    (if (mbe :logic (zp (- (exs$-mid exs$) cyc))
             :exec  (eql cyc (exs$-mid exs$)))
        (cons all0 rslt)
      (exs-clear-fails-ctbl-lo-mid :cyc (1+ cyc)
                                   :rslt (cons all0 rslt)))))

;; function for adding outputs to the list we will generate outputs for:
(define exs-add-out-ctbls (status ndx (ctbls ndx-ctbls-p) exs$)
  :returns (new-exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (b* (((when (and (sim-params->unsat-out-disable (exs$-sim-params exs$))
                   (eq status :unsat)))
        exs$)
       ((when (not (<= (exs$-lo exs$) (exs$-mid exs$))))
        (prog2$ (raise "illegal detection of lo > mid!")
                exs$))
       (id    (acl2::strap status "_" ndx "_" (exs$-lo exs$) "_" (exs$-mid exs$) "_" (exs$-hi exs$)))
       (ctbls (append ctbls (list (exs-clear-fails-ctbl-lo-mid))))
       (exs$  (update-exs$-out-ctbls (cons (cons id ctbls) (exs$-out-ctbls exs$)) exs$)))
    exs$))

(define exs-collect-ndx-map-bits (&key
                                  ((ndx natp) '(lits-length lvals))
                                  ((rslt ndx-map-p) 'nil)
                                  (lvals 'lvals))
  :guard (<= ndx (lits-length lvals))
  :returns (rslt ndx-map-p)
  (if (zp ndx) (ndx-map-fix rslt)
    (b* ((ndx (1- ndx))
         (val (get-lit ndx lvals))
         (rslt (if (bitp val) (acons! ndx val rslt) rslt)))
      (exs-collect-ndx-map-bits :ndx ndx :rslt rslt))))
                           
(define exs-collect-ndx-ctbl-bits (&key
                                   ((cyc natp) '(exs$-cnl-map-length exs$))
                                   ((rslt ndx-ctbl-p) 'nil)
                                   (exs$ 'exs$))
  :guard (<= cyc (exs$-cnl-map-length exs$))
  :returns (rslt ndx-ctbl-p)
  (if (zp cyc) (ndx-ctbl-fix rslt)
    (b* ((cyc (1- cyc))
         (n-map (stobj-let ((lvals (exs$-cnl-mapi cyc exs$)))
                           (n-map) (exs-collect-ndx-map-bits)
                           n-map))
         (rslt (if n-map (acons! cyc n-map rslt) rslt)))
      (exs-collect-ndx-ctbl-bits :cyc cyc :rslt rslt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; ipasir interface ...
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-fail-lits->clauses ((lits lit-listp) &key
                                 ((rslt lit-list-listp) 'nil))
  :returns (rslt lit-list-listp)
  (if (endp lits) (lit-list-list-fix rslt)
    (make-fail-lits->clauses (rest lits)
                             :rslt (cons (list (lit-negate (first lits))) rslt))))

(define exs-collect-ndx-map-lits (&key
                                  ((ndx natp) '(lits-length lvals))
                                  ((rslt ndx-map-p) 'nil)
                                  (lvals 'lvals))
  :guard (<= ndx (lits-length lvals))
  :returns (rslt ndx-map-p)
  (if (zp ndx) (ndx-map-fix rslt)
    (b* ((ndx (1- ndx))
         (val (get-lit ndx lvals))
         (rslt (if (btm-or-bit val) rslt (acons! ndx val rslt))))
      (exs-collect-ndx-map-lits :ndx ndx :rslt rslt))))
                           
(define exs-collect-ndx-ctbl-lits (&key
                                   ((cyc natp) '(exs$-cnl-map-length exs$))
                                   ((rslt ndx-ctbl-p) 'nil)
                                   (exs$ 'exs$))
  :guard (<= cyc (exs$-cnl-map-length exs$))
  :returns (rslt ndx-ctbl-p)
  (if (zp cyc) (ndx-ctbl-fix rslt)
    (b* ((cyc (1- cyc))
         ((when (< cyc (exs$-lo exs$)))
          (ndx-ctbl-fix rslt))
         (n-map (and (<= cyc (exs$-hi exs$))
                     (stobj-let ((lvals (exs$-cnl-mapi cyc exs$)))
                                (n-map) (exs-collect-ndx-map-lits)
                                n-map)))
         (rslt (if n-map (acons! cyc n-map rslt) rslt)))
      (exs-collect-ndx-ctbl-lits :cyc cyc :rslt rslt))))

(define exs-clear-fails-lvals ((ndxs ndx-list-p)
                               &key
                               (lvals 'lvals))
  (if (endp ndxs) lvals
    (b* ((ndx (first ndxs))
         ((when (not (< ndx (lits-length lvals))))
          (prog2$ (raise "fail ndx beyond lvals length:~x0~%"
                         (list ndx (lits-length lvals)))
                  lvals))
         (lvals (set-lit ndx 0 lvals)))
      (exs-clear-fails-lvals (rest ndxs)))))

(define exs-clear-all-fails (&key
                             ((cyc natp) '(exs$-cnl-map-length exs$))
                             (exs$ 'exs$))
  :guard (<= cyc (exs$-cnl-map-length exs$))
  :returns (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (if (zp cyc) exs$
    (b* ((cyc (1- cyc))
         ((when (< cyc (exs$-lo exs$))) exs$)
         ((when (> cyc (exs$-hi exs$))) (exs-clear-all-fails :cyc cyc))
         (ndxs (exs$-fail-ndxs exs$))
         (exs$ (stobj-let ((lvals (exs$-cnl-mapi cyc exs$)))
                          (lvals) (exs-clear-fails-lvals ndxs) exs$)))
      (exs-clear-all-fails :cyc cyc))))

; BOZO -- delete this excess
;
;(define exs-load-sat-map ((nmap ndx-map-p) &key (lvals 'lvals))
;  (if (endp nmap) lvals
;    (b* ((ndx (caar nmap))
;         ((when (not (< ndx (lits-length lvals))))
;          (prog2$ (raise "inernal error: ndx exceeded lits-length:~x0~%"
;                         (list ndx (lits-length lvals)))
;                  lvals))
;         (lvals (set-lit ndx (cdar nmap) lvals)))
;      (exs-load-sat-map (rest nmap)))))

(define exs-load-ndx-ctbl ((ctbl ndx-ctbl-p) &key (exs$ 'exs$))
  :returns (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (if (endp ctbl) exs$
    (b* ((cyc (caar ctbl))
         ((when (not (< cyc (exs$-cnl-map-length exs$))))
          (prog2$ (raise "internal error: cyc exceeded cnl-map:~x0~%"
                         (list cyc (exs$-cnl-map-length exs$)))
                  exs$))
         (exs$ (stobj-let ((lvals (exs$-cnl-mapi cyc exs$)))
                          (lvals) (exs-load-map-lvals (cdar ctbl))
                          exs$)))
      (exs-load-ndx-ctbl (rest ctbl)))))

(define exs-load-ndx-ctbls ((ctbls ndx-ctbls-p) &key (exs$ 'exs$))
  :returns (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (if (endp ctbls) exs$
    (b* ((exs$ (exs-load-ndx-ctbl (first ctbls))))
      (exs-load-ndx-ctbls (rest ctbls)))))

(define exs-add-lit-vars ((ndxs ndx-list-p)
                          (rslt nat-listp)
                          &key (lvals 'lvals))
  :returns (new-rslt nat-listp :hyp (nat-listp rslt))
  (if (endp ndxs) rslt
    (b* ((ndx (first ndxs))
         ((when (>= ndx (lits-length lvals)))
          (raise "oob lvals ndx:~x0~%" ndx))
         (var (lit->var (get-lit ndx lvals))))
      (exs-add-lit-vars (rest ndxs)
                        (if (> var 1) (cons var rslt) rslt)))))

(define exs-get-free-lit-vars (&key
                               ((cyc natp) '(exs$-cnl-map-length exs$))
                               ((rslt nat-listp) 'nil)
                               (exs$ 'exs$))
  :guard (<= cyc (exs$-cnl-map-length exs$))
  :returns (new-rslt nat-listp :hyp (nat-listp rslt))
  (if (zp cyc) rslt
    (b* ((cyc (1- cyc))
         ((when (< cyc (exs$-lo exs$))) rslt)
         (ndxs (exs$-free-ndxs exs$))
         (rslt (if (> cyc (exs$-hi exs$)) rslt
                 (stobj-let ((lvals (exs$-cnl-mapi cyc exs$)))
                            (new-rslt) (exs-add-lit-vars ndxs rslt)
                            new-rslt))))
      (exs-get-free-lit-vars :cyc cyc :rslt rslt))))

(defconst *max-free-var-focus* 100000000)

(define exsim-free-var-focus (focus &key (exs$ 'exs$))
  :guard (exs-solver-rdy exs$)
  :guard-hints (("Goal" :in-theory (enable exs-solver-rdy solver-rdy)))
  :returns (new-exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)
                     :hints (("Goal" :in-theory (enable exs-solver-rdy solver-rdy))))
  ;; focus is either T (only have free-vars as decision var.s), NIL (do
  ;; nothing to focus on free var.s), or a natural number which is the mulitple
  ;; we use to bump the activity values for the free var.s:
  (cond
   ((exs$-use-satlink exs$) exs$)
   ((eq focus nil) exs$)
   ((not (and (natp focus) (< focus *max-free-var-focus*)))
    (prog2$ (raise "internal error: unexpected free-var-focus:~x0~%" focus)
            exs$))
   (t
    (b* ((free-vars (exs-get-free-lit-vars)))
      (stobj-let ((ipasir (exs$-solver exs$)))
                 (ipasir)
                 (ipasir::ipasir-bump-activity-vars ipasir free-vars focus)
                 exs$)))))

(define exs-nmap-sat-cls ((nmap ndx-map-p)
                          (lkup styp-lkup-p)
                          (rslt lit-listp)
                          &key
                          (lvals 'lvals))
  :returns (rslt lit-listp)
  (if (endp nmap) (lit-list-fix rslt)
    (b* ((ndx (caar nmap))
         ((when (not (< ndx (lits-length lvals))))
          (raise "oob lvals ndx:~x0~%" ndx))
         ((when (not (eq (cdr (hons-get ndx lkup)) :free)))
          (exs-nmap-sat-cls (rest nmap) lkup rslt))
         (val (cdar nmap))
         ((when (not (bitp val)))
          (raise "val is not bit:~x0~%" (list ndx val)))
         (lit (get-lit ndx lvals)))
      (exs-nmap-sat-cls (rest nmap) lkup
                        (cons (if (eql val 0) lit (lit-negate lit))
                              rslt)))))

(define exs-ctbl-sat-cls ((ctbl ndx-ctbl-p)
                          &key
                          ((rslt lit-listp) 'nil)
                          (exs$ 'exs$))
  :returns (rslt lit-listp)
  (if (endp ctbl) (lit-list-fix rslt)
    (b* ((cyc (caar ctbl))
         ((when (not (< cyc (exs$-cnl-map-length exs$))))
          (raise "oob cnl-map cyc:~x0~%" cyc))
         (lkup (exs$-styp-lkup exs$))
         (rslt (stobj-let ((lvals (exs$-cnl-mapi cyc exs$)))
                          (rslt) (exs-nmap-sat-cls (cdar ctbl) lkup rslt)
                          rslt)))
      (exs-ctbl-sat-cls (rest ctbl) :rslt rslt))))

(define exs-clear-all-lvals (&key
                             ((ndx natp) '(lits-length lvals))
                             (lvals 'lvals))
  :guard (<= ndx (lits-length lvals))
  (if (zp ndx) lvals
    (b* ((ndx (1- ndx))
         (lvals (set-lit ndx (btm-lit) lvals)))
      (exs-clear-all-lvals :ndx ndx))))

(define exs-clear-all-cnl (&key
                           ((cyc natp) '(exs$-cnl-map-length exs$))
                           (exs$ 'exs$))
  :guard (<= cyc (exs$-cnl-map-length exs$))
  :returns (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (if (zp cyc) exs$
    (b* ((cyc (1- cyc))
         (exs$ (stobj-let ((lvals (exs$-cnl-mapi cyc exs$)))
                          (lvals) (exs-clear-all-lvals) exs$)))
      (exs-clear-all-cnl :cyc cyc))))

;(define exsim-solve-rdx-cnf ((all ndx-ctbl-p) &key (exs$ 'exs$))
;  :guard   (exs-solver-rdy exs$)
;  :returns (mv status (rslt ndx-ctbl-p) (new-exs$ exs-solver-rdy))
;  (exsim-solve-cnf all))

(define exsim-find-n-fails ((n-fails natp)
                            (fail-cube lit-listp)
                            (all ndx-ctbl-p)
                            (bits ndx-ctbl-p)
                            (prev ndx-ctbl-p)
                            &key (exs$ 'exs$))
  :guard (exs-solver-rdy exs$)
  :returns (new-exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (if (or (zp n-fails) (eql n-fails 1)) exs$
    (b* ((cls (exs-ctbl-sat-cls prev))
         (exs$ (exsim-load-cnf (list cls)))
         (exs$ (exsim-assume-cube fail-cube))
         ((mv status next exs$) (exsim-solve-cnf all))
         ((when (eq status :unsat)) exs$)
         ((when (eq status :failed)) exs$)
         (exs$ (exs-add-out-ctbls :sat n-fails (list bits next) exs$)))
      (exsim-find-n-fails (1- n-fails) fail-cube all bits next))))

(define exsim-solve-ipasir ((fail-lits lit-listp) &key (exs$ 'exs$))
  :guard (exs-solver-rdy exs$)
  :returns (mv rslt (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  ;; setup call for ipasir and then process the result..
  ;; different from satlink because we have to account for clauses
  ;; already in the sat space.. 
  ;; NOTE -- we always cleanup the top-level ndx-ctbl to collapse
  ;;         unreferenced cycles here.
  (b* ((fvar-focus (sim-params->free-var-focus (exs$-sim-params exs$)))
       (n-fails    (sim-params->num-fails-gen (exs$-sim-params exs$)))
       (use-ipasir-stats (sim-params->use-ipasir-stats (exs$-sim-params exs$)))
       (base       (exs$-next-base exs$))
       (exs$       (update-exs$-next-base (1+ base) exs$))
       (clause     (cons (make-lit base 0) fail-lits))
       (exs$       (exsim-load-cnf (list clause)))
       (fail-cube  (list (make-lit base 1)))
       (exs$       (exsim-assume-cube fail-cube))
       (ndx-ctbl   (exs-collect-ndx-ctbl-lits))
       (bits-ctbl  (exs-collect-ndx-ctbl-bits))
       (exs$       (exsim-free-var-focus fvar-focus))
       (-          (and use-ipasir-stats
                        (cw "all-stats:~x0~%"
                            (stobj-let ((ipasir (exs$-solver exs$)))
                                       (rslt)
                                       (and (not (eq (ipasir::ipasir-get-status
                                                      ipasir) :undef))
                                            (b* (((mv a b c d e)
                                                  (ipasir::ipasir-get-curr-stats
                                                   ipasir)))
                                              (list a b c d e)))
                                       rslt))))
       ((mv status sat-ctbl exs$) (exsim-solve-cnf ndx-ctbl))
       (exs$ (exs-add-out-ctbls status 0 (list bits-ctbl sat-ctbl) exs$))
       ((when (eq status :unsat))
        (b* ((exs$ (exsim-load-cnf (make-fail-lits->clauses fail-lits)))
             (exs$ (exs-clear-all-fails)))
          (mv :unsat exs$)))
       ((when (eq status :failed)) (mv :failed exs$))
       (exs$ (if (natp n-fails)
                 (exsim-find-n-fails n-fails fail-cube ndx-ctbl bits-ctbl sat-ctbl)
               exs$)))
    (mv :sat exs$)))
    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; satlink interface ...
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exs-eval-lits-lmap ((lmap ndx-map-p)
                            &key
                            ((rslt ndx-map-p) 'nil)
                            (env$ 'env$))
  :returns (rslt ndx-map-p)
  (if (endp lmap) (ndx-map-fix rslt)
    (b* ((val (cdar lmap)))
      (exs-eval-lits-lmap (rest lmap)
                          :rslt
                          (acons! (caar lmap)
                                  (if (bitp val) val (eval-lit val env$))
                                  rslt)))))

(define exs-eval-lits-ctbl ((ctbl ndx-ctbl-p) 
                            &key
                            ((rslt ndx-ctbl-p) 'nil)
                            (env$ 'env$))
  :returns (rslt ndx-ctbl-p)
  (if (endp ctbl) (ndx-ctbl-fix rslt)
    (exs-eval-lits-ctbl (rest ctbl) 
                        :rslt 
                        (acons! (caar ctbl) 
                                (exs-eval-lits-lmap (fast-alist-clean (cdar ctbl)))
                                rslt))))

(defthm append-lit-list-listp-2
  (implies (and (lit-list-listp x) (lit-list-listp y))
           (lit-list-listp (append x y))))

(define exs-clear-lits-lvals (&key
                              ((ndx natp) '(lits-length lvals))
                              (lvals 'lvals))
  :guard (<= ndx (lits-length lvals))
  (if (zp ndx) lvals
    (b* ((ndx (1- ndx))
         (val (get-lit ndx lvals))
         (lvals (if (bitp val) lvals (set-lit ndx (btm-lit) lvals))))
      (exs-clear-lits-lvals :ndx ndx))))

(define exs-clear-all-lits (&key
                            ((cyc natp) '(exs$-cnl-map-length exs$))
                            (exs$ 'exs$))
  :guard (<= cyc (exs$-cnl-map-length exs$))
  :returns (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (if (zp cyc) exs$
    (b* ((cyc (1- cyc))
         ((when (< cyc (exs$-lo exs$))) exs$)
         ((when (> cyc (exs$-hi exs$))) (exs-clear-all-lits :cyc cyc))
         (exs$ (stobj-let ((lvals (exs$-cnl-mapi cyc exs$)))
                          (lvals) (exs-clear-lits-lvals) exs$)))
      (exs-clear-all-lits :cyc cyc))))

(define exsim-solve-satlink ((fail-lits lit-listp) &key (exs$ 'exs$))
  :guard (exs-solver-rdy exs$)
  :returns (mv rslt (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  ;; setup call for sat and then process the result..
  (b* (((local-stobjs env$) (mv rslt exs$ env$))
       ;; NOTE -- we always cleanup the top-level ndx-ctbl to collapse unreferenced cycles here.
       (curr-cnf         (exs$-curr-cnf exs$))
       (sat-cnf          (cons fail-lits curr-cnf))
       ((mv status env$) (satlink::sat sat-cnf env$))
       ((when (eq status :unsat))
        (b* ((bits-ctbl (exs-collect-ndx-ctbl-bits))
             (exs$ (exs-add-out-ctbls status 0 (list bits-ctbl) exs$))
             (exs$ (exs-clear-all-lits))
             (exs$ (update-exs$-curr-cnf () exs$))
             (exs$ (update-exs$-next-base (init-sat-base) exs$)))
          (mv :unsat exs$ env$)))
       ((when (eq status :failed)) (mv :failed exs$ env$))
       (ndx-ctbl   (exs-collect-ndx-ctbl-lits))
       (sat-ctbl   (exs-eval-lits-ctbl ndx-ctbl))
       (bits-ctbl  (exs-collect-ndx-ctbl-bits))
       (exs$       (exs-add-out-ctbls status 0 (list bits-ctbl sat-ctbl) exs$)))
    (mv :sat exs$ env$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; main solve function ...
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exs-collect-fail-lvals ((ndxs ndx-list-p)
                                (rslt lit-listp)
                                &key (lvals 'lvals))
  :returns (mv failed (rslt lit-listp))
  (if (endp ndxs) (mv nil (lit-list-fix rslt))
    (b* ((ndx (first ndxs))
         ((when (not (< ndx (lits-length lvals))))
          (mv nil (raise "ndx out of bounds of lvals:~x0~%"
                         (list ndx (lits-length lvals)))))
         (lit (get-lit ndx lvals)))
      (cond
       ((eql lit 0)
        (exs-collect-fail-lvals (rest ndxs) rslt))
       ((eql lit 1)
        (mv t (lit-list-fix rslt)))
       ((btm-litp lit)
        (exs-collect-fail-lvals (rest ndxs) rslt))
       (t
        (exs-collect-fail-lvals (rest ndxs) (cons lit rslt)))))))

(define exs-collect-all-fails (&key
                               ((cyc natp) '(exs$-cnl-map-length exs$))
                               ((rslt lit-listp) 'nil)
                               (exs$ 'exs$))
  :guard (<= cyc (exs$-cnl-map-length exs$))
  :returns (mv failed (rslt lit-listp))
  (if (zp cyc) (mv nil (lit-list-fix rslt))
    (b* ((cyc (1- cyc))
         ((when (< cyc (exs$-mid exs$)))
          (mv nil (lit-list-fix rslt)))
         ((when (> cyc (exs$-hi exs$)))
          (exs-collect-all-fails :cyc cyc :rslt rslt))
         (ndxs (exs$-fail-ndxs exs$))
         ((mv failed rslt)
          (stobj-let ((lvals (exs$-cnl-mapi cyc exs$)))
                     (failed rslt) (exs-collect-fail-lvals ndxs rslt)
                     (mv failed rslt)))
         ((when failed)
          (mv t (lit-list-fix rslt))))
      (exs-collect-all-fails :cyc cyc :rslt rslt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; main solve routine..
;;

(define exsim-solve-fails (&key (exs$ 'exs$))
  :guard (and (exs-solver-rdy exs$)
              (<= (exs$-lo exs$) (exs$-hi exs$))
              (<= (exs$-mid exs$) (exs$-hi exs$)))
  :returns (mv rslt (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  (b* (((mv failed lits) (exs-collect-all-fails)))
    (cond
     (failed                  (b* ((bits-ctbl (exs-collect-ndx-ctbl-bits))
                                   (exs$ (exs-add-out-ctbls :sat 0 (list bits-ctbl) exs$)))
                                (mv :sat exs$)))
     ((atom lits)             (b* ((bits-ctbl (exs-collect-ndx-ctbl-bits))
                                   (exs$ (exs-add-out-ctbls :unsat 0 (list bits-ctbl) exs$)))
                                (mv :unsat exs$)))
     ((exs$-use-satlink exs$) (exsim-solve-satlink lits))
     (t                       (exsim-solve-ipasir  lits)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exsim-mk-svar ((var sv::svar-p) (dly natp))
  :returns (rslt sv::svar-p)
  (sv::change-svar var :delay dly))

(define exs-var-x-bits ((var sv::svar-p) &key (exs$ 'exs$))
  :returns (rslt sv::4vec-p)
  (b* ((look (hons-get var (exs$-var->ndx exs$)))
       ((when (not look))
        (prog2$ (raise "could not find var in var->ndx:~x0~%" var)
                (sv::4vec-x)))
       (size (len (cdr look))))
    (sv::4vec-part-install 0 size 0 (sv::4vec-x))))

(define exs-add-ndx-lit->vmap ((ndx natp) (cyc natp) (lit litp)
                               (vmap exs-vmap-p) &key (exs$ 'exs$))
  :returns (rslt exs-vmap-p)
  (b* ((look (hons-get ndx (exs$-ndx->var exs$)))
       ((when (not look))
        (raise "could not find ndx in ndx->var:~x0~%" ndx))
       ((ndx->var-elem el) (cdr look))
       (var (exsim-mk-svar el.var cyc))
       (look (hons-get var vmap))
       (old (if look (cdr look) (exs-var-x-bits el.var)))
       (new (if (bitp lit) lit (sv::4vec-x)))
       (val (sv::4vec-part-install el.off 1 old new)))
    (exs-vmap-fix (hons-acons var val vmap))))

(define exs-add-nmap->vmap ((nmap ndx-map-p) (cyc natp) (vmap exs-vmap-p)
                            &key (exs$ 'exs$))
  :returns (rslt exs-vmap-p)
  (if (endp nmap) (exs-vmap-fix vmap)
    (exs-add-nmap->vmap (rest nmap) cyc
                        (exs-add-ndx-lit->vmap (caar nmap) cyc 
                                               (cdar nmap) vmap))))

(define exs-map-ctbl->vmap ((tbl ndx-ctbl-p) (vmap exs-vmap-p)
                            &key (exs$ 'exs$))
  :returns (rslt exs-vmap-p)
  (if (endp tbl) (exs-vmap-fix (fast-alist-clean vmap))
    (exs-map-ctbl->vmap (rest tbl)
                        (exs-add-nmap->vmap (cdar tbl) (caar tbl) vmap))))

(define exs-map-ctbls->vmap ((tbls ndx-ctbls-p) (vmap exs-vmap-p)
                             &key (exs$ 'exs$))
  :returns (rslt exs-vmap-p)
  (if (endp tbls) (exs-vmap-fix (fast-alist-clean vmap))
    (exs-map-ctbls->vmap (rest tbls)
                         (exs-map-ctbl->vmap (first tbls) vmap))))

(define exsim-chk-return-sat (&key (exs$ 'exs$))
  :returns (mv rslt (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  (b* ((exs$ (update-exs$-sat-result :sat exs$)))
    (mv t exs$)))

(define exsim-chk-return-unsat (&key (exs$ 'exs$))
  :returns (mv rslt (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  (b* ((exs$ (update-exs$-sat-result :unsat exs$))
       (exs$ (if (< (exs$-mid exs$) (1- (exs$-hi exs$)))
                 (update-exs$-mid (1- (exs$-hi exs$)) exs$)
               exs$)))
    (mv nil exs$)))

(define exsim-chk-return-failed (&key (exs$ 'exs$))
  :returns (mv rslt (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  (b* ((exs$ (update-exs$-sat-result :failed exs$)))
    (mv nil exs$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; check-fails function:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exsim-check-fails (&key (exs$ 'exs$))
  :guard (and (exs-solver-rdy exs$)
              (<= (exs$-lo exs$) (exs$-hi exs$))
              (<= (exs$-mid exs$) (exs$-hi exs$)))
  :returns (mv rslt (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  (b* (((mv status exs$) (exsim-solve-fails)))  ;; find outstanding fails..
    (case status
      (:sat    (exsim-chk-return-sat))
      (:unsat  (exsim-chk-return-unsat))
      (:failed (exsim-chk-return-failed))
      (t       (mv (raise "unsuspected status result:~x0~%" status)
                   exs$)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;; exsim-cleanup-st
;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exsim-upd-just-failed (&key (exs$ 'exs$))
  :returns (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (update-exs$-sat-result :just-failed exs$))

(define exsim-cleanup-st (&key (exs$ 'exs$))
  :guard (exs-solver-rdy exs$)
  :returns (mv rslt (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  ;; This function is called to periodically cleanup the state of exsim.
  ;; This includes the following actions:
  ;;
  ;; 1. IPASIR-only: reset the ipasir state and then reload the clauses in sat.
  ;; 2. do a cleanup of the objects in the exs$ state that may be holding cruft..
  ;; 3. ???
  (b* ((exs$ (if (exs$-use-satlink exs$) exs$ (exsim-reset-isat)))
       (exs$ (exs-clear-all-lits))
       (exs$ (update-exs$-curr-cnf () exs$))
       (exs$ (exsim-upd-just-failed)))
    (mv nil exs$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;; exsim-choose-step
;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exsim-clear-sat-result (&key (exs$ 'exs$))
  :returns (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (update-exs$-sat-result nil exs$))

(define add->=-pts ((x integer-listp) (y integer-listp))
  :returns (rslt natp)
  (cond ((and (endp x) (endp y)) 0)
        ((or (endp x) (endp y))
         (prog2$ (raise "non-matching nat lists!") 0))
        (t (+ (if (>= (first x) (first y)) 1 0)
              (add->=-pts (rest x) (rest y))))))

(local (include-book "arithmetic-5/top" :dir :system))

(define compute-soft-choice ((sim-params sim-params-p)
                             (choice-vars choice-vars-p))
  :returns (rslt symbolp)
  (b* (((sim-params sp)  sim-params)
       ((choice-vars cv) choice-vars)
       (fails  (list (- sp.min-diff (- cv.hi cv.lo))
                     (- sp.min-vars cv.var-count)
                     (- sp.min-clauses cv.cls-count)))
       (frees  (list (- sp.max-diff (- cv.hi cv.lo))
                     (- sp.max-vars cv.var-count)
                     (- sp.max-clauses cv.cls-count)))
       (checks (list (- sp.mid-diff (- cv.hi cv.mid))
                     (- sp.mid-vars cv.var-count)
                     (- sp.mid-clauses cv.cls-count)))
       (fail-weight  (+ (add->=-pts fails frees)
                        (add->=-pts fails checks)
                        (if (member-eq :step-fail cv.prev-choice)
                            sp.repeat-weight
                          0)))
       (free-weight  (if (member-eq :step-fail cv.prev-choice) 0
                       (+ (add->=-pts frees fails)
                          (add->=-pts frees checks)
                          (if (member-eq :step-fail cv.prev-choice)
                              sp.repeat-weight
                            0))))
       (check-weight (if (eq cv.prev-choice :check-fails) 0
                       (+ (add->=-pts checks frees)
                          (add->=-pts checks fails))))
       (total-weight (+ fail-weight free-weight check-weight))
       ((when (<= total-weight 0)) (raise "impossible weight seen!"))
       (pick-val (mod cv.rand-value total-weight)))
    (cond ((<    pick-val              fail-weight) :step-fail)
          ((and (< (- pick-val fail-weight) free-weight) nil) :step-free)
          (t                                        :check-fails))))

(define compute-choice-inst ((sim-params sim-params-p)
                             (choice-vars choice-vars-p))
  :returns (rslt true-listp)
  (b* (((sim-params sp)  sim-params)
       ((choice-vars cv) choice-vars))
    (cond
     ;; limit rules:
     ((>= (- cv.num-steps cv.last-clean)
          sp.clean-interval)
      (list :cleanup-st))
     ((or (<= (- cv.hi cv.lo) sp.min-diff)
          (<= cv.var-count sp.min-vars)
          (<= cv.cls-count sp.min-clauses)
          (eq cv.prev-choice :check-fails))
      (list :step-fail))
;     ((and (not (eq cv.prev-choice :step-fail))
;           (or (>= (- cv.hi cv.lo) sp.max-diff)
;               (>= cv.var-count sp.max-vars)
;               (>= cv.cls-count sp.max-clauses)))
;      :step-free)
     ((and (not (eq cv.prev-choice :check-fails))
           (or (>= (- cv.hi cv.mid) sp.mid-diff)
               (>= cv.var-count sp.mid-vars)
               (>= cv.cls-count sp.mid-clauses)))
      (list :check-fails))
     ;; soft rules
     (t (list (compute-soft-choice sim-params choice-vars))))))

(encapsulate 
 (((compute-choice * *) => * 
   :formals (sp cv) 
   :guard (and (sim-params-p sp) (choice-vars-p cv))))
 
 (local (defun compute-choice (sp cv)
          (declare (xargs :guard (and (sim-params-p sp) (choice-vars-p cv)))
                   (ignore sp cv))
          nil))

 (defthm compute-choice-returns-list
   (true-listp (compute-choice sp cv))
   :rule-classes (:rewrite :type-prescription)))

(define compute-choice-top ((sim-params sim-params-p)
                            (choice-vars choice-vars-p))
  :returns (rslt true-listp)
  ;;
  ;; Strict rules:
  ;;  State rules:
  ;;   (>= hi max-cycle)
  ;;       --> check-fails then complete-chk
  ;;   (== hi lo)
  ;;       --> step-fail
  ;;   (== sat-result :just-failed)
  ;;       --> step-free
  ;;   (== sat-result :failed)
  ;;       --> cleanup-st
  ;;
  ;;  Limit rules:
  ;;   (<= (- hi lo) min-diff)
  ;;   (<= var-count min-vars)
  ;;   (<= cls-count min-clauses)
  ;;       --> step-fail
  ;;   (>= (- hi lo) max-diff)
  ;;   (>= var-count max-vars)
  ;;   (>= cls-count max-clauses)
  ;;       --> step-free
  ;;   (>= (- hi mid) mid-diff)
  ;;   (>= var-count  mid-vars)
  ;;   (>= cls-count  mid-clauses)
  ;;       --> check-fails
  ;;   (>= (- num-steps last-cleanup) clean-interval)
  ;;       --> cleanup-st
  ;;
  ;;   NOTE on limit rule settings, these settings are
  ;;   defined by parameters specified in sim_params
  ;;   and then adjusted across the board based on a
  ;;   single param called "gain_factor"
  ;;
  ;; Additional rules:
  ;;   (eq prev-choice :step-fail)
  ;;       --> do not pick :step-free
  ;;   basically, we don't want to generally reduce the
  ;;   sat problem before we have had a chance to check it.
  ;;
  ;; Soft rules:
  ;;   if none of the strict rules apply, then we choose
  ;;   randomly from {step-fail, step-free, check-fails}
  ;;   with a bias towards our previous step-fail or
  ;;   step-free in the case of steps using user provided
  ;;   hysteresis/weights..
  ;;   
  (b* (((sim-params sp)  sim-params)
       ((choice-vars cv) choice-vars))
    (cond
     ;; state rules:
     ((and (>= cv.hi cv.max-cycle)
           (not cv.sat-result))       (list :check-fails))
     ((>= cv.hi cv.max-cycle)         (list :complete-chk))
     ((<= cv.hi cv.lo)                (list :step-fail))
     ((eq cv.sat-result :just-failed) (list :step-free))
     ((eq cv.sat-result :failed)      (list :cleanup-st))
     (t (compute-choice sim-params choice-vars)))))

(defattach compute-choice compute-choice-inst)

(define exs-clause-count (exs$)
  :returns (rslt natp)
  (lnfix (if (exs$-use-satlink exs$)
             (length (exs$-curr-cnf exs$))
           (b* ((cls-count (exs$-cls-count exs$))
                (use-ipasir-stats (sim-params->use-ipasir-stats (exs$-sim-params exs$))))
             (stobj-let ((ipasir (exs$-solver exs$)))
                        (num-clauses)
                        (if (or (eq (ipasir::ipasir-get-status ipasir) :undef)
                                (not use-ipasir-stats))
                            cls-count
                          (b* (((mv - num-clauses - - -)
                                (ipasir::ipasir-get-curr-stats ipasir)))
                            num-clauses))
                        num-clauses)))))

(define exsim-choose-step (&key (exs$ 'exs$))
  :guard-hints (("Goal" :in-theory (enable exs-next-random
                                           exsim-clear-sat-result)))
  :returns (mv (rslt true-listp) (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$)))
  (b* (((mv rval exs$) (exs-next-random 100000000))
       (choice-vars    (make-choice-vars
                        :sat-result  (exs$-sat-result exs$)
                        :var-count   (exs$-var-count exs$)
                        :cls-count   (exs-clause-count exs$)
                        :lo          (exs$-lo exs$)
                        :mid         (exs$-mid exs$)
                        :hi          (exs$-hi exs$)
                        :max-cycle   (exs$-max-cycle exs$)
                        :last-clean  (exs$-last-clean exs$)
                        :num-steps   (exs$-num-steps exs$)
                        :prev-choice (exs$-prev-choice exs$)
                        :rand-value  rval))
       ((choice-vars cv) choice-vars)
       (exs$ (exsim-clear-sat-result))
       (choice (compute-choice-top (exs$-sim-params exs$) choice-vars))
       (exs$ (update-exs$-prev-choice choice exs$))
       (exs$ (update-exs$-num-steps (1+ (exs$-num-steps exs$)) exs$))
       (exs$ (update-exs$-compute-aigs
              (if (member-eq :compute-aigs choice) t nil) exs$))
       (exs$ (if (member-eq :cleanup-st choice)
                 (update-exs$-last-clean (exs$-num-steps exs$) exs$)
               exs$)))
    (prog2$ (and (exs$-verbose exs$)
                 (cw "choose: [~x0:~x1:~x2] vcnt=~x3 ccnt=~x4 max=~x5 sat=~x6 choice=~x7~%"
                     cv.lo cv.mid cv.hi cv.var-count cv.cls-count cv.max-cycle cv.sat-result choice))
            (mv choice exs$))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;; main loop function ...
;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exsim-main-loop (&key
                         ((depth natp) '20000)
                         (exs$ 'exs$))
  :guard (exs-solver-rdy exs$)
  :returns (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (if (zp depth)
      (prog2$ (raise "exceeded exsim-main-loop depth!") exs$)
    (b* (((mv choice exs$) (exsim-choose-step))
         ((when (or (not (natp (exs$-lo exs$)))
                    (not (natp (exs$-hi exs$)))
                    (not (natp (exs$-mid exs$)))
                    (> (exs$-lo exs$)  (exs$-hi exs$))
                    (> (exs$-mid exs$) (exs$-hi exs$))
                    (> (exs$-lo exs$)  (exs$-mid exs$))))
          (prog2$ (raise "should never have lo > hi or mid > hi or lo > mid!") exs$))
         ((mv done exs$)
          (cond
           ((member-eq :step-fail choice)    (exsim-step-fail))
           ((member-eq :step-free choice)    (exsim-step-free))
           ((member-eq :check-fails choice)  (exsim-check-fails))
           ((member-eq :cleanup-st choice)   (exsim-cleanup-st))
           ((member-eq :complete-chk choice) (mv t exs$))
           (t (mv (raise "invalid step!:~x0~%" choice) exs$)))))
      ;; BOZO -- need to add check for any fail bit being 1 in least bit..
      (if done exs$ (exsim-main-loop :depth (1- depth))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;; init loop function supports
;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exsim-load-inits ((sim-params sim-params-p) &key (exs$ 'exs$))
  :returns (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (b* (((sim-params sp)                         sim-params)
       ;;
       (exs$ (update-exs$-hi          0              exs$))
       (exs$ (update-exs$-lo          0              exs$))
       (exs$ (update-exs$-mid         0              exs$))
       (exs$ (update-exs$-max-cycle   2              exs$))
       ;;
       ;; NOTE -- important to start sat literals at 2!:
       ;; 0,1 is used for true/false, 2/3 is used for btm/top
       ;; (although I don't use top at the moment..)
       ;;
       (exs$ (update-exs$-next-base  (init-sat-base) exs$))
       (exs$ (update-exs$-curr-cnf    ()             exs$))
       ;;
       (exs$ (update-exs$-fail-ndxs   ()             exs$))
       (exs$ (update-exs$-free-ndxs   ()             exs$))
       (exs$ (update-exs$-rand-ndxs   ()             exs$))
       (exs$ (update-exs$-styp-lkup   ()             exs$))
       ;;
       (exs$ (update-exs$-return-vmap ()             exs$))
       ;;
       (exs$ (update-exs$-var-count   0              exs$))
       (exs$ (update-exs$-sat-result  nil            exs$))
       ;; NOTE -- we cannot change this value here since we are already
       ;; into main-loop which needs this fixed as part of invariant:
       ;;    (exs$ (update-exs$-use-satlink sp.use-satlink exs$))
       (exs$ (update-exs$-verbose     sp.verbose     exs$))
       ;;
       (exs$ (update-exs$-last-clean  0              exs$))
       (exs$ (update-exs$-num-steps   0              exs$))
       (exs$ (update-exs$-prev-choice nil            exs$)))
    exs$))

(define exs-num-ndxs (&key (exs$ 'exs$))
  :returns (rslt natp)
  (stobj-let ((aignet (exs$-aignet exs$)))
             (num-ins num-outs) (mv (num-ins aignet) (num-outs aignet))
             (prog2$ (or (eql num-ins num-outs)
                         (raise "aignet loaded does not have matching ins and outs:~x0~%"
                                (list num-ins num-outs)))
                     num-ins)))

(define exs-btm-lvals ((ndx natp) lvals)
  :guard (<= ndx (lits-length lvals))
  (if (zp ndx) lvals
    (b* ((ndx (1- ndx))
         (lvals (set-lit ndx (btm-lit) lvals)))
      (exs-btm-lvals ndx lvals))))

(define exs-init-cnl-lvals ((num-ndxs natp) &key (lvals 'lvals))
  (b* ((lvals (resize-lits num-ndxs lvals))
       (lvals (exs-btm-lvals num-ndxs lvals)))
    lvals))

(define exs-init-cnl-map ((cyc natp) (num-ndxs natp) &key (exs$ 'exs$))
  :guard (<= cyc (exs$-cnl-map-length exs$))
  :returns (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (if (zp cyc) exs$
    (b* ((cyc (1- cyc))
         (exs$ (stobj-let ((lvals (exs$-cnl-mapi cyc exs$)))
                          (lvals) (exs-init-cnl-lvals num-ndxs)
                          exs$)))
      (exs-init-cnl-map cyc num-ndxs))))

(define exsim-init-cnl-map ((num-cycs natp) &key (exs$ 'exs$))
  :returns (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
  (b* ((exs$ (resize-exs$-cnl-map (1+ num-cycs) exs$))
       (num-ndxs (exs-num-ndxs))
       (exs$ (exs-init-cnl-map (1+ num-cycs) num-ndxs)))
    exs$))

(encapsulate 
 (((compute-var-styp * * *) => * 
   :formals (var sp mod) 
   :guard (and (sv::svar-p var) (sim-params-p sp) (stringp mod))))
 
 (local (defun compute-var-styp (var sp mod) 
          (declare (xargs :guard (and (sv::svar-p var) (sim-params-p sp) (stringp mod)))
                   (ignore var sp mod))
          nil))
 
 (defthm compute-var-styp-returns-symbolp
   (symbolp (compute-var-styp var sp mod))
   :rule-classes (:rewrite :type-prescription)))

;; The following function is the default name for a function
;; which we use to assign an "styp" to a signal (generally
;; either an input category of "randomly" assigned or "freely"
;; chosen in search..
;;
(define compute-var-styp-inst ((var sv::svar-p) (sp sim-params-p) (mod stringp))
  (declare (ignore mod sp))
  (let ((name (sv::svar->name var)))
    (and (stringp name)
         (cond ((str::strprefixp "fail_" name) :fail)
               ((str::strprefixp "wave_" name) :wave)
               ((str::strprefixp "free_" name) :free)
               ((str::strprefixp "rand_" name) :rand)))))

(defattach compute-var-styp compute-var-styp-inst)

(define add-lkup ((ndxs ndx-list-p) (styp symbolp) (rslt styp-lkup-p))
  :returns (rslt styp-lkup-p)
  (if (endp ndxs) (styp-lkup-fix rslt)
    (add-lkup (rest ndxs) styp (acons! (first ndxs) styp rslt))))

(define compute-styp-lkup ((v->n-map var->ndx-map-p)
                           (sim-params sim-params-p)
                           (mod-name stringp)
                           &key
                           ((rslt styp-lkup-p) 'nil)
                           (state 'state))
  :returns (rslt styp-lkup-p)
  (if (endp v->n-map) (styp-lkup-fix (make-fast-alist rslt))
    (compute-styp-lkup (rest v->n-map) sim-params mod-name
                       :rslt
                       (b* ((styp (compute-var-styp (caar v->n-map) sim-params mod-name)))
                         (if styp (add-lkup (cdar v->n-map) styp rslt) rslt)))))

(define lkup->ndxs ((lkup styp-lkup-p) (styp symbolp) &key ((rslt ndx-list-p) 'nil))
  :returns (rslt ndx-list-p)
  (if (endp lkup) (ndx-list-fix rslt)
    (lkup->ndxs (rest lkup) styp
                :rslt (if (eq (cdar lkup) styp) (cons (caar lkup) rslt) rslt))))

(defconst *4vec-1* (sv::make-4vec :upper 1 :lower 1))
(defconst *4vec-0* (sv::make-4vec :upper 0 :lower 0))

(define var->init-map ((ndxs ndx-list-p) (val sv::4vec-p)
                       &key ((rslt ndx-map-p) 'nil))
  :returns (rslt ndx-map-p)
  (if (endp ndxs) (ndx-map-fix rslt)
    (var->init-map (rest ndxs) (sv::4vec-rsh 1 val)
                   :rslt
                   (b* ((b (sv::4vec-bit-extract 0 val)))
                     (cond ((equal b *4vec-1*)
                            (acons! (first ndxs) 1 rslt))
                           ;; BOZO -- 4val? 2val for now..
                           ;; ((equal b *4vec-0*)
                           (t (acons! (first ndxs) 0 rslt)))))))
                     ;; (t rslt))))))

(define cycle->init-map ((vmap exs-vmap-p)
                         (v->n-map var->ndx-map-p)
                         &key
                         ((rslt ndx-map-p) 'nil))
  :returns (rslt ndx-map-p)
  (if (atom vmap) (ndx-map-fix rslt)
    (b* ((look (hons-get (caar vmap) v->n-map))
         ((when (not look))
          ;; (raise "var not found in v->n-map:~x0~%" (car vmap)))
          (cycle->init-map (rest vmap) v->n-map :rslt rslt))
         (nuinit (var->init-map (cdr look) (cdar vmap))))
      (cycle->init-map (rest vmap) v->n-map
                       :rslt (append nuinit rslt)))))

(define waves->init-ctbl ((waves exs-vmaplist-p)
                          (v->n-map var->ndx-map-p)
                          &key
                          ((cyc natp) '0)
                          ((ctbl ndx-ctbl-p) 'nil))
  :returns (rslt ndx-ctbl-p)
  (if (endp waves) (ndx-ctbl-fix ctbl)
    (waves->init-ctbl (rest waves) v->n-map :cyc (1+ cyc)
                      :ctbl (acons! cyc
                                    (cycle->init-map (first waves)
                                                     v->n-map)
                                    ctbl))))

; BOZO -- delete this excess
;
;(define exs-load-ndx-ctbl ((tbl ndx-ctbl-p) &key (exs$ 'exs$))
;  :returns (exs$ exs-solver-rdy :hyp (exs-solver-rdy exs$))
;  (if (endp tbl) exs$
;    (b* ((cyc (caar tbl))
;         ((when (not (< cyc (exs$-cnl-map-length exs$))))
;          (prog2$ (raise "internal error: out of bounds init cyc:~x0~%"
;                         (list cyc (exs$-cnl-map-length exs$)))
;                  exs$))
;         (exs$ (stobj-let ((lvals (exs$-cnl-mapi cyc exs$)))
;                          (lvals) (exs-load-map-lvals (cdar tbl))
;                          exs$)))
;      (exs-load-ndx-ctbl (rest tbl)))))

(define merge-in-reset ((reset exs-vmap-p)
                        (tbl exs-vmap-p)
                        (rslt exs-vmap-p))
  :returns (rslt exs-vmap-p)
  (if (atom reset) (exs-vmap-fix rslt)
    (merge-in-reset (rest reset) tbl
                    (b* ((var (caar reset))
                         (reset-val (cdar reset)))
                      (if (hons-get var tbl) rslt
                        (acons! var reset-val rslt))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;; init loop function ...
;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exsim-init-loop ((waves      exs-vmaplist-p
                                     "wave-provided list of maps of svars to 4vecs")
                         (sim-params sim-params-p
                                     "Structure storing parameters for search loop")
                         &key
                         (exs$       'exs$)
                         (state      'state))
  :guard (exs-solver-undf exs$)
  :returns (mv (exs$ exs-solver-rdy :hyp (exs-solver-undf exs$)) state)
  (b* (((sim-params sp) sim-params)
       (mod-name (exs$-mod-name exs$))
       (reset-vmap (exs$-reset-vmap exs$))
       (v->n (exs$-var->ndx exs$))
       ((mv rand-seed state) (random$ *rand-seed-upper-limit* state))
       (rand-seed (if (natp sp.random-seed) sp.random-seed rand-seed))
       (exs$ (exs-init-random rand-seed))
       ((mv exs$ state) (exsim-init-isat))
       (exs$ (exsim-load-inits sim-params))
       (max-cycle (if (natp sp.max-cycle) sp.max-cycle (length waves)))
       (exs$ (exsim-init-cnl-map max-cycle))
       ((when (atom waves))
        (prog2$ (raise "incoming waves should have at least one cycle!")
                (mv exs$ state)))
       (ftbl  (make-fast-alist (first waves)))
       (waves (cons (merge-in-reset reset-vmap ftbl ftbl) (rest waves)))
       (-     (fast-alist-free ftbl))
       (init-ctbl (waves->init-ctbl waves v->n))
       (exs$ (exs-load-ndx-ctbl init-ctbl))
       (styp-lkup (compute-styp-lkup v->n sim-params mod-name))
       ;; BOZO -- should free sub-aig tbls :(
       (- (fast-alist-free (exs$-in-aig-ctbl exs$)))
       (- (fast-alist-free (exs$-out-aig-ctbl exs$)))
       (exs$ (update-exs$-in-aig-ctbl nil exs$))
       (exs$ (update-exs$-out-aig-ctbl nil exs$))
       (exs$ (update-exs$-fail-ndxs (lkup->ndxs styp-lkup :fail) exs$))
       (exs$ (update-exs$-free-ndxs (lkup->ndxs styp-lkup :free) exs$))
       (exs$ (update-exs$-rand-ndxs (lkup->ndxs styp-lkup :rand) exs$))
       (exs$ (update-exs$-styp-lkup styp-lkup exs$))
       (exs$ (update-exs$-max-cycle max-cycle exs$)))
    (mv exs$ state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
