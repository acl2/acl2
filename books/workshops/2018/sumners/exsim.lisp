;; exsim.lisp
;;
;; Top-level exsim book which defines the function (exsim <mod-name>) which
;; reads in the design in <mod-name>.v (compiling it to an AIGNET) and the
;; waves in <mod-name>.vcd and searches for any failures it can find tracking
;; the waves in the VCD file. In the case it finds a sim. hitting a failure, it
;; will generat a VCD file <mod-name>_out.vcd.

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


(include-book "std/util/defconsts" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "centaur/sv/mods/compile" :dir :system)
(include-book "std/io/read-file-lines" :dir :system)

(include-book "centaur/ipasir/ipasir-logic" :dir :system)
(include-book "centaur/ipasir/ipasir-tools" :dir :system)
(include-book "centaur/misc/seed-random" :dir :system)
(include-book "misc/file-io" :dir :system)
(include-book "misc/random" :dir :system)

(include-book "extypes")
(include-book "nxtbl")
(include-book "exbase")
(include-book "svcnf")
(include-book "vcd")
(include-book "exloop")

(defsection exsim-top-level-definition
  :parents (exsim)
  :short "Book defining top-level exsim function definition."
  :autodoc nil
  :long "
<p> This book defines the @({ (exsim mod-name) }) function which takes an input
  string <top-mod> and reads in the design defined in <mod-name>.v with top
  module defined by the optional <top-mod> input (defaults to just 'top') and
  compiles it into an AIGNET. The function then iterates through the main
  search loop and reports final results which would include generating the
  <mod-name>_out.vcd file for the resulting fail.</p>
")

;;;;;

(define exs-print (&key (exs$ 'exs$))
  (stobj-let ((aignet (exs$-aignet exs$)))
             (rslt)
             (aignet-print aignet)
             rslt))

;;;;;
(defmacro strap! (&rest x) (cons 'acl2::strap! x))

(define exs-wave-vcd  (&key (exs$ 'exs$)) (strap! (exs$-mod-name exs$) "_in.vcd"))
(define exs-rpt-out   (&key (exs$ 'exs$)) (strap! (exs$-mod-name exs$) "_rpt.txt"))
(define exs-out-vcd   (suff &key (exs$ 'exs$)) (strap! (exs$-mod-name exs$) "_"
                                                       suff "_out.vcd"))
(define exs-out-gtkw  (suff &key (exs$ 'exs$)) (strap! (exs$-mod-name exs$) "_"
                                                       suff "_out.gtkw"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define clear-memory-stuff ()
  (b* ((- (clear-memoize-tables))
       (- (hons-wash)))
    nil))

(defthm port-typ-p-symbolp
  (implies (acl2::port-typ-p x) (symbolp x))
  :hints (("Goal" :in-theory (enable acl2::port-typ-p))))

(define nxt-tbl->exs-mod-tbl ((nxt-tbl nxt-tbl-p)
                              &key ((rslt exs-mod-tbl-p) 'nil))
  :returns (rslt exs-mod-tbl-p)
  (if (atom nxt-tbl)
      (exs-mod-tbl-fix (make-fast-alist rslt))
    (b* ((var (caar nxt-tbl))
         ((nxt-tbl-elem el) (cdar nxt-tbl))
         (size (sv::wire->width el.wire)))
      (nxt-tbl->exs-mod-tbl (rest nxt-tbl)
                            :rslt 
                            (acons! var
                                    (make-exs-mod-el :size size
                                                     :reset el.reset
                                                     :port el.port
                                                     :next el.step)
                                    rslt)))))

(define mod-tbl->reset-vmap ((tbl exs-mod-tbl-p) &key ((rslt exs-vmap-p) 'nil))
  :returns (rslt exs-vmap-p)
  (if (endp tbl) (exs-vmap-fix (make-fast-alist rslt))
    (mod-tbl->reset-vmap (rest tbl)
                         :rslt (acons! (caar tbl)
                                       (exs-mod-el->reset (cdar tbl))
                                       rslt))))

(define nxt-tbl->supp-map ((tbl nxt-tbl-p) &key ((rslt var->supp-map-p) 'nil))
  :returns (rslt var->supp-map-p)
  (if (atom tbl) (var->supp-map-fix (make-fast-alist rslt))
    (b* ((var (caar tbl))
         ((nxt-tbl-elem el) (cdar tbl)))
      (nxt-tbl->supp-map (rest tbl) :rslt (acons! var el.supp rslt)))))

(define compile-sv-design ((sv-design sv::design-p))
  :guard (sv::modalist-addr-p (sv::design->modalist sv-design))
  :returns (mv (sv-nexts sv::svex-alist-p)
               (sv-upds  sv::svex-alist-p))
  (b* (((local-stobjs sv::moddb sv::aliases)
        (mv sv-nexts sv-upds sv::moddb sv::aliases))
       ((mv err sv-upds sv-nexts ?comp-constrs
            ?flat-assigns ?flat-delays ?flat-constrs
            sv::moddb sv::aliases)
        (sv::svex-design-compile sv-design))
       ((when err)
        (mv (raise "Error returned by sv-design-compile: ~x0~%" err)
            nil sv::moddb sv::aliases)))
    (mv sv-nexts sv-upds sv::moddb sv::aliases)))

(define exs-all-dlys ((nxts sv::svex-alist-p) (dly natp))
  (or (endp nxts)
      (and (eql dly (sv::svar->delay (caar nxts)))
           (exs-all-dlys (rest nxts) dly))))

(define exs-in-upd (var (nxts sv::svex-alist-p))
  (and (not (endp nxts))
       (or (equal var (sv::svar->name (caar nxts)))
           (exs-in-upd var (rest nxts)))))

(define exs-filter-upds ((upds sv::svex-alist-p) (nxts sv::svex-alist-p)
                         &key ((rslt sv::svex-alist-p) 'nil))
  :returns (rslt sv::svex-alist-p)
  (if (endp upds) (sv::svex-alist-fix rslt)
    (exs-filter-upds (rest upds) nxts
                     :rslt
                     (if (exs-in-upd (sv::svar->name (caar upds)) nxts) rslt
                       (cons (first upds) rslt)))))

(define exsim-sv->aignet ((sv-design sv::design-p)
                          &key
                          (include-upds 'nil)
                          (save-nxt-tbl 'nil)
                          (save-mod-tbl 'nil)
                          ((rew-iterations posp) '20) 
                          (cleanup-memory 'nil)
                          (exs$  'exs$)
                          (state 'state))
  :returns (mv (new-exs$ exs-solver-undf :hyp (exs-solver-undf exs$)) state)
  (b* (((unless (sv::modalist-addr-p (sv::design->modalist sv-design)))
        (prog2$ (raise "Internal error: should have been a modalist-addr-p")
                (mv exs$ state)))
       ((mv sv-nexts sv-upds) (compile-sv-design sv-design))
       ((when (not (exs-all-dlys sv-nexts 1)))
        (prog2$ (raise "Internal error: sv-nexts should bind delay-1 var.s")
                (mv exs$ state)))
       ((when (not (exs-all-dlys sv-upds 0)))
        (prog2$ (raise "Internal error: sv-upds should bind delay-0 var.s")
                (mv exs$ state)))
       ;; BOZO -- need to add path that doesn't include nxt-tbl.. straight from
       ;; compiled sv (with hierarchy) to des-tbl.. (maybe with some rewrites..)
       (nxt-tbl               (acl2::sv-comps->nxt-tbl sv-design sv-nexts
                                                       (and include-upds (exs-filter-upds sv-upds sv-nexts))
                                                       rew-iterations))
       (mod-tbl               (nxt-tbl->exs-mod-tbl nxt-tbl))
       ((mv exs$ state)       (exs-mod-tbl->aignet mod-tbl))
       (reset-vmap            (mod-tbl->reset-vmap mod-tbl))
       (exs$                  (update-exs$-reset-vmap reset-vmap exs$))
       (exs$                  (if save-nxt-tbl
                                  (update-exs$-nxt-tbl nxt-tbl exs$)
                                (prog2$ (fast-alist-free nxt-tbl) exs$)))
       (exs$                  (if save-mod-tbl
                                  (update-exs$-mod-tbl mod-tbl exs$)
                                (prog2$ (fast-alist-free mod-tbl) exs$)))
       (supp-map              (nxt-tbl->supp-map nxt-tbl))
       (exs$                  (update-exs$-var->supp supp-map exs$))
       (-                     (and cleanup-memory (clear-memory-stuff))))
    (mv exs$ state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exs-file-exists ((fname stringp) &key (state 'state))
  (not (eq (read-file-into-string fname :start 0 :bytes 1) nil)))

(local (include-book "std/io/top" :dir :system))

(define exs-write-lines! ((lines string-listp) (chan symbolp)
                          &key (state 'state))
  :guard (non-exec (open-output-channel-p1 chan :character state))
  :returns (new-state (and (state-p1 new-state)
                           (open-output-channel-p1 chan :character new-state))
                      :hyp :guard)
  (if (endp lines) state
    (b* ((state (acl2::princ$ (first lines) chan state))
         (state (acl2::newline chan state)))
      (exs-write-lines! (rest lines) chan))))
           
(define exs-write-lines-file ((lines string-listp) (fname stringp)
                              &key (state 'state))
  (b* (((mv chan state) (acl2::open-output-channel fname :character state))
       ((when (not chan))
        (prog2$ (raise "could not open file:~x0~%" fname) state))
       (state (exs-write-lines! lines chan))
       (state (acl2::close-output-channel chan state)))
    state))

(defthm svarlist-p-implies-true-list
  (implies (sv::svarlist-p x)
           (true-listp x))
  :hints (("Goal" :in-theory (enable sv::svarlist-p)))
  :rule-classes (:rewrite :forward-chaining))

(defthm nth!-svarlist
  (implies (and (consp x) (sv::svarlist-p x))
           (sv::svar-p (nth! n x)))
  :hints (("Goal" :in-theory (enable sv::svarlist-p nth!))))

(define exs-pull-pref (path)
  :returns (x true-listp)
  (if (atom path) (list path) (cons (first path) (exs-pull-pref (rest path)))))

(define len! (x &key ((n natp) '0))
  (if (atom x) n (len! (rest x) :n (1+ n))))

(defthm len!-pos-consp
  (implies (and (consp x) (natp n))
           (posp (len! x :n n)))
  :hints (("Goal" :in-theory (enable len!)))
  :rule-classes (:forward-chaining :rewrite))

(define inject-seps (lst)
  (if (atom lst) (cons "/" lst) (list* "/" (first lst) (inject-seps (rest lst)))))

(define strip-mod (x)
  (if (atom x) x (if (atom (rest x)) (first x) (cons (first x) (strip-mod (rest x))))))

(define strip-time (str)
  (if (not (stringp str)) (raise "expected to have a string here!")
    (b* ((l (length str)))
      (cond ((not (> l 0)) (raise "did not expect empty string!"))
            ((eql (char str 0) #\#)
             (subseq str 1 l))
            (t nil)))))

(define exs-remove-pref (var pref)
  (cond ((atom pref) var)
        ((atom var) nil)
        ((equal (first var) (first pref))
         (exs-remove-pref (rest var) (rest pref)))
        (t nil)))

(define exs-merge-tbls ((x exs-vmap-p) (y exs-vmap-p))
  :returns (z exs-vmap-p :hyp :guard)
  (if (atom x) y
    (exs-merge-tbls (rest x)
                    (hons-acons (caar x) (cdar x) y))))
    
(define exs-uncovered ((x exs-vmap-p) (y exs-vmap-p))
  (and (not (atom x))
       (if (hons-get (caar x) y)
           (exs-uncovered (rest x) y)
         (caar x))))

;; BOZO -- we are assuming posedge on the clock for the change we are trying to
;; capture.. should add a "clock-edge" parameter to the design but it seems
;; like every major synchronoization is on posedge's of clocks.. 

(define exs-map-step ((var sv::svar-p) (val sv::4vec-p) clk reset pref (rslt exs-vmap-p) done)
  :returns (mv new-done (new-rslt exs-vmap-p :hyp :guard))
  (cond ((hons= var clk)
         (mv (or done (eql val 1)) rslt))
        ((hons= var reset)
         (mv done rslt))
        (t
         (mv done (acons! (sv::make-svar :name (exs-remove-pref (sv::svar->name var) pref)
                                         :delay 0 :nonblocking nil)
                          val rslt)))))

(define exs-map-chg ((chg acl2::val-chgs-p) clk reset pref (rslt exs-vmap-p) &key (done 'nil))
  :returns (mv new-done (new-rslt exs-vmap-p :hyp :guard))
  (if (atom chg) (mv done rslt)
    (b* (((mv done rslt)
          (exs-map-step (caar chg) (cdar chg) clk reset pref rslt done)))
      (exs-map-chg (rest chg) clk reset pref rslt :done done))))

(define exs-pull-chg ((chgs acl2::vcd-val-chgs-p) clk reset pref (rslt exs-vmap-p))
  :returns (mv (new-rslt exs-vmap-p :hyp :guard)
               (new-chgs acl2::vcd-val-chgs-p :hyp :guard))
  (if (atom chgs) (mv rslt ())
    (b* (((mv done rslt)
          (exs-map-chg (acl2::vcd-val-chg->val-chgs (first chgs))
                       clk reset pref rslt)))
      (if done (mv rslt (rest chgs))
        (exs-pull-chg (rest chgs) clk reset pref rslt)))))

(defthm len-exs-pull-chgs
  (implies (consp x)
           (< (len (mv-nth 1 (exs-pull-chg x a b c d)))
              (len x)))
  :rule-classes (:linear :rewrite)
  :hints (("Goal" :in-theory (enable exs-pull-chg))))

(define exs-map-chgs ((chgs acl2::vcd-val-chgs-p) clk reset pref)
  :measure (len chgs)
  :returns (rslt exs-vmaplist-p :hyp :guard)
  (if (atom chgs) ()
    (b* (((mv map new-chgs) (exs-pull-chg chgs clk reset pref nil)))
      (cons map (exs-map-chgs new-chgs clk reset pref)))))

(defthm rev!-exs-vmaplist-p
  (implies (and (exs-vmaplist-p x) (exs-vmaplist-p y))
           (exs-vmaplist-p (acl2::rev$! x y)))
  :hints (("Goal" :in-theory (enable acl2::rev$! exs-vmaplist-p))))

(define vcd$->in-lists (exs$ vcd$)
  :returns (rslt exs-vmaplist-p)
  (b* ((chgs (acl2::vcd$-val-chg-lst vcd$))
       (pref (exs$-vcd-prefix exs$))
       (clk (sv::make-svar :name (append! pref "clk") ;; BOZO (exs$-clock-name exs$))
                           :delay 0
                           :nonblocking nil))
       (reset (sv::make-svar :name (append! pref "reset") ;; BOZO (exs$-reset-name exs$))
                             :delay 0
                             :nonblocking nil)))
    (exs-vmaplist-fix (exs-map-chgs chgs clk reset pref))))

(define exs-timestamps ((x acl2::vcd-val-chgs-p) &key ((rslt string-listp) 'nil))
  :returns (r string-listp)
  (if (endp x) (acl2::strs-fix (reverse rslt))
    (exs-timestamps (rest x)
                    :rslt (cons (acl2::vcd-val-chg->timestamp (first x))
                                rslt))))

(define exs-get-restor (vcd$)
  :returns (r vcd-restor-p)
  (make-vcd-restor :comments   (acl2::vcd$-comments vcd$)
                   :date       (acl2::vcd$-date vcd$)
                   :version    (acl2::vcd$-version vcd$)
                   :timescale  (acl2::vcd$-timescale vcd$)
                   :timestamps (exs-timestamps (acl2::vcd$-val-chg-lst vcd$))
                   :parent-map (acl2::vcd$-parent-map vcd$)
                   :child-map  (acl2::vcd$-child-map vcd$)
                   :var-map    (acl2::vcd$-var-tbl vcd$)))

(define exsim-read-wave-vcd (&key (exs$ 'exs$) (state 'state))
  :returns (mv (in-lists exs-vmaplist-p) (vcd-restor vcd-restor-p))
  (b* (((local-stobjs vcd$) (mv in-lists vcd-restor vcd$))
       (vcd$ (read-vcd-file-to-vcd$ (exs-wave-vcd) state vcd$))
       (vcd-restor (exs-get-restor vcd$))
       (in-lists (vcd$->in-lists exs$ vcd$)))
    (mv in-lists vcd-restor vcd$)))

(define exs-write-objs! (objs (chan symbolp) &key (state 'state))
  :guard (non-exec (and (member (acl2::get-serialize-character state)
                                '(nil #\Y #\Z))
                        (open-output-channel-p1 chan :object state)))
  :returns (new-state (and (state-p1 new-state)
                           (member (acl2::get-serialize-character new-state)
                                   '(nil #\Y #\Z))
                           (open-output-channel-p1 chan :object new-state))
                      :hyp :guard)
  (if (atom objs) state
    (b* ((state (acl2::print-object$ (first objs) chan state)))
      (exs-write-objs! (rest objs) chan))))

(defttag :need-file-writing-for-exs-output)

(define exs-write-objs-file (objs (fname stringp) &key (state 'state))
  (b* (((mv chan state) (acl2::open-output-channel! fname :object state))
       ((when (not chan))
        (prog2$ (raise "could not open file:~x0~%" fname) state))
       (state (acl2::set-serialize-character nil state))
       (state (exs-write-objs! objs chan))
       (state (acl2::close-output-channel chan state)))
    state))

(defttag nil)

(define exs-reload-vcd ((v-rep vcd-restor-p) vcd$)
  (b* (((vcd-restor vr) v-rep)
       (vcd$ (acl2::update-vcd$-comments vr.comments vcd$))
       (vcd$ (acl2::update-vcd$-date vr.date vcd$))
       (vcd$ (acl2::update-vcd$-version vr.version vcd$))
       (vcd$ (acl2::update-vcd$-timescale vr.timescale vcd$)))
    vcd$))

(define exs-out-tbl ((vars var->ndx-map-p)
                     &key ((rslt acl2::vcd-out-map-p) ':exs-out-tbl))
  :returns (rslt acl2::vcd-out-map-p)
  (if (endp vars) (acl2::vcd-out-map-fix (make-fast-alist rslt))
    (exs-out-tbl (rest vars)
                 :rslt
                 (acons! (caar vars) (length (cdar vars)) rslt))))

(defmacro 4vec-or-x (x) `(if ,x (cdr ,x) (sv::4vec-x)))

(define exs-out-chg ((vars var->ndx-map-p)
                     (ndx natp)
                     (vmap exs-vmap-p)
                     &key
                     ((r acl2::val-chgs-p) 'nil)
                     (exs$ 'exs$))
  :returns (r acl2::val-chgs-p)
  (if (endp vars) (acl2::val-chgs-fix r)
    (b* ((var   (caar vars))
         (n-var (exsim-mk-svar var ndx))
         (look  (hons-get n-var vmap))
         (n-val (4vec-or-x look))
         (p-val (if (zp ndx) (sv::4vec-x)
                  (b* ((prv   (nfix (1- ndx)))
                       (p-var (exsim-mk-svar var prv))
                       (look  (hons-get p-var vmap)))
                    (4vec-or-x look)))))
      (exs-out-chg (rest vars) ndx vmap
                   :r (if (equal n-val p-val) r
                        (acons! var n-val r))))))

(define exs-out-chgs ((stamps string-listp)
                      (vmap exs-vmap-p)
                      &key
                      ((ndx natp) '0)
                      ((rslt acl2::vcd-val-chgs-p) 'nil)
                      (exs$ 'exs$))
  :returns (r acl2::vcd-val-chgs-p)
  (if (or (endp stamps) (> ndx (exs$-hi exs$)))
      (acl2::vcd-val-chgs-fix (reverse rslt))
    (exs-out-chgs (rest stamps) vmap :ndx (1+ ndx)
                  :rslt (cons (acl2::make-vcd-val-chg
                               :timestamp (first stamps)
                               :val-chgs  (exs-out-chg (exs$-var->ndx exs$)
                                                       ndx vmap))
                              rslt))))

(encapsulate
 (((compute-out-rpt * * * * *) => *
   :formals (var val size port styp)
   :guard (and (sv::svar-p var) (sv::4vec-p val)
               (natp size) (symbolp port) (symbolp styp))))
 
 (local (defun compute-out-rpt (var val size port styp)
          (declare (xargs :guard (and (sv::svar-p var) (sv::4vec-p val)
                                      (natp size) (symbolp port) (symbolp styp)))
                   (ignore var val size port styp))
          nil))
 
 (defthm compute-out-rpt-returns-true-listp
   (true-listp (compute-out-rpt var val size port styp))
   :rule-classes (:rewrite :type-prescription)))

(define compute-out-rpt-inst ((var sv::svar-p) (val sv::4vec-p)
                              (size natp) (port symbolp) (styp symbolp))
  (declare (ignore size))
  :returns (rslt true-listp)
  (and (or (and (eq port :input)
                (or (eq styp :free) (eq styp :rand)))
           (eq styp :fail))
       (list (list (sv::svar->name var) (sv::svar->delay var) '= val))))

(defattach compute-out-rpt compute-out-rpt-inst)

(define exs-gen-vmap ((vmap exs-vmap-p) &key (rslt 'nil) (exs$ 'exs$))
  (if (atom vmap) rslt
    (b* ((var (exsim-mk-svar (caar vmap) 0))
         (look (hons-get var (exs$-var->ndx exs$)))
         ((when (not look))
          (raise "did not find var:~x0~%" var))
         (ndxs (cdr look))
         ((when (atom ndxs))
          (raise "should not be empty ndxs:~x0~%" var)))
      (exs-gen-vmap (rest vmap)
                    :rslt (append 
                           (compute-out-rpt (caar vmap) (cdar vmap) (len! ndxs)
                                            (cdr (hons-get var (exs$-var->port exs$)))
                                            (cdr (hons-get (first ndxs) (exs$-styp-lkup exs$))))
                           rslt)))))

(define exs-gen-vals ((vmaps out-vmaps-p) &key (rslt 'nil) (exs$ 'exs$))
  (if (endp vmaps) rslt
    (exs-gen-vals (rest vmaps)
                  :rslt (cons (list (caar vmaps) 
                                    (exs-gen-vmap (cdar vmaps)))
                              rslt))))

(define set-diff-hons=-each (x y)
  (if (atom y) x (set-diff-hons=-each (set-diff-hons= x (first y)) (rest y))))

(defthm set-diff-hons=-each-svarlist
  (implies (and (sv::svarlist-p x) (svar-lists-p y))
           (sv::svarlist-p (set-diff-hons=-each x y)))
  :hints (("Goal" :in-theory (enable set-diff-hons=-each))))

(define exs-acc-supp ((v->s var->supp-map-p)
                      (max-depth natp)
                      (nxt sv::svarlist-p)
                      &key
                      ((vars sv::svarlist-p) 'nil)
                      ((rslt svar-lists-p) 'nil))
  :returns (rslt svar-lists-p)
  :measure (make-ord (1+ (nfix max-depth)) (1+ (len vars)) 0)
  (cond ((zp max-depth) (svar-lists-fix rslt))
        ((endp vars)
         (exs-acc-supp v->s (1- max-depth) nil
                       :vars nxt :rslt (cons nxt rslt)))
        (t (b* ((var (first vars))
                (supp (cdr (hons-get var v->s))))
             (exs-acc-supp v->s max-depth
                           (set-union-hons= (set-diff-hons=-each supp rslt) nxt)
                           :vars (rest vars)
                           :rslt rslt)))))
        
(define gtkw-map-var (name size)
  :returns (rslt stringp)
  (if (atom name)
      (if (and (natp size) (> size 1))
          (strap! name "[" (1- size) ":0]")
        (strap! name))
    (strap! (first name) "." (gtkw-map-var (rest name) size))))

(defthm rev$!-string-listp
  (implies (and (string-listp x) (string-listp y))
           (string-listp (acl2::rev$! x y)))
  :hints (("Goal" :in-theory (enable acl2::rev$!))))

(define insert-string ((a stringp) (x string-listp))
  :returns (rslt string-listp :hyp :guard)
  (cond ((endp x) (list a))
        ((string< a (first x)) (cons a x))
        (t (cons (first x) (insert-string a (rest x))))))

(define sort-strings ((x string-listp) &key ((rslt string-listp) 'nil))
  :returns (rslt string-listp)
  (if (endp x) (acl2::strs-fix rslt)
    (sort-strings (rest x) :rslt (insert-string (first x) rslt))))

(define exs-gtkw-vars ((vars sv::svarlist-p)
                       (var->ndx var->ndx-map-p)
                       (top-mod stringp)
                       &key
                       ((rslt string-listp) 'nil))
  :returns (rslt string-listp)
  (if (endp vars) (acl2::strs-fix (sort-strings rslt))
    (b* ((var (first vars))
         (size (len! (cdr (hons-get var var->ndx)))))
      (exs-gtkw-vars (rest vars) var->ndx top-mod
                     :rslt
                     (cons (strap! top-mod "."
                                   (gtkw-map-var (sv::svar->name var) size))
                           rslt)))))

(defthm string-listp-cdr-impl
  (implies (string-listp x) (string-listp (cdr x))))

(define exs-gtkw-groups ((groups svar-lists-p)
                         (var->ndx var->ndx-map-p)
                         (top-mod stringp)
                         &key ((rslt string-listp) 'nil))
  :returns (rslt string-listp)
  (if (endp groups) (acl2::strs-fix (rest (rev! rslt)))
    (b* ((rslt (cons (strap! "- ----- " (len! groups) " -----") rslt))
         (rslt (acl2::rev$! (exs-gtkw-vars (first groups) var->ndx top-mod) rslt)))
      (exs-gtkw-groups (rest groups) var->ndx top-mod :rslt rslt))))

(defconst *whitespace-chars* '(#\Space #\Tab #\Newline
                               #\Page #\Rubout #\Return))

(defttag :need-file-writing-for-exs-output)

(define exs-gtkw-header (suff &key (exs$ 'exs$) (state 'state))
  :returns (mv (rslt string-listp) state)
  (b* (((mv erp pwd state) (sys-call+ "pwd" () state))
       ((when erp)
        (mv (raise "pwd sys-call failed! ~x0~%" (list erp pwd))
            state))
       (pwd (first (str::strtok pwd *whitespace-chars*)))
       ((when (not pwd))
        (mv (raise "pwd call did not return valid path?~%")
            state)))
    (mv (list (strap! "[dumpfile] " #\" pwd "/" (exs-out-vcd suff) #\")
              (strap! "[savefile] " #\" pwd "/" (exs-out-gtkw suff) #\")
              (strap! "[timestart] 0")
              (strap! "[treeopen] " (exs$-top-mod exs$) "."))
        state)))

(defttag nil)

(define exs-find-fail-lvals ((ndxs ndx-list-p) &key (lvals 'lvals))
  (if (endp ndxs) nil
    (b* ((ndx (first ndxs))
         ((when (not (< ndx (lits-length lvals))))
          (raise "ndx out-of-bounds for lvals!:~x0~%"
                 (list ndx (lits-length lvals)))))
      (if (eql (get-lit ndx lvals) 1) ndx
        (exs-find-fail-lvals (rest ndxs))))))

(define exs-find-fail-ndx ((cyc natp) &key (exs$ 'exs$))
  :returns (rslt natp)
  (cond ((zp cyc)
         (if (atom (exs$-fail-ndxs exs$))
             (prog2$ (raise "did not find a fail bit set and no fail bits!") 0)
           (lnfix (first (exs$-fail-ndxs exs$)))))
        ((not (< cyc (exs$-cnl-map-length exs$)))
         (prog2$ (raise "hi index exceeds cnl-map-length:~x0~%"
                        (list cyc (exs$-cnl-map-length exs$)))
                 0))
        (t
         (b* ((ndxs (exs$-fail-ndxs exs$)))
           (stobj-let ((lvals (exs$-cnl-mapi cyc exs$)))
                      (ndx) (exs-find-fail-lvals ndxs)
                      (if (natp ndx) ndx (exs-find-fail-ndx (1- cyc))))))))

(define exs-find-fail-var (&key (exs$ 'exs$))
  :returns (rslt sv::svar-p)
  (b* ((ndx (exs-find-fail-ndx (exs$-hi exs$)))
       (look (hons-get ndx (exs$-ndx->var exs$)))
       ((when (not look))
        (prog2$ (raise "did not find var in ndx->var lookup:~x0~%" ndx) "")))
    (ndx->var-elem->var (cdr look))))

(define exs-write-gtkw-file (suff &key (exs$ 'exs$) (state 'state))
  (b* ((fail-var (exs-find-fail-var))
       (groups   (exs-acc-supp (exs$-var->supp exs$)
                               (1+ (sim-params->max-wave-var-depth
                                    (exs$-sim-params exs$)))
                               (list fail-var)))
       ((mv header state) (exs-gtkw-header suff))
       (body     (exs-gtkw-groups groups (exs$-var->ndx exs$) (exs$-top-mod exs$)))
       (footer   (list "[pattern_trace] 1" "[pattern_trace] 0"))
       (lines    (append header body footer))
       (state    (acl2::vcd-write-lines-file (exs-out-gtkw suff) lines)))
    state))

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

(define exs-ctbl->vmap ((ctbls ndx-ctbls-p)
                        &key
                        (exs$ 'exs$))
  :guard (exs-solver-rdy exs$)
  :returns (mv (rslt exs-vmap-p)
               (exs$ (exs-solver-rdy exs$) :hyp (exs-solver-rdy exs$)))
  (b* ((exs$ (exs-clear-all-cnl))
       (exs$ (exs-load-ndx-ctbls ctbls))
       ((when (not (and (natp (exs$-hi exs$))
                        (< (exs$-hi exs$) (exs$-cnl-map-length exs$)))))
        (mv (raise "internal error: insufficient cnl-map size!") exs$))
       ((mv - exs$) (exs-forward-reduce-loop () 0 :force-forward t))
       (ndx-ctbl (exs-collect-ndx-ctbl-bits))
       (vmap (exs-map-ctbl->vmap ndx-ctbl ())))
    (mv vmap exs$)))
                
(define exs-ctbls->vmaps ((out-ctbls out-ctbls-p) 
                          &key
                          ((rslt out-vmaps-p) 'nil)
                          (exs$ 'exs$))
  :guard (exs-solver-rdy exs$)
  :returns (mv (rslt out-vmaps-p)
               (exs$ (exs-solver-rdy exs$) :hyp (exs-solver-rdy exs$)))
  (if (endp out-ctbls) (mv (out-vmaps-fix rslt) exs$)
    (b* (((mv vmap exs$) (exs-ctbl->vmap (cdar out-ctbls))))
      (exs-ctbls->vmaps (rest out-ctbls) 
                        :rslt (acons! (caar out-ctbls) vmap rslt)))))

(encapsulate
 (((compute-gen-vcd *) => *
   :formals (tag)
   :guard (stringp tag)))
 
 (local (defun compute-gen-vcd (tag)
          (declare (xargs :guard (stringp tag))
                   (ignore tag))
          t)))

(define compute-gen-vcd-inst ((tag stringp))
  (declare (ignore tag))
  t)

(defattach compute-gen-vcd compute-gen-vcd-inst)

(define exs-out-vmaps-vcd ((vmaps out-vmaps-p)
                           (timestamps string-listp)
                           &key
                           (exs$ 'exs$)
                           (state 'state)
                           (vcd$ 'vcd$))
  (cond ((endp vmaps) (mv vcd$ state))
        ((not (compute-gen-vcd (caar vmaps)))
         (exs-out-vmaps-vcd (rest vmaps) timestamps))
        (t
         (b* ((val-chgs (exs-out-chgs timestamps (cdar vmaps)))
              (vcd$ (acl2::update-vcd$-val-chg-lst val-chgs vcd$))
              ((mv vcd$ state)
               (acl2::write-vcd$-to-vcd-file (exs-out-vcd (caar vmaps)) state vcd$))
              (state (exs-write-gtkw-file (caar vmaps))))
           (exs-out-vmaps-vcd (rest vmaps) timestamps)))))

(define exsim-report-results (&key (exs$ 'exs$) (state 'state))
  :guard (exs-solver-rdy exs$)
  :returns (mv (exs$ (exs-solver-rdy exs$) :hyp (exs-solver-rdy exs$))
               state)
  (b* (((local-stobjs vcd$) (mv vcd$ exs$ state))
       ((vcd-restor vr) (exs$-vcd-restor exs$))
       (top-mod (exs$-top-mod exs$))
       (var->ndx (exs$-var->ndx exs$))
       ((mv vmaps exs$) (exs-ctbls->vmaps (exs$-out-ctbls exs$)))
       (fail-seq (exs-gen-vals vmaps))
       (state (exs-write-objs-file fail-seq (exs-rpt-out)))
       (vcd$ (exs-reload-vcd vr vcd$))
       (vcd$ (acl2::update-vcd$-top-mod top-mod vcd$))
       (vcd$ (acl2::update-vcd$-out-tbl (exs-out-tbl var->ndx) vcd$))
       ((mv vcd$ state) (exs-out-vmaps-vcd vmaps vr.timestamps)))
    (mv vcd$ exs$ state)))

(define exsim-full-clean-up (&key (exs$ 'exs$))
  :guard (exs-solver-rdy exs$)
  ;; cannot return undf for sure since we may not release (causing fails on some isats..)
  ;;  :returns (new-exs$ exs-solver-undf)
  ;; BOZO -- is there anything else we should cleanup here?
  (b* (((mv - exs$) (exsim-cleanup-st))
       ;; BOZO -- this leads to memory pointer failures.. so bypassing for now..
       (exs$ (if (and (not (exs$-use-satlink exs$))
                      (exs$-release-sat exs$)) 
                 (exsim-release-isat) 
               exs$)))
    exs$))

(define exsim-early-init-sim-params ((sim-params sim-params-p)
                                     &key (exs$ 'exs$))
  :returns (new-exs$ exs-solver-undf
                     :hyp (and (exs-solver-undf exs$)
                               (not (exs$-use-satlink exs$)))
                     :hints (("Goal" :in-theory (enable exs-solver-undf))))
  (b* (((sim-params sp) sim-params))
    (if (not (true-listp sp.vcd-prefix))
        (prog2$ (raise "vcd-prefix must be true-list:~x0~%"
                       sp.vcd-prefix) 
                exs$)
      (b* ((exs$ (update-exs$-sim-params   sp             exs$))
           (exs$ (update-exs$-use-satlink  sp.use-satlink exs$))
           (exs$ (update-exs$-verbose      sp.verbose     exs$))
           (exs$ (update-exs$-release-sat  sp.release-sat exs$))
           (exs$ (update-exs$-vcd-prefix   sp.vcd-prefix  exs$)))
        exs$))))

(defthm exs-use-satlink-create-exs$-is-nil
  (equal (nth *EXS$-USE-SATLINK* (create-exs$)) nil)
  :hints (("Goal" :in-theory (enable create-exs$))))

(define exsim-prep ((mod-name stringp) 
                    (top-mod stringp)
                    (sv-design sv::design-p)
                    (sim-params sim-params-p)
                    &key (exs$ 'exs$) (state 'state))
  :returns (mv (new-exs$ exs-solver-undf
                         :hyp (exs-solver-undf exs$)
                         :hints (("Goal" :in-theory (enable exs-solver-undf
                                                            exs-mod-tbl->aignet
                                                            exsim-sv->aignet))))
               state)
  (b* (((sim-params sp) sim-params)
       (exs$             (update-exs$-sim-params sp exs$))
       (exs$             (update-exs$-verbose sp.verbose exs$))
       (exs$             (update-exs$-mod-name mod-name exs$))
       (exs$             (update-exs$-top-mod top-mod exs$))
       ((mv exs$ state)  (exsim-sv->aignet sv-design
                                           :include-upds sp.include-upds
                                           :save-nxt-tbl sp.save-nxt-tbl
                                           :save-mod-tbl sp.save-mod-tbl
                                           :rew-iterations sp.rew-iterations)))
    (mv exs$ state)))

(define exsim-run ((sim-params sim-params-p)
                   &key (exs$ 'exs$) (state 'state))
  :guard (and (exs-solver-undf exs$)
              (not (exs$-use-satlink exs$)))
  (b* ((-                (acl2::tshell-ensure))
       (-                (seed-random$ 'seed-random$-symbol :freshp t))
       (exs$             (exsim-early-init-sim-params sim-params))
       ((mv waves v-rep) (exsim-read-wave-vcd))
       (exs$             (update-exs$-vcd-restor v-rep exs$))
       ((mv exs$ state)  (exsim-init-loop waves sim-params))
       (exs$             (exsim-main-loop))
       ((mv exs$ state)  (exsim-report-results))
       (exs$             (exsim-full-clean-up)))
    (mv exs$ state)))

(defthm exs-use-satlink-exsim-prep
  (equal (nth *EXS$-USE-SATLINK* (mv-nth 0 (exsim-prep m-n t-m s-d s-p)))
         (nth *EXS$-USE-SATLINK* exs$))
  :hints (("Goal" :in-theory (enable exsim-prep
                                     exs-mod-tbl->aignet
                                     exsim-sv->aignet))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exsim ((mod-name stringp)
               (sv-design sv::design-p)
               &key
               ((top-mod stringp) '"top")
               ((sim-params sim-params-p) '*def-sim-params*)
               (state  'state))
  (b* (((local-stobjs exs$) (mv rslt exs$ state))
       ((mv exs$ state)     (exsim-prep mod-name top-mod sv-design sim-params))
       ((mv exs$ state)     (exsim-run  sim-params)))
    (mv t exs$ state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
