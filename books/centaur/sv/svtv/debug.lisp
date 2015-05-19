; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "SV")

(include-book "process")
(include-book "vcd")
(include-book "oslib/date" :dir :system)
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (include-book "std/io/base" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (in-theory (disable nth update-nth
                           acl2::nth-when-zp)))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable pick-a-point-subset-strategy)))

(defxdoc debug.lisp :parents (svtv-debug))
(local (xdoc::set-default-parents debug.lisp))

(define svtv-debug-lhs-eval ((x lhs-p)
                             (bound natp)
                             (wirevals svex-env-p)
                             (vcd-vals))
  :guard (< bound (4vecs-length vcd-vals))
  :verify-guards nil
  :measure (len x)
  :returns (xval 4vec-p)
  (b* (((mv xf xr) (lhs-decomp x))
       ((unless xf) (4vec-z))
       ((lhrange xf) xf)
       (rest (svtv-debug-lhs-eval xr bound wirevals vcd-vals))
       ((when (eq (lhatom-kind xf.atom) :z))
        (4vec-concat (2vec xf.w) (4vec-z) rest))
       ((lhatom-var xf) xf.atom)
       (idx (and (svar-indexedp xf.name) (svar-index xf.name)))
       (val (if (and idx (< idx (lnfix bound)))
                (get-4vec idx vcd-vals)
              (svex-env-fastlookup xf.name wirevals))))
    (4vec-concat (2vec xf.w)
                 (4vec-rsh (2vec xf.rsh) val)
                 rest))
  ///
  (verify-guards svtv-debug-lhs-eval))

(define svtv-debug-eval-aliases ((n natp)
                                 (aliases)
                                 (wirevals svex-env-p)
                                 (vcd-vals))
  ;; Evaluates each of the LHSes in aliases in terms of wirevals, storing the
  ;; 4vec results in vcd-vals.  We count up from 0, so as a shortcut, for each
  ;; wire that is aliased to an earlier one, we look up the stored value in
  ;; vcd-vals instead.  This saves hash lookups.  Svtv-debug-eval-aliases-track
  ;; is the same, but keeps track of which indices changed values.
  :guard (and (<= n (aliass-length aliases))
              (<= (aliass-length aliases)
                  (4vecs-length vcd-vals)))
  :measure (nfix (- (aliass-length aliases) (nfix n)))
  :returns (vcd-vals1)
  (b* (((when (mbe :logic (zp (- (aliass-length aliases) (nfix n)))
                   :exec (eql (aliass-length aliases) n)))
        vcd-vals)
       (lhs (get-alias n aliases))
       (val (svtv-debug-lhs-eval lhs n wirevals vcd-vals))
       (vcd-vals (set-4vec n val vcd-vals)))
    (svtv-debug-eval-aliases (1+ (lnfix n)) aliases wirevals vcd-vals))
  ///
  (defthm len-vcd-vals-of-svtv-debug-eval-aliases
    (<= (len vcd-vals)
        (len (svtv-debug-eval-aliases n aliases wirevals vcd-vals)))
    :rule-classes :linear))

(define svtv-debug-eval-aliases-track ((n natp)
                                       (aliases)
                                       (wirevals svex-env-p)
                                       (vcd-vals))
  :guard (and (<= n (aliass-length aliases))
              (<= (aliass-length aliases)
                  (4vecs-length vcd-vals)))
  :returns (mv (changes nat-listp)
               (vcd-vals1))
  :measure (nfix (- (aliass-length aliases) (nfix n)))
  (b* (((when (mbe :logic (zp (- (aliass-length aliases) (nfix n)))
                   :exec (eql (aliass-length aliases) n)))
        (mv nil vcd-vals))
       (lhs (get-alias n aliases))
       (val (svtv-debug-lhs-eval lhs n wirevals vcd-vals))
       (prev-val (get-4vec n vcd-vals))
       (vcd-vals (set-4vec n val vcd-vals))
       ((mv rest-changes vcd-vals)
        (svtv-debug-eval-aliases-track
         (1+ (lnfix n)) aliases wirevals vcd-vals)))
    (mv (if (equal prev-val val)
            rest-changes
          (cons (lnfix n) rest-changes))
        vcd-vals))
  ///
  (defthm len-vcd-vals-of-svtv-debug-eval-aliases-track
    (<= (len vcd-vals)
        (len (mv-nth 1 (svtv-debug-eval-aliases-track n aliases wirevals vcd-vals))))
    :rule-classes :linear)

  (defthm nat-list-max-of-svtv-debug-eval-aliases-track
    (implies (consp (mv-nth 0 (svtv-debug-eval-aliases-track n aliases wirevals vcd-vals)))
             (< (nat-list-max
                 (mv-nth 0 (svtv-debug-eval-aliases-track n aliases wirevals vcd-vals)))
                (len aliases)))
    :hints(("Goal" :in-theory (enable nat-list-max)))
    :rule-classes :linear))


(fty::deffixcong svex-env-equiv svex-env-equiv (append a b) a
  :hints(("Goal" :in-theory (enable svex-env-fix))))

(fty::deffixcong svex-env-equiv svex-env-equiv (append a b) b
  :hints(("Goal" :in-theory (enable svex-env-fix append))))

(define svtv-debug-run ((phase natp)
                        (nphases natp)
                        (inalist svex-env-p)
                        (ins svtv-lines-p)
                        (ovlines svtv-overridelines-p)
                        (prev-state svex-env-p)
                        (updates svex-alist-p)
                        (next-states svex-alist-p)
                        (invars svarlist-p)
                        aliases vcd-wiremap vcd-vals
                        (p vl-printedlist-p))
  :guard-hints (("goal" :do-not-induct t))
  :guard (and (<= phase nphases)
              (<= (aliass-length aliases) (vcdwires-length vcd-wiremap))
              (<= (vcdwires-length vcd-wiremap) (4vecs-length vcd-vals))
              (<= (aliass-length aliases) (4vecs-length vcd-vals)))
  :returns (mv vcd-vals1
               (p1 vl-printedlist-p))
  :measure (nfix (- (nfix nphases) (nfix phase)))
  (b* (((when (mbe :logic (zp (- (nfix nphases) (nfix phase)))
                   :exec (eql nphases phase)))
        ;; Just print the new time.
        (mv vcd-vals
            (vcd-dump-delta (* 10 (lnfix phase)) nil vcd-vals vcd-wiremap p)))
       (in-vals (svex-alist-eval (svtv-phase-inputs phase ins ovlines invars)
                                 inalist))
       (eval-alist (append in-vals prev-state))
       ((mv wirevals next-state)
        (with-fast-alist eval-alist
          (mv (svex-alist-eval updates eval-alist)
              (svex-alist-eval next-states eval-alist))))
       (all-wirevals (append in-vals wirevals))
       ((mv changes vcd-vals)
        (with-fast-alist all-wirevals
          ;; evaluate aliases and stick values in vcd-vals,
          ;; tracking changes if phase > 0
          (if (zp phase)
              (let* ((vcd-vals (svtv-debug-eval-aliases 0 aliases all-wirevals vcd-vals)))
                (mv nil vcd-vals))
          (svtv-debug-eval-aliases-track 0 aliases all-wirevals vcd-vals))))
       ;; print out changed vals (or all if phase = 0)
       (p (if (zp phase)
              (vcd-dump-first-snapshot vcd-vals vcd-wiremap p)
            (vcd-dump-delta (* 10 phase) changes vcd-vals vcd-wiremap p))))
    (svtv-debug-run (1+ (lnfix phase))
                    nphases inalist
                    ins ovlines
                    next-state
                    updates next-states invars
                    aliases vcd-wiremap
                    vcd-vals p)))

(defthm true-list-listp-of-append
  (implies (and (true-list-listp a)
                (true-list-listp b))
           (true-list-listp (append a b)))
  :hints(("Goal" :in-theory (enable true-list-listp))))

(defthm svex-env-p-of-pairlis$
  (implies (and (svarlist-p x)
                (4veclist-p y)
                (equal (len x) (len y)))
           (svex-env-p (pairlis$ x y)))
  :hints(("Goal" :in-theory (enable svex-env-p
                                    svarlist-p
                                    4veclist-p
                                    pairlis$))))


(define svtv-debug ((x svtv-p)
                    (inalist svex-env-p)
                    &key
                    ((filename  stringp) '"svtv-debug.vcd")
                    (state 'state))
  :parents (svex-stvs)
  :short "Dump a VCD waveform showing the internal signals of an svex STV."
  :prepwork ((local (in-theory (disable max))))
  :verbosep t
  (b* (((svtv x) x)
       (mod-fn (intern-in-package-of-symbol
                (str::cat (symbol-name x.name) "-MOD")
                x.name))
       ((mv err design)
        (acl2::magic-ev-fncall mod-fn nil state t t))
       ((when err)
        (raise "Error: couldn't run ~x0: ~@1~%" mod-fn err)
        state)
       ((unless (and (design-p design)
                     (modalist-addr-p (design->modalist design))))
        (raise "Error: ~x0 returned a malformed design~%" mod-fn)
        state)

       ((acl2::local-stobjs moddb aliases vcd-wiremap vcd-vals)
        (mv moddb aliases vcd-wiremap vcd-vals state))
       ;; Make a moddb, canonical alias table, and flattened
       ;; (non-alias-normalized) assignments from the design.  These are
       ;; expressed terms of indexed variable names.
       ((mv err assigns moddb aliases)
        (svex-design-flatten design))
       ((when err)
        (raise "~@0~%" err)
        (mv moddb aliases vcd-wiremap vcd-vals state))
       ;; get the index of the top-level module within the moddb
       (modidx (moddb-modname-get-index (design->top design) moddb))
       ;; note: skip this step to leave things in terms of wire indices
       ;; Translate the alias table into named variables.
       ;; (aliases (aliases-indexed->named aliases modidx moddb))

       ;; Alias-normalize the assignments and make a delay table
       ((mv assigns delays)
        (svex-normalize-assigns assigns aliases))

       ;; Process the timing diagram into internal form
       (ins x.orig-ins)
       (overrides x.orig-overrides)
       (outs (append x.orig-outs x.orig-internals))
       ;; really only doing the outs in case (likely) they contain more phases
       ;; than ins/overrides, for nphases computation
       ((mv err ins) (svtv-wires->lhses ins modidx moddb aliases))
       ((when err) (raise "Error resolving inputs: ~@0" err)
        (mv moddb aliases vcd-wiremap vcd-vals state))
       ((mv err overrides) (svtv-wires->lhses overrides modidx moddb aliases))
       ((when err) (raise "Error resolving overrides: ~@0" err)
        (mv moddb aliases vcd-wiremap vcd-vals state))
       ((mv err outs) (svtv-wires->lhses outs modidx moddb aliases))
       ((when err) (raise "Error resolving outputs: ~@0" err)
        (mv moddb aliases vcd-wiremap vcd-vals state))

       ;; get the total number of phases to simulate and extend the
       ;; inputs/overrides to that length
       (nphases (max (svtv-max-length ins)
                     (max (svtv-max-length overrides)
                          (svtv-max-length outs))))
       (ins (svtv-expand-lines ins nphases))
       (overrides (svtv-expand-lines overrides nphases))

       ;; Each override has a unique test variable (determining if the override
       ;; happens in a given phase) and override value variable.  This
       ;; generates them (as tagged indices) and records them in data
       ;; structures to associate the LHS for each override with its variables
       ;; and entries.
       ((mv ovlines ovs) (svtv-lines->overrides overrides 0))

       ;; Apply the overrides to the assigns.  Each wire that is overridden has
       ;; its gate-level assignment replaced with something like:
       ;; (if override-this-phase override-value original-assignment)
       ;; except that extra care is taken to override only the specified range.
       (overridden-assigns (svex-apply-overrides ovs (make-fast-alist assigns)))
       ;; Note! In defsvtv-main, we need to keep the original assigns around so
       ;; that if an output/internal refers to an overridden variable, we can
       ;; get that variable's value before overriding it.  At the moment we
       ;; don't pay attention to output variables in svtv-debug, so we don't
       ;; care about this.  If this changes, revisit this issue.

       (- (fast-alist-free overridden-assigns))
       ;; Compose together the final (gate-level) assignments to get full
       ;; update formulas (in terms of PIs and current states), and compose
       ;; delays with these to get next states.       
       ((mv updates next-states) (svex-compose-assigns/delays overridden-assigns delays))

       ;; Compute an initial state of all Xes
       (states (svex-alist-keys next-states))
       (initst (pairlis$ states (replicate (len states) (4vec-x))))

       ;; Start VCD creation.  Make the wiremap and the scope structure (from
       ;; which we write out the module hierarchy portion of the VCD file.)
       (vcd-wiremap (resize-vcdwires (aliass-length aliases) vcd-wiremap))
       ((mv scope & vcd-wiremap) (vcd-moddb->scopes "top" modidx 0 0 moddb vcd-wiremap))

       ;; Start accumulating the contents of the VCD file into reverse
       ;; string/char accumulator p.  Print the header into p.
       ((mv date state) (oslib::date))
       (p (vcd-print-header date scope nil))

       ;; Set up the VCD values structure, an array of 4vecs -- these are
       ;; conveniently initialized to Xes
       (vcd-vals (resize-4vecs (vcdwires-length vcd-wiremap) vcd-vals))

       ;; collect the set of all input variables.  We generate a unique
       ;; variable per phase for each variable (unless it is bound to an STV
       ;; input variable).  This wouldn't be strictly necessary since we're
       ;; going to set these to Xes anyway, but this is how we do it for now.
       (in-vars (acl2::hons-set-diff (svexlist-collect-vars
                                      (append (svex-alist-vals updates)
                                              (svex-alist-vals next-states)))
                                     (append (svex-alist-keys updates)
                                             states)))

       ((with-fast inalist))
       ;; Run the sequence of steps, recording value changes at each step and
       ;; printing them into p.
       ((mv vcd-vals p)
        (svtv-debug-run 0 nphases inalist
                        ins ovlines initst
                        updates next-states in-vars
                        aliases vcd-wiremap vcd-vals p))

       ;; Write the contents of p to an actual file.
       ((mv channel state)
        (open-output-channel (mbe :logic (acl2::str-fix filename) :exec filename)
                             :character state))
       ((unless channel)
        (raise "Couldn't write vcd file ~s0~%" filename)
        (mv moddb aliases vcd-wiremap vcd-vals state))
       (state (princ$ (vl::vl-printedlist->string p) channel state))
       (state (close-output-channel channel state)))
    (mv moddb aliases vcd-wiremap vcd-vals state))
  ///
  (defmacro stv-debug (&rest args) (cons 'svtv-debug args)))
