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
(include-book "fsm-base")
(include-book "vcd")
(include-book "oslib/date" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))
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
       ((when (equal prev-val val))
        (svtv-debug-eval-aliases-track
         (1+ (lnfix n)) aliases wirevals vcd-vals))
       ((mv rest-changes vcd-vals)
        (svtv-debug-eval-aliases-track
         (1+ (lnfix n)) aliases wirevals vcd-vals)))
    (mv (cons (lnfix n) rest-changes)
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

#||
(trace$ #!sv
        (svtv-debug-writephases
         :entry (list 'svtv-debug-writephases phase nphases inalist ins)
         :exit (list 'svtv-debug-writephases)))
||#

(define svtv-debug-writephases ((phase natp)
                        (nphases natp)
                        (offset natp)
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
               (p1 vl-printedlist-p)
               (final-state svex-env-p))
  :measure (nfix (- (nfix nphases) (nfix phase)))
  (b* (((when (mbe :logic (zp (- (nfix nphases) (nfix phase)))
                   :exec (eql nphases phase)))
        (mv vcd-vals (vl::vl-printedlist-fix p) (svex-env-fix prev-state)))
       (in-vals (svex-alist-eval (svtv-phase-inputs phase ins ovlines invars)
                                 inalist))
       (- (clear-memoize-table 'svex-eval))
       (eval-alist (append in-vals prev-state))
       ((mv wirevals next-state)
        (with-fast-alist eval-alist
          (mv (svex-alist-eval updates eval-alist)
              (svex-alist-eval next-states eval-alist))))
       (all-wirevals (append in-vals wirevals))
       (full-phase (+ (lnfix phase) (lnfix offset)))
       ((mv changes vcd-vals)
        (with-fast-alist all-wirevals
          ;; evaluate aliases and stick values in vcd-vals,
          ;; tracking changes if phase > 0
          (if (zp full-phase)
              (let* ((vcd-vals (svtv-debug-eval-aliases 0 aliases all-wirevals vcd-vals)))
                (mv nil vcd-vals))
          (svtv-debug-eval-aliases-track 0 aliases all-wirevals vcd-vals))))
       ;; print out changed vals (or all if phase = 0)
       (p (if (zp full-phase)
              (vcd-dump-first-snapshot vcd-vals vcd-wiremap p)
            (vcd-dump-delta (* 10 full-phase) changes vcd-vals vcd-wiremap p))))
    (svtv-debug-writephases (1+ (lnfix phase))
                    nphases offset inalist
                    ins ovlines
                    next-state
                    updates next-states invars
                    aliases vcd-wiremap
                    vcd-vals p))
  ///
  (defret len-of-svtv-debug-writephases-vcd-vals
    (<= (len vcd-vals)
        (len vcd-vals1))
    :rule-classes :linear))




(define svtv-debug-fsm-writephases ((cycle natp)
                                    (nphases-per-cycle natp)
                                    (inalists svex-envlist-p)
                                    (ins svtv-lines-p)
                                    (ovlines svtv-overridelines-p)
                                    (prev-st svex-env-p)
                                    (updates svex-alist-p)
                                    (next-states svex-alist-p)
                                    (invars svarlist-p)
                                    aliases vcd-wiremap vcd-vals
                                    (p vl-printedlist-p))
    :guard-hints (("goal" :do-not-induct t))
    :guard (and (<= (aliass-length aliases) (vcdwires-length vcd-wiremap))
                (<= (vcdwires-length vcd-wiremap) (4vecs-length vcd-vals))
                (<= (aliass-length aliases) (4vecs-length vcd-vals)))
    :measure (len inalists)
  :returns (mv vcd-vals1
               (p1 vl-printedlist-p))
    (b* ((cycle (lnfix cycle))
         (nphases-per-cycle (lnfix nphases-per-cycle))
         (phase (* cycle nphases-per-cycle))
         ((when (atom inalists))
          ;; just print the new time.
          (mv vcd-vals (vcd-dump-delta (* 10 (lnfix phase)) nil vcd-vals vcd-wiremap p)))
         (inalist (car inalists))
         ((with-fast inalist))
         ((mv vcd-vals p next-st)
          (svtv-debug-writephases
           0 nphases-per-cycle phase inalist ins ovlines prev-st updates next-states invars aliases vcd-wiremap vcd-vals p)))
      (svtv-debug-fsm-writephases
       (1+ cycle) nphases-per-cycle (cdr inalists) ins ovlines next-st updates next-states invars aliases vcd-wiremap vcd-vals p)))




(defthm true-list-listp-of-append
  (implies (and (true-list-listp a)
                (true-list-listp b))
           (true-list-listp (append a b)))
  :hints(("Goal" :in-theory (enable true-list-listp))))


(defenum debugdata-status-p
  (:empty :initialized :composed))

(local (defun debugdata-renaming (field-names)
         (b* (((when (atom field-names)) nil)
              (field (car field-names))
              (new-field (intern$ (cat "DEBUGDATA->" (symbol-name field)) "SV"))
              (update (intern$ (cat "UPDATE-" (symbol-name field)) "SV"))
              (new-update (intern$ (cat "SET-DEBUGDATA->" (symbol-name field)) "SV")))
           (cons (list field new-field)
                 (cons (list update new-update)
                       (debugdata-renaming (cdr field-names)))))))

(make-event
 (b* ((fields
       `((design     :type (satisfies design-p)           :initially ,(make-design :top ""))
         (modidx     :type (integer 0 *)                  :initially 0)
         (assigns    :type (satisfies svex-alist-p)       :initially nil)
         (delays     :type (satisfies svar-map-p)         :initially nil)
         (updates    :type (satisfies svex-alist-p)       :initially nil)
         (nextstates :type (satisfies svex-alist-p)       :initially nil)
         (svtv       :type (satisfies svtv-p)             :initially ,(make-svtv :nphases 0))
         (nphases    :type (integer 0 *)                  :initially 0)
         (ins        :type (satisfies svtv-lines-p)       :initially nil)
         (outs       :type (satisfies svtv-lines-p)       :initially nil)
         (overrides  :type (satisfies svtv-lines-p)       :initially nil)
         (override-assigns :type (satisfies svex-alist-p) :initially nil)
         (status     :type (satisfies debugdata-status-p) :initially :empty)))
      (field-names (strip-cars fields))
      (renaming (debugdata-renaming field-names))
      ;; (fns (append '(debugdatap create-debugdata)
      ;;              (acl2::strip-cadrs renaming)))
      (make-binder (std::da-make-binder 'debugdata field-names)))
   
   `(progn
      (defstobj debugdata
        ,@fields
        :renaming ,renaming)
      (in-theory (disable create-debugdata debugdatap))
      ,make-binder)))


;; This is much faster in logic mode (even with the svarlist-addr-p guard
;; check) than program mode, where presumably invariant-risk is killing us.
(define svtv-debug-init ((design design-p)
                         &key
                         (moddb 'moddb)
                         (aliases 'aliases)
                         (debugdata 'debugdata))
  :guard (svarlist-addr-p (modalist-vars (design->modalist design)))
  :returns (mv err moddb-out aliases-out debugdata-out)
  :short "Prepares an SV design for SVTV debugging, to the extent possible without
          specifying an SVTV."
  :long "<p>This does the initial compilation of the design, creating the
moddb, aliases table, and local wire assignments and delays.  See @(see
svtv-debug-set-svtv) for the next step, which composes the signals into their
nextstate and update functions given a timing diagram.</p>

<p>Technical: Erases and recreates the moddb, aliases, and debugdata stobjs.</p>"
  (b* ((design (design-fix design))

       ;; Make a moddb, canonical alias table, and flattened, alias-normalized
       ;; assignments from the design.  :Indexedp nil leaves wires expressed in
       ;; terms of paths rather than absolute moddb indices.
       ((mv err assigns delays ?constraints moddb aliases)
        (svex-design-flatten-and-normalize design :indexedp nil))

       ((when err)
        (raise "~@0~%" err)
        (mv err moddb aliases debugdata))
       ;; get the index of the top-level module within the moddb
       (modidx (moddb-modname-get-index (design->top design) moddb))

       (debugdata (set-debugdata->design design debugdata))
       (debugdata (set-debugdata->modidx modidx debugdata))
       (debugdata (set-debugdata->assigns assigns debugdata))
       (debugdata (set-debugdata->delays delays debugdata))
       (debugdata (set-debugdata->updates nil   debugdata)) ;; not available yet
       (debugdata (set-debugdata->nextstates nil debugdata))
       (debugdata (set-debugdata->status :initialized debugdata)))
    (mv nil moddb aliases debugdata))
  ///
  (defret svtv-debug-init-moddb-ok
    (and (moddb-mods-ok moddb-out)
         (moddb-basics-ok moddb-out)))

  (defret svtv-debug-init-modidx-ok
    (implies (not err)
             (< (nth *debugdata->modidx* debugdata-out)
                (nfix (nth *moddb->nmods1* moddb-out)))))

  (defret svtv-debug-init-totalwires-ok
    (implies (not err)
             (<= (moddb-mod-totalwires
                  (nth *debugdata->modidx* debugdata-out) moddb-out)
                 (len aliases-out)))))


(define svtv-debug-set-ios-logic (&key 
                                   ((ins true-list-listp) 'nil)
                                   ((outs true-list-listp) 'nil)
                                   ((internals true-list-listp) 'nil)
                                   ((overrides true-list-listp) 'nil)
                                   (moddb 'moddb)
                                   (aliases 'aliases)
                                   (debugdata 'debugdata)
                                   (rewrite 't))
  :guard (and (moddb-ok moddb)
              (< (debugdata->modidx debugdata) (moddb->nmods moddb))
              (<= (moddb-mod-totalwires (debugdata->modidx debugdata) moddb)
                  (aliass-length aliases)))
  :returns debugdata-out
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable debugdatap))))
  (b* (((debugdata debugdata))
       ((when (eq debugdata.status :empty))
        (raise "Error: Need to do SVTV-DEBUG-INIT before SVTV-DEBUG-SET-IOS~%")
        debugdata)

       ;; Process the timing diagram into internal form       
       (outs (append outs internals))
       ;; really only doing the outs in case (likely) they contain more phases
       ;; than ins/overrides, for nphases computation
       ((mv err ins) (svtv-wires->lhses ins debugdata.modidx moddb aliases))
       ((when err) (raise "Error resolving inputs: ~@0" err)
        debugdata)
       ((mv err overrides) (svtv-wires->lhses overrides debugdata.modidx moddb aliases))
       ((when err) (raise "Error resolving overrides: ~@0" err)
        debugdata)
       ((mv err outs) (svtv-wires->lhses outs debugdata.modidx moddb aliases))
       ((when err) (raise "Error resolving outputs: ~@0" err)
        debugdata)

       ;; get the total number of phases to simulate and extend the
       ;; inputs/overrides to that length
       (nphases (max (svtv-max-length ins)
                     (max (svtv-max-length overrides)
                          (svtv-max-length outs))))
       (overrides (svtv-expand-lines overrides nphases))

       ((mv updates next-states override-assigns)
        (b* (((when (and (eq debugdata.status :composed)
                         (equal debugdata.overrides overrides)))
              ;; Presumably we're just updating some inputs or outputs.  We
              ;; don't need to compose assigns/delays again, which is an
              ;; expensive part of the operation.
              (mv debugdata.updates debugdata.nextstates nil))

             ;; Each override has a unique test variable (determining if the override
             ;; happens in a given phase) and override value variable.  This
             ;; generates them (as tagged indices) and records them in data
             ;; structures to associate the LHS for each override with its variables
             ;; and entries.
             ((mv ?ovlines ovs) (svtv-lines->overrides overrides 0))

             ;; Apply the overrides to the assigns.  Each wire that is overridden has
             ;; its gate-level assignment replaced with something like:
             ;; (if override-this-phase override-value original-assignment)
             ;; except that extra care is taken to override only the specified range.
             (overridden-assigns (svex-apply-overrides ovs (make-fast-alist debugdata.assigns)))
             ;; Note! In defsvtv-main, we need to keep the original assigns around so
             ;; that if an output/internal refers to an overridden variable, we can
             ;; get that variable's value before overriding it.  At the moment we
             ;; don't pay attention to output variables in svtv-debug, so we don't
             ;; care about this.  If this changes, revisit this issue.
             
             (- (fast-alist-free overridden-assigns))
             
             ((mv updates next-states ?constraints)
              ;; Compose together the final (gate-level) assignments to get full
              ;; update formulas (in terms of PIs and current states), and compose
              ;; delays with these to get next states.
              (svex-compose-assigns/delays overridden-assigns
                                           debugdata.delays
                                           nil
                                           :rewrite rewrite)))
          (mv updates next-states overridden-assigns)))

       (debugdata (set-debugdata->updates updates debugdata))
       (debugdata (set-debugdata->nextstates next-states debugdata))
       (debugdata (set-debugdata->nphases nphases debugdata))
       (debugdata (set-debugdata->ins ins debugdata))
       (debugdata (set-debugdata->outs outs debugdata))
       (debugdata (set-debugdata->overrides overrides debugdata))
       (debugdata (set-debugdata->override-assigns override-assigns debugdata))
       (debugdata (set-debugdata->status :composed debugdata)))
    debugdata)
  ///
  (defret svtv-debug-set-ios-modidx-unchanged
    (equal (nth *debugdata->modidx* debugdata-out)
           (nth *debugdata->modidx* debugdata))))

(define svtv-debug-set-ios (&key 
                             ((inputs true-list-listp) 'nil)
                             ((outputs true-list-listp) 'nil)
                             ((internals true-list-listp) 'nil)
                             ((overrides true-list-listp) 'nil)
                             (moddb 'moddb)
                             (aliases 'aliases)
                             (debugdata 'debugdata)
                             (rewrite 't))
  :mode :program
  :hooks nil
  (svtv-debug-set-ios-logic
   :ins inputs :outs outputs :internals internals :overrides overrides
   :rewrite rewrite))


(define svtv-debug-set-svtv ((x svtv-p)
                             &key 
                             (moddb 'moddb)
                             (aliases 'aliases)
                             (debugdata 'debugdata)
                             (rewrite 't))
  :guard (and (moddb-ok moddb)
              (< (debugdata->modidx debugdata) (moddb->nmods moddb))
              (<= (moddb-mod-totalwires (debugdata->modidx debugdata) moddb)
                  (aliass-length aliases)))
  :returns debugdata-out
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable debugdatap))))
  (svtv-debug-set-ios-logic
   :ins (svtv->orig-ins x)
   :outs (svtv->orig-outs x)
   :internals (svtv->orig-internals x)
   :overrides (svtv->orig-overrides x)
   :moddb moddb
   :aliases aliases
   :debugdata debugdata
   :rewrite rewrite)
  ///
  (defret svtv-debug-set-svtv-modidx-unchanged
    (equal (nth *debugdata->modidx* debugdata-out)
           (nth *debugdata->modidx* debugdata))))



(define svtv-debug-run-logic ((inalist svex-env-p)
                              &key
                              ((filename stringp) '"svtv-debug.vcd")
                              (moddb 'moddb)
                              (aliases 'aliases)
                              (debugdata 'debugdata)
                              (vcd-wiremap 'vcd-wiremap)
                              (vcd-vals 'vcd-vals)
                              (state 'state))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable debugdatap))))
  :guard (and (moddb-ok moddb)
              (< (debugdata->modidx debugdata) (moddb->nmods moddb))
              (<= (moddb-mod-totalwires (debugdata->modidx debugdata) moddb)
                  (aliass-length aliases)))

  :returns (mv vcd-wiremap vcd-vals state)
  (b* (((debugdata debugdata))

       ;; (- (acl2::sneaky-save 'debugdata.updates debugdata.updates))
       ;; Compute an initial state of all Xes
       (states (svex-alist-keys debugdata.nextstates))
       (initst (pairlis$ states (replicate (len states) (4vec-x))))

       ;; Start VCD creation.  Make the wiremap and the scope structure (from
       ;; which we write out the module hierarchy portion of the VCD file.)
       (vcd-wiremap (resize-vcdwires (aliass-length aliases) vcd-wiremap))
       ((mv scope & vcd-wiremap) (vcd-moddb->scopes "top" debugdata.modidx 0 0 moddb vcd-wiremap))

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
                                      (append (svex-alist-vals debugdata.updates)
                                              (svex-alist-vals debugdata.nextstates)))
                                     (append (svex-alist-keys debugdata.updates)
                                             states)))

       ((with-fast inalist))

       (ins (svtv-expand-lines debugdata.ins debugdata.nphases))
       ((mv ovlines ?ovs) (svtv-lines->overrides debugdata.overrides 0))
       ;; Run the sequence of steps, recording value changes at each step and
       ;; printing them into p.
       ((mv vcd-vals p)
        (svtv-debug-fsm-writephases
         0 debugdata.nphases (list inalist)
         ins ovlines initst
         debugdata.updates debugdata.nextstates in-vars
         aliases vcd-wiremap vcd-vals p))

       ;; Write the contents of p to an actual file.
       ((mv channel state)
        (open-output-channel (mbe :logic (acl2::str-fix filename) :exec filename)
                             :character state))
       ((unless channel)
        (raise "Couldn't write vcd file ~s0~%" filename)
        (mv vcd-wiremap vcd-vals state))
       (state (princ$ (vl::vl-printedlist->string p) channel state))
       (state (close-output-channel channel state)))
    (mv vcd-wiremap vcd-vals state)))

(define svtv-debug-run ((inalist svex-env-p)
                        &key
                        ((filename stringp) '"svtv-debug.vcd")
                        (moddb 'moddb)
                        (aliases 'aliases)
                        (debugdata 'debugdata)
                        (vcd-wiremap 'vcd-wiremap)
                        (vcd-vals 'vcd-vals)
                        (state 'state))
  :mode :program :hooks nil
  (svtv-debug-run-logic
   inalist
   :filename filename
   :moddb moddb
   :aliases aliases
   :debugdata debugdata
   :vcd-wiremap vcd-wiremap
   :vcd-vals vcd-vals))


(define svtv-debug-run-fsm ((inalists svex-envlist-p)
                            (initst svex-env-p)
                            &key
                            ((filename stringp) '"svtv-debug.vcd")
                            (moddb 'moddb)
                            (aliases 'aliases)
                            (debugdata 'debugdata)
                            (vcd-wiremap 'vcd-wiremap)
                            (vcd-vals 'vcd-vals)
                            (state 'state))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable debugdatap))))
  :guard (and (moddb-ok moddb)
              (< (debugdata->modidx debugdata) (moddb->nmods moddb))
              (<= (moddb-mod-totalwires (debugdata->modidx debugdata) moddb)
                  (aliass-length aliases)))

  :returns (mv vcd-wiremap vcd-vals state)
  (b* (((debugdata debugdata))

       (states (svex-alist-keys debugdata.nextstates))

       ;; Start VCD creation.  Make the wiremap and the scope structure (from
       ;; which we write out the module hierarchy portion of the VCD file.)
       (vcd-wiremap (resize-vcdwires (aliass-length aliases) vcd-wiremap))
       ((mv scope & vcd-wiremap) (vcd-moddb->scopes "top" debugdata.modidx 0 0 moddb vcd-wiremap))

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
                                      (append (svex-alist-vals debugdata.updates)
                                              (svex-alist-vals debugdata.nextstates)))
                                     (append (svex-alist-keys debugdata.updates)
                                             states)))

       (ins (svtv-expand-lines debugdata.ins debugdata.nphases))
       ((mv ovlines ?ovs) (svtv-lines->overrides debugdata.overrides 0))
       ;; Run the sequence of steps, recording value changes at each step and
       ;; printing them into p.
       ((mv vcd-vals p)
        (svtv-debug-fsm-writephases 0 debugdata.nphases inalists
                                    ins ovlines initst
                                    debugdata.updates debugdata.nextstates in-vars
                                    aliases vcd-wiremap vcd-vals p))

       ;; Write the contents of p to an actual file.
       ((mv channel state)
        (open-output-channel (mbe :logic (acl2::str-fix filename) :exec filename)
                             :character state))
       ((unless channel)
        (raise "Couldn't write vcd file ~s0~%" filename)
        (mv vcd-wiremap vcd-vals state))
       (state (princ$ (vl::vl-printedlist->string p) channel state))
       (state (close-output-channel channel state)))
    (mv vcd-wiremap vcd-vals state)))


(define svtv-debug-core ((x svtv-p)
                         (inalist svex-env-p)
                         &key
                         ((filename  stringp) '"svtv-debug.vcd")
                         (moddb 'moddb)
                         (aliases 'aliases)
                         (debugdata 'debugdata)
                         (vcd-wiremap 'vcd-wiremap)
                         (vcd-vals 'vcd-vals)
                         (rewrite 't)
                         (state 'state))

  :returns (mv moddb aliases debugdata vcd-wiremap vcd-vals state)
  :hooks ((:fix :omit (moddb aliases)))
  (b* (((svtv x))
       (mod-fn (intern-in-package-of-symbol
                (str::cat (symbol-name x.name) "-MOD")
                x.name))
       ((mv err design)
        (acl2::magic-ev-fncall mod-fn nil state t t))
       ((when err)
        (raise "Error: couldn't run ~x0: ~@1~%" mod-fn err)
        (mv moddb aliases debugdata vcd-wiremap vcd-vals state))
       ((unless (and (design-p design)
                     (modalist-addr-p (design->modalist design))))
        (raise "Error: ~x0 returned a malformed design~%" mod-fn)
        (mv moddb aliases debugdata vcd-wiremap vcd-vals state))

       ((mv err moddb aliases debugdata) (svtv-debug-init design))
       ((when err)
        (mv moddb aliases debugdata vcd-wiremap vcd-vals state))
       (debugdata (svtv-debug-set-svtv x :rewrite rewrite))
       ((mv vcd-wiremap vcd-vals state)
        (svtv-debug-run-logic inalist :filename filename)))
    (mv moddb aliases debugdata vcd-wiremap vcd-vals state)))

(define svtv-debug-fsm-core ((x svtv-p)
                             (inalists svex-envlist-p)
                             (initst svex-env-p)
                             &key
                             ((filename  stringp) '"svtv-debug.vcd")
                             (moddb 'moddb)
                             (aliases 'aliases)
                             (debugdata 'debugdata)
                             (vcd-wiremap 'vcd-wiremap)
                             (vcd-vals 'vcd-vals)
                             (rewrite 't)
                             (state 'state))

  :returns (mv moddb aliases debugdata vcd-wiremap vcd-vals state)
  :hooks ((:fix :omit (moddb aliases)))
  (b* (((svtv x))
       (mod-fn (intern-in-package-of-symbol
                (str::cat (symbol-name x.name) "-MOD")
                x.name))
       ((mv err design)
        (acl2::magic-ev-fncall mod-fn nil state t t))
       ((when err)
        (raise "Error: couldn't run ~x0: ~@1~%" mod-fn err)
        (mv moddb aliases debugdata vcd-wiremap vcd-vals state))
       ((unless (and (design-p design)
                     (modalist-addr-p (design->modalist design))))
        (raise "Error: ~x0 returned a malformed design~%" mod-fn)
        (mv moddb aliases debugdata vcd-wiremap vcd-vals state))

       ((mv err moddb aliases debugdata) (svtv-debug-init design))
       ((when err)
        (mv moddb aliases debugdata vcd-wiremap vcd-vals state))
       (debugdata (svtv-debug-set-svtv x :rewrite rewrite))
       ((mv vcd-wiremap vcd-vals state)
        (svtv-debug-run-fsm inalists initst :filename filename)))
    (mv moddb aliases debugdata vcd-wiremap vcd-vals state)))

(define svtv-debug ((x svtv-p)
                    (inalist svex-env-p)
                    &key
                    ((filename  stringp) '"svtv-debug.vcd")
                    (state 'state))
  :parents (svex-stvs)
  :short "Dump a VCD waveform showing the internal signals of an svex STV."
  :prepwork ((local (in-theory (disable max))))
  :verbosep t
  (b* (((acl2::local-stobjs moddb aliases debugdata vcd-wiremap vcd-vals)
        (mv moddb aliases debugdata vcd-wiremap vcd-vals state)))
    (svtv-debug-core x inalist :filename filename))
      
  ///
  (defmacro stv-debug (&rest args) (cons 'svtv-debug args)))

(define svtv-debug-fsm ((x svtv-p)
                        (inalists svex-envlist-p)
                        (initst svex-env-p)
                        &key
                        ((filename  stringp) '"svtv-debug.vcd")
                        (state 'state))
  :parents (svex-stvs)
  :short "Dump a VCD waveform showing the internal signals of an svex STV."
  :prepwork ((local (in-theory (disable max))))
  :verbosep t
  (b* (((acl2::local-stobjs moddb aliases debugdata vcd-wiremap vcd-vals)
        (mv moddb aliases debugdata vcd-wiremap vcd-vals state)))
    (svtv-debug-fsm-core x inalists initst :filename filename))
      
  ///
  (defmacro stv-debug-fsm (&rest args) (cons 'svtv-debug-fsm args)))
