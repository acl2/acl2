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

(in-package "SV")

(include-book "debug")
(include-book "chase-base")


(define svtv-chase-inalist-to-evaldata ((inalist svex-env-p)
                                        &key
                                        (debugdata 'debugdata)
                                        )
  :returns (evaldata svtv-evaldata-p)
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable debugdatap)
                       :do-not-induct t)))
  :guard-debug t
  (b* (((debugdata debugdata))

       (ins (svtv-expand-lines debugdata.ins debugdata.nphases))
       ((mv ovlines ?ovs) (svtv-lines->overrides debugdata.overrides 0))
       (states (svex-alist-keys debugdata.nextstates))

       (in-vars (acl2::hons-set-diff (svexlist-collect-vars
                                      (append (svex-alist-vals debugdata.updates)
                                              (svex-alist-vals debugdata.nextstates)))
                                     (append (svex-alist-keys debugdata.updates)
                                             states)))

       (in-alists (if (eql 0 debugdata.nphases)
                      nil
                    (svtv-allphases-inputs 0 debugdata.nphases ins ovlines in-vars)))
       (in-envs (svex-alistlist-eval in-alists inalist))
       (- (clear-memoize-table 'svex-eval))
       (initst (make-fast-alist (pairlis$ states
                                          (replicate (len states) (4vec-x))))))
    (make-svtv-evaldata :nextstate (make-fast-alist debugdata.nextstates)
                        :inputs (make-fast-alists in-envs)
                        :initst (make-fast-alist initst))))

(defthm nth-of-svtv-debug-set-ios-logic
  (implies (not (member (nfix n)
                        (list *debugdata->updates*
                              *debugdata->nextstates*
                              *debugdata->ins*
                              *debugdata->outs*
                              *debugdata->overrides*
                              *debugdata->override-assigns*
                              *debugdata->status*
                              *debugdata->nphases*)))
           (equal (nth n (svtv-debug-set-ios-logic :ins ins :outs outs :internals internals
                                                   :overrides overrides
                                                   :rewrite rewrite))
                  (nth n debugdata)))
  :hints(("Goal" :in-theory (enable svtv-debug-set-ios-logic))))

(defthm nth-of-svtv-debug-set-svtv
  (implies (not (member (nfix n)
                        (list *debugdata->updates*
                              *debugdata->nextstates*
                              *debugdata->ins*
                              *debugdata->outs*
                              *debugdata->overrides*
                              *debugdata->override-assigns*
                              *debugdata->status*
                              *debugdata->nphases*)))
           (equal (nth n (svtv-debug-set-svtv x :rewrite rewrite))
                  (nth n debugdata)))
  :hints(("Goal" :in-theory (enable svtv-debug-set-svtv))))


(defthm svex-alist-p-updates-of-svtv-debug-set-ios-logic
  (implies (svex-alist-p (nth *debugdata->updates* debugdata))
           (svex-alist-p (nth *debugdata->updates*
                              (svtv-debug-set-ios-logic :ins ins
                                                        :outs outs
                                                        :internals internals
                                                        :overrides overrides
                                                        :rewrite rewrite))))
  :hints(("Goal" :in-theory (enable svtv-debug-set-ios-logic))))

(defthm svex-alist-p-override-assigns-of-svtv-debug-set-ios-logic
  (implies (svex-alist-p (nth *debugdata->override-assigns* debugdata))
           (svex-alist-p (nth *debugdata->override-assigns*
                              (svtv-debug-set-ios-logic :ins ins
                                                        :outs outs
                                                        :internals internals
                                                        :overrides overrides
                                                        :rewrite rewrite))))
  :hints(("Goal" :in-theory (enable svtv-debug-set-ios-logic))))

(defthm svex-alist-p-nextstates-of-svtv-debug-set-ios-logic
  (implies (svex-alist-p (nth *debugdata->nextstates* debugdata))
           (svex-alist-p (nth *debugdata->nextstates*
                              (svtv-debug-set-ios-logic :ins ins
                                                        :outs outs
                                                        :internals internals
                                                        :overrides overrides
                                                        :rewrite rewrite))))
  :hints(("Goal" :in-theory (enable svtv-debug-set-ios-logic))))

(local (in-theory (disable append
                           true-listp
                           len
                           not
                           (tau-system)
                           svarlist-addr-p-by-badguy)))

;; BOZO include in ../mods/compile.lisp
;; (defret vars-of-svex-design-flatten-and-normalize-aliases
;;   (implies (and (not err)
;;                 (not indexedp))
;;            (svarlist-addr-p (aliases-vars new-aliases)))
;;   :hints(("Goal" :in-theory (enable svex-design-flatten-and-normalize)))
;;   :fn svex-design-flatten-and-normalize)

(define svtv-chase-update ((env svex-env-p)
                           &key
                           (debugdata 'debugdata)
                           ((moddb moddb-ok) 'moddb)
                           (aliases 'aliases)
                           (svtv-chase-data 'svtv-chase-data)
                           (state 'state))

  :guard (and (open-input-channel-p *standard-oi* :object state)
              ;; (svarlist-addr-p (svexlist-collect-vars (svex-alist-vals (debugdata->override-assigns debugdata))))
              ;; (svarlist-addr-p (svar-map-vars (debugdata->delays debugdata)))
              (< (debugdata->modidx debugdata) (moddb->nmods moddb))
              (<= (moddb-mod-totalwires (debugdata->modidx debugdata) moddb)
                  (aliass-length aliases))
              ;; (svarlist-addr-p (aliases-vars aliases))
              )
  :guard-hints (("goal" :in-theory (enable debugdatap)
                 :do-not-induct t)
                ;; (and stable-under-simplificationp
                ;;      '(:in-theory (enable chase-position-addr-p)))
                )
  :parents (svtv-chase)
  :short "Re-enter the @(see svtv-chase) read-eval-print loop, updating the environment but keeping the same SVTV."
  :returns (mv new-svtv-chase-data new-state)
  (b* ((evaldata (svtv-chase-inalist-to-evaldata env))
       (svtv-chase-data (set-svtv-chase-data->stack nil svtv-chase-data))
       (svtv-chase-data (set-svtv-chase-data->evaldata evaldata svtv-chase-data))
       (svtv-chase-data (set-svtv-chase-data->smartp t svtv-chase-data))
       (svtv-chase-data (set-svtv-chase-data->updates
                         (make-fast-alist (debugdata->updates debugdata)) svtv-chase-data))
       (svtv-chase-data (set-svtv-chase-data->assigns
                         (make-fast-alist (debugdata->override-assigns debugdata)) svtv-chase-data))
       (svtv-chase-data (set-svtv-chase-data->delays
                         (make-fast-alist (debugdata->delays debugdata)) svtv-chase-data))
       (svtv-chase-data (set-svtv-chase-data->modidx (debugdata->modidx debugdata) svtv-chase-data))
       (- 
        (cw! "Entering SVTV-CHASE Read-Eval-Print Loop~%")
        (cw! "Enter X to exit~%")
        (cw! "Enter ? for command list~%"))
       ((mv svtv-chase-data state) (svtv-chase-repl)))
    (mv svtv-chase-data state)))

(define svtv-chase ((x svtv-p)
                    (env svex-env-p)
                    &key
                    (debugdata 'debugdata)
                    ((moddb moddb-ok) 'moddb)
                    (aliases 'aliases)
                    (svtv-chase-data 'svtv-chase-data)
                    (state 'state)
                    (rewrite 't))
  :returns (mv new-debugdata new-moddb new-aliases new-svtv-chase-data new-state)
  :guard (open-input-channel-p *standard-oi* :object state)
  :guard-hints (("goal" :do-not-induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable svtv-debug-init
                                          svtv-debug-set-svtv)))
                (and stable-under-simplificationp
                     '(:in-theory (enable debugdatap))))
  :parents (svtv)
  :short "Diagnose hardware or stimulus bugs by studying an SVTV run in a special-purpose
          read-eval-print loop."
  :long "<p>To enter this read-eval-print loop for the first time, run:</p>
@({
 (svtv-chase svtv env)
 })

<p>where SVTV is an svtv object (as produced by defsvtv) and env is an
assignment to the input/override signals of that SVTV.  Depending on the
complexity of the SVTV, the initial setup done by this command may take a few
minutes.</p>

<p>When setup is complete, you'll be shown an @('SVTV-CHASE >') prompt.  Typing
@('?') at this prompt shows the commands that may be used there.  Typically
you'll start by going to a signal of interest at a certain phase, using the
@('G') command.  At a given signal/phase, SVTV-CHASE will print the type of
signal -- primary input, initial state, previous state, or internal signal.
For internal signals, it will also print the list of signals that are this
signal's immediate dependencies.  To see the expression driving the current
signal, you may enter @('EXPR').  The next step is usually to select one of the
signal's dependencies and go to it, by typing its number.  To go back to the
signal you just left, you may type @('B') to pop the stack of signal/phase
positions.</p>

<p>At some point you may want to exit the read-eval-print loop, which you can
do by typing @('X') at the prompt.  To re-enter the loop, you can skip the
initial setup by running @('(svtv-chase-repl)').  You may also skip much of the
setup but change the input assignment by running @('(svtv-chase-update
env)').</p>

"
  (b* (((svtv x))
       (mod-fn (intern-in-package-of-symbol
                (str::cat (symbol-name x.name) "-MOD")
                x.name))
       ((mv err design)
        (acl2::magic-ev-fncall mod-fn nil state t t))
       ((when err)
        (cw! "Couldn't run ~x0: ~@1~%" mod-fn err)
        (mv debugdata moddb aliases svtv-chase-data state))
       ((unless (and (design-p design)
                     (modalist-addr-p (design->modalist design))))
        (cw! "~x0 returned a malformed design~%" mod-fn)
        (mv debugdata moddb aliases svtv-chase-data state))
       ((mv err moddb aliases debugdata) (svtv-debug-init design))
       ((when err)
        (mv debugdata moddb aliases svtv-chase-data state))
       (debugdata (svtv-debug-set-svtv x :rewrite rewrite))
       ((mv svtv-chase-data state)
        (svtv-chase-update env)))
    (mv debugdata moddb aliases svtv-chase-data state)))




#||

;; A basic example to test.

(defconst *my-design*
  (make-design
   :top "top"
   :modalist
   (make-fast-alist
    (list (cons "top"
                (make-module
                 :wires (list (make-wire :name "ctr"
                                         :width 5
                                         :low-idx 0)
                              (make-wire :name "inc"
                                         :width 1
                                         :low-idx 0)
                              (make-wire :name "reset"
                                         :width 1
                                         :low-idx 0)
                              (make-wire :name "ctrnext"
                                         :width 5
                                         :low-idx 3))
                 :assigns (list (cons (list (make-lhrange
                                             :w 5
                                             :atom (make-lhatom-var :name "ctrnext" :rsh 0))) ;; lhs
                                      (make-driver :value
                                                   (svcall ?
                                                           (svcall zerox 1 "reset")
                                                           0
                                                           (svcall + (svcall ? (svcall zerox 1 "inc") 1 0)
                                                                   (svcall zerox 5 "ctr")))))
                                (cons (list (make-lhrange
                                             :w 5
                                             :atom (make-lhatom-var :name "ctr" :rsh 0)))
                                      (make-driver :value (make-svar :name "ctrnext" :delay 1))))))))))
                                      



(defsvtv my-svtv
  :design *my-design*
  :inputs
  '(("reset"  1 0 0 0)
    ("inc"    inc0 inc1 inc2 inc3))
  :outputs
  '(("ctr"    _ _ _ lastctr)))

(svtv-chase (my-svtv)
            '((inc0 . 0) (inc1 . 1) (inc2 . 0) (inc3 . 1)))

||#

