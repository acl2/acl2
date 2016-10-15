; stobj-frame.lisp - Automatically compute frame theorems for stobj accessor/updater functions
; Copyright (C) 2012 Centaur Technology
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
; Original author: Sol Swords

(in-package "ACL2")

(include-book "rulesets")
(include-book "std/util/bstar" :dir :system)
(program)
(set-state-ok t)

(defxdoc def-stobj-frame
  :parents (stobj)
  :short "Automatically, opportunistically generate @(see nth)/@(see
update-nth) frame theorems for a function that accesses or updates a @(see
stobj)."
  :long "<p>Example:</p>

@({
   (defstobj foo bar baz biz)

   (defun baz-to-bar (foo)
     (declare (xargs :stobjs foo))
     (update-bar (baz foo) foo))

   (include-book \"data-structures/list-defthms\" :dir :system)

   (in-theory (disable nth update-nth))

   (def-stobj-frame baz-to-bar foo
     :hints ('(:in-theory (disable nth update-nth)))
     :ruleset foo-frame-thms)
})

<p>This last event generates the following events:</p>

@({
 (DEFTHMD NTH-FOO-OF-BAZ-TO-BAR
   (IMPLIES (AND (NOT (EQUAL (NFIX N) *BAR*)))
            (EQUAL (NTH N (BAZ-TO-BAR FOO))
                   (NTH N FOO))))

 (ADD-TO-RULESET FOO-FRAME-THMS NTH-FOO-OF-BAZ-TO-BAR)

 (DEFTHM BAZ-TO-BAR-FOO-FRAME
   (IMPLIES (OR (EQUAL (NFIX N) *BIZ*))
            (EQUAL (BAZ-TO-BAR (UPDATE-NTH N V FOO))
                   (UPDATE-NTH N V (BAZ-TO-BAR FOO)))))

 (ADD-TO-RULESET FOO-FRAME-THMS BAZ-TO-BAR-FOO-FRAME)
})

<p>The <b>def-stobj-frame</b> macro attempts to prove the following lemmas for
each field of the stobj:</p>

<ul>
<li>If the function returns the stobj:
    @({
     (equal (nth *field* (fn stobj))            ;; type 1
            (nth *field* stobj))
    })
    and
    @({
     (equal (fn (update-nth *field* val stobj)) ;; type 2
            (update-nth *field val (fn stobj)))
    })</li>

<li>Otherwise,
    @({
     (equal (fn (update-nth *field* val stobj)) ;; type 3
            (fn stobj))
    })</li>
</ul>

<p>It then generates @(see defthm) events based on which of these were
successful.</p>

<p>It is probably important that @(see nth) and @(see update-nth) be disabled
and suitable rules about them, such as the ones in
@('data-structures/list-defthms'), exist.</p>

<p>These proof attempts are done only with simplification and an expand hints.
You may supply an additional hints, but only simplification is used.  In
particular, this utility won't work well on recursive functions, because
generally they'll need induction to do the proofs (future work).</p>")

(defun stobj-length (stobj state)
  (declare (xargs :mode :program :stobjs state))
  (car (dimensions stobj (getprop stobj 'accessor-names nil 'current-acl2-world
                                  (w state)))))


;; (defun stobj-frame-try-n (n concl hint state)
;;   (declare (xargs :mode :program :stobjs state))
;;   (b* (((er simp)
;;         (easy-simplify-term1-fn
;;          concl `((equal n ',n)) hint 'equal t t 1000 1000 state)))
;;     (value (equal simp ''t))))

(defun stobj-frame-try-n (n concl hints state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((term `(implies (equal n ',n) ,concl))
       ; (- (cw "hints: ~x0~%" hints))
       ((mv fail ttree state)
        (state-global-let*
         ((gag-mode t)
          (print-clause-ids nil)
          (inhibit-output-lst '(proof-tree prove summary)))
         (prove-loop
          `((,term))
          (make-pspv (ens state)
                     (w state)
                     state
                     :displayed-goal term
                     :user-supplied-term term
                     :orig-hints hints
                     :otf-flg nil)
          hints (ens state) (w state) 'stobj-frame-try-n state)))
       ((when fail) (value nil))
       ((er &) (chk-assumption-free-ttree ttree 'stobj-frame-try-n state)))
    ;; ttree may contain byes, but we'll ignore them
    (value t)))

;; (mv err changed unchanged state)
(defun stobj-frame-collect-ns (n concl hints state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((when (zp n)) (mv nil nil nil state))
       ((mv er succ state)
        (stobj-frame-try-n (1- n) concl hints state))
       ((when er) (mv er nil nil state))
       ((mv er ch unch state)
        (stobj-frame-collect-ns (1- n) concl hints state))
       ((when er) (mv er nil nil state)))
    (mv nil
        (if succ ch (cons (1- n) ch))
        (if succ (cons (1- n) unch) unch)
        state)))

(defun stobj-frame-n-equal-hyps (lst stobj state)
  (if (atom lst)
      nil
    (cons `(equal (nfix n) ,(accessor-root (car lst) stobj (w state)))
          (stobj-frame-n-equal-hyps (cdr lst) stobj state))))

(defun stobj-frame-hyps (ch unch stobj state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((unchp (< (len unch) (len ch)))
       (lst (if unchp unch ch))
       (equals (stobj-frame-n-equal-hyps lst stobj state)))
    (if unchp
        `(or . ,equals)
      `(and . ,(dumb-negate-lit-lst equals)))))



(defun def-stobj-nth-frame (fn stobj hints ruleset state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((wrld (w state))
       (fn$ (deref-macro-name fn (macro-aliases wrld)))
       (formals (formals fn$ wrld))
       ;; Replace the variable named N in the formals, because we use it in the
       ;; theorem.
       (formals (let ((pos (position 'n formals)))
                  (if pos
                      (update-nth pos (genvar 'n "N" 0 formals) formals)
                    formals)))
       (stobjs-out (stobjs-out fn$ wrld))
       (pos (position stobj stobjs-out))
       ((unless pos) (value nil))
       (call$ `(,fn$ . ,formals))
       (mv-call$ (if (cdr stobjs-out)
                       `(mv-nth ',pos ,call$)
                     call$))
       (call `(,fn . ,formals))
       (mv-call (if (cdr stobjs-out)
                       `(mv-nth ,pos ,call)
                     call))
       (len (stobj-length stobj state))
       (concl$ `(equal (nth n ,mv-call$) (nth n ,stobj)))
       (concl `(equal (nth n ,mv-call) (nth n ,stobj)))
       (ind-hint (and (not hints)
                      (let ((recp (recursivep fn$ t wrld)))
                        (if (and recp
                                 (not (cdr recp))) ;; not mutually recursive
                            `(:induct ,call
                              :do-not-induct t
                              :in-theory (enable (:induction ,fn)))
                          '(:do-not-induct t)))))
       (exp-hint (and (not hints)
                      `(:expand (,call))))
       (hints (or hints `(("goal" . ,(append ind-hint exp-hint)))))
       ((er thints) (translate-hints+ 'def-stobj-nth-frame
                                     hints (default-hints wrld)
                                     'def-stobj-nth-frame wrld state))
       ((mv er ch unch state)
        (stobj-frame-collect-ns len concl$ thints state))
       ((when er) (mv er nil state))
       ((when (atom unch))
        ;; no elements preserved
        (value nil))
       (hyp (stobj-frame-hyps ch unch stobj state))
       (thm (intern-in-package-of-symbol
             (concatenate 'string "NTH-" (symbol-name stobj) "-OF-"
                          (symbol-name fn))
             fn)))
    (value
     `((defthmd ,thm
         (implies ,hyp ,concl)
         :hints ,hints)
       (add-to-ruleset ,ruleset ,thm)))))


(defun def-stobj-update-mv (mv stobj-out stobj fn fn$ formals formals-upd
                              stobj-len hints ruleset state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((wrld (w state))
       (upd-call$ `(,fn$ . ,formals-upd))
       (upd-mvcall$ (if mv `(mv-nth ',mv ,upd-call$) upd-call$))
       (upd-call `(,fn . ,formals-upd))
       (upd-mvcall (if mv `(mv-nth ,mv ,upd-call) upd-call))
       (call `(,fn . ,formals))
       (call$ `(,fn$ . ,formals))
       (mvcall (if mv `(mv-nth ,mv ,call) call))
       (mvcall$ (if mv `(mv-nth ',mv ,call$) call$))
       (concl$ (if (eq stobj-out stobj)
                  `(equal ,upd-mvcall$
                          (update-nth n v ,mvcall$))
                `(equal ,upd-mvcall$
                        ,mvcall$)))
       (concl (if (eq stobj-out stobj)
                  `(equal ,upd-mvcall
                          (update-nth n v ,mvcall))
                `(equal ,upd-mvcall
                        ,mvcall)))
       (ind-hint (and (not hints)
                      (let ((recp (recursivep fn$ t wrld)))
                        (if (and recp
                                 (not (cdr recp))) ;; not mutually recursive
                            `(:induct ,call
                              :do-not-induct t
                              :in-theory (enable (:induction ,fn)))
                          '(:do-not-induct t)))))
       (exp-hint (and (not hints)
                      `(:expand (,call (:free (n) ,upd-call)))))
       (hints (or hints `(("goal" . ,(append ind-hint exp-hint)))))
       ((er thints) (translate-hints+ 'def-stobj-update-mv
                                     hints (default-hints wrld)
                                     'def-stobj-update-mv wrld state))
       ((mv er ch unch state)
        (stobj-frame-collect-ns stobj-len concl$ thints state))
       ((when er) (mv er nil state))
       ((when (atom unch))
        ;; no elements preserved
        (value nil))
       (hyp (stobj-frame-hyps ch unch stobj state))
       (thm (intern-in-package-of-symbol
             (if mv
                 (concatenate 'string (symbol-name fn) "-" (symbol-name stobj) "-FRAME-"
                              (coerce (explode-nonnegative-integer mv 10 nil) 'string))
               (concatenate 'string (symbol-name fn) "-" (symbol-name stobj) "-FRAME"))
             fn)))
    (value
     `((defthmd ,thm
         (implies ,hyp ,concl)
         :hints ,hints)
       (add-to-ruleset ,ruleset ,thm)))))

(defun def-stobj-update-mvs (n stobjs-out stobj fn fn$ formals formals-upd
                              stobj-len hints ruleset state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((when (atom stobjs-out)) (value nil))
       ((er first) (def-stobj-update-mv n (car stobjs-out) stobj fn fn$ formals
                     formals-upd stobj-len hints ruleset state))
       ((er rest)
        (def-stobj-update-mvs (1+ n) (cdr stobjs-out) stobj
          fn fn$ formals formals-upd stobj-len hints ruleset state)))
    (value (append first rest))))

(defun def-stobj-update-frame (fn stobj hints ruleset state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((wrld (w state))
       (fn$ (deref-macro-name fn (macro-aliases wrld)))
       (formals (formals fn$ wrld))
       ;; Replace the variables N and V in the formals, because we use it in the
       ;; theorem.
       (formals (let ((pos (position 'n formals)))
                  (if pos
                      (update-nth pos (genvar 'n "N" 0 formals) formals)
                    formals)))
       (formals (let ((pos (position 'n formals)))
                  (if pos
                      (update-nth pos (genvar 'v "V" 0 formals) formals)
                    formals)))
       (stobjs-out (stobjs-out fn$ wrld))
       (stobj-pos (position stobj formals))
       (formals-upd (update-nth stobj-pos `(update-nth n v ,stobj) formals))
       (stobj-len (stobj-length stobj state))
       ((er forms) (if (cdr stobjs-out)
                       (def-stobj-update-mvs
                         0 stobjs-out stobj fn fn$ formals formals-upd
                         stobj-len hints ruleset state)
                     (def-stobj-update-mv
                       nil (car stobjs-out) stobj fn fn$ formals formals-upd
                       stobj-len hints ruleset state))))
    (value forms)))

(def-ruleset! stobj-frame-rules nil)

(defun def-stobj-frame-fn (fn stobj hints ruleset state)
  (b* (((er nthforms) (def-stobj-nth-frame fn stobj hints ruleset state))
       ((er frameforms) (def-stobj-update-frame fn stobj hints ruleset state)))
    (value `(progn ,@nthforms . ,frameforms))))

(defmacro def-stobj-frame (fn stobj &key hints (ruleset 'stobj-frame-rules))
  `(make-event
    (def-stobj-frame-fn ',fn ',stobj ',hints ',ruleset state)))


(logic)

(local
 (progn

   (def-ruleset! foo-frame-thms nil)

   (defstobj foo bar baz biz)

   (defun baz-to-bar (foo)
     (declare (xargs :stobjs foo))
     (update-bar (baz foo) foo))

   (include-book "data-structures/list-defthms" :dir :system)

   (in-theory (disable nth update-nth))

   (def-stobj-frame baz-to-bar foo
     :ruleset foo-frame-thms)

   (defun baz-to-bar-return-biz (foo)
     (declare (xargs :stobjs foo))
     (let* ((biz (biz foo))
            (foo (update-bar (baz foo) foo)))
       (mv biz foo)))

   (def-stobj-frame baz-to-bar-return-biz foo
     :ruleset foo-frame-thms)))
