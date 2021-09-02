; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2019 Centaur Technology
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
; Original author: Mertcan Temel <mert@utexas.edu>

;; Mertcan Temel

(in-package "SVL")

(include-book "centaur/sv/svex/eval" :dir :system)

(include-book "projects/rp-rewriter/top" :dir :system)

(include-book "centaur/svl/svex-simplify" :dir :system)

(include-book "centaur/svl/svl-openers" :dir :system)

(include-book "centaur/svl/svexl/svexl-correct" :dir :system)

(local
 (include-book "projects/rp-rewriter/proofs/rp-rw-lemmas" :dir :system))

(rp::def-rp-rule$
 t nil
 assoc-equal-opener-when-not-equal
 (implies (not (equal key1 key2))
          (equal (assoc-equal key1 (cons (cons key2 val) rest))
                 (assoc-equal key1 rest))))

(rp::def-rp-rule$
 t nil
 assoc-equal-opener-when-equal
 (implies t
          (equal (assoc-equal key (cons (cons key val) rest))
                 (cons key val))))


;; :i-am-here
;; (rp::def-rp-rule$
;;  t t
;;  bits-of-bits-exact-match
;;  (implies (and (natp x)
;;                (natp y))
;;           (equal (bits (bits term x y) x y )
;;                  (bits term x y )))
;;  :hints (("Goal"
;;           :in-theory (e/d () ()))))

(defconst *svl-compose-rules*
  (reverse
   '(svex-alist-eval-opener-nil
     svex-alist-eval-opener-cons

     ;;svex-eval-is-svex-eval-wog
     ;;svexlist-eval-is-svexlist-eval-wog

     svl-start-env-opener-error
     svl-start-env-cons-1
     svl-start-env-nil
     svl-start-env-cons-2
     svl-retrieve-values-opener-error
     svl-retrieve-values-nil
     svl-retrieve-values-cons-1
     svl-retrieve-values-cons-2
     save-wires-to-env-wires-opener-error
     save-wires-to-env-wires-cons-1
     save-wires-to-env-wires-nil
     save-wires-to-env-wires-cons-2
     save-wires-to-env-wires-cons-3
     svex-env-append-opener-error
     svex-env-append-opener-cons
     svex-env-append-opener-nil
     create-next-env-for-wires-opener-nil
     create-next-env-for-wires-opener-cons
     svl-save-mod-outputs-opener-error
     svl-save-mod-outputs-nil
     svl-save-mod-outputs-cons
     svl-well-ranked-module-is-svl-well-ranked-module$
     svl-run-phase-opener-error
     svl-run-phase-occs-opener-error
     svl-run-phase-is-svl-run-phase-wog
     svl-run-phase-occs-is-svl-run-phase-occs-wog
     svl-run-phase-wog-opener-error
     svl-run-phase-wog-opener
     ;;rp::svl-run-phase-wog-opener_lambda-opener
     svl-run-phase-occs-wog-opener-error
     svl-run-phase-occs-wog-opener-nil
     svl-run-phase-occs-wog-opener-cons-assign
     svl-run-phase-occs-wog-opener-cons-module
     ;;rp::svl-run-phase-occs-wog-opener-cons-module_lambda-opener
     pairlis3-opener-error
     pairlis3-opener-done
     pairlis3-opener-cons
     svl-run-save-output-opener-error
     svl-run-save-output-opener-nil
     svl-run-save-output-opener-cons
     ;;rp::svl-run-save-output-opener-cons_lambda-opener
     svl-run-aux-opener-error
     svl-run-aux-wog-opener-error
     svl-run-aux-is-svl-run-aux-wog
     svl-run-aux-wog-opener-nil
     svl-run-aux-opener-cons
     ;;rp::svl-run-aux-opener-cons_lambda-opener
     svl-run-opener-error
     svl-run-def-opener
     ;;rp::svl-run-def-opener_lambda-opener
     sv::4veclist-p-of-cons
     SV::SVEX-ENV-P-when-cons
     SV::SVEX-ENV-FIX-opener
     SV::SVEX-ENV-P-nil

     RP::CONSP-CONS

     svexlist-list-eval-wog-opener-error
     svexlist-list-eval-wog-opener-cons
     svexlist-list-eval-wog-opener-nil

     ;;svexlist-eval-wog-is-svexlist-eval
     svexlist-eval-wog-cons-def
     svexlist-eval-wog-nil-def

     rp::make-fast-alist-def

     return-last
     entry-4vec-fix

     cdr-cons
     car-cons
     acons

     assoc-equal-opener-when-not-equal
     assoc-equal-opener-when-equal

     append-of-cons
     4vec-part-install-is-sbits-without-inserting-bits
     ;;4vec-part-install-is-sbits
     4vec-part-select-is-bits

     svexllist-correct
     svexl-correct

     svexl-node-kind-is-svexl-node-kind-wog
     svexl-node-kind-wog-is-svexl-node-kind
     svexl-nodelist-eval-wog-of-cons
     svexl-nodelist-eval-wog-of-nil

     svexllist-eval-is-svexllist-eval-wog
     svexl-eval-is-svexl-eval-wog
     svexl-eval-wog-for-rp
     ;;rp::svexl-eval-wog-opener_lambda-opener
     svex-env-fastlookup-wog-def
     RP::APPEND-OF-NIL
     SVEXL-EVAL-AUX-WOG-nil
     svexl-eval-aux-wog-cons
     ;;rp::svexl-eval-aux-wog-cons_lambda-opener
     svexl-node-eval-is-svexl-node-eval-wog
     svexl-nodelist-eval-is-svexl-nodelist-eval-wog

     svexl-eval-aux-is-svexl-eval-aux-wog


     rp::force$-fail
     rp::force$-of-t

     )))

(define alist-term-to-entry-list (term)
  (case-match term
    (('cons ('cons key val) rest)
     (b* (((mv keys vals)
           (alist-term-to-entry-list rest)))
       (mv (cons key keys)
           (cons val vals))))
    (''nil
     (mv nil nil))
    (&
     (mv (hard-error
          'alist-term-to-entry-list
          "Unexpected alist-term ~p0 ~%"
          (list (cons #\0 term)))
         nil))))

(local
 (Include-Book "projects/rp-rewriter/proofs/extract-formula-lemmas" :dir :system))

(local
 (Include-Book "projects/rp-rewriter/proofs/rp-state-functions-lemmas" :dir :system))

(define rw-svl-run-to-svex-alist ((term rp::rp-termp)
                                  &key
                                  (context 'nil)
                                  (state 'state)
                                  (rp::rp-state 'rp::rp-state))
  :guard (and (rp::rp-term-listp context))
  :verify-guards nil
  :prepwork ((local
              (defthm valid-rw-step-limit
                (implies (rp::rp-statep rp::rp-state)
                         (and (natp (rp::rw-step-limit rp-state))
                              (unsigned-byte-p 58 (rp::rw-step-limit rp-state))
                              (integerp (rp::rw-step-limit rp-state))))
                :hints (("Goal"
                         :do-not-induct t
                         :in-theory (e/d (rp::rp-statep
                                          RP::RW-STEP-LIMITP)
                                         (unsigned-byte-p))))))

             (local
              (defthm rp-statep-of-not-simplified-action
                (implies (and (rp::rp-statep rp-state)
                              (symbolp x))
                         (RP::RP-STATEP (RP::UPDATE-NOT-SIMPLIFIED-ACTION x
                                                                          RP-STATE)))
                :hints (("Goal"
                         :in-theory (e/d (RP::RP-STATEP) ())))))
             
             (local
              (in-theory (e/d ()
                              (unsigned-byte-p
                               natp
                               RP::UPDATE-NOT-SIMPLIFIED-ACTION
                               RP::NOT-SIMPLIFIED-ACTION
                               rp::rw-step-limit)))))
  
  (b* ((world (w state))
       ;; do not let rp-rewriter complain when simplified term is not ''t
       (- (rp::check-if-clause-processor-up-to-date world))
       (tmp-rp-not-simplified-action (rp::not-simplified-action rp::rp-state))
       (rp::rp-state (rp::update-not-simplified-action :none rp::rp-state))
       (rp::rp-state (rp::rp-state-new-run rp::rp-state))
       (rp::rp-state (rp::rp-state-init-rules nil nil nil rp::rp-state state))


       ((mv context rp::rp-state)
        (rp::rp-rw-subterms
         context nil nil nil (rp::rw-step-limit rp::rp-state) rp::rp-state state))

       ((mv rw rp::rp-state)
        (rp::rp-rw
         term nil context nil nil (rp::rw-step-limit rp::rp-state) rp::rp-state state))
       (rp::rp-state (rp::update-not-simplified-action
                      tmp-rp-not-simplified-action rp::rp-state))
       
       ((mv keys vals)
        (alist-term-to-entry-list rw))
       ((mv err svexlist) (svl::4vec-to-svex-lst vals nil t))
       #|((mv err svex-res)
       (svl::4vec-to-svex rw nil nil))||#
       (- (and err
               (hard-error ; ;
                'rw-svl-run-to-svex-alist ; ;
                "There was a problem while converting the term below to its ~
svex equivalent. Read above for the printed messages. ~p0 ~%" 
                (list (cons #\0 rw)))))
       
       (svex-alist (pairlis$ (rp::unquote-all keys) svexlist))
       
       )
    (mv svex-alist rp::rp-state))
  ///

  (Local
   (defthm true-listp-of-unquote-all
     (implies (true-listp x)
              (true-listp (rp::unquote-all x)))))

  (Local
   (defthm true-listp-of-alist-term-to-entry-list
     (implies t;; (true-listp x)
              (true-listp (mv-nth 0 (alist-term-to-entry-list x))))
     :hints (("Goal"
              :in-theory (e/d (alist-term-to-entry-list) ())))))

  (local
   (defthm unsigned-byte-p-58-of-rw-step-limit
       (implies (force (rp::rp-statep rp::rp-state))
                (UNSIGNED-BYTE-P
                 58
                 (RP::RW-STEP-LIMIT rp::rp-state)))))
   
  
  (verify-guards rw-svl-run-to-svex-alist-fn
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (rp::rp-statep
                              rp::not-simplified-action
                              rp::not-simplified-actionp)
                             (rp::rw-step-limit))))))

(progn
  (define svl-run-to-svex-alist-create-env-aux (vars)
    (if (atom vars)
        ''nil
      `(cons
        (cons ',(car vars) ,(car vars))
        ,(svl-run-to-svex-alist-create-env-aux (cdr vars)))))

  (define get-vars-from-port-binds (port-binds)
    :mode :program
    (b* ((lst (strip-cdrs port-binds))
         (lst (acl2::flatten lst)))
      (loop$ for x in lst when (and (symbolp x)
                                    (let* ((x (symbol-name x)))
                                      (and (not (equal x "_"))
                                           (not (equal x "~"))
                                           (not (equal x "X"))
                                           (not (equal x "-"))
                                           (not (equal x "x")))))
             collect x)))

  (define svl-run-to-svex-alist-fn-create-env (binds-ins-alist)
    :mode :program
    (b* ((vars (get-vars-from-port-binds binds-ins-alist)))
      `(make-fast-alist
        ,(svl-run-to-svex-alist-create-env-aux vars))))

  (define svl-run-to-svex-alist-create-hyp (binds-ins-alist)
    :mode :program
    (b* ((vars (get-vars-from-port-binds binds-ins-alist)))
      (loop$ for x in vars collect `(sv::4vec-p ,x)))))

(define svl-run->svex-alist-aux (&key
                                 modname
                                 binds-ins-alist
                                 binds-out-alist
                                 svl-design
                                 svex-alist-name
                                 rw-rule-name)
  (b* (((unless (and modname
                     binds-ins-alist
                     binds-out-alist
                     svl-design
                     svex-alist-name
                     rw-rule-name))
        (hard-error 'svl-run-compose-fn
                    "You need to assign values to keys ~
                     modname~
                     binds-ins-alist~
                     binds-out-alist~
                     svl-design~
                     svex-alist-name rw-rule-name ~%"
                    nil)))

    `(encapsulate
         nil
         (local
          (rp::disable-all-rules))

       (local
        (rp::enable-rules *svl-compose-rules*))

       (local
        (memoize 'rp::rp-equal))
       
       (local
        (rp::disable-exc-counterpart fmt-to-comment-window))

       (local
        (rp::disable-all-meta-rules))

       (local
        (rp::enable-meta-rules
         ;; bits-of-meta-fn
         ;; concat-meta
         ;; 4vec-rsh-of-meta
         svex-eval-wog-meta-main
         svexl-node-eval-wog-meta-main
         rp::HONS-ACONS-META
         rp::FAST-ALIST-FREE-META
         rp::ASSOC-EQ-VALS-META
         rp::HONS-GET-META
         rp::RP-EQUAL-META
         rp::MV-NTH-META))
       
       (with-output
           :off :all
         :gag-mode nil
         (make-event
          (b* ((env (svl-run-to-svex-alist-fn-create-env ,binds-ins-alist))
               (?hyp (svl-run-to-svex-alist-create-hyp ,binds-ins-alist))
               (?hyp (append hyp (list `(equal env ,env))))
               (?hyp (list '(sv::svex-env-p svex-env)))
               (term `(svl::svl-run ',,modname
                                    svex-env
                                    ',,binds-ins-alist
                                    ',,binds-out-alist
                                    ',,svl-design))
               ((mv svex-alist rp::rp-state)
                (rw-svl-run-to-svex-alist term :context hyp)))
            (mv nil
                `(progn

                   (defconst ,',svex-alist-name
                     ',svex-alist)

                   (defthmd
                       ,',rw-rule-name
                       (implies (and  ,@hyp)
                                (equal (svl::svl-run ,',modname
                                                     svex-env
                                                     ,',binds-ins-alist
                                                     ,',binds-out-alist
                                                     ,',svl-design)
                                       (sv::svex-alist-eval ,',svex-alist-name
                                                            svex-env)))

                     :hints (("Goal"
                              :do-not-induct t
                              :rw-cache-state nil
                              :do-not '(preprocess generalize fertilize)
                              :clause-processor (rp::rp-cl :runes nil
                                                           :new-synps nil)))
                     )
                   #|(rp::disable-rules '(,',rw-rule-name))||#
                   #|(in-theory (disable ,',rw-rule-name))||#

                   (value-triple (cw "~%An svex-alist ~p0 and a disabled rewrite ~
rule ~p1 are created. ~%~%" ',',svex-alist-name ',',rw-rule-name))
                   )
                state
                rp::rp-state)))))))

(defmacro svl-run->svex-alist (&key
                               modname
                               binds-ins-alist
                               binds-out-alist
                               svl-design
                               svex-alist-name
                               rw-rule-name)
  (svl-run->svex-alist-aux :modname modname
                           :binds-ins-alist binds-ins-alist
                           :binds-out-alist binds-out-alist
                           :svl-design svl-design
                           :rw-rule-name rw-rule-name
                           :svex-alist-name svex-alist-name))

(xdoc::defxdoc
 svl-run->svex-alist
 :parents (acl2::svl)
 :short "Convert an SVL design to an @(see sv::svex-alist)."
 :long " <p> Using @(see rp::rp-rewriter), converts an SVL design usign svl-run
to an @(see sv::svex-alist).
</p>

<code>
@('
(svl-run->svex-alist :modname <modname>
                     :svl-design <svl-design>
                     :binds-ins-alist <binds-ins-alist>
                     :binds-out-alist <binds-out-alist>
                     :svex-alist-name <svex-alist-name>
                     :rw-rule-name <rw-rule-name>)
')
</code>

<p>Users should provide a value for all the keys.</p>

<p>modname: name of the main module in an SVL design.</p>

<p>svl-design: SVL design constant. </p>

<p>binds-ins-alist: Input simulation pattern constant similar to inputs key of
@(see acl2::defsvtv).
</p>

<p>binds-out-alist: Output simulation pattern constant similar to outputs key of
@(see acl2::defsvtv).
</p>

<p>svex-alist-name: when the SVL-design is converted to an svex-alist, the
program will create a constant provided by svex-alist-name.</p>

<p>
rw-rule-name: the program also creates a rewrite rule with this given name. The
LHS of this rewrite rule is svl-run of the given module with given
configuration, and the RHS is svex-alist-eval of the newly generated
svex-alist.
</p>

<p>The keys in created svex-alist are the variables designated in
binds-out-alist. The variables in the values (svexes) share the same name as
the variables from binds-ins-alist.
</p>

<p> An example call to svl-run-compose is given below. It submits an event that
exports svl-run-top-module-composed and *svl-run-top-module-composed*.

<code>
@('
(svl-run->svex-alist :modname \"top_module\"
                     :binds-ins-alist *ins-alist*
                     :binds-out-alist *outs-alist*
                     :svl-design *svl-netlist*
                     :rw-rule-name svl-run-top-module-composed
                     :svex-alist-name *svl-run-top-module-composed*)
')
</code>
</p>

<p> This will  produce a constant *svl-run-top-module-composed*,  which has the
svex-alist representation  of the  given svl-run instance;  and a  rewrite rule
with the name svl-run-top-module-composed,  which rewrites the svl-run instance
to evaluation of this svex-alist. See @(see svl::svl-run) for concrete examples
of  the   first  four   keys  (:modname,   :binds-ins-alist,  :binds-out-alist,
:svl-design).  </p>

")




