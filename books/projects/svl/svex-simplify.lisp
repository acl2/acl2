; SVL - Listener-based Hierachical Verilog Analysis Framework
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

;; A tool to apply existing rewrite rules about 4vec functions to simplify sv
;; expresions by wrappaing them with "svex-eval" and an environment with all
;; the variables in svex pointing to some automatically created free variables.

(in-package "SVL")

(include-book "meta/top")
(include-book "xdoc/topics" :dir :system)

(in-theory (disable bitp natp))

(defttag t)
(set-register-invariant-risk nil)
(defttag nil)

(defrec svex-simplify-preloaded
  (enabled-exec-rules
   rules
   . meta-rules)
  t)

(encapsulate
  nil

  (define merge-sets (set1 set2)
    (declare (xargs :guard (true-listp set2)))
    :returns (res true-listp :hyp (true-listp set2))
    (if (atom set1)
        set2
      (merge-sets
       (cdr set1)
       (add-to-set (car set1) set2 :test 'equal))))

  (local
   (in-theory (enable svex-p
                      SV::SVAR-P
                      SVEX-KIND
                      sv::svexlist-p)))

  ;; returns a list of variables in an svex
  (acl2::defines
   get-svex-vars
   (define get-svex-vars (svex)
     (declare (xargs :guard (svex-p svex)
                     :verify-guards nil
                     :hints (("Goal"
                              :in-theory (e/d (svex-kind) ())))))
     (let* ((svex.kind (svex-kind svex)))
       (case svex.kind
         (:quote nil)
         (:var (list svex))
         (otherwise
          (get-svex-vars-lst (cdr svex))))))
   (define get-svex-vars-lst ((lst sv::svexlist-p))
     :returns (res true-listp)
     (if (atom lst)
         nil
       (merge-sets (get-svex-vars (car lst))
                   (get-svex-vars-lst (cdr lst)))))
   ///

   (verify-guards get-svex-vars)))

(mutual-recursion
 (defun to-string (val)
   (declare (xargs :measure (+ (if (consp val) 1 -1) (cons-countw val 3))
                   :guard t
                   :hints (("Goal"
                            :in-theory (e/d (rp::measure-lemmas cons-countw) ())))))
;(declare (xargs :mode :program))
   (cond
    ((symbolp val)
     (if (keywordp val)
         (string-append ":" (symbol-name val))
       (symbol-name val)))
    ((stringp val)
     (string-append "\"" (string-append val "\"")))
    ((consp val)
     (string-append "(" (string-append (to-string-lst val) ")")))
    (t
     (str::intstr (ifix val)))))

 (defun to-string-lst (lst)
   (declare (xargs :measure (cons-countw lst 3)
                   :guard t))
   (if (atom lst)
       (if (equal lst nil)
           ""
         (string-append " . " (to-string lst)))

     (string-append
      (to-string (car lst))
      (string-append
       (if (consp (cdr lst)) " " "")
       (to-string-lst (cdr lst)))))))

(define to-symbol (val)
  (intern$ (to-string val) *PACKAGE-NAME*))

(progn
  ;; creates a dummy environment with all the variables in svex binding them to
  ;; a unique symbol.
  (define create-dummy-svex-env-aux (vars)
    (if (atom vars)
        (mv ''nil nil nil)
      (b* (((mv rest-term rest-falist rest-reverselist)
            (create-dummy-svex-env-aux (cdr vars)))
           (cur-symbol (to-symbol (car vars))))
        (mv `(cons (cons ',(car vars) (rp '4vec-p ,cur-symbol))
                   ,rest-term)
            (hons-acons (car vars) `(rp '4vec-p ,cur-symbol)
                        rest-falist)
            (hons-acons cur-symbol (car vars)
                        rest-reverselist)))))

  (define create-dummy-svex-env (vars)
    (b* (((mv term falist reverse-env)
          (create-dummy-svex-env-aux vars)))
      (mv `(rp 'svex-env-p (falist ',falist ,term))
          reverse-env))))

(define svex-simplify-preload (&key (runes '(let ((world (w state))) (current-theory :here)))
                                    (state 'state))
  ;; you need to remember to run fat-alist-free for  rules-alist
  (declare (xargs :guard-hints (("Goal"
                                 :in-theory (e/d () (table-alist))))
                  :stobjs (state)))
  (b* ((world (w state))
       (- (rp::check-if-clause-processor-up-to-date world))
       ;;(runes (if runes runes (current-theory :here)))
       (enabled-exec-rules (rp::get-enabled-exec-rules runes))
       (rules-alist (rp::get-rules runes state))
       (meta-rules-entry (hons-assoc-equal 'rp::meta-rules-list
                                           (table-alist 'rp::rp-rw world)))
       (meta-rules (if (consp meta-rules-entry)
                       (make-fast-alist
                        (cdr meta-rules-entry))
                     nil)))
    (make svex-simplify-preloaded :enabled-exec-rules enabled-exec-rules
          :meta-rules meta-rules
          :rules rules-alist)))

(define svex-simplify-preloaded-guard (svex-simplify-preloaded state)
  (declare (xargs :stobjs (state)))
  :enabled t
  (or (not svex-simplify-preloaded)
      (and (weak-svex-simplify-preloaded-p svex-simplify-preloaded)
           (rp::rules-alistp (access svex-simplify-preloaded
                                     svex-simplify-preloaded
                                     :rules))
           (symbol-alistp (access svex-simplify-preloaded
                                  svex-simplify-preloaded
                                  :enabled-exec-rules))
           (rp::rp-meta-rule-recs-p (access svex-simplify-preloaded
                                            svex-simplify-preloaded
                                            :meta-rules)
                                    state))))

(define svex-rw-free-preload (svex-simplify-preloaded state)
  (declare (xargs :stobjs (state)
                  :guard (svex-simplify-preloaded-guard
                          svex-simplify-preloaded state))
           (ignorable state))
  (if svex-simplify-preloaded
      (progn$
       (fast-alist-free (access svex-simplify-preloaded
                                svex-simplify-preloaded
                                :meta-rules))
       (fast-alist-free (access svex-simplify-preloaded
                                svex-simplify-preloaded
                                :rules))
       nil)
    nil))

(define rw-svex-to-4vec ((svex svex-p)
                         &KEY
                         (state 'state)
                         (rp::rp-state 'rp::rp-state)
                         (hyp ''t) ;; "Have more context for variables."
                         (runes '(let ((world (w state))) (current-theory :here))) ;; runes/rule-names to work with. Can
                         ;; be overridden by svex-simplied-preloaded
                         (svex-simplify-preloaded 'nil)
                         ;; structure  creation for the rewriter. This value
                         ;; can be created with (svex-simplify-preload)
                         )
  (declare (xargs ;:mode :program
            :verify-guards nil
            :stobjs (state rp::rp-state)
            :guard (svex-simplify-preloaded-guard
                    svex-simplify-preloaded state)))
  ;; :guard (and (or (not created-rules)
  ;;                 (and (consp created-rules)
  ;;                      (symbol-alistp (cdr created-rules))
  ;;                      (rp::rules-alistp (car created-rules)))))
  :prepwork
  ((local
    (in-theory (disable rp::rules-alistp
                        RP::RP-STATEP
                        RP::RP-SYNTAXP
                        STATE-P
                        TABLE-ALIST)))
   (local
    (include-book "projects/rp-rewriter/proofs/extract-formula-lemmas" :dir :system)))

  (b* ((world (w state))
       (- (if (mbe :exec t :logic (svex-p svex)) nil
            (hard-error 'rw-svex-to-4vec  "Input is not an svex" nil)))
       ;; this indirectly checks that all the meta rules added are also proved.
       (- (rp::check-if-clause-processor-up-to-date world))
       ;; find the variables in the svex
       (vars (get-svex-vars svex))
       ;; create the env and reverse-env (same as env but keys and vals swapped)
       ((mv env-term reverse-env) (create-dummy-svex-env vars))
       ;; get the list of runes/rule names

       ((mv enabled-exec-rules
            rules-alist
            meta-rules)
        (if svex-simplify-preloaded
            (mv (access svex-simplify-preloaded
                        svex-simplify-preloaded
                        :enabled-exec-rules)
                (access svex-simplify-preloaded
                        svex-simplify-preloaded
                        :rules)
                (access svex-simplify-preloaded
                        svex-simplify-preloaded
                        :meta-rules))
          (mv (rp::get-enabled-exec-rules runes)
              (rp::get-rules runes state)
              (let ((res
                     (cdr (hons-assoc-equal 'rp::meta-rules-list
                                            (table-alist 'rp::rp-rw (w
                                                                     state))))))
                (if (RP::RP-META-RULE-RECS-P res state)
                    (make-fast-alist res)
                  nil)))))

       (old-not-simplified-action (rp::not-simplified-action rp::rp-state))
       (rp::rp-state (rp::update-not-simplified-action :none rp::rp-state))
       ;; CREATE THE TERM TO BE REWRITTEN
       (term `(implies ,hyp (svex-eval ',svex ,env-term)))
       ((mv rw rp::rp-state)
        (rp::rp-rw-aux term
                       rules-alist
                       enabled-exec-rules
                       meta-rules
                       rp::rp-state
                       state))
       ;; restore rp-state setting
       (rp::rp-state (rp::update-not-simplified-action
                      old-not-simplified-action rp::rp-state))
       (- (if svex-simplify-preloaded nil (fast-alist-free rules-alist)))
       (- (if svex-simplify-preloaded nil (fast-alist-free meta-rules)))
       (- (fast-alist-free (cadr (cadr (caddr env-term))))))
    (mv rw reverse-env rp::rp-state)))

(define to-svex-fnc (term)
;(declare (xargs :mode :program))
  (case-match term
    (('svl::bits & & &)         (cons 'sv::partsel  (cdr term)))
    (('svl::sbits & & & &)      (cons 'sv::partinst (cdr term)))
    (('svl::4vec-concat$ & & &) (cons 'sv::concat   (cdr term)))
    (('svl::4vec-bitnot$ size x) `(partsel 0 ,size (sv::bitnot ,x)))

    (('sv::4vec-fix &) (cons 'id (cdr term)))
    (('sv::4vec-bit-extract & &) (cons 'sv::bitsel (cdr term)))
    (('sv::3vec-fix &)           (cons 'sv::unfloat  (cdr term)))
    (('4vec-bitnot &)            (cons 'sv::bitnot   (cdr term)))
    (('4vec-bitand & &)          (cons 'sv::bitand   (cdr term)))
    (('4vec-bitor & &)           (cons 'sv::bitor    (cdr term)))
    (('sv::4vec-bitxor & &)      (cons 'sv::bitxor   (cdr term)))
    (('sv::4vec-res & &)         (cons 'sv::res      (cdr term)))
    (('sv::4vec-resand & &)      (cons 'sv::resand   (cdr term)))
    (('sv::4vec-resor & &)       (cons 'sv::resor    (cdr term)))
    (('sv::4vec-override & &)    (cons 'sv::override (cdr term)))
    (('sv::4vec-onset &)         (cons 'sv::onp      (cdr term)))
    (('sv::4vec-offset &)        (cons 'sv::offp     (cdr term)))
    (('sv::4vec-reduction-and &) (cons 'sv::uand     (cdr term)))
    (('sv::4vec-reduction-or &)  (cons 'sv::uor      (cdr term)))
    (('4vec-parity &)            (cons 'sv::uxor     (cdr term)))
    (('4vec-zero-ext & &)        (cons 'sv::zerox    (cdr term)))
    (('sv::4vec-sign-ext & &)    (cons 'sv::signx    (cdr term)))
    (('4vec-concat & & &)        (cons 'concat       (cdr term)))
    (('sv::4vec-rev-blocks & & &)(cons 'sv::blkrev   (cdr term)))
    (('4vec-rsh & &)             (cons 'sv::rsh      (cdr term)))
    (('4vec-lsh & &)             (cons 'sv::lsh      (cdr term)))
    (('4vec-plus & &)            (cons '+            (cdr term)))
    (('sv::4vec-minus & &)       (cons 'sv::b-       (cdr term)))
    (('sv::4vec-uminus & &)      (cons 'sv::u-       (cdr term)))
    (('sv::4vec-times & &)       (cons '*            (cdr term)))
    (('sv::4vec-quotient & &)    (cons '/            (cdr term)))
    (('sv::4vec-remainder & &)   (cons 'sv::%        (cdr term)))
    (('sv::4vec-xdet &)          (cons 'sv::xdet     (cdr term)))
    (('sv::4vec-countones &)     (cons 'sv::countones(cdr term)))
    (('sv::4vec-onehot &)        (cons 'sv::onehot   (cdr term)))
    (('sv::4vec-onehot0 &)       (cons 'sv::onehot0  (cdr term)))
    (('sv::4vec-< & &)           (cons '<            (cdr term)))
    (('4vec-== & &)              (cons 'sv::==       (cdr term)))
    (('sv::4vec-=== & &)         (cons 'sv::===      (cdr term)))
    (('sv::4vec-wildeq & &)      (cons 'sv::==?      (cdr term)))
    (('sv::4vec-wildeq-safe & &) (cons 'sv::safer-==?(cdr term)))
    (('sv::4vec-symwildeq & &)   (cons 'sv::==??     (cdr term)))
    (('sv::4vec-clog2 &)         (cons 'sv::clog2    (cdr term)))
    (('sv::4vec-pow & &)         (cons 'sv::pow      (cdr term)))
    (('4vec-? & & &)             (cons 'sv::?        (cdr term)))
    (('4vec-?* & & &)            (cons 'sv::?*       (cdr term)))
    (('sv::4vec-bit? & & &)      (cons 'sv::bit?     (cdr term)))
    (('4vec-part-select & & &)   (cons 'partsel      (cdr term)))
    (('4vec-part-install & & & &)(cons 'sv::partinst (cdr term)))
    (& (hard-error '4vec-to-svex "cannot match ~p0 with ~p1 arguments to any ~
  svex function. If you think this is a bug, consider changing ~
  svl::to-svex-fnc. ~%"
                   (list (cons #\0 (if (consp term) (car term) term))
                         (cons #\1 (1- (len term))))))))

(mutual-recursion
 (defun 4vec-to-svex (term reverse-env)
;(declare (xargs :mode :program))
   (declare (xargs :guard t))
   (b* ((term (rp::ex-from-rp term)))
     (cond ((atom term)
            (let ((entry (hons-get term reverse-env)))
              (cdr entry)))
           ((and (quotep term)
                 (consp (cdr term)))
            (unquote term))
           (t (b* ((fnc (car term))
                   (args (4vec-to-svex-lst (cdr term)
                                           reverse-env)))
                (to-svex-fnc (cons fnc args)))))))
 (defun 4vec-to-svex-lst (lst reverse-env)
;(declare (xargs :mode :program))
   (if (atom lst)
       nil
     (cons (4vec-to-svex (car lst) reverse-env)
           (4vec-to-svex-lst (cdr lst) reverse-env)))))

(define svex-simplify (svex
                       &KEY
                       (state 'state)
                       (rp::rp-state 'rp::rp-state)
                       (hyp ''t) ;; "Have more context for variables."
                       (runes '(let ((world (w state))) (current-theory
                                                         :here)))
                       ;; "if need to work with only certain rules other than current-theory"
                       (svex-simplify-preloaded 'nil) ;; Non-nil overrides rule
                       ;; structure  creation for the rewriter. This value
                       ;; can be created with (svex-simplify-preload)
                       )
  (declare (xargs ;:mode :program
            :verify-guards nil
            :stobjs (state
                     rp::rp-state)))
  (b* (((mv rw reverse-env rp::rp-state)
        (rw-svex-to-4vec svex
                         :state state
                         :hyp hyp
                         :runes runes
                         :svex-simplify-preloaded svex-simplify-preloaded))
       (svex-res (case-match rw
                   (('implies & term) (4vec-to-svex term
                                                    reverse-env))
                   (& (4vec-to-svex rw reverse-env)))))
    (mv svex-res rp::rp-state)))

;:i-am-here

(acl2::defxdoc svex-simplify
               :parents (projects/svl)
               :short "With existing rewrite rules for svex-eval and 4vec functions,
  rewrites an @('sv::svex')."
               :long "<p> SVEX-SIMPLIFY wraps an sv expression with an @('sv::svex-eval'),
  attaches some optional hypotheses for extra context and runs the main
  rp-rewriter function to perform rewriting, and then it converts the resulting
  term back to an equivalent sv expression. If you want to avoid conveting back
  to svex expression but get the rewritten term you may use rw-svex-to-4vec.
  </p>

<p> Example Use: </p>

@({
(defconst *test-svex*
   '(sv::partsel 0 3
     (sv::zerox 4
       (sv::concat 3 (sv::concat 2 (sv::concat 1 x y) z) k))))

;; This call will return an equivalent expression for *test-svex*
(svl::svex-simplify *test-svex*)

;; Returned value:
'(CONCAT 1 (PARTSEL 0 1 X)
         (CONCAT 1 (PARTSEL 0 1 Y)
                 (PARTSEL 0 1 Z)))

;; This call will what the term is rewritten to before trying to convert it
;; back to svex format.
(svl::rw-svex-to-4vec *test-svex*)

;; Returned value
'(implies t
          (4vec-concat$ '1
                        (bits '0 '1 (rp '4vec-p x))
                        (4vec-concat$ '1
                                      (bits '0 '1 (rp '4vec-p y))
                                      (bits '0 '1 (rp '4vec-p z)))))
 })

<p> Users may also add more rewrite rules to have a different rewriting scheme than the
one that comes with this book. Should these new rewrite rules need more context
about the variables, you may pass an extra hyp argument (should be a translated term) to
rw-svex-to-4vec or svex-simplify. Note: the functions assume that even without any
hypothesis, all the variables in the svex satisfy 4vec-p.</p>

<p> If you anticipate to call svl::svex-simplify or svl::rw-svex-to-4vec many
times for the same set of rules, you may want to use
(svl::svex-simplify-preload). This function call will return a structure and can
be passed to svl::svex-simplify and svl::rw-svex-to-4vec with the key
:svex-simplify-preloaded. This avoids retrieval and parsion of rules from the
world. When you are finished, it is advisable to execute (svex-rw-free-preload
svex-rw-free-preloaded state) in order to free some fast-alists created. </p>

")
