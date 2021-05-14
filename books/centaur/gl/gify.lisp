; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "std/util/bstar" :dir :system)
(include-book "defapply")
(include-book "misc/hons-help" :dir :system)
(include-book "factor-fns")
(include-book "g-primitives-help")
(include-book "tools/templates" :dir :system)
(program)

(mutual-recursion
 ;; Collect the functions called within a term.
 (defun collect-fns (term clique acc)
   (cond ((or (atom term) (eq (car term) 'quote)) acc)
         ((eq (car term) 'if)
          (collect-fns-lst (cdr term) clique acc))
         ((symbolp (car term))
          (let ((acc (collect-fns-lst (cdr term) clique acc)))
            (if (or (hons-get (car term) acc)
                    (member-eq (car term) clique))
                acc
              (hons-acons (car term) t acc))))
         (t ;; lambda
          (collect-fns (caddar term) clique
                       (collect-fns-lst (cdr term) clique acc)))))
 (defun collect-fns-lst (lst clique acc)
   (if (atom lst)
       acc
     (collect-fns-lst (cdr lst) clique
                      (collect-fns (car lst) clique acc)))))


(defun clique-bodies (clique world)
  (if (atom clique)
      nil
    (cons (norm-function-body (car clique) world)
          (clique-bodies (cdr clique) world))))

(mutual-recursion
 (defun collect-fns-fn (fn done acc world)
   (if (hons-get fn done)
       (mv done acc)
     (b* ((clique (or (wgetprop fn 'recursivep) (list fn)))
          (bodies (clique-bodies clique world))
          (body-fns (collect-fns-lst bodies clique nil))
          (body-fns (strip-cars (flush-hons-get-hash-table-link body-fns)))
          (done (acl2::hons-put-list clique t done))
          ((mv done acc) (collect-fns-list body-fns done acc world)))
       (mv done (cons (car clique) acc)))))
 (defun collect-fns-list (lst done acc world)
   (if (atom lst)
       (mv done acc)
     (mv-let (done acc)
       (collect-fns-fn (car lst) done acc world)
       (collect-fns-list (cdr lst) done acc world)))))


(defun collect-fn-deps-with-exclusions (fns done-fal world)
  (mv-let (done acc)
    (collect-fns-list fns done-fal nil world)
    (prog2$ (flush-hons-get-hash-table-link done)
            (reverse acc))))


(defun collect-fn-deps (fns world)
  (mv-let (done acc)
    (collect-fns-list fns (make-fal (append '((acl2::return-last))
                                            (table-alist 'gl-function-info world)) nil)
                      nil world)
    (prog2$ (flush-hons-get-hash-table-link done)
            (reverse acc))))






(mutual-recursion
 (defun gify-term (x fn)
   (cond ((atom x) (if (constant-syntax-p x) `(mk-g-concrete ,x) x))
         ((eq (car x) 'quote) `(g-concrete-quote ,x))
         ((eq (car x) 'return-last)
          (cond ((eq (cadr x) ''time$1-raw)
                 `(time$ ,(gify-term (car (last x)) fn)))
                (t (gify-term (car (last x)) fn))))
         ((eq (car x) 'gl-aside) `(gl-aside (hide ,(cadr x))))
         ;; BOZO.  GL-ERROR behaves very differently in the symbolic
         ;; interpretation case: it runs its argument and saves it in a state
         ;; global.  We can't do that here because symbolic counterparts don't
         ;; take state.
         ((eq (car x) 'gl-error) `(gl-error ,(gify-term (cadr x) fn)))
         ((eq (car x) 'if)
          (if (equal (cadr x) (caddr x))
              (let* ((test (gify-term (cadr x) fn))
                     (else (gify-term (cadddr x) fn)))
                `(g-or ,test ,else))
            (let* ((test (gify-term (cadr x) fn))
                   (then (gify-term (caddr x) fn))
                   (else (gify-term (cadddr x) fn)))
              `(g-if ,test ,then ,else))))
         ((consp (car x))
          (er hard 'gify-term
              "We expect lambdas to all have been factored out of functions to
be gified.  If not, implement this case.  Culprit (in function ~x0): ~x1~%"
              fn (car x)))
         (t (cons (gl-fnsym (car x))
                  (append (gify-term-list (cdr x) fn)
                          '(hyp clk config bvar-db state))))))
 (defun gify-term-list (x fn)
   (if (endp x)
       nil
     (cons (gify-term (car x) fn)
           (gify-term-list (cdr x) fn)))))

(defun gify-body (x fn)
  (let ((body (cond ((acl2::throw-nonexec-error-p x nil nil)
                     (car (last x)))
                    (t x))))
    (gify-term body fn)))



;; (defun gobjectp-guards (formals)
;;   (if (atom formals)
;;       nil
;;     (cons `(gobjectp ,(car formals))
;;           (gobjectp-guards (cdr formals)))))

;; (defun gobjectp-hyps (formals)
;;   (if (atom formals)
;;       nil
;;     (cons `(gobjectp ,(car formals))
;;           (gobjectp-hyps (cdr formals)))))

(defun eval-thm-bindings (vars ev)
  (if (atom vars)
      nil
    (if (not (or (eq (car vars) 'hyp)
                 (eq (car vars) 'clk)))
        (cons (list (car vars) `(,ev ,(car vars) env))
              (eval-thm-bindings (cdr vars) ev))
      (eval-thm-bindings (cdr vars) ev))))



(defun formals-general-concretep (formals)
  (if (atom formals)
      nil
    (cons `(general-concretep ,(car formals))
          (formals-general-concretep (cdr formals)))))

(defun formals-general-concrete-obj (formals)
  (if (atom formals)
      nil
    (cons `(general-concrete-obj ,(car formals))
          (formals-general-concrete-obj (cdr formals)))))

;; The last function in this list should be the Gified version of top-fn; we
;; ignore its name.
(defun gify-factored-fns (top-fn fns idx world defuns)
  (if (endp fns)
      (er hard 'gify-factored-fns "Empty list of functions; top: ~x0~%" top-fn)
    (b* ((fn (car fns))
         (endp (endp (cdr fns)))
         (body (body (car fns) nil world))
         (gbody (gify-body body (car fns)))
         (formals (wgetprop fn 'formals))
         (recursivep (wgetprop top-fn 'recursivep))
         (guards `(and (natp clk)
                       (glcp-config-p config)))
         (name (gl-fnsym (if endp top-fn fn)))
         (defun
           `(defun ,name ,(append formals '(hyp clk config bvar-db state))
              (declare
               (xargs
                :guard ,guards
                :stobjs (bvar-db state)
                :verify-guards nil
                . ,(and recursivep
                        `(:measure
                          (acl2::two-nats-measure clk ,(if endp 0 idx))
                          . ,(and endp
                                  `(:hints (("goal" :in-theory
                                             (e/d** ((:ruleset
                                                      clk-measure-rules))))))))))
               (ignorable hyp clk config bvar-db state . ,formals))
                ,(if endp
                     (let ((clkbody `(if (zp clk)
                                         (prog2$
                                          (cw "~
Warning: Clock ran out in ~x0~%" ',(gl-fnsym top-fn))
                                          (g-apply ',top-fn (gl-list . ,formals)))
                                       (let ((clk (1- clk)))
                                         (declare (ignorable clk))
                                         ,gbody))))
                       (if (or (wgetprop top-fn 'non-executablep)
                               (wgetprop top-fn 'constrainedp)
                               (assoc-eq top-fn (table-alist 'do-not-execute
                                                             world)))
                           clkbody
                         `(if (and . ,(formals-general-concretep formals))
                              (mk-g-concrete
                               ,(make-mv-call top-fn (formals-general-concrete-obj
                                                      formals) world))
                            ,clkbody)))
                   gbody))))
      (if endp
          (cons defun defuns)
        (gify-factored-fns top-fn (cdr fns) (1+ idx) world
                           (cons defun defuns))))))



(defmacro factored-fns (fn)
  `(cdr (assoc-eq ,fn (table-alist 'factored-fns world))))

(defun gify-fn-clique (clique world defuns)
  (if (atom clique)
      defuns
    (gify-fn-clique (cdr clique) world
                    (gify-factored-fns
                     (car clique)
                     (or (factored-fns (car clique))
                         (list (car clique)))
                     1 world defuns))))


(defun gify-fn (fn world)
  (let* ((recp (wgetprop fn 'recursivep))
         (clique (or recp (list fn)))
         (defuns (gify-fn-clique clique world nil)))
    (if (and recp (<= 2 (length defuns)))
        `(mutual-recursion . ,defuns)
      `(progn . ,(reverse defuns)))))


(defun gify-stub (fn world)
  (let* ((formals (wgetprop fn 'formals))
         (name (gl-fnsym fn))
         (nonexec (or (wgetprop fn 'constrainedp)
                      (wgetprop fn 'non-executablep)
                      (assoc-eq fn (table-alist 'do-not-execute
                                                world)))))
    `(defun ,name (,@formals hyp clk config bvar-db state)
       (declare (xargs :guard (and (natp clk)
                                   (glcp-config-p config))
                       :stobjs (bvar-db state)
                       :verify-guards nil))
       ,(if nonexec
            `(g-apply ',fn (gl-list . ,formals))
          `(if (and . ,(formals-general-concretep formals))
               (mk-g-concrete
                ,(make-mv-call fn (formals-general-concrete-obj formals)
                               world))
             (g-apply ',fn (gl-list . ,formals)))))))

(defconst *no-factor-fns* '(acl2::return-last))

(defun gify-fns-and-deps1 (deps world)
  (if (endp deps)
      nil
    (if (and (norm-function-body (car deps) world)
             (not (member (car deps) '(acl2::return-last))))
        ;; This is nonnil when the function has a definition.
        `(,@(and (not (member (car deps) *no-factor-fns*))
                 `((factor-fn ,(car deps))))
            (make-event (gify-fn ',(car deps) (w state)))
            . ,(gify-fns-and-deps1 (cdr deps) world))
      ;; If this is nil, the function is undefined.
      (prog2$
       (cw "Warning: GIFYing undefined function ~x0~%" (car deps))
       (cons `(make-event (gify-stub ',(car deps) (w state)))
             (gify-fns-and-deps1 (cdr deps) world))))))

(defun gify-fns-and-deps (fns world)
  (let ((deps (collect-fn-deps fns world)))
    `(progn . ,(gify-fns-and-deps1 deps world))))











;; (defun gobjectp-thmname (fn)
;;   (incat 'gl-thm::foo "GOBJECTP-" (symbol-name fn)))


;; (defun gobjectp-factored-thm-bodies-rec (top-fn fns world entries)
;;   (if (endp fns)
;;       (prog2$ (acl2::break$)
;;               (er hard 'gobjectp-factored-thm-bodies-rec "Empty list of functions; top: ~x0~%"
;;                   top-fn))
;;     (b* ((fn (car fns))
;;          (formals (wgetprop fn 'formals))
;;          (endp (endp (cdr fns)))
;;          (name (gl-fnsym (if endp top-fn fn)))
;;          (gobjectp-thm `(,name
;;                          (gobjectp (,name ,@formals hyp clk config bvar-db state))
;;                          :name ,(gobjectp-thmname name))))
;;       (if endp
;;           (cons gobjectp-thm entries)
;;         (gobjectp-factored-thm-bodies-rec top-fn (cdr fns) world
;;                                           (cons gobjectp-thm entries))))))

;; (defun gobjectp-clique-thm-bodies (clique world entries)
;;   (if (endp clique)
;;       entries
;;     (b* ((fn (car clique))
;;          (fns (factored-fns fn))
;;          (entries (gobjectp-factored-thm-bodies-rec fn fns world entries)))
;;       (gobjectp-clique-thm-bodies (cdr clique) world entries))))

;; (defun gobjectp-redundant-top-thms (clique world)
;;   (if (endp clique)
;;       nil
;;     (b* ((fn (car clique))
;;          (name (gl-fnsym fn))
;;          (thmname (gobjectp-thmname name))
;;          (formals (wgetprop fn 'formals)))
;;       (cons `(defthm ,thmname
;;                (gobjectp (,name ,@formals hyp clk config bvar-db state)))
;;             (gobjectp-redundant-top-thms (cdr clique) world)))))




(defmacro defname (name)
  `(or (cdr (assoc-eq ,name (table-alist 'preferred-defs world)))
       ,name))

;; (defun gobjectp-factored-thms (top-fn fns world thms)
;;   (if (endp fns)
;;       (er hard 'gobjectp-factored-thms "Empty list of functions; top: ~x0~%"
;;           top-fn)
;;     (b* ((fn (car fns))
;;          (formals (wgetprop fn 'formals))
;;          (endp (endp (cdr fns)))
;;          (name (gl-fnsym (if endp top-fn fn)))
;;          (gobjectp-name (gobjectp-thmname name))
;;          (defname (defname name))
;;          (gobjectp-thm
;;           `(defthm ,gobjectp-name
;;              (gobjectp (,name ,@formals hyp clk config bvar-db state))
;;              :hints (("goal" :expand ((:with (:definition ,defname)
;;                                              (,name ,@formals hyp clk config bvar-db state)))
;;                       :do-not '(preprocess)))))
;;          (gobjectp-thm (if endp gobjectp-thm `(local ,gobjectp-thm))))
;;       (if endp
;;           (cons gobjectp-thm thms)
;;         (gobjectp-factored-thms
;;          top-fn (cdr fns) world (cons gobjectp-thm thms))))))

(defun g-factored-fn-names (top-fn fns acc)
  (if (endp fns)
      (er hard 'g-factored-fn-names "Empty list of functions; top: ~x0~%"
          top-fn)
    (if (endp (cdr fns))
        (cons (gl-fnsym top-fn) acc)
      (g-factored-fn-names
         top-fn (cdr fns)
         (cons (gl-fnsym (car fns)) acc)))))


(defun g-clique-fn-names (clique world)
  (wgetprop (car clique) 'recursivep))

(defun clique-fn-names (clique world)
  (if (endp clique)
      nil
    (append (factored-fns (car clique))
            (clique-fn-names (cdr clique) world))))


;; (defun gobjectp-flag-lemma (fn)
;;   (incat 'gl-thm::foo "GOBJECTP-" (symbol-name fn) "-LEMMA"))

;; (defun gobjectp-thmnames (fns)
;;   (if (endp fns)
;;       nil
;;     (cons (gobjectp-thmname (car fns))
;;           (gobjectp-thmnames (cdr fns)))))

(defun make-expand-list (terms world)
  (if (atom terms)
      nil
    (let ((defname (defname (caar terms))))
      (cons `(:with (:definition ,defname) ,(car terms))
            (make-expand-list (cdr terms) world)))))

(defun expand-calls-computed-hint (clause fns world)
  (let ((expand-list (flag::find-calls-of-fns-term
                      (car (last clause)) fns nil)))
    `(:expand ,(make-expand-list expand-list world))))

(defun gl-fnsym-list (lst)
  (if (atom lst)
      nil
    (cons (gl-fnsym (car lst))
          (gl-fnsym-list (Cdr lst)))))

(defun make-redundant-list (names)
  (if (atom names)
      nil
    (cons `(acl2::make-redundant ,(car names))
          (make-redundant-list (cdr names)))))

;; (defun gobjectp-thms (top-fn world)
;;   (b* ((recp (wgetprop top-fn 'recursivep)))
;;     (if recp
;;         (b* ((entries (gobjectp-clique-thm-bodies recp world nil))
;;              (gfn1 (gl-fnsym (car recp)))
;;              (gfns (wgetprop gfn1 'recursivep))
;;              (gfn (car gfns))
;;              (flag-fn (flag-fn-name gfn world))
;;              (flag-formals (wgetprop flag-fn 'formals))
;;              (thmnames (gobjectp-thmnames gfns)))
;;           `(progn
;;              (local (in-theory
;;                      (e/d** (minimal-theory
;;                              ;; (:executable-counterpart-theory :here)
;;                              (:ruleset g-gobjectp-lemmas)
;;                              (:induction ,flag-fn)
;;                              ,(flag-equivs-name gfn world))
;;                             ((immediate-force-modep) not))))
;;              ;; Submit the flag defthm locally, then redundantly
;;              ;; resubmit the top-level lemmas nonlocally; the
;;              ;; lower-level lemmas will remain local to the
;;              ;; make-g-world.
;;              (local
;;               (,(flag-defthm-macro gfn world)
;;                ,(gobjectp-flag-lemma gfn)
;;                ,@entries
;;                :hints (("goal" :induct (,flag-fn . ,flag-formals)
;;                         :do-not '(preprocess))
;;                        (and stable-under-simplificationp
;;                             (expand-calls-computed-hint
;;                              acl2::clause ',gfns world)))))
;;              ,@(gobjectp-redundant-top-thms recp world)
;;              (local (add-to-ruleset g-gobjectp-lemmas ',thmnames))
;;              (add-to-ruleset g-gobjectp-lemmas
;;                              ',(gobjectp-thmnames (gl-fnsym-list
;;                                                    recp)))))
;;       (b* ((fns (or (factored-fns top-fn) (list top-fn)))
;;            (thms (gobjectp-factored-thms top-fn fns world nil)))
;;         `(progn
;;            (local (in-theory
;;                    (e/d** (minimal-theory
;;                            ;; (:executable-counterpart-theory :here)
;;                            (:ruleset g-gobjectp-lemmas))
;;                           ((immediate-force-modep)
;;                            (force) not))))
;;            ,@(reverse thms)
;;            (local (add-to-ruleset
;;                    g-gobjectp-lemmas
;;                    ',(gobjectp-thmnames
;;                       (g-factored-fn-names top-fn fns nil))))
;;            (add-to-ruleset
;;             g-gobjectp-lemmas
;;             '(,(gobjectp-thmname (gl-fnsym top-fn)))))))))


(defun flag-fn (top-fn)
  (incat 'gl-flag::foo (symbol-name top-fn) "-IND"))

(defun flagify-g-fns-and-deps1 (deps world)
  (if (endp deps)
      nil
    (let* ((gfn (gl-fnsym (car deps)))
           (gfn-recp (wgetprop gfn 'recursivep))
           (rest (flagify-g-fns-and-deps1 (cdr deps) world))
           (rest (if (and (<= 1 (length gfn-recp))
                          (not (flag-present gfn world)))
                     (let ((gfn (car gfn-recp)))
                       (cons `(flag::make-flag
                               ,(flag-fn gfn) ,gfn
                               :local t
                               :hints (("goal" :in-theory
                                        (e/d** ((:ruleset
                                                 clk-measure-rules))))))
                             rest))
                   rest)))
      rest)))

(defun flagify-g-fns-and-deps (fns world)
  (let ((deps (collect-fn-deps fns world)))
    `(progn
       . ,(flagify-g-fns-and-deps1 deps world))))

(defun flagify-fns-and-deps1 (deps world)
  (if (endp deps)
      nil
    (let* ((fn-recp (wgetprop (car deps) 'recursivep))
           (rest (flagify-fns-and-deps1 (cdr deps) world))
           (rest (if (and (<= 2 (length fn-recp))
                          (not (flag-present (car deps) world)))
                     (let ((fn (car fn-recp)))
                       (cons `(flag::make-flag
                               ,(flag-fn fn) ,fn
                               :local t)
                             rest))
                   rest)))
      rest)))

(defun flagify-fns-and-deps (fns world)
  (let ((deps (collect-fn-deps fns world)))
    `(progn . ,(flagify-fns-and-deps1 deps world))))




;; (defun gobjectp-fns-and-deps1 (deps)
;;   (if (endp deps)
;;       nil
;;     `((make-event (gobjectp-thms ',(car deps) (w state)))
;;       . ,(gobjectp-fns-and-deps1 (cdr deps)))))

;; (defun gobjectp-fns-and-deps (fns world)
;;   (let ((deps (collect-fn-deps fns world)))
;;     `(progn . ,(gobjectp-fns-and-deps1 deps))))










(defun g-factored-fns-verify-guards (top-fn fns world)
 (if (endp fns)
      (er hard 'g-factored-fns-verify-guards
          "Empty list of functions; top: ~x0~%" top-fn)
    (if (endp (cdr fns))
        (let ((stobjs-out (wgetprop top-fn 'stobjs-out)))
          `((verify-guards
             ,(gl-fnsym top-fn)
             ,@(and stobjs-out (<= 2 (length stobjs-out))
                    (acl2::runep `(:type-prescription ,top-fn) world)
                    `(:hints (("Goal" :in-theory
                               (enable (:type-prescription ,top-fn)))))))))
      `((verify-guards ,(gl-fnsym (car fns)))
        . ,(g-factored-fns-verify-guards top-fn (cdr fns) world)))))

(defun type-prescriptions-of-mv-fns (clique world)
  (if (atom clique)
      nil
    (let ((stobjs-out (wgetprop (car clique) 'stobjs-out)))
      (if (and stobjs-out (<= 2 (length stobjs-out))
               (acl2::runep `(:type-prescription ,(car clique)) world))
          (cons `(:type-prescription ,(car clique))
                (type-prescriptions-of-mv-fns (cdr clique) world))
        (type-prescriptions-of-mv-fns (cdr clique) world)))))



(defun g-guards-fns-and-deps1 (deps world)
  (if (endp deps)
      nil
    (let* ((gfn (gl-fnsym (car deps)))
           (recp (wgetprop gfn 'recursivep)))
      (if recp
          (let ((mvtyps (type-prescriptions-of-mv-fns
                         (or (wgetprop (car deps) 'recursivep)
                             (list (car deps))) world)))
            (cons `(verify-guards
                    ,(car recp)
                    ,@(and mvtyps
                           `(:hints (("goal" :in-theory (enable . ,mvtyps))))))
                  (g-guards-fns-and-deps1 (cdr deps) world)))
        (append (g-factored-fns-verify-guards
                 (car deps)
                 (or (factored-fns (car deps)) (list (car deps)))
                 world)
                (g-guards-fns-and-deps1 (cdr deps) world))))))

(defun g-guards-fns-and-deps (fns world)
  (let ((deps (collect-fn-deps fns world)))
    `(progn
       (logic)
       (local (in-theory (e/d** (minimal-theory
                                 ;; (:executable-counterpart-theory :here)
                                 ;; (:ruleset g-gobjectp-lemmas)
                                 (:ruleset g-guard-lemmas)
                                 zp natp)
                                ((immediate-force-modep) not))))
       . ,(g-guards-fns-and-deps1 deps world))))










(defun ruleset-for-eval (ev)
  (incat ev (symbol-name ev) "-RULESET"))



(defun eval-list-env (ev lst)
  (if (endp lst)
      nil
    (cons `(,ev ,(car lst) env)
          (eval-list-env ev (cdr lst)))))




(defun g-correct-factored-thm-bodies-rec (top-fn fns ev world entries)
  (if (endp fns)
      (er hard 'g-correct-factored-thm-bodies-rec "Empty list of functions; top: ~x0~%"
          top-fn)
    (b* ((endp (endp (cdr fns)))
         (fn (if endp top-fn (car fns)))
         (formals (wgetprop fn 'formals))
         (name (gl-fnsym fn))
         (g-correct-thm `(,name
                          (implies (bfr-eval hyp (car env))
                                   (equal (,ev (,name ,@formals hyp clk config bvar-db state) env)
                                          (,fn . ,(eval-list-env ev formals))))
                          . ,(if endp
                                 `(:name ,(correct-thmname name))
                               `(:skip t)))))
      (if endp
          (cons g-correct-thm entries)
        (g-correct-factored-thm-bodies-rec top-fn (cdr fns) ev world
                                           (cons g-correct-thm entries))))))

(defun g-correct-clique-thm-bodies (clique ev world entries)
  (if (endp clique)
      entries
    (b* ((fn (car clique))
         (fns (factored-fns fn))
         (entries (g-correct-factored-thm-bodies-rec fn fns ev world entries)))
      (g-correct-clique-thm-bodies (cdr clique) ev world entries))))


(defun factored-fn-correct-thms (clique world)
  (if (atom clique)
      nil
    (if (factored-fns (car clique))
        (cons (correct-thmname (factored-fnname (car clique)))
              (factored-fn-correct-thms (cdr clique) world))
      (factored-fn-correct-thms (cdr clique) world))))

(defun g-correct-factored-thms (top-fn fns ev world thms)
  (if (endp fns)
      (er hard 'g-correct-factored-thms "Empty list of functions; top: ~x0~%"
          top-fn)
    (b* ((endp (endp (cdr fns)))
         (fn (if endp top-fn (car fns)))
         (definedp (norm-function-body fn world))
         (formals (wgetprop fn 'formals))
         (name (gl-fnsym fn))
         (g-correct-name (correct-thmname name))
         (g-correct-thm
          `(defthm ,g-correct-name
             (implies (bfr-eval hyp (car env))
                      (equal (,ev (,name ,@formals hyp clk config bvar-db state) env)
                             (,fn . ,(eval-list-env ev formals))))
             :hints (("goal" :expand
                      ((,name ,@formals hyp clk config bvar-db state))
                      ,@(and endp definedp
                             `(:in-theory (e/d ()
                                               ,(factored-fn-correct-thms
                                                 (list top-fn) world))))
                      ;; :do-not '(preprocess)
                      )
                     ,@(and endp definedp
                            `((and stable-under-simplificationp
                                   '(:in-theory (e/d ,(factored-fn-correct-thms
                                                       (list top-fn) world))))))
                     ,@(and definedp
                            `((and stable-under-simplificationp
                                   (let ((lit (car (last clause))))
                                     (case-match lit
                                       (('equal term ('quote &))
                                        (and (consp term)
                                             (not (eq (car term) 'quote))
                                             `(:expand (,term))))
                                       (('equal & term)
                                        (and (consp term)
                                             (not (eq (car term) 'quote))
                                             `(:expand (,term))))
                                       (('not term)
                                        (and (consp term)
                                             (not (eq (car term) 'quote))
                                             `(:expand
                                               (,term)))))))))
                     (and stable-under-simplificationp
                          '(:expand ((:free (x) (hide x))))))))
         (g-correct-thm (if endp g-correct-thm `(local ,g-correct-thm))))
      (if endp
          (cons g-correct-thm thms)
        (g-correct-factored-thms
         top-fn (cdr fns) ev world (cons g-correct-thm thms))))))




(defun g-correct-flag-lemma (fn)
  (incat 'gl-thm::foo (symbol-name fn) "-CORRECT-LEMMA"))

(defun g-correct-thmnames (fns)
  (if (endp fns)
      nil
    (cons (correct-thmname (car fns))
          (g-correct-thmnames (cdr fns)))))




(defun clique-gl-function-info-table-events (clique ev)
  (if (atom clique)
      nil
    (cons `(table gl-function-info ',(car clique)
                  '(,(gl-fnsym (car clique))
                    (,(correct-thmname (gl-fnsym (car clique)))
                     . ,ev)))
          (clique-gl-function-info-table-events (cdr clique) ev))))


(defun g-correct-thms (top-fn ev world)
  (declare (xargs :mode :program))
  (b* ((recp (wgetprop top-fn 'recursivep))
       (definedp (norm-function-body top-fn world)))
    (if recp
        (b* ((entries (g-correct-clique-thm-bodies recp ev world nil))
             (gfn1 (gl-fnsym (car recp)))
             (gfns (wgetprop gfn1 'recursivep))
             (gfn (car gfns))
             (flag-fn (flag-fn-name gfn world))
             (flag-formals (wgetprop flag-fn 'formals))
             (thmnames (g-correct-thmnames
                        (gl-fnsym-list recp))))
          `(progn
             (local (in-theory
                     (e/d** (minimal-theory
                             car-cons cdr-cons
                             ;; (:executable-counterpart-theory :here)
                             (cons) (not) (equal)
                             kwote-lst kwote
                             ;; (:ruleset g-gobjectp-lemmas)
                             (:ruleset g-correct-lemmas)
                             (:ruleset ,(ruleset-for-eval ev))
                             (:ruleset apply-rewrites)
                             ,@(factored-fn-correct-thms recp world)
                             ;; (:ruleset factor-ruleset)
                             (:induction ,flag-fn)
                             ,(flag-equivs-name gfn world))
                            ((immediate-force-modep) not))))
             (,(flag-defthm-macro gfn world)
              ,(g-correct-flag-lemma gfn)
              ,@entries
              :hints (("goal" :induct (,flag-fn . ,flag-formals)
;;                        :do-not '(preprocess)
                       :in-theory (e/d ()
                                       ,@(and definedp
                                              `(,(factored-fn-correct-thms
                                                  recp world)))))
                      ,@(and definedp
                             `((expand-calls-computed-hint
                                 acl2::clause
                                 '(,@gfns) world)
                               (and stable-under-simplificationp
                                    '(:in-theory
                                      (enable . ,(factored-fn-correct-thms
                                                  recp world))))
                               (and stable-under-simplificationp
                                    (let ((lit (car (last clause))))
                                     (case-match lit
                                       (('equal term ('quote &))
                                        (and (consp term)
                                             (not (eq (car term) 'quote))
                                             `(:expand (,term))))
                                       (('equal & term)
                                        (and (consp term)
                                             (not (eq (car term) 'quote))
                                             `(:expand (,term))))
                                       (('not term)
                                        (and (consp term)
                                             (not (eq (car term) 'quote))
                                             `(:expand (,term)))))))
                               (and stable-under-simplificationp
                                    '(:expand ((:free (x) (hide x))))))))

                      ;; BOZO. This is an ugly sort of desperation move. Blech.
                      ;; (and stable-under-simplificationp
;;                            '(:in-theory (union-theories
;;                                          (current-theory :here)
;;                                          (all-of-ruleclass :type-prescription
;;                                                            (universal-theory :here)))))
                      )
             (add-to-ruleset ,(ruleset-for-eval ev) ',thmnames)
             . ,(clique-gl-function-info-table-events recp ev)))
      (b* ((fns (or (factored-fns top-fn) (list top-fn)))
           (thms (g-correct-factored-thms top-fn fns ev world nil)))
        `(progn
           (local (in-theory
                   (e/d** (minimal-theory
                           car-cons cdr-cons
                           ;; (:executable-counterpart-theory :here)
                           (cons) (not) (equal)
                           kwote-lst kwote
                           (:ruleset g-correct-lemmas)
                           (:ruleset ,(ruleset-for-eval ev))
                           ,@(and (member-eq
                                   (correct-thmname (factored-fnname top-fn))
                                   (acl2::ruleset 'factor-ruleset))
                                  (list (correct-thmname (factored-fnname top-fn))))
                           ;; (:ruleset factor-ruleset)
                           (:ruleset apply-rewrites))
                          ((immediate-force-modep) not))))
           ,@(reverse thms)
           (add-to-ruleset
            ,(ruleset-for-eval ev)
            '(,(correct-thmname (gl-fnsym top-fn))))
           (table gl-function-info ',top-fn
                  '(,(gl-fnsym top-fn)
                    (,(correct-thmname (gl-fnsym top-fn))
                     . ,ev))))))))



(defun g-correct-fns-and-deps1 (deps ev)
  (if (endp deps)
      nil
    `((make-event (g-correct-thms ',(car deps) ',ev (w state)))
      . ,(g-correct-fns-and-deps1 (cdr deps) ev))))

(defun g-correct-fns-and-deps (fns ev world)
  (let ((deps (collect-fn-deps fns world)))
    `(progn . ,(g-correct-fns-and-deps1 deps ev))))






(defun hons-get-any (lst al)
  (if (atom lst)
      nil
    (or (hons-get (car lst) al)
        (hons-get-any (cdr lst) al))))

(defun remove-cliques-in-al (fns al world)
  (if (atom fns)
      nil
    (b* ((fn (car fns))
         (clique (or (wgetprop fn 'recursivep) (list fn))))
      (if (hons-get-any clique al)
          (remove-cliques-in-al (cdr fns) al world)
        (cons fn (remove-cliques-in-al (cdr fns) al world))))))


(defun lambda-for-apply-stub-fi (oldfns newfns world)
  `(lambda (f args)
     (cond ,@(make-apply-entries
              (remove-cliques-in-al newfns (acl2::hons-put-list oldfns t nil) world)
              world nil)
           (t (apply-stub f args)))))

(mutual-recursion
 (defun subst-fns-term (term subst)
   (cond ((or (atom term) (eq (car term) 'quote)) term)
         ((atom (car term))
          (let ((lookup (assoc (car term) subst)))
            (cons (if lookup (cdr lookup) (car term))
                  (subst-fns-list (cdr term) subst))))
         (t
          (cons (list 'lambda (cadar term)
                      (subst-fns-term (caddar term) subst))
                (subst-fns-list (cdr term) subst)))))
 (defun subst-fns-list (lst subst)
   (if (atom lst)
       nil
     (cons (subst-fns-term (car lst) subst)
           (subst-fns-list (cdr lst) subst)))))


(defun equal-f-fns (lst)
  (if (atom lst)
      nil
    (cons `(equal f ',(car lst))
          (equal-f-fns (cdr lst)))))


;; (defun eval-g-fi (eval oldeval thmname world)
;;   (let* ((apply (caddr (assoc eval (table-alist 'eval-g-table world))))
;;          (oldapply (caddr (assoc oldeval (table-alist 'eval-g-table world))))
;;          (applyfns
;;           (cdr (assoc apply (table-alist 'g-apply-table world))))
;;          (oldapplyfns
;;           (cdr (assoc oldapply (table-alist 'g-apply-table world)))))
;;   `(:functional-instance
;;     ,thmname
;;     ,@(if (eq oldapply 'apply-stub)
;;           `((apply-stub ,apply))
;;         `((apply-stub ,(lambda-for-apply-stub-fi
;;                         oldapplyfns applyfns world))
;;           (,oldapply ,apply)))
;;     (,oldeval ,eval))))


(defun eval-g-fi (eval oldeval thmname world)
  (b* (((list eval-list new-ev new-evlst)
        (cdr (assoc eval (table-alist 'eval-g-table world))))
       ((list oldeval-list old-ev old-evlst)
        (cdr (assoc oldeval (table-alist 'eval-g-table world)))))
    `(:functional-instance
      ,thmname
      (,old-ev ,new-ev)
      (,old-evlst ,new-evlst)
      (,oldeval ,eval)
      (,oldeval-list ,eval-list))))

(defconst *eval-g-prove-f-i-template*
  '(:computed-hint-replacement
    ((and stable-under-simplificationp
          '(:expand ((:free (f ar)
                      (_oldgeval_-apply f ar))
                     (:free (f ar)
                      (_newgeval_-apply f ar))))))
    :use
    ((:functional-instance
      _theorem_
      (_oldgeval_ _newgeval_)
      (_oldgeval_-list _newgeval_-list)
      (_oldgeval_-ev _newgeval_-ev)
      (_oldgeval_-ev-lst _newgeval_-ev-lst)))
    :in-theory (e/d**
                (;; nth-of-_oldgeval_-ev-concrete-lst
                 ;; nth-of-_newgeval_-ev-concrete-lst
                 acl2::car-to-nth-meta-correct
                 acl2::nth-of-cdr
                 acl2::list-fix-when-true-listp
                 acl2::kwote-list-list-fix
                 (:t acl2::list-fix)
                 _oldgeval_-apply-agrees-with-_oldgeval_-ev-rev
                 _newgeval_-apply-agrees-with-_newgeval_-ev-rev
                 _oldgeval_-ev-rules
                 _newgeval_-ev-rules
                 _newgeval_-ev-of-fncall-args
                 _oldgeval_-ev-of-fncall-args
                 _newgeval_-ev-of-nonsymbol-atom
                 _oldgeval_-ev-of-nonsymbol-atom
                 _newgeval_-ev-of-bad-fncall
                 _oldgeval_-ev-of-bad-fncall
                 car-cons cdr-cons nth-0-cons (nfix)))
    :expand (; (_oldgeval_ x env)
             (:with _newgeval_ (_newgeval_ x env))
             (:with _newgeval_-list (_newgeval_-list x env)))
    :do-not-induct t))

(defun eval-g-prove-f-i-fn (eval oldeval thmname)
  (declare (xargs :mode :program))
  `(defthm ,thmname
     t
     :hints (',(acl2::template-subst
                *eval-g-prove-f-i-template*
                :atom-alist `((_theorem_ . (:theorem
                                            (equal (,oldeval x env)
                                                   (,oldeval x env))))
                              (_oldgeval_ . ,oldeval)
                              (_newgeval_ . ,eval))
                :str-alist `(("_OLDGEVAL_" ,(symbol-name oldeval) . ,oldeval)
                             ("_NEWGEVAL_" ,(symbol-name eval) . ,eval))))
     :rule-classes nil))

     ;;                          (:computed-hint-replacement
     ;;           ((case-match
     ;;              clause
     ;;              ((('equal (fn . &) . &))
     ;;               (cond
     ;;                ((eq fn ',apply)
     ;;                 '(:computed-hint-replacement
     ;;                   ((use-by-computed-hint clause)
     ;;                    '(:clause-processor
     ;;                      (apply-cond-cp clause)
     ;;                      :do-not nil))
     ;;                   :clause-processor
     ;;                   (rw-cp clause
     ;;                          (rws-from-ruleset-fn
     ;;                           '((:definition ,apply))
     ;;                           (w state)))))
     ;;                ((eq fn ',eval)
     ;;                 '(:expand ((,eval x env))
     ;;                           :do-not nil))))))
     ;;           :use (,(eval-g-fi
     ;;                   eval oldeval
     ;;                   `(:theorem (equal (,oldeval x env)
     ;;                                     (,oldeval x env)))
     ;;                   world))

     ;;           :do-not '(preprocess simplify)
     ;;           :in-theory nil))
     ;; :rule-classes nil)))

(defmacro eval-g-prove-f-i
  (thmname eval oldeval
           &key (output '(:off (warning warning! observation prove acl2::proof-builder
                                        acl2::history event  proof-tree))))
  `(with-output ,@output
                (make-event (eval-g-prove-f-i-fn ',eval ',oldeval ',thmname))))

(defun f-i-thmname (thm eval)
  (incat 'gl-thm::foo (symbol-name thm) "-FOR-" (symbol-name eval)))

(defun eval-g-functional-instance-fn (eval oldeval thmname world)
  (b* (((list neweval-list new-ev new-evlst new-apply)
        (cdr (assoc eval (table-alist 'eval-g-table world))))
       ((list oldeval-list old-ev old-evlst old-apply)
        (cdr (assoc oldeval (table-alist 'eval-g-table world))))
       (thmbody (wgetprop thmname 'theorem))
       (subst-body (subst-fns-term thmbody (list (cons oldeval eval)
                                                 (cons old-apply new-apply)
                                                 (cons oldeval-list neweval-list)
                                                 (cons old-ev new-ev)
                                                 (cons old-evlst new-evlst))))
       (newthmname (f-i-thmname thmname eval)))
    `(defthm ,newthmname
       ,subst-body
       :hints (("goal" :in-theory (theory 'minimal-theory)
                :use (,(eval-g-fi eval oldeval thmname world)))))))

(defmacro eval-g-functional-instance (thmname eval oldeval)
  `(make-event (eval-g-functional-instance-fn ',eval ',oldeval ',thmname (w state))))




(defun correctness-lemmas-for-new-apply11
  (alist eval world done-finsts thms theory)
  (declare (ignorable world))
  (if (atom alist)
      (mv done-finsts thms theory)
    (b* ((thmbase (caar alist))
         (thmeval (cdar alist)))
      (if (cdar alist)
          (b* ((newthmname (f-i-thmname thmbase eval))
               ((mv thms done-finsts)
                (if (member thmeval done-finsts)
                    (mv thms done-finsts)
                  (mv (cons `(local (eval-g-prove-f-i
                                     ,(incat 'gl-thm::foo
                                             (symbol-name eval)
                                             "-IS-FUNCTIONAL-INSTANCE-OF-"
                                             (symbol-name thmeval))
                                     ,eval ,thmeval))
                            thms)
                      (cons thmeval done-finsts))))
               (thms (cons `(eval-g-functional-instance
                             ,thmbase ,eval ,thmeval)
                           thms))
               (theory (cons newthmname theory)))
            (correctness-lemmas-for-new-apply11
             (cdr alist) eval world done-finsts
             thms theory))
        (correctness-lemmas-for-new-apply11
         (cdr alist) eval world done-finsts thms (cons thmbase theory))))))



(defun correctness-lemmas-for-new-apply1 (alist eval world
                                                done-finsts thms theory)
  (if (atom alist)
      (mv (reverse thms) theory)
    (mv-let (done-finsts thms theory)
      (correctness-lemmas-for-new-apply11 (cddar alist) eval world
                                          done-finsts thms theory)
      (correctness-lemmas-for-new-apply1 (cdr alist) eval world
                                         done-finsts thms theory))))


(defun pair-onto (lst name)
  (if (atom lst)
      nil
    (cons (cons (car lst) name)
          (pair-onto (cdr lst) name))))

(defun correctness-lemmas-for-new-apply (eval world)
  ;; We functionally instantiate lemmas from two sources:
  ;; the ruleset GENERIC-GEVAL-G-CORRECT-LEMMAS, and the GL-FUNCTION-INFO
  ;; table.
  (let ((ruleset (acl2::get-ruleset 'generic-geval-g-correct-lemmas world)))
    (mv-let (done thms theory)
      (correctness-lemmas-for-new-apply11
       (pair-onto ruleset 'generic-geval) eval world nil nil nil)
      (correctness-lemmas-for-new-apply1 (table-alist 'gl-function-info world)
                                         eval world done thms theory))))


(defun geval-thm-names (names eval)
  (if (atom names)
      nil
    (cons (intern-in-package-of-symbol
                 (concatenate 'string
                              (symbol-name (car names)) "-"
                              (symbol-name eval))
                 eval)
          (geval-thm-names (cdr names) eval))))

(defmacro correctness-lemmas (eval)
  ;; (let ((ev-fn (incat eval (symbol-name eval) "-GIFY-EV"))
  ;;       (evlst-fn (incat eval (symbol-name eval) "-GIFY-EV-LST")))
    `(make-event
      (mv-let (events theory)
        (correctness-lemmas-for-new-apply
         ',eval (w state))
        (cons 'progn
              (append events
                      ;; `((def-geval-meta ,',eval ,',ev-fn ,',evlst-fn))
                      `((def-ruleset! ,',(ruleset-for-eval eval)
                          '(,@'nil
                            ;; ,(geval-thm-names
                            ;;   '(g-or-geval-meta-correct
                            ;;     g-if-geval-meta-correct
                            ;;     geval-g-if-marker
                            ;;     geval-g-or-marker
                            ;;     geval-g-test-marker
                            ;;     geval-g-branch-marker)
                            ;;   eval)
                            . ,theory))))))))

(defun find-definition-nume (pairs)
  (if (atom pairs)
      nil
    (if (eq (cadar pairs) :definition)
        (caar pairs)
      (find-definition-nume (cdr pairs)))))

(defun find-lemma-entry (props nume)
  (if (atom props)
      nil
    (if (and (eq (cadar props) 'acl2::lemmas)
             (eql (acl2::access acl2::rewrite-rule
                                (caddar props) :nume)
                  nume))
        (car props)
      (find-lemma-entry (cdr props) nume))))

(defun clique-and-controller-alist (fn world)
  (declare (xargs :mode :program))
  (let* ((props (acl2::actual-props (acl2::world-to-next-event
                                     (cdr (acl2::decode-logical-name
                                           fn world)))
                                    nil nil))
         (nume (find-definition-nume
                (getprop fn 'acl2::runic-mapping-pairs
                         nil 'current-acl2-world world)))
         (lemma (find-lemma-entry props nume)))
    (acl2::access acl2::rewrite-rule (caddr lemma)
                  :heuristic-info)))





(defun make-unnorm-preferred-defs1 (fns world)
  (declare (xargs :mode :program))
  (if (atom fns)
      nil
    (b* ((fn (car fns))
         (entry (assoc fn (table-alist 'preferred-defs world)))
         (formals (wgetprop fn 'formals 'none))
         (body (wgetprop fn 'unnormalized-body))
         ((when (or entry (not body) (eq formals 'none)))
          (make-unnorm-preferred-defs1 (cdr fns) world))
         ((when (member fn acl2::*definition-minimal-theory*))
          (make-unnorm-preferred-defs1 (cdr fns) world))
         (thmname (incat 'gl-thm::foo
                         (symbol-package-name fn)
                         "::" (symbol-name fn)
                         "-UNNORM-DEF")))
      (list* `(defthm ,thmname
                (equal (,fn . ,formals)
                       ,body)
                :hints (("goal" :by ,fn))
                :rule-classes
                ((:definition
                  :install-body t
                  . ,(and
                      (wgetprop fn 'recursivep)
                      (let ((pair (clique-and-controller-alist
                                   fn world)))
                        `(:clique
                          ,(car pair)
                          :controller-alist ,(cdr pair)))))))
             `(in-theory (disable ,thmname))
             `(table preferred-defs ',fn ',thmname)
             (make-unnorm-preferred-defs1 (cdr fns) world)))))


(defun make-unnorm-preferred-defs (fns world)
  `(progn . ,(make-unnorm-preferred-defs1 fns world)))

;; (defun apply-rw-names-clique (ap clique)
;;   (if (atom clique)
;;       nil
;;     (cons (apply-rw-name ap (car clique))
;;           (apply-rw-names-clique ap (cdr clique)))))

;; (defun apply-rw-names (ap fns world)
;;   (if (atom fns)
;;       nil
;;     (append (apply-rw-names-clique ap (or (wgetprop (car fns) 'recursivep)
;;                                           (list (car fns))))
;;             (apply-rw-names ap (cdr fns) world))))

(defun union-eq-lists (a)
  (if (atom a)
      nil
    (union-eq (car a)
              (union-eq-lists (cdr a)))))

(defun strip-nthcdrs (n a)
  (if (atom a)
      nil
    (cons (nthcdr n (Car a))
          (strip-nthcdrs n (cdr a)))))

(defun prev-apply-fns (world)
  (declare (Xargs :mode :program))
  (union-eq-lists (strip-nthcdrs 6 (table-alist 'eval-g-table world))))



(defun make-g-world-fn (fns ev state)
  (declare (xargs :stobjs state :mode :program))
  (b* ((world (w state))
       ;; (ap (incat ev (symbol-name ev) "-APPLY"))
       (new-fns (set-difference-eq
                 (collect-fn-deps fns world)
                 '(acl2::return-last)))
       (apply-fns (union-eq new-fns
                            (prev-apply-fns world)
                            (strip-cars (table-alist 'gl-function-info world)))))
    `(encapsulate nil
       (logic)
       (local (table acl2::theory-invariant-table nil nil :clear))
       (local (in-theory nil))
       (local (set-default-hints nil))
       (set-bogus-mutual-recursion-ok t)
       (set-bogus-defun-hints-ok t)
       (set-ignore-ok t)
       (set-irrelevant-formals-ok t)
       (local (make-event (make-unnorm-preferred-defs ',new-fns (w state))))
       (def-eval-g ,ev ,apply-fns)

       (make-event (gify-fns-and-deps ',new-fns (w state)))
       (make-event (flagify-g-fns-and-deps ',new-fns (w state)))



       ;; (make-event (gobjectp-fns-and-deps ',new-fns (w state)))
       (make-event (g-guards-fns-and-deps ',new-fns (w state)))

       (local (def-ruleset! apply-rewrites
                (acl2::ruleset ',(intern-in-package-of-symbol
                                  (concatenate 'string (symbol-name ev)
                                               "-EV-RULES")
                                  ev))))
       (correctness-lemmas ,ev)

       (make-event (g-correct-fns-and-deps ',new-fns ',ev (w state))))))


(defmacro make-g-world
  (fns ev
       &key (output
             '(:off (warning warning! observation prove acl2::proof-builder
                             acl2::history event proof-tree)
                    :summary-off (:other-than acl2::form)
                    :gag-mode nil)))
  `(with-output ,@output (make-event (make-g-world-fn ',fns ',ev
                                                      state))))

(defun make-geval-fn (geval new-fns state)
  (declare (xargs :stobjs state :mode :program))
  (b* ((world (w state))
       (new-fns (set-difference-eq
                 (collect-fn-deps new-fns world)
                 '(acl2::return-last)))
       (fns (union-eq new-fns
                      (strip-cars (table-alist 'gl-function-info world))
                      (prev-apply-fns world)))
       ;; (ap (incat geval (symbol-name geval) "-APPLY"))
       )
    `(encapsulate nil
       (logic)
       (local (table acl2::theory-invariant-table nil nil :clear))
       (local (in-theory nil))
       ; (local (set-default-hints nil))
       (set-bogus-mutual-recursion-ok t)
       (set-bogus-defun-hints-ok t)
       (set-ignore-ok t)
       (set-irrelevant-formals-ok t)
       (def-eval-g ,geval ,fns)
       ;; (local (def-ruleset! apply-rewrites
       ;;          ',(apply-rw-names ap fns world)))
       (correctness-lemmas ,geval))))


(defmacro make-geval
  (geval fns &key (output '(:off (warning warning! observation prove
                                          acl2::proof-builder
                                          acl2::history event proof-tree)
                                 :summary-off (:other-than acl2::form)
                                 :gag-mode nil)))
  `(with-output ,@output
                (make-event (make-geval-fn ',geval ',fns state))))



