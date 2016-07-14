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
(include-book "rws")
(include-book "clause-processors/generalize" :dir :system)
(include-book "misc/hons-help" :dir :system)
(include-book "gl-util")

(program)

(defun constant-syntax-p (name)
  ;; This is adapted from legal-variable-or-constant-namep, but only performs
  ;; the checks necessary to distinguish variable from constant.
  (or (eq name t) (eq name nil)
      (let ((s (symbol-name name)))
        (and (not (= (length s) 0))
             (eql (char s 0) #\*)
             (eql (char s (1- (length s))) #\*)))))


(defun gen-branch-fn-name (fn idx thenelse)
  (incat 'gl-fact::foo
         (symbol-package-name fn) "::" (symbol-name fn) "-"
         (symbol-name thenelse)
         "-" (acl2::nat-to-str idx)))

(defun gen-if-fn-name (fn idx)
  (incat 'gl-fact::foo
         (symbol-package-name fn) "::" (symbol-name fn) "-IF-"
         (acl2::nat-to-str idx)))

(defun gen-lambda-fn-name (fn idx)
  (incat 'gl-fact::foo
         (symbol-package-name fn) "::" (symbol-name fn) "-LAMBDA-"
         (acl2::nat-to-str idx)))

(mutual-recursion
 (defun calldepth-greaterp (term depth)
   (cond ((or (atom term)
              (eq (car term) 'quote))
          nil)
         ((zp depth) t)
         ((consp (car term))
          (or (calldepth-greaterp (caddar term) (1- depth))
              (calldepth-greaterp-lst (cdr term) (1- depth))))
         (t (calldepth-greaterp-lst (cdr term) (1- depth)))))
 (defun calldepth-greaterp-lst (lst depth)
   (if (atom lst)
       nil
     (or (calldepth-greaterp (car lst) depth)
         (calldepth-greaterp-lst (cdr lst) depth)))))


(defun correct-thmname (fn)
  (incat 'gl-thm::foo (symbol-name fn) "-CORRECT"))




(defun factor-add-fn (name vars defbody eqbody fnacc top world)
  (let* ((defun
           ;; NOTE: Keep this in syn with events-strip-fn-names, below.
           `(defun-nx ,name ,vars
              (declare (xargs :normalize nil)
                       (ignorable . ,vars))
              ,defbody))
         (thmname (correct-thmname name))
         (defname (and top
                       (consp eqbody)
                       (symbolp (car eqbody))
                       (or (cdr (assoc-eq (car eqbody)
                                          (table-alist 'preferred-defs world)))
                           (car eqbody))))
         (thm
          `(encapsulate nil
             (local (def-ruleset! factor-defs
                      '((:definition ,name))))
             (defthm ,thmname
               ,(if top
                    `(equal ,eqbody (,name . ,vars))
                  `(equal (,name . ,vars) ,eqbody))
               :hints (("Goal" :do-not '(preprocess simplify)
                        :clause-processor
                        (rw-cp clause
                               ,(if defname
                                    `(cons (rw-from-name ',defname (w state))
                                           (rws-from-ruleset factor-defs))
                                  `(rws-from-ruleset factor-defs))))
                       (use-by-computed-hint clause)
                       '(:clause-processor
                         (rw-cp clause (rws-from-ruleset factor-tmp-ruleset))
                         :do-not '(preprocess simplify))
                       '(:clause-processor (beta-reduce-cp clause))
                       '(:clause-processor
                         (rw-cp clause
                                (rws-from-ruleset-fn
                                 '((:definition acl2::return-last))
                                 (w state))))
                       '(:clause-processor (reduce-trivial-equality-cp clause))
;;                        '(:expand
;;                          (:lambdas
;;                           (:free (x) (hide x))
;;                           (:free (x y) (acl2::must-be-equal x y)))
;;                          :do-not '(preprocess)
;;                          :in-theory nil)
                       ))))
         (thm `(local ,thm))
         (ruleset (if top
                      `(local (add-to-ruleset! factor-ruleset '(,thmname)))
                    `(local (add-to-ruleset! factor-tmp-ruleset '(,thmname))))))
    (list* ruleset thm defun '(local (in-theory nil)) fnacc)))


(defun factor-maybe-push-if-branch (branch xbranch vars fn thenelse idx fnacc world)
  ;; Heuristic: If the branch has nesting depth of function calls > 1, then
  ;; define it as a new function.
  (if nil ;; (calldepth-greaterp branch 1)
      (b* ((fnname (gen-branch-fn-name fn idx thenelse))
           (fnacc
            (factor-add-fn fnname vars branch xbranch fnacc nil world))
           (call `(,fnname . ,vars)))
        (mv call fnacc))
    (mv branch fnacc)))


(mutual-recursion
 (defun fn-factor-term (x fn idx fnacc memo world)
   (cond
    ((atom x)
     (if (constant-syntax-p x)
         (mv x nil fnacc memo)
       (mv x (list x) fnacc memo)))
    ((eq (car x) 'quote)
     (mv x nil fnacc memo))
    (t (let ((lookup (hons-get x memo)))
         (cond
          (lookup
           (mv (cadr lookup) (cddr lookup) fnacc memo))

          ((eq (car x) 'return-last)
           (fn-factor-term (car (last x)) fn idx fnacc memo world))

          ((eq (car x) 'if)
           (b* ((xtest (cadr x))
                (xthen (caddr x))
                (xelse (cadddr x))
                (orp (equal xtest xthen))
                ((mv test testvars fnacc memo)
                 (fn-factor-term xtest fn (* 2 idx) fnacc memo world))
                ((mv then thenvars fnacc memo)
                 (if orp
                     (mv test testvars fnacc memo)
                   (fn-factor-term xthen fn (+ 2 (* 4 idx)) fnacc memo world)))
                ((mv else elsevars fnacc memo)
                 (fn-factor-term xelse fn
                                 (if orp (+ 1 (* 2 idx)) (+ 3 (* 4 idx)))
                                 fnacc memo world))
                ((mv then fnacc)
                 (if orp
                     (mv then fnacc)
                   (factor-maybe-push-if-branch
                    then xthen thenvars fn 'then idx fnacc world)))
                ((mv else fnacc)
                 (factor-maybe-push-if-branch
                  else xelse elsevars fn 'else idx fnacc world))
                (branchvars (if orp elsevars (union-eq thenvars elsevars)))
                (vars (union-eq testvars branchvars))
                ((when nil)
                 (b* ((term `(if ,test ,then ,else))
                      (memo (hons-acons x (cons term vars) memo)))
                   (mv term vars fnacc memo)))
                (fnname (gen-if-fn-name fn idx))
                (fnacc
                 (factor-add-fn fnname (cons 'test branchvars)
                                (if orp
                                    `(if test test ,else)
                                  `(if test ,then ,else))
                                (if orp
                                    `(if test test ,xelse)
                                  `(if test ,xthen ,xelse))
                                fnacc nil world))
                (call `(,fnname ,test . ,branchvars))
                (memo (hons-acons x (cons call vars) memo)))
             (mv call vars fnacc memo)))
          ((atom (car x))
           (b* (((mv args argsvars fnacc memo)
                 (fn-factor-termlist (cdr x) fn idx fnacc memo world))
                (newx (cons (car x) args))
                (memo (hons-acons x (cons newx argsvars) memo)))
             (mv newx argsvars fnacc memo)))
          (t
           (b* (((mv args argsvars fnacc memo)
                 (fn-factor-termlist (cdr x) fn (* 2 idx) fnacc memo world))
                (xbody (caddar x))
                ((mv body & fnacc memo)
                 (fn-factor-term xbody fn (+ 1 (* 2 idx)) fnacc memo world))
                (bindings (cadar x))
                ((when nil)
                 (b* ((term `((lambda ,bindings ,body) . ,args))
                      (memo (hons-acons x (cons term argsvars) memo)))
                   (mv term argsvars fnacc memo)))
                (fnname (gen-lambda-fn-name fn idx))
                (fnacc
                 (factor-add-fn fnname bindings body
                                ;; `((lambda ,bindings ,xbody) . ,bindings)
                                xbody
                                fnacc nil world))
                (call `(,fnname . ,args))
                (memo (hons-acons x (cons call argsvars) memo)))
             (mv call argsvars fnacc memo))))))))
 (defun fn-factor-termlist (x fn idx fnacc memo world)
   (if (endp x)
       (mv nil nil fnacc memo)
     (b* (((mv a avars fnacc memo)
           (fn-factor-term (car x) fn (* 2 idx) fnacc memo world))
          ((mv d dvars fnacc memo)
           (fn-factor-termlist (cdr x) fn (+ 1 (* 2 idx)) fnacc memo world)))
       (mv (cons a d) (union-eq dvars avars) fnacc memo)))))

(defun fn-factor-body (x fn events world)
  (let ((body (cond ((acl2::throw-nonexec-error-p x nil nil)
                     (car (last x)))
                    (t x))))
    (fn-factor-term (hons-copy body) fn 1 events nil world)))

(defun factored-fnname (fn)
  (incat 'gl-fact::foo
         (symbol-package-name fn) "::FACTORED-" (symbol-name fn)))

(defun events-strip-fn-names (events oldevents acc)
  (if (or (endp events) (equal events oldevents))
      acc
    (let ((event (car events)))
      (case-match event
        (('defun-nx name . &)
         (events-strip-fn-names (cdr events) oldevents
                                (cons name acc)))
        (& (events-strip-fn-names (cdr events) oldevents acc))))))




(defun factor-fn-clique (clique world events)
  (if (atom clique)
      events
    (b* ((fn (car clique))
         (body (norm-function-body fn world))
         (- (or body
                (er hard 'factor-fn-clique
                    "No body retrieved for ~x0~%" fn)))
         (vars (wgetprop fn 'formals))
         ((mv newbody & newevents memo)
          (fn-factor-body body fn events world))
         (- (flush-hons-get-hash-table-link memo))
         (name (factored-fnname fn))
         (newevents
          (factor-add-fn name vars newbody
                         `(,fn . ,vars) newevents t world))
         (fnlist (events-strip-fn-names newevents events nil))
         (events (cons `(table factored-fns ',fn ',fnlist) newevents)))
      (factor-fn-clique (cdr clique) world events))))




(defmacro factor-fn (fn)
  `(with-output
    :off (warning warning! observation prove acl2::proof-builder
                  acl2::history event  proof-tree)
    (make-event
     (let* ((world (w state))
            (clique (or (wgetprop ',fn 'recursivep) '(,fn))))
       `(progn (logic)
               ,@(reverse (factor-fn-clique clique world nil))
               (local (in-theory (disable* (:ruleset factor-ruleset)))))))))


