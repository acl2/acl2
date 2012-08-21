
(in-package "GL")

(include-book "g-if")
(include-book "g-primitives-help")
(include-book "symbolic-arithmetic-fns")
(include-book "eval-g-base")
;(include-book "tools/with-arith5-help" :dir :system)
(local (include-book "symbolic-arithmetic"))
(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix-logic"))
;(local (allow-arith5-help))

(local (defthm nth-open-when-constant-idx
         (implies (syntaxp (quotep n))
                  (equal (nth n x)
                         (if (zp n) (car x)
                           (nth (1- n) (cdr x)))))))


(local (defthm eval-g-base-atom
         (implies (and (not (consp x)) (gobjectp x))
                  (equal (eval-g-base x env) x))
         :hints (("goal" :expand ((:with eval-g-base (eval-g-base x env)))))
         :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))))


(program)

; what is the reason for this switch over to program mode?
; who did it?  ????? -- Boyer

(defun strip-correct-lemmas (alist)
  (if (atom alist)
      nil
    (append (strip-cars (cddr (car alist)))
            (strip-correct-lemmas (cdr alist)))))




(defun def-g-predicate-fn (fn cases
                              corr-hints guard-hints gobj-hints
                              encap gobj-encap guard-encap corr-encap formals)
  (declare (xargs :mode :program))
  (let* ((gfn (gl-fnsym fn))
         (booleanp-thmname
          (incat 'gl-thm::foo (symbol-package-name fn) "::"
                 (symbol-name fn) "-IS-BOOLEANP"))
         (x (car formals)))
    `(encapsulate nil
       (logic)
       (local (def-ruleset! g-correct-lemmas
                (strip-correct-lemmas (table-alist 'gl-function-info world))))
       (def-g-fn ,fn
         `(if (atom ,',x)
              (,',fn ,',x)
            (pattern-match ,',x
              ((g-concrete obj) (,',fn obj))
              ((g-ite test then else)
               (if (zp clk)
                   (g-apply ',',fn (list ,',x))
                 (g-if test
                       (,gfn then hyp clk)
                       (,gfn else hyp clk))))
              ((g-apply & &) (g-apply ',',fn (list ,',x)))
              ((g-var &) (g-apply ',',fn (list ,',x)))
              . ,',cases)))
       (local (in-theory (disable ,gfn)))
       (local (defthm ,booleanp-thmname
                (booleanp (,fn ,x))))
       (local (defthm tag-of-cons
                (equal (tag (cons a b)) a)
                :hints(("Goal" :in-theory (enable tag)))))
       (encapsulate nil
         (local (in-theory
                 (e/d** (minimal-theory
                         (:executable-counterpart-theory :here)
                         (:induction ,gfn)
                         ; (:ruleset g-gobjectp-lemmas)
                         (:ruleset gl-tag-rewrites)
                         (:ruleset gl-wrong-tag-rewrites)
                         gobjectp-tag-rw-to-types
                         gobjectp-ite-case
                         bfr-p-bfr-binary-and
                         bfr-p-bfr-binary-or
                         bfr-p-bfr-not
                         bfr-p-bfr-fix
;;                          bfr-p-of-bfr-and
;;                          bfr-p-of-bfr-or
                         gobjectp-boolean-case
                         gobjectp-g-if-marker
                         g-if-gobjectp-meta-correct
                         gobjectp-g-or-marker
                         g-or-gobjectp-meta-correct
                         hyp-fix-bfr-p
;                         bfr-and-is-bfr-and
;                         bfr-not-is-bfr-not
;                         bfr-or
                         gtests-wfp
                         gtests-g-test-marker
                         ; gobjectp-g-ite-branches
                         booleanp-gobjectp
                         gobjectp-mk-g-boolean
                         gobjectp-gobj-fix
                         gobjectp-cons
                         gobjectp-g-apply
                         ,booleanp-thmname)
                        ((immediate-force-modep)
                         (gobjectp)
                         (general-concretep)
                         (gobject-hierarchy)))))
         ,@encap
         ,@gobj-encap
         (def-gobjectp-thm ,fn
           :hints `(("goal"
                     :induct (,gfn ,',x hyp clk)
                     :expand ((,gfn ,',x hyp clk)))
                    . ,',gobj-hints)))
       (encapsulate nil
         (local (in-theory
                 (e/d** (minimal-theory
                         (:executable-counterpart-theory :here)
                         (:ruleset g-gobjectp-lemmas)
                         gobjectp-tag-rw-to-types
                         gobjectp-ite-case
;                         bfr-and-is-bfr-and
;                         bfr-not-is-bfr-not
;                         bfr-and-macro-exec-part
                         bfr-and-of-nil
                         bfr-or-of-t
                         bfr-p-bfr-binary-and
                         bfr-p-bfr-not
                         bfr-p-bfr-binary-or
                         bfr-p-bfr-fix
                         bfr-fix-when-bfr-p
                         gobjectp-gobj-ite-merge
                         gobjectp-mk-g-ite
                         gobjectp-boolean-case
                         gobj-fix-when-gobjectp
                         ; gobjectp-g-ite-branches
;                         bfr-or
                         gobjectp-g-test-marker
                         gtests-g-test-marker
                         natp
                         gtestsp-gtests
                         gtests-wfp
                         hyp-fix-bfr-p
                         gobjectp-g-branch-marker
                         booleanp-gobjectp
                         ,booleanp-thmname
                         ;; (:ruleset g-guard-lemmas)
                         bfr-p-g-hyp-marker)
                        ((immediate-force-modep)
                         (force)
                         (gobjectp)
                         (gobject-hierarchy)
                         (general-concretep)
;;                          (assume-true-under-hyp)
;;                          (assume-false-under-hyp)
                         ))))
         ,@encap
         ,@guard-encap
         (verify-g-guards ,fn
                          :hints ',guard-hints))
       (encapsulate nil
         (local (in-theory (e/d* (gobjectp-tag-rw-to-types
                                  gobjectp-gobj-fix
                                  ; g-eval-non-consp
                                  booleanp-compound-recognizer
                                  eval-g-base-g-apply
                                  (:type-prescription bfr-eval)
                                  (:type-prescription
                                   components-to-number-fn)
                                  gobjectp-cons gobjectp-gobj-fix
                                  apply-base
                                  nth-open-when-constant-idx
                                  eval-g-base-cons
                                  geval-g-if-marker-eval-g-base
                                  geval-g-or-marker-eval-g-base
                                  g-if-geval-meta-correct-eval-g-base
                                  g-or-geval-meta-correct-eval-g-base
                                  eval-g-base-atom
                                  booleanp-gobjectp)
                                 (bfr-p-of-boolean
                                  general-number-components-ev
                                  (:type-prescription booleanp)
                                  
                                  bfr-eval-booleanp
                                  general-boolean-value-correct
                                  bool-cond-itep-eval
                                  eval-g-base-alt-def
                                  ; eval-g-non-keyword-cons
                                  eval-concrete-gobjectp)
                                 ())))
         ,@encap
         ,@corr-encap
         (def-g-correct-thm ,fn eval-g-base
           :hints `(("goal" :in-theory (enable (:induction ,gfn))
                     :induct (,gfn ,',x hyp clk)
                     :expand ((,gfn ,',x hyp clk)))
                    (and stable-under-simplificationp
                         '(:expand ((:with eval-g-base (eval-g-base ,',x env))
                                    (:with eval-g-base (eval-g-base nil env))
                                    (:with eval-g-base (eval-g-base t env)))))
                    . ,',corr-hints))))))


(defmacro def-g-predicate
  (fn cases &key 
      corr-hints guard-hints gobj-hints encap
      gobj-encap guard-encap corr-encap (formals '(x)))
  (def-g-predicate-fn 
    fn cases corr-hints guard-hints gobj-hints
    encap gobj-encap guard-encap corr-encap formals))

(logic)



(def-g-predicate booleanp
  (((g-boolean &) t)
   (& nil)))

(def-g-predicate not
  (((g-boolean bdd) (mk-g-boolean (bfr-not bdd)))
   (& nil))
  :formals (p))

(def-g-predicate symbolp
  (((g-boolean &) t)
   (& nil)))

(def-g-predicate acl2-numberp
  (((g-number &) t)
   (& nil)))

(def-g-predicate stringp ((& nil)))

(def-g-predicate characterp ((& nil)))

(def-g-predicate consp
  (((g-boolean &) nil)
   ((g-number &) nil)
   (& t)))


         
(encapsulate nil
  (local (defthm g-number-p-by-tag
           (implies (and (gobjectp x)
                         (equal (tag x) :g-number))
                    (g-number-p x))))
  (def-g-predicate integerp
    (((g-number num)
      (mv-let (arn ard ain aid)
        (break-g-number num)
        (declare (ignore arn))
        (if (equal ard '(t))
            (mk-g-boolean
             (bfr-or (=-ss ain nil)
                   (=-uu aid nil)))
          (g-apply 'integerp (list x)))))
     (& nil))
    :encap ((local (in-theory (enable bfr-p-bfr-binary-or
                                      bfr-p-=-ss
                                      bfr-p-=-uu
                                      gobjectp-number-case
                                      gobjectp-bfr-listp-break-g-number
                                      g-number-p-by-tag
                                      bfr-eval-bfr-binary-or
                                      bfr-or-of-t
                                      =-uu-correct
                                      =-ss-correct
                                      (:type-prescription break-g-number)))))
    :guard-encap ((local (bfr-reasoning-mode t))
                  (local (add-bfr-pats (=-uu . &) (=-ss . &))))
    :corr-hints ((and stable-under-simplificationp
                      (append '(:in-theory (enable components-to-number-alt-def))
                              (flag::expand-calls-computed-hint
                               clause '(eval-g-base)))))))


(encapsulate nil
  (local (defthm g-number-p-by-tag
           (implies (and (gobjectp x)
                         (equal (tag x) :g-number))
                    (g-number-p x))))
  (def-g-predicate rationalp
    (((g-number num)
      (mv-let (arn ard ain aid)
        (break-g-number num)
        (declare (ignore arn ard))
        (mk-g-boolean
         (bfr-or (=-ss ain nil)
               (=-uu aid nil)))))
     (& nil))
    :encap ((local (in-theory (enable bfr-p-bfr-binary-or
                                      bfr-p-=-ss
                                      bfr-p-=-uu
                                      gobjectp-number-case
                                      gobjectp-bfr-listp-break-g-number
                                      g-number-p-by-tag
                                      bfr-eval-bfr-binary-or
                                      =-uu-correct
                                      =-ss-correct
                                      bfr-or-of-t
                                      (:type-prescription break-g-number)))))
    :guard-encap ((local (bfr-reasoning-mode t)))
    :corr-hints ((and stable-under-simplificationp
                      (append '(:in-theory (enable components-to-number-alt-def))
                              (flag::expand-calls-computed-hint
                               clause '(eval-g-base)))))))








