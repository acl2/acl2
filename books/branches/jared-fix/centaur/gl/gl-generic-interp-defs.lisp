
(in-package "GL")


(include-book "ite-merge")
(include-book "gtests")
(include-book "glcp-templates")
(include-book "shape-spec-defs")
(include-book "symbolic-arithmetic-fns")
(include-book "centaur/misc/rewrite-rule" :dir :system)

(defmacro glcp-value (res)
  `(mv nil obligs ,res state))

;; (defmacro glcp-er-let* (alist body)
;;   (declare (xargs :guard (and (acl2::doubleton-list-p alist)
;;                               (symbol-alistp alist))))
;;   (if (null alist)
;;       `(check-vars-not-free
;;         (glcp-er-let*-use-nowhere-else)
;;         ,body)
;;     `(mv-let (glcp-er-let*-use-nowhere-else
;;               obligs ,(caar alist) state)
;;        ,(cadar alist)
;;        (if glcp-er-let*-use-nowhere-else
;;            (mv glcp-er-let*-use-nowhere-else
;;                obligs ,(caar alist) state)
;;          (glcp-er-let* ,(cdr alist) ,body)))))

(defmacro patbind-glcp-er (args bindings expr)
  (declare (xargs :guard (and (consp args) (eq (cdr args) nil))))
  `(b* (((mv patbind-glcp-er-error obligs ,(car args) state)
         ,(car bindings))
        ((when patbind-glcp-er-error)
         (mv patbind-glcp-er-error obligs nil state)))
     (check-vars-not-free
      (patbind-glcp-er-error) ,expr)))

(verify-termination acl2::evisc-tuple)
(verify-guards acl2::evisc-tuple)

(defun glcp-case-split-report (test then else)
  (declare (xargs :guard t)
           (ignore test then else))
  nil)
                  

(defmacro glcp-if (test then else &key report)
  `(b* ((gtests (gtests ,test hyp))
        (then-hyp (hf (bfr-or (gtests-unknown gtests)
                               (gtests-nonnil gtests))))
        (else-hyp (hf (bfr-or (gtests-unknown gtests)
                               (bfr-not (gtests-nonnil gtests)))))
        (- (and then-hyp else-hyp ,report))
        ((glcp-er then)
         (if then-hyp
             (let ((hyp (bfr-and hyp then-hyp)))
               (declare (ignorable hyp))
               ,then)
           (glcp-value nil)))
        ((glcp-er else)
         (if else-hyp
             (let ((hyp (bfr-and hyp else-hyp)))
               (declare (ignorable hyp))
               ,else)
           (glcp-value nil)))
        (merge (gobj-ite-merge (gtests-nonnil gtests) then else
                               (bfr-and (bfr-not (gtests-unknown gtests))
                                         hyp))))
     (if (hf (gtests-unknown gtests))
         (glcp-value
          (mk-g-ite (mk-g-boolean (gtests-unknown gtests))
                    (mk-g-ite (gtests-obj gtests) then else)
                    merge))
       (glcp-value merge))))


(defmacro glcp-or (test else)
  `(b* ((test ,test)
        (gtests (gtests test hyp))
        (else-hyp (hf (bfr-or (gtests-unknown gtests)
                               (bfr-not (gtests-nonnil gtests)))))
        ((glcp-er else)
         (if else-hyp
             (let ((hyp (bfr-and hyp else-hyp)))
               (declare (ignorable hyp))
               ,else)
           (glcp-value nil)))
        (merge (gobj-ite-merge (gtests-nonnil gtests) test else
                               (bfr-and (bfr-not (gtests-unknown gtests))
                                         hyp))))
     (if (hf (gtests-unknown gtests))
         (glcp-value
          (mk-g-ite (mk-g-boolean (gtests-unknown gtests))
                    (mk-g-ite (gtests-obj gtests) test else)
                    merge))
       (glcp-value merge))))

(defun gl-cp-hint (x)
  (declare (ignore x))
  t)

(in-theory (disable gl-cp-hint (:type-prescription gl-cp-hint) (gl-cp-hint)))

(defun gl-hide (x)
  (declare (xargs :guard t))
  x)

(def-eval-g glcp-generic-geval
  (
   ;; used in shape specs
   logapp int-set-sign maybe-integer
          cons car cdr consp if not equal nth len iff
          shape-spec-slice-to-env
          ss-append-envs
          shape-spec-obj-in-range-iff
          shape-spec-obj-in-range
          shape-spec-env-slice
          shape-spec-iff-env-slice

          if gl-cp-hint shape-spec-obj-in-range return-last use-by-hint equal
      acl2::typespec-check implies iff not cons gl-aside gl-ignore gl-error gl-hide
      BINARY-*
      BINARY-+
      PKG-WITNESS
;   UNARY-/
      UNARY--
      COMPLEX-RATIONALP
;   BAD-ATOM<=
      ACL2-NUMBERP
      SYMBOL-PACKAGE-NAME
      INTERN-IN-PACKAGE-OF-SYMBOL
      CODE-CHAR
;   DENOMINATOR
      CDR
;   COMPLEX
      CAR
      CONSP
      SYMBOL-NAME
      CHAR-CODE
      IMAGPART
      SYMBOLP
      REALPART
;   NUMERATOR
      EQUAL
      STRINGP
      RATIONALP
      CONS
      INTEGERP
      CHARACTERP
      <
      COERCE
      booleanp
      logbitp
      binary-logand
      binary-logior
      lognot
      ash
      integer-length
      floor
      mod
      truncate
      rem
      acl2::boolfix

      ;; these are from the constant *expandable-boot-strap-non-rec-fns*.
      NOT IMPLIES
      EQ ATOM EQL = /= NULL ENDP ZEROP ;; SYNP
      PLUSP MINUSP LISTP ;; RETURN-LAST causes guard violation
      ;; FORCE CASE-SPLIT
      ;; DOUBLE-REWRITE
      
      ;; used for shape specs
      acl2::logapp int-set-sign maybe-integer
      ))

(in-theory (disable glcp-generic-geval))

(acl2::def-meta-extract glcp-generic-geval-ev glcp-generic-geval-ev-lst)

(encapsulate
  (((glcp-generic-run-gified * * * * state)
    => (mv * *)
    :formals (fn actuals hyp clk state)
    :guard (and (symbolp fn)
                (gobj-listp actuals)
                (natp clk)))
   ;; ((glcp-generic-geval-ev * *) => *)
   ;; ((glcp-generic-geval-ev-lst * *) => *)
   ;; ((glcp-generic-geval * *) => *)
   )

  ;; (local (def-eval-g glcp-generic-geval
  ;;          (if gl-cp-hint shape-spec-obj-in-range return-last use-by-hint equal
  ;;              acl2::typespec-check implies iff not cons gl-aside gl-ignore gl-error)))

  ;; (local (defun glcp-generic-geval (x env)
  ;;          (generic-geval x env)))

  (local (defun glcp-generic-run-gified (fn actuals hyp clk state)
           (declare (xargs :stobjs state
                           :guard (and (symbolp fn)
                                       (natp clk)))
                    (ignorable fn actuals hyp clk state))
           (mv nil nil)))

  ;; (local (acl2::defevaluator-fast
  ;;         glcp-generic-ev glcp-generic-ev-lst
  ;;         ((if a b c)
  ;;          (gl-cp-hint x)
  ;;          (shape-spec-obj-in-range a b)
  ;;          (return-last fn arg1 arg2)
  ;;          (use-by-hint x)
  ;;          (equal a b)
  ;;          (acl2::typespec-check ts x)
  ;;          (implies a b)
  ;;          (iff a b)
  ;;          (not x)
  ;;          (cons a b)
  ;;          (gl-aside x)
  ;;          (gl-ignore x)
  ;;          (gl-error x))
  ;;         :namedp t))

  (defthm glcp-generic-run-gified-correct
    (implies (and (bfr-eval hyp (car env))
                  (gobj-listp actuals)
                  (mv-nth 0 (glcp-generic-run-gified fn actuals hyp
                                                     clk state)))
             (equal (glcp-generic-geval
                     (mv-nth 1 (glcp-generic-run-gified
                                fn actuals hyp clk state))
                     env)
                    (glcp-generic-geval-ev
                     (cons fn
                           (acl2::kwote-lst
                            (glcp-generic-geval actuals env))) nil))))

  ;; (defthm true-listp-glcp-generic-run-gified
  ;;   (true-listp (glcp-generic-run-gified fn actuals hyp clk state)))

  ;; (make-event
  ;;  `(progn
  ;;     . ,(acl2::defevaluator-fast-form/defthms-named
  ;;         'glcp-generic-geval-ev 'glcp-generic-geval-ev-lst
  ;;         '((if a b c)
  ;;           (gl-cp-hint x)
  ;;           (shape-spec-obj-in-range a b)
  ;;           (return-last fn arg1 arg2)
  ;;           (use-by-hint x)
  ;;           (equal a b)
  ;;           (acl2::typespec-check ts x)
  ;;           (implies a b)
  ;;           (iff a b)
  ;;           (not x)
  ;;           (cons a b)
  ;;           (gl-aside x)
  ;;           (gl-ignore x)
  ;;           (gl-error x)))))

  )

(defun general-concrete-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (general-concretep (car x))
         (general-concrete-listp (cdr x)))))

(defun general-concrete-obj-list (x)
  (declare (xargs :guard (general-concrete-listp x)))
  (if (atom x)
      nil
    (cons (general-concrete-obj (car x))
          (general-concrete-obj-list (cdr x)))))


(mutual-recursion
 (defun sublis-into-term (x alist)
   (declare (xargs :guard t))
   (cond ((null x) nil)
         ((atom x)
          (let ((look (hons-assoc-equal x alist)))
            (if look (acl2::kwote (cdr look)) x)))
         ((eq (car x) 'quote) x)
         (t (cons (car x) (sublis-into-list (cdr x) alist)))))
 (defun sublis-into-list (x alist)
   (declare (xargs :guard t))
   (if (atom x)
       nil
     (cons (sublis-into-term (car x) alist)
           (sublis-into-list (cdr x) alist)))))



(defund gl-aside-wormhole (term alist)
  (declare (xargs :guard t))
  (wormhole 'glcp-interp-gl-aside
            '(lambda (whs) whs)
            nil
            `(prog2$ ,(sublis-into-term
                       term alist)
                     (value :q))
            :ld-prompt nil
            :ld-pre-eval-print nil
            :ld-post-eval-print nil
            :ld-verbose nil))

(defun glcp-interp-error-fn (msg state)
  (declare (xargs :guard t :stobjs state))
  (mv msg nil nil state))

(defmacro glcp-interp-error (msg)
  (declare (xargs :guard t))
  `(glcp-interp-error-fn ,msg state))

(add-macro-alias glcp-interp-error glcp-interp-error-fn)

(defthmd acl2-count-last-cdr-when-cadr-hack
  (implies (< 1 (len x))
           (< (acl2-count (car (last x)))
              (+ 1 (acl2-count (cdr x)))))
  :rule-classes (:rewrite :linear))

(cutil::defaggregate glcp-config
  ((abort-unknown booleanp :default t)
   (abort-ctrex booleanp :default t)
   (exec-ctrex booleanp :default t)
   (abort-vacuous booleanp :default t)
   (nexamples natp :rule-classes :type-prescription :default 3)
   (hyp-clk natp :rule-classes :type-prescription :default 1000000)
   (concl-clk natp :rule-classes :type-prescription :default 1000000)
   (clause-proc-name symbolp :rule-classes :type-prescription)
   (overrides) ;;  acl2::interp-defs-alistp but might be too expensive to check the guards in clause processors
   run-before
   run-after
   case-split-override)
  :tag :glcp-config)


(acl2::def-b*-binder
 rewrite-rule
 #!acl2
 (cutil::da-patbind-fn 'rewrite-rule
                       #!GL '(rune hyps lhs rhs equiv subclass heuristic-info)
                       args forms rest-expr))
;; Note: careful with this; variable names that are imported symbols yield
;; names in the other package.  In particular, since we import single-letter
;; variables from the ACL2 package, use multiletter variables.

;; used for measure
(defun pos-fix (x)
  (if (posp x) x 1))



;; x is a concrete object
(defund glcp-unify-concrete (pat x alist)
  (declare (xargs :guard (pseudo-termp pat)))
  (b* (((when (eq pat nil))
        (if (eq x nil)
            (mv t alist)
          (mv nil nil)))
       ((when (atom pat))
        (let ((pair (hons-assoc-equal pat alist)))
          (if pair
              (if (and (general-concretep (cdr pair))
                       (equal (general-concrete-obj (cdr pair)) x))
                  (mv t alist)
                (mv nil nil))
            (mv t (cons (cons pat (g-concrete-quote x)) alist)))))
       ((when (eq (car pat) 'quote))
        (if (equal (cadr pat) x)
            (mv t alist)
          (mv nil nil)))
       ((when (and (eq (car pat) 'cons)
                   (int= (len pat) 3)))
        (if (consp x)
            (b* (((mv car-ok alist)
                  (glcp-unify-concrete (second pat) (car x) alist))
                 ((unless car-ok) (mv nil nil)))
              (glcp-unify-concrete (third pat) (cdr x) alist))
          (mv nil nil))))
    ;; ((and (eq (car pat) 'binary-+)
    ;;       (int= (len pat) 3))
    ;;  (cond ((not (acl2-numberp x))
    ;;         (mv nil nil))
    ;;        ((quotep (second pat))
    ;;         (let ((num (unquote (second pat))))
    ;;           (if (acl2-numberp num)
    ;;               (glcp-unify-concrete (third pat) (- x num) alist)
    ;;             (mv nil nil))))
    ;;        ((quotep (third pat))
    ;;         (let ((num (unquote (third pat))))
    ;;           (if (acl2-numberp num)
    ;;               (glcp-unify-concrete (second pat) (- x num) alist)
    ;;             (mv nil nil))))
    ;;        (t (mv nil nil))))
    (mv nil nil)))


(mutual-recursion
 (defun glcp-unify-term/gobj (pat x alist)
   (declare (xargs :guard (pseudo-termp pat)
                   :guard-debug t))
   (b* (((when (eq pat nil))
         (if (eq x nil) (mv t alist) (mv nil nil)))
        ((when (atom pat))
         (let ((pair (hons-assoc-equal pat alist)))
           (if pair
               (if (equal x (cdr pair))
                   (mv t alist)
                 (mv nil nil))
             (mv t (cons (cons pat x) alist)))))
        ((when (eq (car pat) 'quote))
         (if (and (general-concretep x)
                  (equal (general-concrete-obj x) (cadr pat)))
             (mv t alist)
           (mv nil nil)))
        ((when (atom x))
         (glcp-unify-concrete pat x alist))
        ((when (eq (tag x) :g-concrete))
         (glcp-unify-concrete pat (g-concrete->obj x) alist))
        ((when (or (eq (tag x) :g-boolean)
                   (eq (tag x) :g-number)
                   (eq (tag x) :g-ite)
                   (eq (tag x) :g-var)))
         (mv nil nil))
        ((unless (eq (tag x) :g-apply))
         ;; cons case
         (if (and (eq (car pat) 'cons)
                  (int= (len pat) 3))
             (b* (((mv ok alist) (glcp-unify-term/gobj (cadr pat) (car x) alist))
                  ((unless ok) (mv nil nil)))
               (glcp-unify-term/gobj (caddr pat) (cdr x) alist))
           (mv nil nil)))
        ;; g-apply case remains
        ((when (equal (g-apply->fn x) (car pat)))
         (glcp-unify-term/gobj-list (cdr pat) (g-apply->args x) alist)))
     (mv nil nil)))
 (defun glcp-unify-term/gobj-list (pat x alist)
   (declare (xargs :guard (pseudo-term-listp pat)))
   (b* (((when (atom pat))
         (if (eq x nil) (mv t alist) (mv nil nil)))
        ((when (atom x)) (mv nil nil))
        ((when (g-keyword-symbolp (tag x)))
         ;;for now at least
         (mv nil nil))
        ((mv ok alist)
         (glcp-unify-term/gobj (car pat) (car x) alist))
        ((unless ok) (mv nil nil)))
     (glcp-unify-term/gobj-list (cdr pat) (cdr x) alist))))

(in-theory (disable glcp-unify-term/gobj
                    glcp-unify-term/gobj-list))

(defund glcp-relieve-hyp-synp (hyp bindings state)
  (declare (xargs :stobjs state
                  :guard (and (consp hyp)
                              (pseudo-termp hyp))))
  (b* ((args (cdr hyp))
       ((unless #!acl2 (and 
                        ;; check that synp is defined as expected
                        (fn-check-def 'synp state '(vars form term) ''t)
                        ;; check that all three args are quoted
                        (equal (len args) 3)
                        (quote-listp args)))
        (mv (acl2::msg "Bad synp hyp: ~x0~%" hyp) nil nil))
       (hyp-form (second (second args)))
       ((unless (and (consp hyp-form) (eq (car hyp-form) 'syntaxp)))
        (mv (acl2::msg "Bind-free isn't supported yet: ~x0~%" hyp) nil nil))
       (form (second ;; unquote
              (third args)))
       ((unless (and (pseudo-termp form)
                     (symbol-alistp bindings)))
        (mv (acl2::msg "ill-formed syntaxp form: ~x0~%" form) nil nil))
       ((mv err val) (acl2::magic-ev form bindings state t t))
       ((when err)
        (mv (acl2::msg "synp error: ~@0~%" (if (eq err t) "error" err)) nil nil)))
    (mv nil val bindings)))


(defund glcp-interp-args-split-ite-cond (test args)
  (declare (xargs :guard t))
  (b* (((when (atom args)) (mv nil nil))
       (obj (car args))
       ((mv rest-then rest-else)
        (glcp-interp-args-split-ite-cond test (cdr args)))
       ((when (and (consp obj)
                   (eq (tag obj) :g-ite)
                   (hons-equal (g-ite->test obj) test)))
        (mv (gl-cons (g-ite->then obj) rest-then)
            (gl-cons (g-ite->else obj) rest-else))))
    (mv (gl-cons obj rest-then)
        (gl-cons obj rest-else))))
    

(defund glcp-interp-args-split-ite (args)
  (declare (xargs :guard t))
  (b* (((when (atom args))
        (mv nil nil nil nil))
       (obj (car args))
       ((when (and (consp obj)
                   (eq (tag obj) :g-ite)))
        (b* ((test (g-ite->test obj))
             (then (g-ite->then obj))
             (else (g-ite->else obj))
             ((mv then-rest else-rest)
              (glcp-interp-args-split-ite-cond test (cdr args))))
          (mv t test (gl-cons then then-rest) (gl-cons else else-rest))))
       ((mv has-if test then else)
        (glcp-interp-args-split-ite (cdr args)))
       ((unless has-if)
        (mv nil nil nil nil)))
    (mv has-if test (gl-cons obj then) (gl-cons obj else))))

(defund g-ite-depth (x)
  (declare (xargs :guard t))
  (if (mbe :logic (eq (tag x) :g-ite)
           :exec (and (consp x)
                      (eq (tag x) :g-ite)))
      (+ 1 (max (g-ite-depth (g-ite->then x))
                (g-ite-depth (g-ite->else x))))
    0))

(defthm posp-g-ite-depth
  (implies (equal (tag x) :g-ite)
           (posp (g-ite-depth x)))
  :hints(("Goal" :in-theory (enable g-ite-depth)))
  :rule-classes :type-prescription)


(defthm g-ite-depth-of-g-ite->then
  (implies (eq (tag x) :g-ite)
           (< (g-ite-depth (g-ite->then x))
              (g-ite-depth x)))
  :hints(("Goal" :expand ((g-ite-depth x))))
  :rule-classes :linear)

(defthm g-ite-depth-of-g-ite->else
  (implies (eq (tag x) :g-ite)
           (< (g-ite-depth (g-ite->else x))
              (g-ite-depth x)))
  :hints(("Goal" :expand ((g-ite-depth x))))
  :rule-classes :linear)

(defund g-ite-depth-sum (x)
  (declare (xargs :guard t))
  (if (atom x)
      0
    (+ (g-ite-depth (car x))
       (g-ite-depth-sum (cdr x)))))

(defthm g-ite-depth-of-g-concrete
  (equal (g-ite-depth (g-concrete x)) 0)
  :hints(("Goal" :in-theory (enable g-ite-depth))))

(defthm g-ite-depth-sum-of-glcp-interp-args-split-ite-cond-0
  (<= (g-ite-depth-sum (mv-nth 0 (glcp-interp-args-split-ite-cond test args)))
      (g-ite-depth-sum args))
  :hints(("Goal" :in-theory (enable glcp-interp-args-split-ite-cond
                                    g-ite-depth-sum gl-cons)))
  :rule-classes :linear)

(defthm g-ite-depth-sum-of-glcp-interp-args-split-ite-cond-1
  (<= (g-ite-depth-sum (mv-nth 1 (glcp-interp-args-split-ite-cond test args)))
      (g-ite-depth-sum args))
  :hints(("Goal" :in-theory (enable glcp-interp-args-split-ite-cond
                                    g-ite-depth-sum gl-cons)))
  :rule-classes :linear)

(defthm g-ite-depth-sum-of-glcp-interp-args-split-ite-then
  (b* (((mv has-ite ?test ?then ?else)
        (glcp-interp-args-split-ite args)))
    (implies has-ite
             (< (g-ite-depth-sum then) (g-ite-depth-sum args))))
  :hints(("Goal" :in-theory (enable glcp-interp-args-split-ite
                                    g-ite-depth-sum gl-cons)))
  :rule-classes :linear)

(defthm g-ite-depth-sum-of-glcp-interp-args-split-ite-else
  (b* (((mv has-ite ?test ?then ?else)
        (glcp-interp-args-split-ite args)))
    (implies has-ite
             (< (g-ite-depth-sum else) (g-ite-depth-sum args))))
  :hints(("Goal" :in-theory (enable glcp-interp-args-split-ite
                                    g-ite-depth-sum gl-cons)))
  :rule-classes :linear)


(mutual-recursion
 (defun gl-term-to-apply-obj (x alist)
   (declare (xargs :guard (pseudo-termp x)
                   :verify-guards nil))
   (b* (((when (not x)) nil)
        ((when (atom x)) (cdr (hons-assoc-equal x alist)))
        ((when (eq (car x) 'quote)) (g-concrete-quote (cadr x)))
        (args (gl-termlist-to-apply-obj-list (cdr x) alist))
        (fn (car x))
        ((when (consp fn))
         (b* ((formals (cadr fn))
              (body (caddr fn)))
           (gl-term-to-apply-obj body (pairlis$ formals args))))
        ((when (eq fn 'if))
         (g-ite (first args) (second args) (third args)))
        ((when (eq fn 'cons))
         (gl-cons (first args) (second args))))
     (g-apply fn args)))
 (defun gl-termlist-to-apply-obj-list (x alist)
   (declare (xargs :guard (pseudo-term-listp x)))
   (if (atom x)
       nil
     (gl-cons (gl-term-to-apply-obj (car x) alist)
              (gl-termlist-to-apply-obj-list (cdr x) alist)))))

(in-theory (disable gl-term-to-apply-obj
                    gl-termlist-to-apply-obj-list))


(flag::make-flag gl-term-to-apply-obj-flag gl-term-to-apply-obj)

(defthm-gl-term-to-apply-obj-flag
  (defthm true-listp-gl-termlist-to-apply-obj-list
    (true-listp (gl-termlist-to-apply-obj-list x alist))
    :hints ('(:expand ((gl-termlist-to-apply-obj-list x alist))))
    :rule-classes :type-prescription
    :flag gl-termlist-to-apply-obj-list)
  :skip-others t)

(verify-guards gl-term-to-apply-obj)
         



(defconst *glcp-generic-template-subst*
  `((interp-term . glcp-generic-interp-term)
    (interp-list . glcp-generic-interp-list)
    (interp-if . glcp-generic-interp-if)
    (interp-fncall-ifs . glcp-generic-interp-fncall-ifs)
    (interp-fncall . glcp-generic-interp-fncall)
    (rewrite-fncall . glcp-generic-rewrite-fncall)
    (rewrite-fncall-apply-rules . glcp-generic-rewrite-fncall-apply-rules)
    (rewrite-fncall-apply-rule . glcp-generic-rewrite-fncall-apply-rule)
    (relieve-hyps . glcp-generic-relieve-hyps)
    (relieve-hyp . glcp-generic-relieve-hyp)
    (run-cases . glcp-generic-run-cases)
    (run-parametrized . glcp-generic-run-parametrized)
    (clause-proc . glcp-generic)
    (clause-proc-name . (glcp-generic-clause-proc-name))
    (run-gified . glcp-generic-run-gified)))


(make-event
 (sublis *glcp-generic-template-subst*
         *glcp-interp-template*))
               
  
#||
;; redundant
(mutual-recursion
 (defun glcp-generic-interp-term
   (x alist pathcond clk obligs config state)
   (declare (xargs
             :measure (list clk 20 (acl2-count x) 20)
             :well-founded-relation acl2::nat-list-<
             :hints (("goal"
                      :in-theory (e/d** ((:rules-of-class :executable-counterpart :here)
                                         acl2::open-nat-list-<
                                         acl2-count len nfix fix
                                         car-cons cdr-cons commutativity-of-+
                                         unicity-of-0 null atom
                                         eq acl2-count-last-cdr-when-cadr-hack
                                         car-cdr-elim natp-compound-recognizer
                                         acl2::zp-compound-recognizer
                                         acl2::posp-compound-recognizer
                                         pos-fix
                                         g-ite-depth-sum-of-glcp-interp-args-split-ite-then
                                         g-ite-depth-sum-of-glcp-interp-args-split-ite-else
                                         (:type-prescription acl2-count)))))
             :verify-guards nil
             :guard (and (natp clk)
                         (pseudo-termp x)
                         (acl2::interp-defs-alistp obligs)
                         (glcp-config-p config)
                         (acl2::interp-defs-alistp (glcp-config->overrides config)))
             :stobjs state))
   (b* (((when (zp clk))
         (glcp-interp-error "The clock ran out.~%"))
        ((when (null x)) (glcp-value nil))
        ((when (symbolp x))
         (glcp-value (cdr (hons-assoc-equal x alist))))
        ((when (atom x))
         (glcp-interp-error
          (acl2::msg "GLCP:  The unquoted atom ~x0 is not a term~%"
                     x)))
        ((when (eq (car x) 'quote))
         (glcp-value (g-concrete-quote (car (cdr x)))))
        ((when (consp (car x)))
         (b*
           (((glcp-er actuals)
             (glcp-generic-interp-list (cdr x)
                                       alist pathcond clk obligs config state))
            (formals (car (cdar x)))
            (body (car (cdr (cdar x)))))
           (if (and (mbt (and (equal (len actuals) (len formals))
                              (symbol-listp formals)))
                    (acl2::fast-no-duplicatesp formals)
                    (not (member-eq nil formals)))
               (glcp-generic-interp-term body (pairlis$ formals actuals)
                                         pathcond clk obligs config state)
             (glcp-interp-error (acl2::msg "Badly formed lambda application: ~x0~%"
                                           x)))))
        ((when (eq (car x) 'if))
         (let ((test (car (cdr x)))
               (tbr (car (cdr (cdr x))))
               (fbr (car (cdr (cdr (cdr x))))))
           (glcp-generic-interp-if test tbr fbr alist pathcond clk obligs
                                   config state)))
        
        ((when (eq (car x) 'gl-aside))
         (if (eql (len x) 2)
             (prog2$ (gl-aside-wormhole (cadr x) alist)
                     (glcp-value nil))
           (glcp-interp-error "Error: wrong number of args to GL-ASIDE~%")))
        ((when (eq (car x) 'gl-ignore))
         (glcp-value nil))
        ((when (eq (car x) 'gl-hide))
         (glcp-value (gl-term-to-apply-obj x alist)))
        ((when (eq (car x) 'gl-error))
         (if (eql (len x) 2)
             (b* (((glcp-er result)
                   (glcp-generic-interp-term (cadr x)
                                             alist pathcond clk obligs config state))
                  (state (f-put-global 'gl-error-result
                                       result state)))
               (glcp-interp-error
                (acl2::msg
                 "Error: GL-ERROR call encountered.  Data associated with the ~
                      error is accessible using (@ ~x0).~%"
                 'gl-error-result)))
           (glcp-interp-error "Error: wrong number of args to GL-ERROR~%")))
        ((when (eq (car x) 'return-last))
         (if (eql (len x) 4)
             (if (equal (cadr x) ''acl2::time$1-raw)
                 (b* (((mv err & time$-args state)
                       (glcp-generic-interp-term (caddr x)
                                                 alist pathcond clk obligs config state)))
                   (mbe :logic (glcp-generic-interp-term
                                (car (last x)) alist pathcond clk obligs config state)
                        :exec
                        (if (and (not err)
                                 (general-concretep time$-args))
                            (return-last
                             'acl2::time$1-raw
                             (general-concrete-obj time$-args)
                             (glcp-generic-interp-term (car (last x))
                                                       alist pathcond clk obligs config state))
                          (time$
                           (glcp-generic-interp-term (car (last x))
                                                     alist pathcond clk obligs config state)))))
               (glcp-generic-interp-term (car (last x))
                                         alist pathcond clk obligs config state))
           (glcp-interp-error "Error: wrong number of args to RETURN-LAST~%")))
        (fn (car x))
        ;; outside-in rewriting?
        ((glcp-er actuals)
         (glcp-generic-interp-list (cdr x)
                                   alist pathcond clk obligs config state)))
     (glcp-generic-interp-fncall-ifs fn actuals x pathcond clk obligs config
                                     state)))

 (defun glcp-generic-interp-fncall-ifs
   (fn actuals x pathcond clk obligs config state)
   (declare (xargs
             :measure (list (pos-fix clk) 15 (g-ite-depth-sum actuals) 20)
             :guard (and (posp clk)
                         (symbolp fn)
                         (not (eq fn 'quote))
                         (gobj-listp actuals)
                         (acl2::interp-defs-alistp obligs)
                         (glcp-config-p config)
                         (acl2::interp-defs-alistp (glcp-config->overrides config)))
             :stobjs state))
   (b* (((mv has-if test then-args else-args)
         (glcp-interp-args-split-ite actuals))
        ((when has-if)
         (b* ((hyp pathcond))
           (glcp-if
            test
            (glcp-generic-interp-fncall-ifs fn then-args x hyp clk obligs config state)
            (glcp-generic-interp-fncall-ifs fn else-args x hyp clk obligs config
                                            state)))))
     (glcp-generic-interp-fncall fn actuals x pathcond clk obligs config state)))


 (defun glcp-generic-interp-fncall
   (fn actuals x pathcond clk obligs config state)
   (declare (xargs
             :measure (list (pos-fix clk) 14 0 20)
             :guard (and (posp clk)
                         (symbolp fn)
                         (not (eq fn 'quote))
                         (gobj-listp actuals)
                         (acl2::interp-defs-alistp obligs)
                         (glcp-config-p config)
                         (acl2::interp-defs-alistp (glcp-config->overrides config)))
             :stobjs state))
   (b* (((mv fncall-failed ans)
         (if (general-concrete-listp actuals)
             (acl2::magic-ev-fncall fn (general-concrete-obj-list actuals)
                                    state t nil)
           (mv t nil)))
        ((unless fncall-failed)
         (glcp-value (mk-g-concrete ans)))
        ((mv erp obligs1 successp term bindings state)
         (glcp-generic-rewrite-fncall fn actuals pathcond clk obligs config state))
        ((when erp) (mv erp obligs nil state))
        ((when successp)
         (glcp-generic-interp-term term bindings pathcond (1- clk) obligs1 config state))
        ((mv ok ans)
         (glcp-generic-run-gified fn actuals pathcond clk state))
        ((when ok) (glcp-value ans))
        ((when (cdr (hons-assoc-equal fn (table-alist 'gl-uninterpreted-functions (w state)))))
         (glcp-value (g-apply fn actuals)))
        ((mv erp body formals obligs)
         (acl2::interp-function-lookup fn
                                       obligs (glcp-config->overrides config)
                                       (w state)))
        ((when erp) (glcp-interp-error erp))
        ((unless (equal (len formals) (len actuals)))
         (glcp-interp-error
          (acl2::msg
           "~
In the function call ~x0, function ~x1 is given ~x2 arguments,
but its arity is ~x3.  Its formal parameters are ~x4."
           x fn (len actuals)
           (len formals)
           formals))))
     (glcp-generic-interp-term body (pairlis$ formals actuals)
                               pathcond (1- clk)
                               obligs config state)))

 (defun glcp-generic-interp-if (test tbr fbr alist pathcond clk obligs
                                     config state)
   (declare (xargs
             :measure (list clk 20 (+ 1 (+ (acl2-count test)
                                           (acl2-count tbr)
                                           (acl2-count fbr))) 10)
             :verify-guards nil
             :guard (and (natp clk)
                         (pseudo-termp test)
                         (pseudo-termp tbr)
                         (pseudo-termp fbr)
                         (acl2::interp-defs-alistp obligs)
                         (glcp-config-p config)
                         (acl2::interp-defs-alistp (glcp-config->overrides config)))
             :stobjs state))
   (b* ((hyp pathcond)
        ((glcp-er test-obj)
         (glcp-generic-interp-term test alist hyp clk obligs config state)))
     ;; BOZO glcp-or and glcp-if assume we're using the variable name HYP
     ;; for pathcond
     (if (hons-equal test tbr)
         (glcp-or
          test-obj
          (glcp-generic-interp-term fbr alist hyp clk obligs config state))
       (glcp-if
        test-obj
        (glcp-generic-interp-term tbr alist hyp clk obligs config state)
        (glcp-generic-interp-term fbr
                                  alist hyp clk obligs config state)))))

 (defun glcp-generic-rewrite-fncall (fn actuals pathcond clk obligs config state)
   (declare (xargs :stobjs state
                   :guard (and (posp clk)
                               (symbolp fn)
                               (not (eq fn 'quote))
                               (acl2::interp-defs-alistp obligs)
                               (glcp-config-p config)
                               (acl2::interp-defs-alistp
                                (glcp-config->overrides config)))
                   :measure (list (pos-fix clk) 12 0 0)))
   
   ;; (mv erp obligs1 successp term bindings state)
   (b* ((rules (cdr (hons-assoc-equal fn (table-alist 'gl-rewrite-rules (w state)))))
        ;; or perhaps we should pass the table in the obligs? see if this is
        ;; expensive
        ((unless (and rules (true-listp rules))) ;; optimization (important?)
         (mv nil obligs nil nil nil state))
        (fn-rewrites (getprop fn 'acl2::lemmas nil 'current-acl2-world (w state))))
     (glcp-generic-rewrite-fncall-apply-rules
      fn-rewrites rules fn actuals pathcond clk obligs config state)))
 
 
 (defun glcp-generic-rewrite-fncall-apply-rules
   (fn-rewrites rules fn actuals pathcond clk obligs config state)
   (declare (xargs :stobjs state
                   :guard (and (true-listp rules)
                               (posp clk)
                               (symbolp fn)
                               (not (eq fn 'quote))
                               (acl2::interp-defs-alistp obligs)
                               (glcp-config-p config)
                               (acl2::interp-defs-alistp
                                (glcp-config->overrides config)))
                   :measure (list (pos-fix clk) 8 (len fn-rewrites) 0)))
   (b* (((when (atom fn-rewrites))
         ;; no more rules, fail
         (mv nil obligs nil nil nil state))
        (rule (car fn-rewrites))
        ((unless (acl2::weak-rewrite-rule-p rule))
         (cw "malformed rewrite rule?? ~x0~%" rule)
         (glcp-generic-rewrite-fncall-apply-rules
          (cdr fn-rewrites) rules fn actuals pathcond clk obligs config state))
        ((unless (member-equal (acl2::rewrite-rule->rune rule) rules))
         (glcp-generic-rewrite-fncall-apply-rules
          (cdr fn-rewrites) rules fn actuals pathcond clk obligs config state))
        ((mv erp obligs1 successp term bindings state)
         (glcp-generic-rewrite-fncall-apply-rule
          rule fn actuals pathcond clk obligs config state))
        ((when erp)
         (mv erp obligs nil nil nil state))
        ((when successp)
         (mv nil obligs1 successp term bindings state)))
     (glcp-generic-rewrite-fncall-apply-rules
      (cdr fn-rewrites) rules fn actuals pathcond clk obligs config state)))

 (defun glcp-generic-rewrite-fncall-apply-rule
   (rule fn actuals pathcond clk obligs config state)
   (declare (xargs :stobjs state
                   :guard (and (acl2::weak-rewrite-rule-p rule)
                               (posp clk)
                               (symbolp fn)
                               (not (eq fn 'quote))
                               (acl2::interp-defs-alistp obligs)
                               (glcp-config-p config)
                               (acl2::interp-defs-alistp
                                (glcp-config->overrides config)))
                   :measure (list (pos-fix clk) 4 0 0)))
   (b* (((rewrite-rule rule) rule)
        ((unless (and (eq rule.equiv 'equal)
                      (not (eq rule.subclass 'acl2::meta))
                      (pseudo-termp rule.lhs)
                      (consp rule.lhs)
                      (eq (car rule.lhs) fn)))
         (cw "malformed gl rewrite rule (lhs)?? ~x0~%" rule)
         (mv nil obligs nil nil nil state))
        ((mv unify-ok gobj-bindings)
         (glcp-unify-term/gobj-list (cdr rule.lhs) actuals nil))
        ((unless unify-ok)
         (mv nil obligs nil nil nil state))
        ((unless (pseudo-term-listp rule.hyps))
         (cw "malformed gl rewrite rule (hyps)?? ~x0~%" rule)
         (mv nil obligs nil nil nil state))
        ((mv erp obligs1 hyps-ok gobj-bindings state)
         (glcp-generic-relieve-hyps rule.hyps gobj-bindings pathcond clk obligs config state))
        ((when erp)
         (mv erp obligs nil nil nil state))
        ((unless hyps-ok)
         (mv nil obligs nil nil nil state))
        ((unless (pseudo-termp rule.rhs))
         (cw "malformed gl rewrite rule (rhs)?? ~x0~%" rule)
         (mv nil obligs nil nil nil state)))
     (mv nil obligs1 t rule.rhs gobj-bindings state)))

 (defun glcp-generic-relieve-hyps (hyps bindings pathcond clk obligs config state)
   (declare (xargs :stobjs state
                   :guard (and (pseudo-term-listp hyps)
                               (posp clk)
                               (acl2::interp-defs-alistp obligs)
                               (glcp-config-p config)
                               (acl2::interp-defs-alistp
                                (glcp-config->overrides config)))
                   :measure (list (pos-fix clk) 2 (len hyps) 0)))
   (b* (((when (atom hyps))
         (mv nil obligs t bindings state))
        ((mv erp obligs ok bindings state)
         (glcp-generic-relieve-hyp (car hyps) bindings pathcond clk obligs
                                   config state))
        ((when (or erp (not ok)))
         (mv erp obligs ok bindings state)))
     (glcp-generic-relieve-hyps (cdr hyps) bindings pathcond clk obligs config
                                state)))

 (defun glcp-generic-relieve-hyp (hyp bindings pathcond clk obligs config state)
   (declare (xargs :stobjs state
                   :guard (and (pseudo-termp hyp)
                               (posp clk)
                               (acl2::interp-defs-alistp obligs)
                               (glcp-config-p config)
                               (acl2::interp-defs-alistp
                                (glcp-config->overrides config)))
                   :measure (list (pos-fix clk) 1 0 0)))
   ;; "Simple" version for now; maybe free variable bindings, syntaxp, etc later...
   (b* (((when (and (consp hyp) (eq (car hyp) 'synp)))
         (b* (((mv erp successp bindings)
               (glcp-relieve-hyp-synp hyp bindings state)))
           (mv erp obligs successp bindings state)))
         ((mv erp obligs val state)
         (glcp-generic-interp-term hyp bindings pathcond (1- clk) obligs config
                                   state))
        ((when erp)
         (mv erp obligs nil nil state))
        (test (gtests val pathcond))
        ((when (and (eq (gtests-nonnil test) t)
                    (eq (gtests-unknown test) nil)))
         (mv nil obligs t bindings state)))
     (mv nil obligs nil bindings state)))

 (defun glcp-generic-interp-list
   (x alist pathcond clk obligs config state)
   (declare
    (xargs
     :measure (list clk 20 (acl2-count x) 20)
     :guard (and (natp clk)
                 (pseudo-term-listp x)
                 (acl2::interp-defs-alistp obligs)
                 (glcp-config-p config)
                 (acl2::interp-defs-alistp (glcp-config->overrides config)))
     :stobjs state))
   (if (atom x)
       (glcp-value nil)
     (b* (((glcp-er car)
           (glcp-generic-interp-term (car x)
                                     alist pathcond clk obligs config state))
          ((glcp-er cdr)
           (glcp-generic-interp-list (cdr x)
                                     alist pathcond clk obligs config state)))
       (glcp-value (gl-cons car cdr))))))
||#
