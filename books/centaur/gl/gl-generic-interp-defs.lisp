
(in-package "GL")


(include-book "ite-merge")
(include-book "gtests")
(include-book "glcp-templates")
(include-book "shape-spec-defs")
(include-book "symbolic-arithmetic-fns")
(include-book "centaur/misc/rewrite-rule" :dir :system)
(include-book "param")
(include-book "bfr-sat")
(include-book "glcp-config")
(include-book "centaur/misc/beta-reduce-full" :dir :system)
(include-book "gl-mbe")

(defmacro glcp-value (res)
  `(mv nil obligs ,res bvar-db state))

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
  `(b* (((mv patbind-glcp-er-error obligs ,(car args) bvar-db state)
         ,(car bindings))
        ((when patbind-glcp-er-error)
         (mv patbind-glcp-er-error obligs nil bvar-db state)))
     (check-vars-not-free
      (patbind-glcp-er-error) ,expr)))

(verify-termination acl2::evisc-tuple)
(verify-guards acl2::evisc-tuple)

(defun glcp-case-split-report (test then else)
  (declare (xargs :guard t)
           (ignore test then else))
  nil)
                  

(defmacro glcp-if (test then else &key report)
  `(b* ((hyp pathcond)
        (gtests (gtests ,test hyp))
        (then-hyp (hf (bfr-or (gtests-unknown gtests)
                               (gtests-nonnil gtests))))
        (else-hyp (hf (bfr-or (gtests-unknown gtests)
                               (bfr-not (gtests-nonnil gtests)))))
        (- (and then-hyp else-hyp ,report))
        ((glcp-er then)
         (if then-hyp
             (let ((pathcond (bfr-and hyp then-hyp)))
               (declare (ignorable pathcond))
               ,then)
           (glcp-value nil)))
        ((glcp-er else)
         (if else-hyp
             (let ((pathcond (bfr-and hyp else-hyp)))
               (declare (ignorable pathcond))
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
  `(b* ((hyp pathcond)
        (test ,test)
        (gtests (gtests test hyp))
        (else-hyp (hf (bfr-or (gtests-unknown gtests)
                               (bfr-not (gtests-nonnil gtests)))))
        ((glcp-er else)
         (if else-hyp
             (let ((pathcond (bfr-and hyp else-hyp)))
               (declare (ignorable pathcond))
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

      ;; force checks
      gl-force-check gl-force-check-strong gl-force-false gl-force-true
      ))

(in-theory (disable glcp-generic-geval))

(acl2::def-meta-extract glcp-generic-geval-ev glcp-generic-geval-ev-lst)

(encapsulate
  (((glcp-generic-run-gified * * * * * bvar-db state)
    => (mv * *)
    :formals (fn actuals hyp clk config bvar-db state)
    :guard (and (symbolp fn)
                (true-listp actuals)
                (glcp-config-p config)
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

  (local (defun glcp-generic-run-gified (fn actuals hyp clk config bvar-db state)
           (declare (xargs :stobjs (bvar-db state)
                           :guard (and (symbolp fn)
                                       (natp clk)))
                    (ignorable fn actuals hyp clk config bvar-db state))
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
                  ;; (gobj-listp actuals)
                  (mv-nth 0 (glcp-generic-run-gified fn actuals hyp
                                                     clk config bvar-db state)))
             (equal (glcp-generic-geval
                     (mv-nth 1 (glcp-generic-run-gified
                                fn actuals hyp clk config bvar-db state))
                     env)
                    (glcp-generic-geval-ev
                     (cons fn
                           (acl2::kwote-lst
                            (glcp-generic-geval-list actuals env))) nil))))

  (defthm gobj-depends-on-of-glcp-generic-run-gified
    (implies (not (gobj-list-depends-on k p actuals))
             (not (gobj-depends-on k p (mv-nth 1 (glcp-generic-run-gified
                                                  fn actuals hyp clk config bvar-db state))))))
                  

  ;; (defthm true-listp-glcp-generic-run-gified
  ;;   (true-listp (glcp-generic-run-gified fn actuals hyp clk config bvar-db state)))

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

(defun glcp-interp-error-fn (msg obligs bvar-db state)
  (declare (xargs :guard t :stobjs (bvar-db state)))
  (mv msg obligs nil bvar-db state))

(defmacro glcp-interp-error (msg)
  (declare (xargs :guard t))
  `(glcp-interp-error-fn ,msg obligs bvar-db state))

(add-macro-alias glcp-interp-error glcp-interp-error-fn)

(defthmd acl2-count-last-cdr-when-cadr-hack
  (implies (< 1 (len x))
           (< (acl2-count (car (last x)))
              (+ 1 (acl2-count (cdr x)))))
  :rule-classes (:rewrite :linear))



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
        ((when (and (eq (car pat) 'if)
                    (eql (len pat) 4)
                    (eq (tag x) :g-ite)))
         (b* ((test (g-ite->test x))
              (then (g-ite->then x))
              (else (g-ite->else x))
              ((mv ok alist)
               (glcp-unify-term/gobj (second pat) test alist))
              ((unless ok) (mv nil nil))
              ((mv ok alist)
               (glcp-unify-term/gobj (third pat) then alist))
              ((unless ok) (mv nil nil)))
           (glcp-unify-term/gobj (fourth pat) else alist)))
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
        (mv (cons (g-ite->then obj) rest-then)
            (cons (g-ite->else obj) rest-else))))
    (mv (cons obj rest-then)
        (cons obj rest-else))))
    

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
          (mv t test (cons then then-rest) (cons else else-rest))))
       ((mv has-if test then else)
        (glcp-interp-args-split-ite (cdr args)))
       ((unless has-if)
        (mv nil nil nil nil)))
    (mv has-if test (cons obj then) (cons obj else))))

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
     (cons (gl-term-to-apply-obj (car x) alist)
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

;; NOTE.  This is provably equal to pseudo-term-listp, but we use it
;; differently.  When an element is a symbol, it stands for an equivalence
;; relation; otherwise, it is a context "fixing" term.
(defun contextsp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (or (symbolp (car x))
             (pseudo-termp (car x)))
         (contextsp (cdr x)))))
     

;; (defund-nx glcp-generic-eval-context-equivs (contexts x y a)
;;   (b* (((when (atom contexts))
;;         (equal (glcp-generic-geval-ev x a)
;;                (glcp-generic-geval-ev y a)))
;;        (ctx (car contexts))
;;        (ctx-fn (if (symbolp ctx)
;;                    ctx
;;                  `(lambda (x y)
;;                     (equal ,ctx
;;                            ((lambda (x) ,ctx) y))))))
;;     (or (glcp-generic-geval-ev (list ctx-fn x y) a)
;;         (glcp-generic-eval-context-equivs (cdr contexts) x y a))))

;; (defun-sk glcp-generic-equiv-under-contexts (contexts x y)
;;   (forall (a)
;;           (glcp-generic-eval-context-equivs contexts x y a))
;;   :rewrite :direct)


(defun-sk glcp-generic-equiv-relp (f)
  (forall (a x y z)
          (and (booleanp (glcp-generic-geval-ev (list f x y) a))
               (glcp-generic-geval-ev (list f x x) a)
               (implies (glcp-generic-geval-ev (list f x y) a)
                        (glcp-generic-geval-ev (list f y x) a))
               (implies (and (glcp-generic-geval-ev (list f x y) a)
                             (glcp-generic-geval-ev (list f y z) a))
                        (glcp-generic-geval-ev (list f x z) a))))
  :rewrite :direct)

(in-theory (disable glcp-generic-equiv-relp))

(defun proper-contextsp (contexts)
  (if (atom contexts)
      t
    (and (or (not (symbolp (car contexts)))
             (glcp-generic-equiv-relp (car contexts)))
         (proper-contextsp (cdr contexts)))))

(defund-nx glcp-generic-eval-context-equiv (contexts x y)
  (b* (((when (atom contexts)) (equal x y))
       (ctx (car contexts))
       (ctx-fn (if (symbolp ctx)
                   ctx
                 `(lambda (x y)
                    (equal ((lambda (x) ,ctx) x)
                           ((lambda (x) ,ctx) y))))))
    (or (glcp-generic-geval-ev (list ctx-fn (kwote x) (kwote y)) nil)
        (glcp-generic-eval-context-equiv (cdr contexts) x y))))
           

(defthmd glcp-generic-eval-context-equiv-commute
  (implies (and (proper-contextsp contexts)
                (glcp-generic-eval-context-equiv contexts x y))
           (glcp-generic-eval-context-equiv contexts y x))
  :hints (("goal" :induct (glcp-generic-eval-context-equiv contexts x y)
           :in-theory (enable glcp-generic-eval-context-equiv
                              glcp-generic-geval-ev-of-fncall-args)
           :expand ((glcp-generic-eval-context-equiv contexts y x)
                    (proper-contextsp contexts)))))

(defun glcp-generic-eval-context-equiv-chain (contexts chain)
  (declare (xargs :hints(("Goal" :in-theory (enable acl2-count)))))
  (if (atom (cdr chain))
      t
    (and (glcp-generic-eval-context-equiv contexts
                                          (car chain)
                                          (cadr chain))
         (glcp-generic-eval-context-equiv-chain contexts (cdr chain)))))

(defun-sk glcp-generic-eval-context-equiv* (contexts x y)
  (exists chain
          (and (consp chain)
               (equal (car chain) x)
               (equal (car (last chain)) y)
               (glcp-generic-eval-context-equiv-chain contexts chain))))

(in-theory (disable glcp-generic-eval-context-equiv*))

(defthm glcp-generic-eval-context-equiv*-refl
  (glcp-generic-eval-context-equiv* contexts x x)
  :hints (("goal" :use ((:instance glcp-generic-eval-context-equiv*-suff
                         (chain (list x)) (y x))))))



(defthm glcp-generic-eval-context-equiv*-chain-append
  (implies (and (glcp-generic-eval-context-equiv-chain contexts c1)
                (glcp-generic-eval-context-equiv-chain contexts c2)
                (equal (car (last c1)) (car c2)))
           (glcp-generic-eval-context-equiv-chain contexts (append c1 (cdr
                                                                       c2))))
  :hints(("Goal" :in-theory (disable glcp-generic-eval-context-equiv-commute))))


(encapsulate nil
  (local (defthm last-of-append-when-first/last-equal
           (implies (equal (car b) (car (last a)))
                    (equal (car (last (append a (cdr b))))
                           (car (last b))))))

  (local (defthm car-append-when-consp
           (implies (consp x)
                    (equal (car (append x y))
                           (car x)))))

  (defthm glcp-generic-eval-context-equiv*-trans
    (implies (and (glcp-generic-eval-context-equiv* contexts x y)
                  (glcp-generic-eval-context-equiv* contexts y z))
             (glcp-generic-eval-context-equiv* contexts x z))
    :hints (("goal" :use ((:instance glcp-generic-eval-context-equiv*-suff
                           (chain (append
                                   (glcp-generic-eval-context-equiv*-witness
                                    contexts x y)
                                   (cdr (glcp-generic-eval-context-equiv*-witness
                                         contexts y z))))
                           (y z)))
             :expand ((glcp-generic-eval-context-equiv* contexts x y)
                      (glcp-generic-eval-context-equiv* contexts y z))))))


(encapsulate nil

  (local (defthm chain-of-append-when-last/first-related
           (implies (and (consp x)
                         (glcp-generic-eval-context-equiv contexts (car (last x))
                                                          (car y))
                         (glcp-generic-eval-context-equiv-chain contexts x)
                         (glcp-generic-eval-context-equiv-chain contexts y))
                    (glcp-generic-eval-context-equiv-chain contexts (append x
                                                                            y)))))

  (local (defthm last-of-append-when-consp-second
           (implies (consp y)
                    (equal (last (append x y))
                           (last y)))))


  (local (defthm car-last-of-rev
           (implies (consp x)
                    (equal (car (last (acl2::rev x)))
                           (car x)))
           :hints(("Goal" :in-theory (enable acl2::rev)))))

  (defthmd glcp-generic-eval-context-equiv-chain-rev
    (implies (and (proper-contextsp contexts)
                  (glcp-generic-eval-context-equiv-chain contexts chain))
             (glcp-generic-eval-context-equiv-chain contexts (acl2::rev chain)))
    :hints(("Goal" :in-theory (e/d (acl2::rev) (proper-contextsp))
            :induct (acl2::rev chain))
           (and stable-under-simplificationp
                '(:expand ((acl2::rev (cdr chain)))
                  :in-theory (e/d (glcp-generic-eval-context-equiv-commute)
                                  (acl2::associativity-of-append))))))

  (local (in-theory (enable glcp-generic-eval-context-equiv-chain-rev)))

  (local (defthm consp-rev
           (equal (consp (acl2::rev x))
                  (consp x))))

  (local (defthm car-append-when-consp
           (implies (consp x)
                    (equal (car (append x y))
                           (car x)))))

  
  (local (defthm car-rev-when-consp
           (implies (consp x)
                    (equal (car (acl2::rev x))
                           (car (last x))))
           :hints(("Goal" :in-theory (enable acl2::rev)))))

  (defthmd glcp-generic-eval-context-equiv*-commute
    (implies (and (proper-contextsp contexts)
                  (glcp-generic-eval-context-equiv* contexts x y))
             (glcp-generic-eval-context-equiv* contexts y x))
    :hints (("goal" :use ((:instance glcp-generic-eval-context-equiv*-suff
                           (chain (acl2::rev
                                   (glcp-generic-eval-context-equiv*-witness
                                    contexts x y)))
                           (x y) (y x)))
             :in-theory (disable proper-contextsp)
             :expand ((glcp-generic-eval-context-equiv* contexts x y))))))


(defthm g-ite->test-acl2-count-decr
  (implies (equal (tag x) :g-ite)
           (< (acl2-count (g-ite->test x)) (acl2-count x)))
  :hints(("Goal" :in-theory (enable tag g-ite->test)))
  :rule-classes :linear)

(defthm g-ite->then-acl2-count-decr
  (implies (equal (tag x) :g-ite)
           (< (acl2-count (g-ite->then x)) (acl2-count x)))
  :hints(("Goal" :in-theory (enable tag g-ite->then)))
  :rule-classes :linear)

(defthm g-ite->else-acl2-count-decr
  (implies (equal (tag x) :g-ite)
           (< (acl2-count (g-ite->else x)) (acl2-count x)))
  :hints(("Goal" :in-theory (enable tag g-ite->else)))
  :rule-classes :linear)



(in-theory (disable glcp-generic-equiv-relp))

(defsection ensure-equiv-relationp

  (acl2::def-unify glcp-generic-geval-ev glcp-generic-geval-ev-alist)
  (acl2::def-meta-extract glcp-generic-geval-ev glcp-generic-geval-ev-lst)

  (defund search-match-in-conjunction (pat term)
    (declare (xargs :guard (and (pseudo-termp pat)
                                (pseudo-termp term))))
    (b* (((mv ok &) (acl2::simple-one-way-unify term pat nil))
         ((when ok) t)
         ((when (atom term)) nil)
         ((unless (and (eq (car term) 'if)
                       (equal (fourth term) ''nil)))
          nil))
      (or (search-match-in-conjunction pat (second term))
          (search-match-in-conjunction pat (third term)))))

  (defthmd glcp-generic-geval-ev-theoremp-of-conjunction
    (implies (and (equal (car term) 'if)
                  (equal (fourth term) ''nil))
             (iff (glcp-generic-geval-ev-theoremp term)
                  (and (glcp-generic-geval-ev-theoremp (second term))
                       (glcp-generic-geval-ev-theoremp (third term)))))
    :hints (("goal" :use ((:instance glcp-generic-geval-ev-falsify
                           (x term) (a (glcp-generic-geval-ev-falsify (second term))))
                          (:instance glcp-generic-geval-ev-falsify
                           (x term) (a (glcp-generic-geval-ev-falsify (third term))))
                          (:instance glcp-generic-geval-ev-falsify
                           (x (second term))
                           (a (glcp-generic-geval-ev-falsify term)))
                          (:instance glcp-generic-geval-ev-falsify
                           (x (third term))
                           (a (glcp-generic-geval-ev-falsify term))))
             :in-theory (disable pseudo-termp pseudo-term-listp))))

  (local (in-theory (enable glcp-generic-geval-ev-theoremp-of-conjunction)))

  (defthmd search-match-in-conjunction-correct
    (implies (and (glcp-generic-geval-ev-theoremp term)
                  (pseudo-termp term)
                  (pseudo-termp pat)
                  (search-match-in-conjunction pat term))
             (glcp-generic-geval-ev pat a))
    :hints(("Goal" :in-theory (e/d (search-match-in-conjunction)
                                   (glcp-generic-geval-ev-alist
                                    symbol-listp
                                    nonnil-symbol-listp))
            :induct (search-match-in-conjunction pat term))
           (and stable-under-simplificationp
                '(:use ((:instance glcp-generic-geval-ev-falsify
                         (x term)
                         (a (glcp-generic-geval-ev-alist
                             (mv-nth 1 (acl2::simple-one-way-unify term pat nil))
                             a))))))))

  (defund check-equiv-formula (form e)
    (declare (xargs :guard (and (pseudo-termp form)
                                (symbolp e)
                                (not (eq e 'quote)))))
    (and (search-match-in-conjunction `(booleanp (,e x y)) form)
         (search-match-in-conjunction `(,e x x) form)
         (search-match-in-conjunction `(implies (,e x y) (,e y x)) form)
         (search-match-in-conjunction `(implies (if (,e x y)
                                                    (,e y z)
                                                  'nil)
                                                (,e x z))
                                      form)))

  (local (defthm lemma1
           (implies (and (pseudo-termp form)
                         (glcp-generic-geval-ev-theoremp form)
                         (search-match-in-conjunction `(booleanp (,e x y)) form)
                         (symbolp e)
                         (not (equal e 'quote)))
                    (booleanp (glcp-generic-geval-ev (list e x y) a)))
           :hints (("goal" :in-theory (e/d (check-equiv-formula
                                            glcp-generic-geval-ev-of-fncall-args)
                                           (search-match-in-conjunction-correct))
                    :use ((:instance search-match-in-conjunction-correct
                           (term form) (pat `(booleanp (,e x y)))
                           (a `((x . ,(glcp-generic-geval-ev x a))
                                (y . ,(glcp-generic-geval-ev y a))
                                (z . ,(glcp-generic-geval-ev z a))))))))))

  (local (defthm lemma2
           (implies (and (pseudo-termp form)
                         (glcp-generic-geval-ev-theoremp form)
                         (search-match-in-conjunction `(,e x x) form)
                         (symbolp e)
                         (not (equal e 'quote)))
                    (glcp-generic-geval-ev (list e x x) a))
           :hints (("goal" :in-theory (e/d (check-equiv-formula
                                            glcp-generic-geval-ev-of-fncall-args)
                                           (search-match-in-conjunction-correct))
                    :use ((:instance search-match-in-conjunction-correct
                           (term form) (pat `(,e x x))
                           (a `((x . ,(glcp-generic-geval-ev x a))
                                (y . ,(glcp-generic-geval-ev y a))
                                (z . ,(glcp-generic-geval-ev z a))))))))))

  (local (defthm lemma3
           (implies (and (pseudo-termp form)
                         (glcp-generic-geval-ev-theoremp form)
                         (search-match-in-conjunction
                          `(implies (,e x y) (,e y x)) form)
                         (symbolp e)
                         (not (equal e 'quote))
                         (glcp-generic-geval-ev (list e x y) a))
                    (glcp-generic-geval-ev (list e y x) a))
           :hints (("goal" :in-theory (e/d (check-equiv-formula
                                            glcp-generic-geval-ev-of-fncall-args)
                                           (search-match-in-conjunction-correct))
                    :use ((:instance search-match-in-conjunction-correct
                           (term form) (pat `(implies (,e x y) (,e y x)))
                           (a `((x . ,(glcp-generic-geval-ev x a))
                                (y . ,(glcp-generic-geval-ev y a))
                                (z . ,(glcp-generic-geval-ev z a))))))))))

  (local (defthm lemma4
           (implies (and (pseudo-termp form)
                         (glcp-generic-geval-ev-theoremp form)
                         (search-match-in-conjunction
                          `(implies (if (,e x y) (,e y z) 'nil) (,e x z)) form)
                         (symbolp e)
                         (not (equal e 'quote))
                         (glcp-generic-geval-ev (list e x y) a)
                         (glcp-generic-geval-ev (list e y z) a))
                    (glcp-generic-geval-ev (list e x z) a))
           :hints (("goal" :in-theory (e/d (check-equiv-formula
                                            glcp-generic-geval-ev-of-fncall-args)
                                           (search-match-in-conjunction-correct))
                    :use ((:instance search-match-in-conjunction-correct
                           (term form) (pat `(implies (if (,e x y) (,e y z) 'nil) (,e x z)))
                           (a `((x . ,(glcp-generic-geval-ev x a))
                                (y . ,(glcp-generic-geval-ev y a))
                                (z . ,(glcp-generic-geval-ev z a))))))))))

  (defthmd check-equiv-formula-correct
    (implies (and (check-equiv-formula form e)
                  (glcp-generic-geval-ev-theoremp form)
                  (pseudo-termp form)
                  (symbolp e)
                  (not (eq e 'quote)))
             (glcp-generic-equiv-relp e))
    :hints(("Goal" :in-theory '(check-equiv-formula
                                glcp-generic-equiv-relp
                                lemma1 lemma2 lemma3 lemma4))))

  (local (in-theory (enable check-equiv-formula-correct)))

  (local (in-theory (disable w)))

  (defund check-equiv-rule (rune e w)
    (declare (xargs :guard (and (symbolp e)
                                (not (eq e 'quote))
                                (plist-worldp w))))
    (b* ((rule (if (symbolp rune)
                   rune
                 (and (symbol-listp rune)
                      (cadr rune))))
         ((unless rule) nil)
         (form (acl2::meta-extract-formula-w rule w))
         ((unless (pseudo-termp form)) nil))
      (check-equiv-formula form e)))

  (defthmd check-equiv-rule-correct
    (implies (and (check-equiv-rule rune e w)
                  (glcp-generic-geval-ev-meta-extract-global-facts)
                  (equal w (w state))
                  (symbolp e) (not (eq e 'quote)))
             (glcp-generic-equiv-relp e))
    :hints(("Goal" :in-theory (e/d (check-equiv-rule)
                                   (pseudo-termp)))))

  (local (in-theory (enable check-equiv-rule-correct)))
  

  (defund congruences-find-equiv-rule (congs e w)
    (declare (xargs :guard (and (symbolp e)
                                (not (eq e 'quote))
                                (plist-worldp w))))
    (b* (((when (atom congs)) nil)
         (cong (car congs))
         ((unless (and (acl2::weak-congruence-rule-p cong)
                       (eq (acl2::access acl2::congruence-rule
                                         cong :equiv)
                           e)))
          (congruences-find-equiv-rule (cdr congs) e w))
         (rune (acl2::access acl2::congruence-rule cong :rune)))
      (or (check-equiv-rule rune e w)
          (congruences-find-equiv-rule (cdr congs) e w))))

  (defthmd congruences-find-equiv-rule-correct
    (implies (and (congruences-find-equiv-rule congs e w)
                  (glcp-generic-geval-ev-meta-extract-global-facts)
                  (equal w (w state))
                  (symbolp e) (not (eq e 'quote)))
             (glcp-generic-equiv-relp e))
    :hints(("Goal" :in-theory (e/d (congruences-find-equiv-rule)
                                   (pseudo-termp
                                    acl2::weak-congruence-rule-p
                                    default-car)))))
  
  (local (in-theory (enable congruences-find-equiv-rule-correct)))

  (defund ensure-equiv-relationp (e w)
    (declare (xargs :guard (and (symbolp e)
                                (plist-worldp w))))
    (b* (((when (member-eq e '(equal iff))) t)
         ((when (eq e 'quote)) nil)
         (coarsenings (getprop e 'acl2::coarsenings nil 'current-acl2-world w))
         ((unless coarsenings) nil)
         ;; shortcut: ACL2 always stores e as a coarsening of itself if it's an
         ;; equivalence relation.  In fact, it should only have coarsenings if it
         ;; is one.  But we don't get to assume that in meta-extract so we look
         ;; for a theorem stating it.
         (congruences (getprop e 'acl2::congruences nil 'current-acl2-world w))
         (equal-congs (cdr (hons-assoc-equal 'equal congruences)))
         (first-arg-congs (and (consp equal-congs) (car equal-congs))))
      (congruences-find-equiv-rule first-arg-congs e w)))

  (defthmd ensure-equiv-relationp-correct
    (implies (and (ensure-equiv-relationp e w)
                  (glcp-generic-geval-ev-meta-extract-global-facts)
                  (equal w (w state))
                  (symbolp e))
             (glcp-generic-equiv-relp e))
    :hints(("Goal" :in-theory (e/d (ensure-equiv-relationp)
                                   (pseudo-termp
                                    acl2::weak-congruence-rule-p
                                    default-car))
            :expand ((glcp-generic-equiv-relp 'iff)
                     (glcp-generic-equiv-relp 'equal))))))


;; X is a gobj. Returns OK, repl, negp.
;; OK implies that equiv-term <=> (xor negp (equiv x repl)) of x, where equiv
;; is an equivalence ok under the contexts.
(defund check-equiv-replacement (x equiv-term contexts state)
  (declare (xargs :guard (contextsp contexts)
                  :stobjs state)
           (ignorable state))
  ;; BOZO fix these to work with context fixing terms, refinements, etc
  (b* (((when (hqual x equiv-term))
        (mv t nil t))
       ((unless (and (consp equiv-term)
              (eq (tag equiv-term) :g-apply)))
        (mv nil nil nil))
       (equiv (g-apply->fn equiv-term))
       ((unless (and (symbolp equiv)
                     (not (eq equiv 'quote))
                     (or (eq equiv 'equal)
                         (member-eq equiv contexts))))
        (mv nil nil nil))
       (args (g-apply->args equiv-term))
       ((unless (equal (len args) 2))
        (mv nil nil nil))
       ((when (hqual (car args) x))
        (mv t (cadr args) nil))
       ((when (hqual (cadr args) x))
        (mv t (car args) nil)))
    (mv nil nil nil)))


;; (defund check-equiv-replacement-ok (x equiv-term contexts state)
;;   (declare (xargs :guard (contextsp contexts)
;;                   :stobjs state)
;;            (ignorable state))
;;   ;; BOZO fix these to work with context fixing terms, refinements, etc
;;   (b* (((unless (and (consp equiv-term)
;;                      (eq (tag equiv-term) :g-apply)))
;;         nil)
;;        (equiv (g-apply->fn equiv-term))
;;        ((unless (and (symbolp equiv)
;;                      (not (eq equiv 'quote))
;;                      (or (eq equiv 'equal)
;;                          (member-eq equiv contexts))))
;;         nil)
;;        (args (g-apply->args equiv-term))
;;        ((unless (equal (len args) 2))
;;         nil)
;;        ((when (or (hqual (car args) x)
;;                   (hqual (cadr args) x)))
;;         t))
;;     nil))

;; (trace$ (check-equiv-replacement :cond (check-equiv-replacement-ok x equiv-term
;;                                                                    contexts
;;                                                                    state)
;;                                  :entry (list 'check-equiv)
;;                                  :exit (list 'check-equiv x (cadr values))
;;                                  :evisc-tuple '(nil 5 10 nil)
;;                                  :hide nil))


(defund try-equivalences (x bvars pathcond contexts p bvar-db state)
  (declare (xargs :guard (and (contextsp contexts)
                              (non-exec (ec-call (bvar-listp bvars bvar-db))))
                  :stobjs (bvar-db state)))
  (b* (((when (atom bvars)) (mv nil nil))
       (bvar (car bvars))
       (equiv-term (get-bvar->term bvar bvar-db))
       ((mv check-ok repl negp)
        (check-equiv-replacement x equiv-term contexts state))
       ((unless check-ok)
        (try-equivalences x (cdr bvars) pathcond contexts p bvar-db state))
       ((when negp)
        (if (false-under-hyp
             (hyp-fix (bfr-to-param-space p (bfr-var bvar))
                      pathcond)
             pathcond)
            (mv t repl)
          (try-equivalences x (cdr bvars) pathcond contexts p bvar-db state)))
       ((unless (true-under-hyp
                 (hyp-fix (bfr-to-param-space p (bfr-var bvar))
                          pathcond)
                 pathcond))
        (try-equivalences x (cdr bvars) pathcond contexts p bvar-db state)))
    (mv t repl)))

                               

(defund try-equivalences-loop (x pathcond contexts clk p bvar-db state)
  (declare (xargs :guard (and (natp clk)
                              (contextsp contexts))
                  :stobjs (bvar-db state)
                  :measure (nfix clk)))
  (b* (((when (zp clk)) (mv "try-equivalences ran out of clock -- equiv loop?"
                            x))
       (equivs (get-term->equivs x bvar-db))
       ((mv ok repl) (try-equivalences x equivs pathcond contexts p bvar-db
                                       state))
       ((when ok)
        (try-equivalences-loop repl pathcond contexts (1- clk) p bvar-db
                               state)))
    (mv nil x)))


(defund maybe-add-equiv-term (test-obj bvar bvar-db state)
  (declare (xargs :stobjs (bvar-db state)
                  :guard (and (integerp bvar)
                              (<= (base-bvar bvar-db) bvar)
                              (< bvar (next-bvar bvar-db))))
           (ignorable state))
  (b* (;; (equivp (getprop fn 'acl2::coarsenings nil 'current-acl2-world (w state)))
       ;; ((unless equivp)
       ;;  ;; not an equivalence relation
       ;;  bvar-db)
       ((unless (consp test-obj))
        bvar-db)

       ((when (eq (tag test-obj) :g-var))
        (add-term-equiv test-obj bvar bvar-db))

       ((unless (eq (tag test-obj) :g-apply))
        bvar-db)

       (fn (g-apply->fn test-obj))
       (args (g-apply->args test-obj))

       ((unless (and (eq fn 'equal)
                     (equal (len args) 2)))
        (add-term-equiv test-obj bvar bvar-db))
       ((list a b) args)
       ;; The rest is just a heuristic determination of which should rewrite to
       ;; the other.
       (a-goodp (or (atom a)
                    (member (tag a) '(:g-number :g-boolean))
                    (general-concretep a)))
       ((when a-goodp)
        (add-term-equiv b bvar bvar-db))
       (b-goodp (or (atom b)
                    (member (tag b) '(:g-number :g-boolean))
                    (general-concretep b)))
       ((when b-goodp)
        (add-term-equiv a bvar bvar-db)))
    bvar-db))

;; (defund glcp-generic-geval-ev-theoremsp (rules)
;;   (if (atom rules)
;;       t
;;     (and (glcp-generic-geval-ev-theoremp (car rules))
;;          (glcp-generic-geval-ev-theoremsp (cdr rules)))))



;; (defund meta-extract-formulas (names wrld)
;;   (declare (xargs :guard (plist-worldp wrld)))
;;   (b* (((when (atom names)) nil)
;;        (name (car names))
;;        ((unless (symbolp name)) (meta-extract-formulas (cdr names) wrld))
;;        (thm (acl2::meta-extract-formula-w name wrld)))
;;     (cons thm (meta-extract-formulas (cdr names) wrld))))

;; (defthm glcp-generic-geval-ev-theoremsp-of-meta-extract-formulas
;;   (implies (and (glcp-generic-geval-ev-meta-extract-global-facts)
;;                 (equal wrld (w state)))
;;            (glcp-generic-geval-ev-theoremsp (meta-extract-formulas names wrld)))
;;   :hints(("Goal" :in-theory (e/d (glcp-generic-geval-ev-theoremsp
;;                                   meta-extract-formulas)
;;                                  (w)))))

(defund conjunction-to-list (x)
  (declare (xargs :guard (pseudo-termp x)))
  (if (or (atom x)
          (not (eq (car x) 'if))
          (not (equal (fourth x) ''nil)))
      (list x)
    (cons (second x)
          (conjunction-to-list (third x)))))

(defthm conjunction-to-list-pseudo-term-listp
  (implies (pseudo-termp x)
           (pseudo-term-listp (conjunction-to-list x)))
  :hints(("Goal" :in-theory (enable conjunction-to-list))))


(defsection glcp-branch-merge-formula-to-rule

  (local (defthm pseudo-termp-subterms
           (implies (and (pseudo-termp x)
                         (consp x)
                         (not (eq (car x) 'quote)))
                    (and (pseudo-termp (cadr x))
                         (pseudo-termp (caddr x))
                         (pseudo-termp (cadddr x))
                         (implies (cdr x)
                                  (consp (cdr x)))
                         (implies (cddr x)
                                  (consp (cddr x)))
                         (implies (cdddr x)
                                  (consp (cdddr x)))))
           :hints(("Goal" :expand ((pseudo-termp x)
                                   (pseudo-term-listp (cdr x))
                                   (pseudo-term-listp (cddr x))
                                   (pseudo-term-listp (cdddr x)))))))

  (local (in-theory (disable acl2::beta-reduce-full
                             pseudo-termp)))


  (defund glcp-branch-merge-formula-to-rule (name wrld)
    (declare (xargs :guard (and (symbolp name) (plist-worldp wrld))
                    :guard-hints
                    (("goal" :use ((:instance
                                    acl2::pseudo-termp-of-beta-reduce-full
                                    (x (acl2::meta-extract-formula-w name wrld))))
                      :in-theory (disable acl2::pseudo-termp-of-beta-reduce-full)))))
    (b* ((thm (acl2::meta-extract-formula-w name wrld))
         ((unless (pseudo-termp thm)) (mv nil nil))
         (thm (acl2::beta-reduce-full thm))
         ((when (atom thm)) (mv nil nil))
         ((mv hyps concl)
          (if (eq (car thm) 'implies)
              (mv (conjunction-to-list (second thm))
                  (third thm))
            (mv nil thm)))
         ((when (atom concl)) (mv nil nil))
         (equiv (car concl))
         ((unless (and (symbolp equiv)
                       (not (eq equiv 'quote))
                       (getprop equiv 'acl2::coarsenings nil 'current-acl2-world wrld)
                       (eql (len concl) 3)))
          (mv nil nil)))
      (mv t (acl2::make-rewrite-rule
             :rune `(:gl-branch-merge ,name)
             :nume -1
             :hyps hyps
             :equiv equiv
             :lhs (second concl)
             :rhs (third concl)
             :subclass 'acl2::backchain)))))

(defund glcp-branch-merge-formulas-to-rules (names wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (b* (((when (atom names)) nil)
       ((unless (symbolp (car names)))
        (glcp-branch-merge-formulas-to-rules (cdr names) wrld))
       ((mv ok rule) (glcp-branch-merge-formula-to-rule (car names) wrld)))
    (if ok
        (cons rule (glcp-branch-merge-formulas-to-rules (cdr names) wrld))
      (glcp-branch-merge-formulas-to-rules (cdr names) wrld))))


(defund glcp-get-branch-merge-rules (fn wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp wrld))))
  (b* ((thms (cdr (hons-assoc-equal fn (acl2::table-alist 'gl-branch-merge-rules wrld)))))
    (glcp-branch-merge-formulas-to-rules thms wrld)))

(memoize 'glcp-get-branch-merge-rules)
                              
(defun weak-rewrite-rule-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (acl2::weak-rewrite-rule-p (car x))
         (weak-rewrite-rule-listp (cdr x)))))

(defund rewrite-rules->runes (x)
  (declare (xargs :guard (weak-rewrite-rule-listp x)))
  (if (atom x)
      nil
    (cons (acl2::rewrite-rule->rune (car x))
          (rewrite-rules->runes (cdr x)))))

(defun-inline glcp-if-or-condition (test tbr contexts)
  (declare (xargs :guard t))
  (and (hons-equal test tbr)
       ;; dumb
       (or (not contexts) (equal contexts '(iff)))))

(defun-inline glcp-or-test-contexts (contexts)
  (declare (xargs :guard t))
  (if (equal contexts '(iff))
      '(iff)
    nil))

(defconst *glcp-generic-template-subst*
  '((run-gified . glcp-generic-run-gified)
    (interp-test . glcp-generic-interp-test)
    (interp-term . glcp-generic-interp-term)
    (interp-term-equivs . glcp-generic-interp-term-equivs)
    (interp-fncall-ifs . glcp-generic-interp-fncall-ifs)
    (interp-fncall . glcp-generic-interp-fncall)
    (interp-if/or . glcp-generic-interp-if/or)
    (maybe-interp . glcp-generic-maybe-interp)
    (interp-if . glcp-generic-interp-if)
    (interp-or . glcp-generic-interp-or)
    (merge-branches . glcp-generic-merge-branches)
    (simplify-if-test . glcp-generic-simplify-if-test)
    (rewrite . glcp-generic-rewrite)
    (rewrite-apply-rules . glcp-generic-rewrite-apply-rules)
    (rewrite-apply-rule . glcp-generic-rewrite-apply-rule)
    (relieve-hyps . glcp-generic-relieve-hyps)
    (relieve-hyp . glcp-generic-relieve-hyp)
    (interp-list . glcp-generic-interp-list)
    (interp-top-level-term . glcp-generic-interp-top-level-term)
    (interp-concl . glcp-generic-interp-concl)
    (interp-hyp/concl . glcp-generic-interp-hyp/concl)
    (run-parametrized . glcp-generic-run-parametrized)
    (run-cases . glcp-generic-run-cases)
    (clause-proc . glcp-generic)
    (clause-proc-name . (glcp-generic-clause-proc-name))))

(defthmd acl2-count-of-car
  (<= (acl2-count (car x)) (acl2-count x))
  :rule-classes :linear)

(defthmd acl2-count-of-cdr
  (<= (acl2-count (cdr x)) (acl2-count x))
  :rule-classes :linear)

(defthmd acl2-count-of-car-g-apply->args
  (implies (equal (tag x) :g-apply)
           (< (acl2-count (car (g-apply->args x))) (acl2-count x)))
  :hints(("Goal" :in-theory (enable acl2-count-of-car)))
  :rule-classes :linear)

(defthmd acl2-count-of-cadr-g-apply->args
  (implies (equal (tag x) :g-apply)
           (< (acl2-count (cadr (g-apply->args x))) (acl2-count x)))
  :hints(("Goal" :in-theory (enable acl2-count-of-car
                                    acl2-count-of-cdr)))
  :rule-classes :linear)

;; (local (defthm acl2-count-of-g-apply->args-consp
;;          (implies (consp x)
;;                   (< (acl2-count (g-apply->args x)) (acl2-count x)))
;;          :rule-classes :linear))


(make-event
 (sublis *glcp-generic-template-subst*
         *glcp-interp-template*))




(make-event
 (sublis *glcp-generic-template-subst*
         *glcp-interp-wrappers-template*))

  
#||
;; redundant
(mutual-recursion
 (defun glcp-generic-interp-term
   (x alist pathcond contexts clk obligs config bvar-db state)
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
                                         g-ite->test-acl2-count-decr
                                         g-ite->then-acl2-count-decr
                                         g-ite->else-acl2-count-decr
                                         (:type-prescription acl2-count)
                                         (:t len)))))
             :verify-guards nil
             :guard (and (natp clk)
                         (pseudo-termp x)
                         (contextsp contexts)
                         (acl2::interp-defs-alistp obligs)
                         (glcp-config-p config)
                         (acl2::interp-defs-alistp (glcp-config->overrides config)))
             :stobjs (bvar-db state)))
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
                                       alist pathcond clk obligs config bvar-db state))
            (formals (car (cdar x)))
            (body (car (cdr (cdar x)))))
           (if (and (mbt (and (equal (len actuals) (len formals))
                              (symbol-listp formals)))
                    (acl2::fast-no-duplicatesp formals)
                    (not (member-eq nil formals)))
               (glcp-generic-interp-term body (pairlis$ formals actuals)
                                         pathcond contexts clk obligs config bvar-db state)
             (glcp-interp-error (acl2::msg "Badly formed lambda application: ~x0~%"
                                           x)))))
        ((when (eq (car x) 'if))
         (let ((test (car (cdr x)))
               (tbr (car (cdr (cdr x))))
               (fbr (car (cdr (cdr (cdr x))))))
           (glcp-generic-interp-if test tbr fbr alist pathcond contexts clk obligs
                                   config bvar-db state)))
        
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
                                             alist pathcond nil clk obligs config bvar-db state))
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
                 (b* (((mv err & time$-args bvar-db state)
                       (glcp-generic-interp-term (caddr x)
                                                 alist pathcond nil clk obligs config bvar-db state)))
                   (mbe :logic (glcp-generic-interp-term
                                (car (last x)) alist pathcond contexts clk obligs config bvar-db state)
                        :exec
                        (if (and (not err)
                                 (general-concretep time$-args))
                            (return-last
                             'acl2::time$1-raw
                             (general-concrete-obj time$-args)
                             (glcp-generic-interp-term (car (last x))
                                                       alist pathcond contexts clk obligs config bvar-db state))
                          (time$
                           (glcp-generic-interp-term (car (last x))
                                                     alist pathcond contexts clk obligs config bvar-db state)))))
               (glcp-generic-interp-term (car (last x))
                                         alist pathcond contexts clk obligs config bvar-db state))
           (glcp-interp-error "Error: wrong number of args to RETURN-LAST~%")))
        (fn (car x))
        ;; outside-in rewriting?
        ((glcp-er actuals)
         (glcp-generic-interp-list (cdr x)
                                   alist pathcond clk obligs config bvar-db state)))
     (glcp-generic-interp-fncall-ifs fn actuals x pathcond contexts clk obligs config
                                     bvar-db state)))

 (defun glcp-generic-interp-fncall-ifs
   (fn actuals x pathcond contexts clk obligs config bvar-db state)
   (declare (xargs
             :measure (list (pos-fix clk) 15 (g-ite-depth-sum actuals) 20)
             :guard (and (posp clk)
                         (symbolp fn)
                         (contextsp contexts)
                         (not (eq fn 'quote))
                         (true-listp actuals)
                         (acl2::interp-defs-alistp obligs)
                         (glcp-config-p config)
                         (acl2::interp-defs-alistp (glcp-config->overrides config)))
             :stobjs (bvar-db state)))
   (b* (((mv has-if test then-args else-args)
         (glcp-interp-args-split-ite actuals))
        ((when has-if)
         (b* ((hyp pathcond))
           (glcp-if
            test
            (glcp-generic-interp-fncall-ifs fn then-args x hyp contexts clk obligs config bvar-db state)
            (glcp-generic-interp-fncall-ifs fn else-args x hyp contexts clk obligs config bvar-db state)))))
     (glcp-generic-interp-fncall fn actuals x pathcond contexts clk obligs config bvar-db state)))


 (defun glcp-generic-interp-fncall
   (fn actuals x pathcond contexts clk obligs config bvar-db state)
   (declare (xargs
             :measure (list (pos-fix clk) 14 0 20)
             :guard (and (posp clk)
                         (symbolp fn)
                         (not (eq fn 'quote))
                         (true-listp actuals)
                         (contextsp contexts)
                         (acl2::interp-defs-alistp obligs)
                         (glcp-config-p config)
                         (acl2::interp-defs-alistp (glcp-config->overrides config)))
             :stobjs (bvar-db state)))
   (b* (((mv fncall-failed ans)
         (if (general-concrete-listp actuals)
             (acl2::magic-ev-fncall fn (general-concrete-obj-list actuals)
                                    state t nil)
           (mv t nil)))
        ((unless fncall-failed)
         (glcp-value (mk-g-concrete ans)))
        ((mv erp obligs successp term bindings bvar-db state)
         (glcp-generic-rewrite
          fn actuals :fncall pathcond contexts clk obligs config bvar-db state))
        ((when erp) (mv erp obligs nil bvar-db state))
        ((when successp)
         (glcp-generic-interp-term term bindings pathcond contexts (1- clk) obligs config bvar-db state))
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
                               pathcond contexts (1- clk)
                               obligs config bvar-db state)))

 (defun glcp-generic-interp-if (test tbr fbr alist pathcond contexts clk obligs
                                     config bvar-db state)
   (declare (xargs
             :measure (list (pos-fix clk) 20 (+ 1 (+ (acl2-count test)
                                                     (acl2-count tbr)
                                                     (acl2-count fbr))) 10)
             :verify-guards nil
             :guard (and (natp clk)
                         (pseudo-termp test)
                         (pseudo-termp tbr)
                         (pseudo-termp fbr)
                         (contextsp contexts)
                         (acl2::interp-defs-alistp obligs)
                         (glcp-config-p config)
                         (acl2::interp-defs-alistp (glcp-config->overrides config)))
             :stobjs (bvar-db state)))
   (b* ((orp (glcp-if-or-condition test tbr contexts))
        ((glcp-er test-obj)
         (glcp-generic-interp-term
          test alist pathcond
          ;; bozo do something smarter
          (glcp-if-test-contexts orp contexts)
          clk obligs config bvar-db state))
        ((glcp-er test-bfr)
         (glcp-generic-simplify-if-test test-obj pathcond clk obligs config bvar-db
                                        state))
        ((when orp)
         (glcp-generic-finish-or test-bfr test-obj fbr alist pathcond contexts
                                 clk obligs config bvar-db state)))
     (glcp-generic-finish-if test-bfr tbr fbr alist pathcond contexts clk
                             obligs config bvar-db state)))
 

 (defun glcp-generic-finish-or (test-bfr then-obj fbr alist pathcond contexts clk obligs
                                         config bvar-db state)
   (declare (xargs
             :measure (list (pos-fix clk) 20 (+ 1 (acl2-count fbr)) 8)
             :verify-guards nil
             :guard (and (natp clk)
                         (pseudo-termp fbr)
                         (contextsp contexts)
                         (acl2::interp-defs-alistp obligs)
                         (glcp-config-p config)
                         (acl2::interp-defs-alistp (glcp-config->overrides config)))
             :stobjs (bvar-db state)))
   
   (b* ((hyp pathcond)
        (else-hyp (hf (bfr-not test-bfr)))
        ((glcp-er else)
         (if else-hyp
             (let ((hyp (bfr-and hyp else-hyp)))
               (glcp-generic-interp-term
                fbr alist hyp contexts clk obligs config bvar-db state))
           (glcp-value nil))))
     (glcp-value (gobj-ite-merge test-bfr then-obj else hyp))))

 (defun glcp-generic-finish-if (test-bfr tbr fbr alist pathcond contexts clk
                                         obligs config bvar-db state)
   (declare (xargs
             :measure (list (pos-fix clk) 20 (+ 1 (acl2-count tbr)
                                                (acl2-count fbr)) 8)
             :verify-guards nil
             :guard (and (natp clk)
                         (pseudo-termp tbr)
                         (pseudo-termp fbr)
                         (contextsp contexts)
                         (acl2::interp-defs-alistp obligs)
                         (glcp-config-p config)
                         (acl2::interp-defs-alistp (glcp-config->overrides config)))
             :stobjs (bvar-db state)))
   (b* ((hyp pathcond)
        (then-hyp (hf test-bfr))
        (else-hyp (hf (bfr-not test-bfr)))
        ((glcp-er then)
         (if then-hyp
             (let ((hyp (bfr-and hyp then-hyp)))
               (glcp-generic-interp-term tbr alist hyp contexts
                                         clk obligs config bvar-db state))
           (glcp-value nil)))
        ((glcp-er else)
         (if else-hyp
             (let ((hyp (bfr-and hyp else-hyp)))
               (glcp-generic-interp-term fbr alist hyp contexts
                                         clk obligs config bvar-db state))
           (glcp-value nil))))
     (glcp-value (gobj-ite-merge test-bfr then else hyp))))

 ;; ;; BOZO glcp-or and glcp-if assume we're using the variable name HYP
 ;; ;; for pathcond
 ;; (if (hons-equal test tbr)
 ;;     (glcp-or
 ;;      test-obj
 ;;      (glcp-generic-interp-term fbr alist hyp clk obligs config bvar-db state))
 ;;   (glcp-if
 ;;    test-obj
 ;;    (glcp-generic-interp-term tbr alist hyp clk obligs config bvar-db state)
 ;;    (glcp-generic-interp-term fbr
 ;;                              alist hyp clk obligs config bvar-db state)))))

 ;; returns a glcp-value of a bfr
 (defun glcp-generic-simplify-if-test (test-obj pathcond clk obligs config bvar-db
                                                state)
   (declare (xargs
             :measure (list clk 18 (acl2-count test-obj) 10)
             :verify-guards nil
             :guard (and (natp clk)
                         (acl2::interp-defs-alistp obligs)
                         (glcp-config-p config)
                         (acl2::interp-defs-alistp (glcp-config->overrides config)))
             :stobjs (bvar-db state)))
   (if (atom test-obj)
       (glcp-value (and test-obj t))
     (pattern-match test-obj
       ((g-boolean bfr) (glcp-value bfr))
       ((g-number &) (glcp-value t))
       ((g-concrete v) (glcp-value (and v t)))
       ((g-var &)
        (b* (((mv bvar bvar-db) (add-term-bvar-unique test-obj bvar-db)))
          (glcp-value (bfr-to-param-space (glcp-config->param-bfr config)
                                          (bfr-var bvar)))))
       ((g-ite test then else)
        (b* ((hyp pathcond)
             ((glcp-er test-bfr) (glcp-generic-simplify-if-test
                                  test hyp clk obligs config bvar-db state))
             (then-hyp (hf test-bfr))
             (else-hyp (hf (bfr-not test-bfr)))
             ((glcp-er then-bfr)
              (if then-hyp
                  (let ((hyp (bfr-and hyp then-hyp)))
                    (glcp-generic-simplify-if-test
                     then hyp clk obligs config bvar-db state))
                (glcp-value nil)))
             ((glcp-er else-bfr)
              (if else-hyp
                  (let ((hyp (bfr-and hyp else-hyp)))
                    (glcp-generic-simplify-if-test
                     else hyp clk obligs config bvar-db state))
                (glcp-value nil))))
          (glcp-value (bfr-ite test-bfr then-bfr else-bfr))))
       ((g-apply fn args)
        (b* (((when (or (not (symbolp fn))
                        (eq fn 'quote)))
              (glcp-interp-error (acl2::msg "Non function symbol in g-apply: ~x0" fn)))
             ((when (zp clk))
              (glcp-interp-error "Clock ran out in simplify-if-test"))

             ((mv erp obligs successp term bindings bvar-db state)
              (glcp-generic-rewrite fn args :if-test pathcond '(iff) clk obligs config
                                    bvar-db state))
             ((when erp) (mv erp obligs nil bvar-db state))
             ((when successp)
              (b* (((glcp-er newterm)
                    (glcp-generic-interp-term term bindings pathcond '(iff)
                                              (1- clk) obligs config bvar-db
                                              state)))
                (glcp-generic-simplify-if-test newterm pathcond (1- clk) obligs
                                               config bvar-db state)))
             ((mv bvar bvar-db) (add-term-bvar-unique test-obj bvar-db)))
          (glcp-value (bfr-to-param-space (glcp-config->param-bfr config)
                                          (bfr-var bvar)))))
       (& ;; cons
        (glcp-value t)))))
 
 
 

 (defun glcp-generic-rewrite (fn actuals rwtype pathcond contexts clk obligs config bvar-db state)
   (declare (xargs :stobjs (bvar-db state)
                   :guard (and (posp clk)
                               (symbolp fn)
                               (not (eq fn 'quote))
                               (contextsp contexts)
                               (acl2::interp-defs-alistp obligs)
                               (glcp-config-p config)
                               (acl2::interp-defs-alistp
                                (glcp-config->overrides config)))
                   :measure (list (pos-fix clk) 12 0 0))
            (ignorable rwtype))
   
   ;; (mv erp obligs1 successp term bindings bvar-db state)
   (b* ((rules (cdr (hons-assoc-equal fn (table-alist 'gl-rewrite-rules (w state)))))
        ;; or perhaps we should pass the table in the obligs? see if this is
        ;; expensive
        ((unless (and rules (true-listp rules))) ;; optimization (important?)
         (mv nil obligs nil nil nil bvar-db state))
        (fn-rewrites (getprop fn 'acl2::lemmas nil 'current-acl2-world (w state))))
     (glcp-generic-rewrite-apply-rules
      fn-rewrites rules fn actuals pathcond contexts clk obligs config bvar-db state)))
 
 
 (defun glcp-generic-rewrite-apply-rules
   (fn-rewrites rules fn actuals pathcond contexts clk obligs config bvar-db state)
   (declare (xargs :stobjs (bvar-db state)
                   :guard (and (true-listp rules)
                               (posp clk)
                               (symbolp fn)
                               (not (eq fn 'quote))
                               (contextsp contexts)
                               (acl2::interp-defs-alistp obligs)
                               (glcp-config-p config)
                               (acl2::interp-defs-alistp
                                (glcp-config->overrides config)))
                   :measure (list (pos-fix clk) 8 (len fn-rewrites) 0)))
   (b* (((when (atom fn-rewrites))
         ;; no more rules, fail
         (mv nil obligs nil nil nil bvar-db state))
        (rule (car fn-rewrites))
        ((unless (acl2::weak-rewrite-rule-p rule))
         (cw "malformed rewrite rule?? ~x0~%" rule)
         (glcp-generic-rewrite-apply-rules
          (cdr fn-rewrites) rules fn actuals pathcond contexts clk obligs config bvar-db state))
        ((unless (member-equal (acl2::rewrite-rule->rune rule) rules))
         (glcp-generic-rewrite-apply-rules
          (cdr fn-rewrites) rules fn actuals pathcond contexts clk obligs config bvar-db state))
        ((mv erp obligs successp term bindings bvar-db state)
         (glcp-generic-rewrite-apply-rule
          rule fn actuals pathcond contexts clk obligs config bvar-db state))
        ((when erp)
         (mv erp obligs nil nil nil bvar-db state))
        ((when successp)
         (mv nil obligs successp term bindings bvar-db state)))
     (glcp-generic-rewrite-apply-rules
      (cdr fn-rewrites) rules fn actuals pathcond contexts clk obligs config bvar-db state)))

 (defun glcp-generic-rewrite-apply-rule
   (rule fn actuals pathcond contexts clk obligs config bvar-db state)
   (declare (xargs :stobjs (bvar-db state)
                   :guard (and (acl2::weak-rewrite-rule-p rule)
                               (posp clk)
                               (symbolp fn)
                               (not (eq fn 'quote))
                               (contextsp contexts)
                               (acl2::interp-defs-alistp obligs)
                               (glcp-config-p config)
                               (acl2::interp-defs-alistp
                                (glcp-config->overrides config)))
                   :measure (list (pos-fix clk) 4 0 0)))
   (b* (((rewrite-rule rule) rule)
        ((unless (and (symbolp rule.equiv)
                      (not (eq rule.equiv 'quote))
                      (or (eq rule.equiv 'equal)
                          ;; bozo check refinements
                          (member rule.equiv contexts))
                      ;; (ensure-equiv-relationp rule.equiv (w state))
                      (not (eq rule.subclass 'acl2::meta))
                      (pseudo-termp rule.lhs)
                      (consp rule.lhs)
                      (eq (car rule.lhs) fn)))
         (cw "malformed gl rewrite rule (lhs)?? ~x0~%" rule)
         (mv nil obligs nil nil nil bvar-db state))
        ((mv unify-ok gobj-bindings)
         (glcp-unify-term/gobj-list (cdr rule.lhs) actuals nil))
        ((unless unify-ok)
         (mv nil obligs nil nil nil bvar-db state))
        ((unless (pseudo-term-listp rule.hyps))
         (cw "malformed gl rewrite rule (hyps)?? ~x0~%" rule)
         (mv nil obligs nil nil nil bvar-db state))
        ((mv erp obligs hyps-ok gobj-bindings bvar-db state)
         (glcp-generic-relieve-hyps rule.hyps gobj-bindings pathcond clk obligs config bvar-db state))
        ((when erp)
         (mv erp obligs nil nil nil bvar-db state))
        ((unless hyps-ok)
         (mv nil obligs nil nil nil bvar-db state))
        ((unless (pseudo-termp rule.rhs))
         (cw "malformed gl rewrite rule (rhs)?? ~x0~%" rule)
         (mv nil obligs nil nil nil bvar-db state)))
     (mv nil obligs t rule.rhs gobj-bindings bvar-db state)))

 (defun glcp-generic-relieve-hyps (hyps bindings pathcond clk obligs config bvar-db state)
   (declare (xargs :stobjs (bvar-db state)
                   :guard (and (pseudo-term-listp hyps)
                               (posp clk)
                               (acl2::interp-defs-alistp obligs)
                               (glcp-config-p config)
                               (acl2::interp-defs-alistp
                                (glcp-config->overrides config)))
                   :measure (list (pos-fix clk) 2 (len hyps) 0)))
   (b* (((when (atom hyps))
         (mv nil obligs t bindings bvar-db state))
        ((mv erp obligs ok bindings bvar-db state)
         (glcp-generic-relieve-hyp (car hyps) bindings pathcond clk obligs
                                   config bvar-db state))
        ((when (or erp (not ok)))
         (mv erp obligs ok bindings bvar-db state)))
     (glcp-generic-relieve-hyps (cdr hyps) bindings pathcond clk obligs config
                                bvar-db state)))

 (defun glcp-generic-relieve-hyp (hyp bindings pathcond clk obligs config bvar-db state)
   (declare (xargs :stobjs (bvar-db state)
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
           (mv erp obligs successp bindings bvar-db state)))
        ((mv erp obligs val bvar-db state)
         (glcp-generic-interp-term hyp bindings pathcond '(iff) (1- clk) obligs config
                                   bvar-db state))
        ((when erp)
         (mv erp obligs nil nil bvar-db state))
        (test (gtests val pathcond))
        ((when (and (eq (gtests-nonnil test) t)
                    (eq (gtests-unknown test) nil)))
         (mv nil obligs t bindings bvar-db state)))
     (mv nil obligs nil bindings bvar-db state)))

 (defun glcp-generic-interp-list
   (x alist pathcond clk obligs config bvar-db state)
   (declare
    (xargs
     :measure (list (pos-fix clk) 20 (acl2-count x) 20)
     :guard (and (natp clk)
                 (pseudo-term-listp x)
                 (acl2::interp-defs-alistp obligs)
                 (glcp-config-p config)
                 (acl2::interp-defs-alistp (glcp-config->overrides config)))
     :stobjs (bvar-db state)))
   (if (atom x)
       (glcp-value nil)
     (b* (((glcp-er car)
           (glcp-generic-interp-term (car x)
                                     alist pathcond nil clk obligs config bvar-db state))
          ((glcp-er cdr)
           (glcp-generic-interp-list (cdr x)
                                     alist pathcond clk obligs config bvar-db state)))
       (glcp-value (cons car cdr))))))
||#
