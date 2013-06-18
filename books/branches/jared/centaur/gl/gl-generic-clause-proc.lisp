
(in-package "GL")


(include-book "param")
(include-book "gl-generic-interp-defs")
(local (include-book "gl-generic-interp"))
(include-book "gify")
(include-book "bfr-sat")

(include-book "misc/untranslate-patterns" :dir :system)
(include-book "data-structures/no-duplicates" :dir :system)
(include-book "clause-processors/use-by-hint" :dir :system)
(include-book "clause-processors/decomp-hint" :dir :system)
(include-book "centaur/misc/interp-function-lookup" :dir :system)

(local (include-book "general-object-thms"))
(local (include-book "centaur/misc/hons-sets" :dir :system))
(local (include-book "tools/with-quoted-forms" :dir :system))
(local (include-book "hyp-fix-logic"))
(local (in-theory (disable* sets::double-containment
                            w)))
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "clause-processors/find-matching" :dir :system))
(local (include-book "clause-processors/just-expand" :dir :system))

(local
 (defsection glcp-generic-geval
   (local (in-theory (enable glcp-generic-geval)))

   (acl2::def-functional-instance
    glcp-generic-geval-shape-spec-oblig-term-correct
    shape-spec-oblig-term-correct
    ((sspec-geval-ev glcp-generic-geval-ev)
     (sspec-geval-ev-lst glcp-generic-geval-ev-lst)
     (sspec-geval glcp-generic-geval))
    :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
                                glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
                               (glcp-generic-geval-apply))
              :expand ((:with glcp-generic-geval (glcp-generic-geval x env))))))

   (acl2::def-functional-instance
    glcp-generic-geval-gobj-to-param-space-correct
    gobj-to-param-space-correct
    ((generic-geval-ev glcp-generic-geval-ev)
     (generic-geval-ev-lst glcp-generic-geval-ev-lst)
     (generic-geval glcp-generic-geval))
    :hints ('(:in-theory (e/d* (glcp-generic-geval-ev-of-fncall-args
                                glcp-generic-geval-apply-agrees-with-glcp-generic-geval-ev)
                               (glcp-generic-geval-apply))
              :expand ((:with glcp-generic-geval (glcp-generic-geval x env))))))))


;; redundant but included only locally
(make-event
 (b* (((er &) (in-theory nil))
      ((er thm) (get-guard-verification-theorem 'glcp-generic-interp-term state)))
   (value
    `(defthm glcp-generic-interp-guards-ok
       ,thm
       :rule-classes nil))))


(defun strip-cadrs (x)
  (if (atom x)
      nil
    (cons (cadr (car x))
          (strip-cadrs (cdr x)))))


(mutual-recursion
 (defun collect-vars (x)
   (cond ((null x) nil)
         ((atom x) (list x))
         ((eq (car x) 'quote) nil)
         (t (collect-vars-list (cdr x)))))
 (defun collect-vars-list (x)
   (if (atom x)
       nil
     (union-equal (collect-vars (car x))
                  (collect-vars-list (cdr x))))))


(defun shape-spec-bindingsp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (equal x nil)
    (and (consp (car x))
         (symbolp (caar x))
         (not (keywordp (caar x)))
         (caar x)
         (consp (cdar x))
         (shape-specp (cadar x))
         (shape-spec-bindingsp (cdr x)))))


(defun gobj-alist-to-param-space (alist p)
  (if (atom alist)
      nil
    (cons (cons (caar alist) (gobj-to-param-space (cdar alist) p))
          (gobj-alist-to-param-space (cdr alist) p))))





(set-state-ok t)


(local
 (progn
   (defthm alistp-shape-specs-to-interp-al
     (alistp (shape-specs-to-interp-al x)))

   (defun norm-alist (vars alist)
     (if (atom vars)
         nil
       (let ((look (assoc-equal (car vars) alist)))
         (cons (cons (car vars) (cdr look))
               (norm-alist (cdr vars) alist)))))



   (defthm car-assoc-equal
     (equal (car (assoc-equal x a))
            (and (assoc-equal x a)
                 x)))

   (defthm assoc-equal-norm-alist
     (equal (cdr (assoc-equal v (norm-alist vars alist)))
            (and (member-equal v vars)
                 (cdr (assoc-equal v alist)))))

   (flag::make-flag collect-vars-flg collect-vars)

   (defthm subsetp-equal-union-equal
     (iff (subsetp-equal (union-equal a b) c)
          (and (subsetp-equal a c)
               (subsetp-equal b c)))
     :hints ((acl2::set-reasoning)))

   (defthm-collect-vars-flg
     glcp-generic-geval-ev-norm-alist-collect-vars-lemma
     (collect-vars
      (implies (and (pseudo-termp x)
                    (subsetp-equal (collect-vars x) vars))
               (equal (glcp-generic-geval-ev x (norm-alist vars alist))
                      (glcp-generic-geval-ev x alist)))
      :name glcp-generic-geval-ev-norm-alist-collect-vars1)
     (collect-vars-list
      (implies (and (pseudo-term-listp x)
                    (subsetp-equal (collect-vars-list x) vars))
               (equal (glcp-generic-geval-ev-lst x (norm-alist vars alist))
                      (glcp-generic-geval-ev-lst x alist)))
      :name glcp-generic-geval-ev-lst-norm-alist-collect-vars-list1)
     :hints (("goal" :induct (collect-vars-flg flag x)
              :in-theory (enable subsetp-equal))
             ("Subgoal *1/3"
              :in-theory (enable glcp-generic-geval-ev-of-fncall-args))))


        

   (encapsulate nil
     (local (defthm member-equal-second-revappend
              (implies (member-equal x b)
                       (member-equal x (revappend a b)))))
     (defthm member-equal-revappend
       (iff (member-equal x (revappend a b))
            (or (member-equal x a)
                (member-equal x b)))))

   (defthm revappend-set-equiv-union
     (acl2::set-equiv (revappend a b) (union-equal a b))
     :hints ((acl2::set-reasoning)))


   (defun gobj-alistp (x)
     (if (atom x)
         (equal x nil)
       (and (consp (car x))
            (symbolp (caar x))
            (not (keywordp (caar x)))
            (caar x)
            (gobj-alistp (cdr x)))))

   (defthm gobj-alistp-shape-specs-to-interp-al
     (implies (shape-spec-bindingsp x)
              (gobj-alistp (shape-specs-to-interp-al x)))
     :hints(("Goal" :in-theory (enable shape-specs-to-interp-al))))

   ;; (defthm gobj-listp-strip-cdrs
   ;;   (implies (gobj-alistp x)
   ;;            (gobj-listp (strip-cdrs x)))
   ;;   :hints(("Goal" :in-theory (enable strip-cdrs gobj-listp))))

   (defun gobj-strip-cdrs (x)
     (declare (xargs :guard (alistp x)))
     (if (atom x)
         nil
       (gl-cons (cdar x)
                (gobj-strip-cdrs (cdr x)))))

   (defthm gobj-listp-gobj-strip-cdrs
     (gobj-listp (gobj-strip-cdrs x)))

   (local (defthm cdr-of-gl-cons
            (equal (cdr (gl-cons x y)) y)
            :hints(("Goal" :in-theory (enable gl-cons)))))

   (local (defthm eval-car-of-gl-cons
            (equal (glcp-generic-geval (car (gl-cons x y)) env)
                   (glcp-generic-geval x env))
            :hints (("goal" :use ((:instance glcp-generic-geval-of-gl-cons)
                                  (:instance
                                   glcp-generic-geval-g-concrete-quote-correct
                                   (b env)))
                     :in-theory (e/d (gl-cons g-concrete-quote g-keyword-symbolp)
                                     (glcp-generic-geval-of-gl-cons
                                      glcp-generic-geval-g-concrete-quote-correct))))))

   (defthm glcp-generic-geval-alist-gobj-alistp
     (implies (alistp x)
              (equal (glcp-generic-geval-alist x env)
                     (pairlis$ (strip-cars x)
                               (glcp-generic-geval (gobj-strip-cdrs x) env))))
     :hints(("Goal" :in-theory (enable strip-cars glcp-generic-geval-alist))))

   (defthm strip-cdrs-shape-specs-to-interp-al
     (implies (shape-spec-bindingsp x)
              (equal (gobj-strip-cdrs (shape-specs-to-interp-al x))
                     (shape-spec-to-gobj (strip-cadrs x))))
     :hints(("Goal" :induct (len x)
             :expand ((:free (a b) (shape-spec-to-gobj (cons a b)))))))


   ;; (defthm gobject-alistp-gobj-alist-to-param-space
   ;;   (implies (gobject-alistp x)
   ;;            (gobject-alistp (gobj-alist-to-param-space x p))))

   (defthm strip-cars-gobj-alist-to-param-space
     (equal (strip-cars (gobj-alist-to-param-space x p))
            (strip-cars x)))

   (defthm gobj-to-param-space-of-gl-cons
     (equal (gobj-to-param-space (gl-cons a b) p)
            (gl-cons (gobj-to-param-space a p)
                     (gobj-to-param-space b p)))
     :hints(("Goal" :in-theory (enable gobj-to-param-space
                                       g-keyword-symbolp
                                       gl-cons tag)
             :expand ((:free (a b) (gobj-to-param-space (cons a b) p))))))

   (defthm strip-cdrs-gobj-alist-to-param-space
     (equal (gobj-strip-cdrs (gobj-alist-to-param-space x p))
            (gobj-to-param-space (gobj-strip-cdrs x) p))
     :hints(("Goal" :in-theory (enable strip-cdrs 
                                       gobj-to-param-space
                                       tag)
             :induct (gobj-alist-to-param-space x p)
             :expand ((:free (a b) (gobj-to-param-space (cons a b) p))))))

   (defthm alistp-gobj-alist-to-param-space
     (alistp (gobj-alist-to-param-space x p)))


   (defthm nonnil-symbol-listp-strip-cars-shape-spec-bindings
     (implies (shape-spec-bindingsp x)
              (nonnil-symbol-listp (strip-cars x)))
     :hints(("Goal" :in-theory (enable nonnil-symbol-listp))))


   (defthm shape-spec-listp-strip-cadrs
     (implies (shape-spec-bindingsp x)
              (shape-spec-listp (strip-cadrs x))))

   (defthm shape-specp-strip-cadrs-bindings
     (implies (shape-spec-bindingsp x)
              (shape-specp (strip-cadrs x)))
     :hints(("Goal" :in-theory (enable shape-specp tag)
             :induct (shape-spec-bindingsp x)
             :expand ((:free (a b) (shape-specp (cons a b)))))))))



(defun quote-if-needed (obj)
  (declare (xargs :mode :logic :guard t))
  (if (or (booleanp obj)
          (keywordp obj)
          (acl2-numberp obj)
          (characterp obj)
          (stringp obj))
      obj
    (list 'quote obj)))

(defun bindings-quote-if-needed (bindings)
  (declare (xargs :guard (true-list-listp bindings)))
  (if (atom bindings)
      nil
    (cons (list (caar bindings)
                (quote-if-needed (cadar bindings)))
          (bindings-quote-if-needed (cdr bindings)))))

(defun glcp-make-pretty-bindings (alist)
  (if (atom alist)
      nil
    (cons (list (caar alist) (quote-if-needed (cdar alist)))
          (glcp-make-pretty-bindings (cdr alist)))))


(defun max-max-max-depth (x)
  (if (atom x)
      0
    (max (acl2::max-max-depth (car x))
         (max-max-max-depth (cdr x)))))


;; Gets the maximum depth of a BDD in gobject X.
(defund gobj-max-depth (x)
  (if (atom x)
      0
    (pattern-match x
      ((g-concrete &) 0)
      ((g-boolean b) (max-depth b))
      ((g-number n) (max-max-max-depth n))
      ((g-ite if then else)
       (max (gobj-max-depth if)
            (max (gobj-max-depth then)
                 (gobj-max-depth else))))
      ((g-apply & args) (gobj-max-depth args))
      ((g-var &) 0)
      (& (max (gobj-max-depth (car x))
              (gobj-max-depth (cdr x)))))))

(defun max-list (x)
  (if (atom x)
      0
    (max (car x) (max-list (cdr x)))))

(defun max-list-list (x)
  (if (atom x)
      0
    (max (max-list (car x))
         (max-list-list (cdr x)))))

(defund inspec-max-index (x)
  (if (atom x)
      0
    (pattern-match x
      ((g-concrete &) 0)
      ((g-boolean b) b)
      ((g-number n) (max-list-list n))
      ((g-ite if then else)
       (max (inspec-max-index if)
            (max (inspec-max-index then)
                 (inspec-max-index else))))
      ((g-apply & args) (inspec-max-index args))
      ((g-var &) 0)
      (& (max (inspec-max-index (car x))
              (inspec-max-index (cdr x)))))))




(defun bool-to-bit (x)
  (cond ((eq x t) 1)
        ((eq x nil) 0)
        (t x)))


(defun nth-list-bits (x lst)
  (if (atom x)
      nil
    (cons (bool-to-bit (nth (car x) lst))
          (nth-list-bits (cdr x) lst))))

(defun nth-list-list-bits (x lst)
  (if (atom x)
      nil
    (cons (nth-list-bits (car x) lst)
          (nth-list-list-bits (cdr x) lst))))






;; To-satisfying-assign-spec generates the same satisfying assignment as
;; to-satisfying-assign given the same lst and bdd, except that when a
;; variable's value is irrelevant (car and cdr are equal), we put X in the list
;; instead of T or NIL.
(defun to-satisfying-assign-spec (lst bdd)
  (declare (xargs :hints (("goal" :in-theory (enable acl2-count)))))
  (cond ((atom bdd) lst)
        ((eq (cdr bdd) nil) (cons t (to-satisfying-assign-spec lst (car bdd))))
        ((eq (car bdd) nil) (cons nil (to-satisfying-assign-spec lst (cdr bdd))))
        ((hqual (car bdd) (cdr bdd))
         (cons 'x (to-satisfying-assign-spec (cdr lst) (car bdd))))
        (t (cons (car lst) (to-satisfying-assign-spec
                            (cdr lst)
                            (if (car lst) (car bdd) (cdr bdd)))))))




;; For each index N in an shape spec, this substitutes the Nth value found in
;; lst.  In the number case, it substitutes 1 and 0 for booleans.
(defund inspec-show-assign-spec (x lst)
  (if (atom x)
      x
    (pattern-match x
      ((g-concrete &) x)
      ((g-boolean b) (g-boolean (nth b lst)))
      ((g-number n) (g-number (nth-list-list-bits n lst)))
      ((g-ite if then else)
       (g-ite (inspec-show-assign-spec if lst)
              (inspec-show-assign-spec then lst)
              (inspec-show-assign-spec else lst)))
      ((g-apply fn args) (g-apply fn (inspec-show-assign-spec args lst)))
      ((g-var &) x)
      (& (cons (inspec-show-assign-spec (car x) lst)
               (inspec-show-assign-spec (cdr x) lst))))))



(include-book "centaur/misc/vecs-ints" :dir :system)


(defun n-satisfying-assigns-and-specs (n hyp-bdd bdd bound state)
  (if (zp n)
      (value nil)
    (b* (((mv rand state) (acl2::random$ (ash 1 bound) state))
         (lst (acl2::nat-to-v rand bound))
         ;; From when we passed in the unparametrized counterexample BDD:
;;          (assign (to-satisfying-assign lst bdd))
;;          (assign-spec (to-satisfying-assign-spec lst bdd))
         (assign (acl2::unparam-env hyp-bdd (to-satisfying-assign lst bdd)))
         (assign-spec (acl2::unparam-env hyp-bdd (to-satisfying-assign-spec lst bdd)))
         ((er rest) (n-satisfying-assigns-and-specs (1- n) hyp-bdd bdd bound state)))
      (value (cons (list* "generated randomly:" assign assign-spec) rest)))))

(defthm n-satisfying-assigns-does-not-fail
  (not (mv-nth 0 (n-satisfying-assigns-and-specs n hyp-bdd bdd bound state))))


(defun vars-onto-alist (vars val al)
  (if (atom vars)
      al
    (if (hons-get (car vars) al)
        (vars-onto-alist (cdr vars) val al)
      (vars-onto-alist (cdr vars) val (hons-acons (car vars) val al)))))

(defun glcp-gen-assignments (ctrex-info alist hyp-bdd n state)
  (if (and (bfr-mode) ;; AIG mode
           (bfr-counterex-mode)) ;; alist counterexample mode
      (b* ((al (acl2::aig-extract-iterated-assigns-alist hyp-bdd 10))
           ;; Careful: al is memoized so we can't steal it.
           (cex-alist (hons-shrink-alist (append al ctrex-info) nil)))
        (value (list (list "counterexample from SAT:"
                           (vars-onto-alist
                            ;; WRONG:
                            ;; Hmm, logically this isn't really well-typed,
                            ;; because alist consists of real g-objects whereas
                            ;; shape-spec-indices wants shape-specs.  But in the
                            ;; AIG case, parametrization doesn't do anything, so
                            ;; this works.  If we were to apply this in cases
                            ;; where alist was not generated by parametrizing a
                            ;; shape-spec-alist, this would need to be changed.

                            ;; Actually, parametrization gets rid of any AIG
                            ;; variables that are constrained to concrete values.
                            ;; So we need to reproduce the parametrized binding
                            ;; alist here.
                            (shape-spec-indices (strip-cdrs alist)) nil
                            cex-alist)))))
    (b* ((bound (inspec-max-index alist))
         ((er assigns) (n-satisfying-assigns-and-specs
                        (max 0 (- n 2)) hyp-bdd ctrex-info bound state))
         (nils (acl2::nat-to-v 0 bound))
         (ts (acl2::nat-to-v -1 bound)))
      (value (take n
                   (list* (list* "generated by assigning 0/NIL to all possible bits:"
                                 (acl2::unparam-env
                                  hyp-bdd
                                  (to-satisfying-assign nils ctrex-info))
                                 (acl2::unparam-env
                                  hyp-bdd
                                  (to-satisfying-assign-spec nils ctrex-info)))
                          (list* "generated by assigning 1/T to all possible bits:"
                                 (acl2::unparam-env
                                  hyp-bdd
                                  (to-satisfying-assign ts ctrex-info))
                                 (acl2::unparam-env
                                  hyp-bdd
                                  (to-satisfying-assign-spec ts ctrex-info)))
                          assigns))))))

(defthm glcp-gen-assignments-does-not-fail
  (not (mv-nth 0 (glcp-gen-assignments n hyp-bdd bdd bound state)))) 


(defun glcp-pretty-print-assignments (n ctrexes concl execp state)
  (declare (xargs :stobjs state
                  :guard (and (natp n)
                              (true-list-listp ctrexes)
                              (pseudo-termp concl))))
  (if (atom ctrexes)
      nil
    (b* (((list string assign-alist assign-spec-alist) (car ctrexes))
         (bindings (ec-call (bindings-quote-if-needed assign-alist)))
         (- (if (bfr-mode)
                (cw "Example ~x2, ~@0~%Assignment:~%~x1~%~%" string bindings n)
              (cw "Example ~x3, ~@0~%Template:~%~x1~%Assignment:~%~x2~%~%" string assign-spec-alist
                  bindings n)))
         ((unless execp)
          (glcp-pretty-print-assignments (1+ n) (cdr ctrexes) concl execp state))
         (- (cw "Running conclusion:~%"))
         ;; ((acl2::cmp concl-term)
         ;;  (acl2::translate-cmp 
         ;;   concl t t t 'glcp-print-ctrexamples (w state)
         ;;   (default-state-vars state)))

         ;; assign-alist is actually of the form
         ;; ((var0 val0) (var1 val1)...) --
         ;; change it to ((var0 . val0) (var1 . val1) ...)
         (alist (pairlis$ (acl2::alist-keys assign-alist)
                          (acl2::alist-keys (acl2::alist-vals assign-alist))))
         ((mv err val)
          (ec-call (acl2::magic-ev concl alist state t t)))
         ((when err)
          (cw "Failed to execute the counterexample: ~@0~%"
              (if (eq err t) "(t)" err)))
         (- (cw "Result: ~x0~%~%" val)))
      (glcp-pretty-print-assignments (1+ n) (cdr ctrexes) concl execp state))))

(defun glcp-print-ctrexamples (ctrexes warn-err type concl execp state)
  (declare (xargs :stobjs state
                  :guard (and (true-list-listp ctrexes)
                              (pseudo-termp concl))))
  (b* ((- (cw "
*** SYMBOLIC EXECUTION ~@0 ***: ~@1 found." warn-err type))
       (- (and ctrexes
               (if (and (bfr-mode)
                        (bfr-counterex-mode))
                   (cw "~%Showing the example produced by SAT.~%~%")
                 (cw "
Showing ~x0 examples. Each example consists of a template and a
concrete assignment.  The template shows a class of examples, and the
concrete assignment represents a specific example from that
class:~%~%" (len ctrexes))))))
    (glcp-pretty-print-assignments 1 ctrexes concl execp state)))

;; (defun glcp-counterexample-wormhole (ctrexes warn-err type concl execp)
;;   (wormhole
;;    'glcp-counterexample-wormhole
;;    '(lambda (whs) whs)
;;    nil
;;    `(b* (((er &)
;;           (glcp-print-ctrexamples
;;            ',ctrexes ',warn-err ',type ',concl ',execp state)))
;;       (value :q))
;;    :ld-prompt nil
;;    :ld-pre-eval-print nil
;;    :ld-post-eval-print nil
;;    :ld-verbose nil))


;; (in-theory (disable glcp-counterexample-wormhole))

(defun glcp-error-fn (msg state)
  (declare (xargs :guard t))
  (mv msg nil state))

(defmacro glcp-error (msg)
  `(glcp-error-fn ,msg state))

(add-macro-alias glcp-error glcp-error-fn)



(mutual-recursion
 (defun magicer-ev (x alist clk state hard-errp aokp)
   (declare (xargs :guard (and (natp clk)
                               (pseudo-termp x)
                               (symbol-alistp alist))
                   :well-founded-relation acl2::nat-list-<
                   :measure (list clk (acl2-count x))
                   :hints(("Goal" :in-theory (enable nfix)))
                   :verify-guards nil
                   :stobjs state))
   (cond ((not x) (mv nil nil))
         ((atom x)
          (mv nil (cdr (assoc-eq x alist))))
         ((eq (car x) 'quote) (mv nil (cadr x)))
         ((zp clk) (mv "clock ran out" nil))
         ((consp (car x))
          (b* (((mv err args)
                (magicer-ev-lst (cdr x) alist clk state hard-errp aokp))
               ((when err)
                (mv err nil))
               (new-alist (pairlis$ (cadar x) args)))
            (magicer-ev (caddar x) new-alist clk state hard-errp aokp)))
         ((eq (car x) 'if)
          (b* (((mv err test)
                (magicer-ev (cadr x) alist clk state hard-errp aokp))
               ((when err) (mv err nil)))
            (if test
                (magicer-ev (caddr x) alist clk state hard-errp aokp)
              (magicer-ev (cadddr x) alist clk state hard-errp aokp))))
         (t (b* (((mv err args)
                  (magicer-ev-lst (cdr x) alist clk state hard-errp aokp))
                 ((when err)
                  (mv err nil))
                 (fn (car x))
                 ((mv ev-err val)
                  (acl2::magic-ev-fncall fn args state hard-errp aokp))
                 ((unless ev-err) (mv nil val))
                 ((mv ok formals body) (acl2::fn-get-def fn state))
                 ((unless ok) (mv (acl2::msg
                                   "can't execute and no definition: ~x0 ~@1~%"
                                   fn (if (eq ev-err t) "" ev-err))
                                  nil)))
              (magicer-ev body (pairlis$ formals args) (1- clk) state hard-errp
                          aokp)))))

 (defun magicer-ev-lst (x alist clk state hard-errp aokp)
   (declare (xargs :guard (and (posp clk)
                               (pseudo-term-listp x)
                               (symbol-alistp alist))
                   :measure (list (pos-fix clk) (acl2-count x))
                   :stobjs state))
   (if (endp x)
       (mv nil nil)
     (b* (((mv err first) (magicer-ev (car x) alist clk state hard-errp aokp))
          ((when err) (mv err nil))
          ((mv err rest) (magicer-ev-lst (cdr x) alist clk state hard-errp aokp))
          ((when err) (mv err nil)))
       (mv nil (cons first rest))))))

(defun magic-geval (x env state)
  (declare (xargs :guard (consp env)
                  :stobjs state
                  :measure (acl2-count x)
                  :hints (("goal" :in-theory '(measure-for-geval atom)))))
  (if (atom x)
      ;; Every atom represents itself.
      (mv nil x)
    (pattern-match x

      ;; A Concrete is like an escape sequence; we take (cdr x) as a concrete
      ;; object even if it looks symbolic.
      ((g-concrete obj) (mv nil obj))

      ;; Boolean
      ((g-boolean bool) (mv nil (bfr-eval bool (car env))))

      ;; Number.  This is the hairy case.  Can represent all ACL2-NUMBERPs,
      ;; but naturals are more compact than integers, which are more compact
      ;; than rationals, which are more compact than complexes.  Denominators
      ;; are coerced to 1 if they evaluate to 0 -- ugly.
      ((g-number num)
       (b* (((mv real-num
                 real-denom
                 imag-num
                 imag-denom)
             (break-g-number num)))
         (flet ((uval (n env)
                      (v2n (bfr-eval-list n (car env))))
                (sval (n env)
                      (v2i (bfr-eval-list n (car env)))))
           (mv nil (components-to-number (sval real-num env)
                                         (uval real-denom env)
                                         (sval imag-num env)
                                         (uval imag-denom env))))))

      ;; If-then-else.
      ((g-ite test then else)
       (b* (((mv err test) (magic-geval test env state))
            ((unless err)
             (if test
                 (magic-geval then env state)
               (magic-geval else env state))))
         (mv err nil)))

      ;; Apply: Unevaluated function call.
      ((g-apply fn args)
       (b* (((mv err args) (magic-geval args env state))
            ((when err) (mv err nil))
            (term (cons fn (ec-call (kwote-lst args)))))
         (mv-let (err val)
           (ec-call (magicer-ev term nil 10000 state t t))
           (if err
               (mv err nil)
             (mv nil val)))))
      
      ;; Var: untyped variable.
      ((g-var name)   (mv nil (cdr (het name (cdr env)))))

      ;; Conses where the car is not a recognized flag represent conses.
      (& (b* (((mv err car) (magic-geval (car x) env state))
              ((when err) (mv err nil))
              ((mv err cdr) (magic-geval (cdr x) env state))
              ((when err) (mv err nil)))
           (mv nil (cons car cdr)))))))



(defun glcp-bit-to-obj-ctrexamples (assigns sspec-alist gobj-alist state)
  (declare (xargs :stobjs state))
  (if (atom assigns)
      nil
    (if (or (atom (car assigns))
            (atom (cdar assigns)))
        (glcp-bit-to-obj-ctrexamples (cdr assigns) sspec-alist gobj-alist state)
      (cons (list (caar assigns)
                  (mv-let (err val)
                    (magic-geval gobj-alist (list (cadar assigns)) state)
                    (if err
                        :unknown
                      val))
                  (ec-call (inspec-show-assign-spec sspec-alist (cddar assigns))))
            (glcp-bit-to-obj-ctrexamples (cdr assigns) sspec-alist gobj-alist state)))))

(defun glcp-gen-ctrexes (ctrex-info alist hyp-bdd n state)
  (declare (xargs :stobjs state :verify-guards nil))
  (b* (((er assigns) (glcp-gen-assignments ctrex-info alist hyp-bdd n state)))
    (value (glcp-bit-to-obj-ctrexamples assigns alist (shape-spec-to-gobj
                                                       alist) state))))

(defthm glcp-gen-ctrexes-does-not-fail
  (not (mv-nth 0 (glcp-gen-ctrexes n hyp-bdd bdd bound state)))
  :hints(("Goal" :in-theory (disable glcp-gen-assignments))))

(in-theory (disable glcp-gen-ctrexes))

(defun glcp-analyze-interp-result (val al hyp-bdd id concl config state)
  (b* (((glcp-config config) config)
       (test (gtests val t))
       (hyp-param (bfr-to-param-space hyp-bdd hyp-bdd))
       (unk (bfr-and hyp-param (gtests-unknown test)))
       (false (bfr-and hyp-param
                       (bfr-not (gtests-unknown test))
                       (bfr-not (gtests-nonnil test))))
       (state (acl2::f-put-global 'glcp-var-bindings al state))
       (state (acl2::f-put-global 'glcp-counterex false state))
       (state (acl2::f-put-global 'glcp-indeterminate unk state))
       ((mv false-sat false-succ false-ctrex) (bfr-sat false))
       ((when (and false-sat false-succ))
        (b* (((er ctrexes) (glcp-gen-ctrexes
                            false-ctrex al hyp-bdd config.nexamples state))
             (state (acl2::f-put-global 'glcp-counterex-assignments
                                        ctrexes state)))
          (prog2$ (glcp-print-ctrexamples
                   ctrexes "ERROR" "Counterexamples"
                   concl config.exec-ctrex state)
                  (if config.abort-ctrex
                      (glcp-error
                       (acl2::msg "~
~x0: Counterexamples found in ~@1; aborting~%" config.clause-proc-name id))
                    (value (list ''nil))))))
       ;; False was either unsat or the check failed.  Either way we check unknown.
       ((mv unk-sat unk-succ unk-ctrex) (bfr-sat unk))
       ((when (and unk-sat unk-succ))
        (b* (((er ctrexes) (glcp-gen-ctrexes
                            unk-ctrex al hyp-bdd config.nexamples state))
             (state (acl2::f-put-global 'glcp-indeterminate-assignments
                                        ctrexes state)))
          (prog2$ (glcp-print-ctrexamples
                   ctrexes (if config.abort-unknown "ERROR" "WARNING")
                   "Indeterminate results" concl config.exec-ctrex state)
                  (if config.abort-unknown
                      (glcp-error
                       (acl2::msg "~
~x0: Indeterminate results found in ~@1; aborting~%"
                                  config.clause-proc-name id))
                    (value (list ''nil))
                    ;; NOTE: We used to produce the following clause when an
                    ;; unknown result was encountered, giving the user the chance
                    ;; to prove that the resulting symbolic object actually
                    ;; represented something constant-true.  But this seems
                    ;; impractical, and it requires that the evaluator used to
                    ;; prove the clause processor correct recognize geval, which
                    ;; causes soundness problems regarding bfr-mode attachment,
                    ;; because we're producing a term whose meaning depends on
                    ;; the current bfr-mode.  A fix might be to create separate
                    ;; geval functions for the separate bfr modes and put down
                    ;; whichever matches the current bfr mode.
                    ;; 
                    ;; (value `((not (gl-cp-hint 'result))
                    ;;          (,geval-name ',val env)))
                    ))))
       ((when (and false-succ unk-succ))
        ;; Both checks succeeded and were UNSAT, so the theorem is proved
        ;; (modulo side-goals).
        (value (list ''t))))
    ;; One or both of the SAT checks failed.
    (if config.abort-unknown
        (glcp-error
         (acl2::msg "~ ~x0: SAT check failed in ~@1; aborting~%"
                    config.clause-proc-name id))
      (value (list ''nil))
      ;; NOTE: See above comment about soundness problems with
      ;; geval/bfr-mode/attachment.
;;       (value `((not (gl-cp-hint 'result))
;;                (,geval-name ',val env)))
      )))

(local
 (encapsulate nil
   (local (defthm equal-of-cons
            (equal (equal (cons a b) c)
                   (and (consp c)
                        (equal a (car c))
                        (equal b (cdr c))))))
   (defthm glcp-analyze-interp-result-irrelevant
     (and (implies (syntaxp (not (and (equal al ''nil)
                                      (equal concl ''nil)
                                      (equal st ''nil))))
                   (and (equal (mv-nth 0 (glcp-analyze-interp-result
                                          val al hyp-bdd id concl config st))
                               (mv-nth 0 (glcp-analyze-interp-result
                                          val nil hyp-bdd id nil config nil)))
                        (equal (mv-nth 1 (glcp-analyze-interp-result
                                          val al hyp-bdd id concl config st))
                               (mv-nth 1 (glcp-analyze-interp-result
                                          val nil hyp-bdd id nil config nil)))))
          ;; (implies (syntaxp (not (and (equal al ''nil)
          ;;                             (equal concl ''nil)
          ;;                             (equal st ''nil))))
          ;;          (equal (mv-nth 1 (glcp-analyze-interp-result
          ;;                            val al hyp-bdd id concl config st))
          ;;                 (mv-nth 1 (glcp-analyze-interp-result
          ;;                            val nil hyp-bdd abort-unknown abort-ctrex nil nil
          ;;                            geval-name nil nil nil nil))))
          )
     :hints(("Goal" :in-theory '(glcp-analyze-interp-result
                                 glcp-gen-ctrexes-does-not-fail
                                 glcp-error))))))


(local
 (defthm glcp-analyze-interp-result-correct
   (implies (and (not (glcp-generic-geval val (cdr (assoc-equal 'env alist))))
                 (bfr-eval (bfr-to-param-space hyp-bdd hyp-bdd)
                           (car (cdr (assoc-equal 'env alist)))))
            (not (glcp-generic-geval-ev
                  (disjoin
                   (mv-nth 1 (glcp-analyze-interp-result
                              val al hyp-bdd id concl config state)))
                  alist)))
   :hints (("goal" :use
            ((:instance glcp-generic-geval-gtests-nonnil-correct
                        (x val) (hyp t)
                        (env (cdr (assoc-equal 'env alist))))
             (:instance
              bfr-sat-unsat
              (prop (bfr-and (bfr-to-param-space hyp-bdd hyp-bdd)
                             (bfr-not (gtests-unknown (gtests val t)))
                             (bfr-not (gtests-nonnil (gtests val t)))))
              (env (cadr (assoc-equal 'env alist))))
             (:instance
              bfr-sat-unsat
              (prop (bfr-and (bfr-to-param-space hyp-bdd hyp-bdd)
                             (gtests-unknown (gtests val t))))
              (env (cadr (assoc-equal 'env alist)))))
            :in-theory (e/d (gl-cp-hint)
                            (glcp-generic-geval-gtests-nonnil-correct
                             gtests-nonnil-correct
                             bfr-sat-unsat))
            :do-not-induct t)
           (bfr-reasoning))
   :otf-flg t))

(defthm w-of-read-acl2-oracle
  (equal (w (mv-nth 2 (read-acl2-oracle state)))
         (w state))
  :hints(("Goal" :in-theory (enable w read-acl2-oracle
                                    get-global
                                    update-acl2-oracle))))

(local
 (defthm w-state-of-n-satisfying-assigns-and-specs
   (equal (w (mv-nth 2 (n-satisfying-assigns-and-specs
                        n  hyp-bdd ctrex-info max-index state)))
          (w state))
   :hints(("Goal" :in-theory (enable random$)))))

(local
 (defthm w-state-of-glcp-gen-assignments
   (equal (w (mv-nth 2 (glcp-gen-assignments ctrex-info alist hyp-bdd n
                                             state)))
          (w state))))

(local
 (defthm w-state-of-glcp-gen-ctrexes
   (equal (w (mv-nth 2 (glcp-gen-ctrexes ctrex-info alist hyp-bdd n
                                             state)))
          (w state))
   :hints(("Goal" :in-theory (enable glcp-gen-ctrexes)))))

(local (in-theory (disable w put-global)))

(local
 (defthm w-state-of-glcp-analyze-interp-result
   (equal (w (mv-nth 2 (glcp-analyze-interp-result
                        val al hyp-bdd id concl config state)))
          (w state))
   :hints(("Goal" :in-theory (enable glcp-analyze-interp-result)))))

(local
 (defthm glcp-analyze-interp-result-pseudo-term-listp
   (pseudo-term-listp
    (mv-nth 1 (glcp-analyze-interp-result
               val al hyp-bdd id concl config state)))))

(in-theory (disable glcp-analyze-interp-result))

(local
 (progn
   (defun gobj-list-to-param-space (list p)
     (if (atom list)
         nil
       (gl-cons (gobj-to-param-space (car list) p)
             (gobj-list-to-param-space (cdr list) p))))


   (defthm glcp-generic-geval-alist-gobj-alist-to-param-space
     (equal (glcp-generic-geval-alist
             (gobj-alist-to-param-space alist p)
             env)
            (pairlis$ (strip-cars alist)
                      (glcp-generic-geval
                       (gobj-to-param-space (gobj-strip-cdrs alist) p)
                       env)))
     :hints(("Goal" :in-theory (enable strip-cdrs))))))




   ;; ;; (defthmd gobject-listp-gobj-to-param-space
   ;; ;;   (implies (gobject-listp lst)
   ;; ;;            (gobject-listp (gobj-to-param-space lst p)))
   ;; ;;   :hints(("Goal" :in-theory (enable gobj-to-param-space tag
   ;; ;;                                     gobject-listp))))

   ;; (defthmd gobj-list-to-param-space-when-gobject-listp
   ;;   (implies (gobject-listp lst)
   ;;            (equal (gobj-list-to-param-space lst p)
   ;;                   (gobj-to-param-space lst p)))
   ;;   :hints(("Goal" :in-theory (enable gobj-to-param-space
   ;;                                     gobject-listp tag))))

   ;; (defthmd glcp-generic-geval-lst-to-glcp-generic-geval
   ;;   (implies (gobject-listp x)
   ;;            (equal (glcp-generic-geval-lst x env)
   ;;                   (glcp-generic-geval x env)))
   ;;   :hints(("Goal" :in-theory (enable glcp-generic-geval-of-gobject-list))))

   ;; (defthm gobj-list-to-param-space-eval-env-for-glcp-generic-geval-lst
   ;;   (implies (and (gobject-listp x)
   ;;                 (bfr-eval p (car env)))
   ;;            (equal (glcp-generic-geval-lst
   ;;                    (gobj-list-to-param-space x p)
   ;;                    (genv-param p env))
   ;;                   (glcp-generic-geval-lst x env)))
   ;;   :hints (("goal" :use
   ;;            glcp-generic-geval-gobj-to-param-space-correct
   ;;            :in-theory (enable gobject-listp-gobj-to-param-space
   ;;                               gobj-list-to-param-space-when-gobject-listp
   ;;                               glcp-generic-geval-lst-to-glcp-generic-geval
   ;;                               gobject-listp-impl-gobjectp))))

   ;; (defthm gobj-list-to-param-space-eval-env-for-glcp-generic-geval-lst
   ;;   (implies (and (gobj-listp x)
   ;;                 (bfr-eval p (car env)))
   ;;            (equal (glcp-generic-geval-lst
   ;;                    (gobj-list-to-param-space x p)
   ;;                    (genv-param p env))
   ;;                   (glcp-generic-geval-lst x env)))
   ;;   :hints (("goal" :use
   ;;            glcp-generic-geval-gobj-to-param-space-correct
   ;;            :in-theory (enable gobject-listp-gobj-to-param-space
   ;;                               gobj-list-to-param-space-when-gobject-listp
   ;;                               glcp-generic-geval-lst-to-glcp-generic-geval
   ;;                               gobject-listp-impl-gobjectp))))

(defthm strip-cars-shape-specs-to-interp-al
  (equal (strip-cars (shape-specs-to-interp-al al))
         (strip-cars al))
  :hints(("Goal" :in-theory (enable shape-specs-to-interp-al))))

(defun preferred-defs-to-overrides (alist state)
  (declare (xargs :stobjs state :guard t))
  (if (atom alist)
      (value nil)
    (b* (((when (atom (car alist)))
          (preferred-defs-to-overrides (cdr alist) state))
         ((cons fn defname) (car alist))
         ((unless (and (symbolp fn) (symbolp defname)))
          (glcp-error
           (acl2::msg "~
The GL preferred-defs table contains an invalid entry ~x0.
The key and value of each entry should both be symbols."
                      (car alist))))
         (rule (ec-call (fgetprop defname 'theorem nil (w state))))
         ((unless rule)
          (glcp-error
           (acl2::msg "~
The preferred-defs table contains an invalid entry ~x0.
The :definition rule ~x1 was not found in the ACL2 world."
                      (car alist) defname)))
         ((unless (case-match rule
                    (('equal (rulefn . &) &) (equal fn rulefn))))
          (glcp-error
           (acl2::msg "~
The preferred-defs table contains an invalid entry ~x0.
The :definition rule ~x1 is not suitable as a GL override.
Either it is a conditional definition rule, it uses a non-EQUAL
equivalence relation, or its format is unexpected.  The rule
found is ~x2." (car alist) defname rule)))
         (formals (cdadr rule))
         (body (caddr rule))
         ((unless (and (nonnil-symbol-listp formals)
                       (acl2::no-duplicatesp formals)))
          (glcp-error
           (acl2::msg "~
The preferred-defs table contains an invalid entry ~x0.
The formals used in :definition rule ~x1 either are not all
variable symbols or have duplicates, making this an unsuitable
definition for use in a GL override.  The formals listed are
~x2." (car alist) defname formals)))
         ((unless (pseudo-termp body))
          (glcp-error
           (acl2::msg "~
The preferred-defs table contains an invalid entry ~x0.
The definition body, ~x1, is not a pseudo-term."
                      (car alist) body)))
         ((er rest) (preferred-defs-to-overrides (cdr alist) state)))
      (value (hons-acons fn (list* formals body defname)
                         rest)))))


(local
 (defthm interp-defs-alistp-preferred-defs-to-overrides
   (mv-let (erp overrides state)
     (preferred-defs-to-overrides alist state)
     (declare (ignore state))
     (implies (not erp)
              (acl2::interp-defs-alistp overrides)))
   :hints(("Goal" :in-theory
           (e/d (acl2::interp-defs-alistp)
                (fgetprop
                 pseudo-term-listp
                 pseudo-term-listp-cdr
                 pseudo-termp-car true-listp))))))

(in-theory (disable preferred-defs-to-overrides))

;; A version of ACL2's dumb-negate-lit that behaves logically wrt an evaluator.
(defun dumb-negate-lit (term)
  (cond ((null term) ''t)
        ((atom term) `(not ,term))
        ((eq (car term) 'quote)
         (acl2::kwote (not (cadr term))))
        ((eq (car term) 'not)
         (cadr term))
        ((eq (car term) 'equal)
         (cond ((or (eq (cadr term) nil)
                    (equal (cadr term) ''nil))
                (caddr term))
               ((or (eq (caddr term) nil)
                    (equal (caddr term) ''nil))
                (cadr term))
               (t `(not ,term))))
        (t `(not ,term))))

(local
 (progn
   (defthm glcp-generic-geval-ev-dumb-negate-lit
     (iff (glcp-generic-geval-ev (dumb-negate-lit lit) a)
          (not (glcp-generic-geval-ev lit a))))


   (defthm glcp-generic-geval-ev-list*-macro
     (equal (glcp-generic-geval-ev (list*-macro (append x (list ''nil))) al)
            (glcp-generic-geval-ev-lst x al))
     :hints(("Goal" :in-theory (enable append))))


   (defthm pairlis-eval-alist-is-norm-alist
     (implies (nonnil-symbol-listp vars)
              (equal (pairlis$ vars
                               (glcp-generic-geval-ev-lst vars alist))
                     (norm-alist vars alist)))
     :hints(("Goal" :in-theory (enable nonnil-symbol-listp
                                       pairlis$))))



   (defthmd glcp-generic-geval-ev-disjoin-is-or-list-glcp-generic-geval-ev-lst
     (iff (glcp-generic-geval-ev (disjoin lst) env)
          (acl2::or-list (glcp-generic-geval-ev-lst lst env)))
     :hints (("goal" :induct (len lst))))

   (defthm glcp-generic-geval-ev-disjoin-norm-alist
     (implies (and (pseudo-term-listp clause)
                   (subsetp-equal (collect-vars-list clause) vars))
              (iff (glcp-generic-geval-ev (disjoin clause) (norm-alist vars alist))
                   (glcp-generic-geval-ev (disjoin clause) alist)))
     :hints(("Goal" :in-theory (enable
                                glcp-generic-geval-ev-disjoin-is-or-list-glcp-generic-geval-ev-lst))))))




(make-event
 (sublis *glcp-generic-template-subst* *glcp-run-parametrized-template*))

(local (progn
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;          (defthm member-eq-is-member-equal
;            (equal (member-eq x y) (member-equal x y)))
;          
;          (defthm set-difference-eq-is-set-difference-equal
;            (equal (set-difference-eq x y) (set-difference-equal x y))
;            :hints(("Goal" :in-theory (enable set-difference-equal))))

         (defthm set-difference-equal-to-subsetp-equal-iff
           (iff (set-difference-equal x y)
                (not (subsetp-equal x y)))
           :hints(("Goal" :in-theory (enable set-difference-equal subsetp-equal))))))



(local 
 (encapsulate nil
   (local (defthm true-listp-when-nat-listp
            (implies (nat-listp x)
                     (true-listp x))
            :hints(("Goal" :in-theory (enable nat-listp)))))

   (defun shape-spec-bindings-indices (x)
     (declare (xargs :guard (shape-spec-bindingsp x)))
     (if (atom x)
         nil
       (append (shape-spec-indices (cadar x))
               (shape-spec-bindings-indices (cdr x)))))

   (defun shape-spec-bindings-vars (x)
     (declare (xargs :guard (shape-spec-bindingsp x)))
     (if (atom x)
         nil
       (append (shape-spec-vars (cadar x))
               (shape-spec-bindings-vars (cdr x)))))))

;; (defthm eval-of-shape-spec-to-interp-al-alist
;;   (implies (and (shape-spec-bindingsp bindings)
;;                 (no-duplicatesp (shape-spec-bindings-indices bindings))
;;                 (no-duplicatesp (shape-spec-bindings-vars bindings)))
;;            (equal (glcp-generic-geval-alist
;;                    (shape-specs-to-interp-al bindings)
;;                    (shape-spec-to-env (strip-cadrs bindings)
;;                                       (glcp-generic-geval-ev-lst (strip-cars bindings)
;;                                                       alist)))
;;                   (pairlis$ (strip-cars bindings)
;;                             (glcp-generic-geval-ev-lst (strip-cars bindings) alist))))
;;   hie)

;;                 ((GLCP-GENERIC-GEVAL-ALIST
;;    (SHAPE-SPECS-TO-INTERP-AL BINDINGS)
;;    (SHAPE-SPEC-TO-ENV (STRIP-CADRS BINDINGS)
;;                       (GLCP-GENERIC-GEVAL-EV-LST (STRIP-CARS BINDINGS)
;;                                       ALIST)))


(local
 (encapsulate nil
   ;; (defthm bfr-p-bfr-to-param-space
   ;;   (implies (and (bfr-p p) (bfr-p x))
   ;;            (bfr-p (bfr-to-param-space p x)))
   ;;   :hints(("Goal" :in-theory (enable bfr-to-param-space bfr-p))))


   (local (in-theory (disable shape-specs-to-interp-al
                              pseudo-termp pseudo-term-listp
                              glcp-generic-interp-term-ok-obligs
                              shape-spec-bindingsp
                              acl2::consp-by-len
                              list*-macro)))

   (encapsulate nil
     (local (in-theory
             (e/d (gl-cp-hint)
                  (shape-specs-to-interp-al
                   shape-spec-listp pseudo-term-listp
                   pseudo-termp pairlis$
                   shape-spec-bindingsp
                   dumb-negate-lit
                   gtests-nonnil-correct
                   no-duplicatesp-equal
                   (bfr-to-param-space)
                   gobj-alist-to-param-space
                   list*-macro binary-append strip-cadrs strip-cars member-equal))))
     (defthm glcp-generic-run-parametrized-correct
       (b* (((mv erp (cons clauses out-obligs) &)
             (glcp-generic-run-parametrized
              hyp concl  vars bindings id obligs
              config state)))
         (implies (and (not (glcp-generic-geval-ev concl alist))
                       (glcp-generic-geval-ev-theoremp
                        (conjoin-clauses
                         (acl2::interp-defs-alist-clauses out-obligs)))
                       (not erp)
                       (glcp-generic-geval-ev hyp alist)
                       (acl2::interp-defs-alistp obligs)
                       (acl2::interp-defs-alistp (glcp-config->overrides config))
                       (pseudo-termp concl)
                       (pseudo-termp hyp)
                       (equal vars (collect-vars concl))
                       (glcp-generic-geval-ev-meta-extract-global-facts :state state1)
                       (equal (w state) (w state1)))
                  (not (glcp-generic-geval-ev-theoremp (conjoin-clauses clauses)))))
       :hints (("goal" :do-not-induct
                t
                :in-theory
                (e/d* ()
                      (glcp-generic-geval-alist-gobj-alist-to-param-space
                       glcp-generic-geval-gtests-nonnil-correct
                       glcp-generic-interp-bad-obligs-term
                       ;; shape-spec-listp-impl-shape-spec-to-gobj-list
                       (:rules-of-class :definition :here)
                       (:rules-of-class :type-prescription :here))
                      (gl-cp-hint acl2::clauses-result assoc-equal
                                  glcp-generic-run-parametrized not
                                  glcp-error
                                  acl2::fast-no-duplicatesp
                                  acl2::fast-no-duplicatesp-equal))
                :restrict ((glcp-generic-geval-ev-disjoin-append ((a alist)))))
               (and stable-under-simplificationp
                    (acl2::bind-as-in-definition
                     (glcp-generic-run-parametrized
                      hyp concl  (collect-vars concl) bindings id obligs config state)
                     (cov-clause val-clause hyp-bdd hyp-val)
                     (b* ((binding-env
                           '(let ((slice (glcp-generic-geval-ev
                                          (shape-spec-env-term
                                           (strip-cadrs bindings)
                                           (list*-macro (append (strip-cars
                                                                 bindings) '('nil)))
                                           nil)
                                          alist)))
                              (cons (slice-to-bdd-env (car slice) nil)
                                    (cdr slice))))
                          (param-env `(genv-param ,hyp-bdd ,binding-env)))
                       `(:use
                         ((:instance glcp-generic-geval-ev-falsify
                                     (x (disjoin ,cov-clause))
                                     (a alist))
                          (:instance glcp-generic-geval-ev-falsify
                                     (x (disjoin ,val-clause))
                                     (a `((env . ,,param-env))))
                          (:instance glcp-generic-geval-gtests-nonnil-correct
                                     (x ,hyp-val)
                                     (hyp t)
                                     (env ,binding-env)))))))
               (bfr-reasoning))))

   (defthm glcp-generic-run-parametrized-bad-obligs
     (b* (((mv erp (cons & out-obligs) &)
           (glcp-generic-run-parametrized
            hyp concl  vars bindings id obligs config state)))
       (implies (and (not erp)
                     (not (glcp-generic-geval-ev-theoremp
                           (conjoin-clauses
                            (acl2::interp-defs-alist-clauses obligs)))))
                (not (glcp-generic-geval-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs)))))))

   (defthm glcp-generic-run-parametrized-ok-obligs
     (b* (((mv erp (cons & out-obligs) &)
           (glcp-generic-run-parametrized
            hyp concl  vars bindings id obligs config state)))
       (implies (and (not erp)
                     (glcp-generic-geval-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs))))
                (glcp-generic-geval-ev-theoremp
                 (conjoin-clauses
                  (acl2::interp-defs-alist-clauses obligs))))))

   (defthm glcp-generic-run-parametrized-defs-alistp
     (b* (((mv erp (cons & out-obligs) &)
           (glcp-generic-run-parametrized
            hyp concl  vars bindings id obligs config state)))
       (implies (and (acl2::interp-defs-alistp obligs)
                     (acl2::interp-defs-alistp (glcp-config->overrides config))
                     (pseudo-termp concl)
                     (not erp))
                (acl2::interp-defs-alistp out-obligs))))

   (defthm glcp-generic-run-paremetrized-w-state
     (equal (w (mv-nth 2 (glcp-generic-run-parametrized
                          hyp concl  vars bindings id obligs config state)))
            (w state)))))


(in-theory (disable glcp-generic-run-parametrized))

(defun glcp-cases-wormhole (term id)
  (wormhole 'glcp-cases-wormhole
            '(lambda (whs) whs)
            nil
            `(prog2$ (let ((id ',id))
                       (declare (ignorable id))
                       ,term)
                     (value :q))
            :ld-prompt nil
            :ld-pre-eval-print nil
            :ld-post-eval-print nil
            :ld-verbose nil))

(in-theory (disable glcp-cases-wormhole))



(make-event
 (sublis *glcp-generic-template-subst* *glcp-run-cases-template*))

(local
 (encapsulate nil
   (local (in-theory (disable pseudo-termp
                              acl2::consp-by-len
                              shape-spec-bindingsp
                              nonnil-symbol-listp-pseudo-term-listp)))

   (defthm glcp-generic-run-cases-interp-defs-alistp
     (b* (((mv erp (cons & out-obligs) &)
           (glcp-generic-run-cases
            param-alist concl  vars obligs config state)))
       (implies (and (acl2::interp-defs-alistp obligs)
                     (acl2::interp-defs-alistp (glcp-config->overrides config))
                     (pseudo-termp concl)
                     (not erp))
                (acl2::interp-defs-alistp out-obligs))))


   (defthm glcp-generic-run-cases-ok-w-state
     (equal (w (mv-nth 2 (glcp-generic-run-cases
                          param-alist concl  vars obligs config
                          state)))
            (w state)))

   (defthm glcp-generic-run-cases-correct
     (b* (((mv erp (cons clauses out-obligs) &)
           (glcp-generic-run-cases
            param-alist concl  vars obligs config state)))
       (implies (and (glcp-generic-geval-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs)))
                     (not (glcp-generic-geval-ev concl a))
                     (glcp-generic-geval-ev (disjoin (strip-cars param-alist))
                                      a)
                     (not erp)
                     (acl2::interp-defs-alistp obligs)
                     (acl2::interp-defs-alistp (glcp-config->overrides config))
                     (pseudo-termp concl)
                     (pseudo-term-listp (strip-cars param-alist))
                     (equal vars (collect-vars concl))
                     (glcp-generic-geval-ev-meta-extract-global-facts :state state1)
                     (equal (w state) (w state1)))
                (not (glcp-generic-geval-ev-theoremp (conjoin-clauses clauses))))))


   (defthm glcp-generic-run-cases-bad-obligs
     (b* (((mv erp (cons & out-obligs) &)
           (glcp-generic-run-cases
            param-alist concl  vars obligs config state)))
       (implies (and (not erp)
                     (not (glcp-generic-geval-ev-theoremp
                           (conjoin-clauses
                            (acl2::interp-defs-alist-clauses obligs)))))
                (not (glcp-generic-geval-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs)))))))

   (defthm glcp-generic-run-cases-ok-obligs
     (b* (((mv erp (cons & out-obligs) &)
           (glcp-generic-run-cases
            param-alist concl  vars obligs config state)))
       (implies (and (not erp)
                     (glcp-generic-geval-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs))))
                (glcp-generic-geval-ev-theoremp
                 (conjoin-clauses
                  (acl2::interp-defs-alist-clauses obligs))))))))


(in-theory (disable glcp-generic-run-cases))






(defun doubleton-list-to-alist (x)
  (if (atom x)
      nil
    (cons (cons (caar x) (cadar x))
          (doubleton-list-to-alist (cdr x)))))

(defun bindings-to-vars-vals (x)
  (if (atom x)
      (mv nil nil)
    (mv-let (vars vals)
      (bindings-to-vars-vals (cdr x))
      (if (and (symbolp (caar x))
               (pseudo-termp (cadar x)))
          (mv (cons (caar x) vars)
              (cons (cadar x) vals))
        (mv vars vals)))))

(defun bindings-to-lambda (bindings term)
  (mv-let (vars vals)
    (bindings-to-vars-vals bindings)
    `((lambda ,vars ,term) . ,vals)))

(defthm bindings-to-vars-vals-wfp
  (mv-let (vars vals)
    (bindings-to-vars-vals x)
    (and (symbol-listp vars)
         (pseudo-term-listp vals)
         (true-listp vals)
         (equal (len vals) (len vars))
         (not (stringp vars))
         (not (stringp vals))))
  :hints(("Goal" :in-theory (disable pseudo-termp))))

(defthm bindings-to-lambda-pseudo-termp
  (implies (pseudo-termp term)
           (pseudo-termp (bindings-to-lambda bindings term)))
  :hints(("Goal" :in-theory (enable true-listp length))))

(in-theory (disable bindings-to-lambda))

;; Transforms an alist with elements of the form
;; (((param1 val1) (param2 val2)) shape-spec)
;; to the form (parametrized-hyp . shape-spec).
(defun param-bindings-to-alist (hyp bindings)
  (if (atom bindings)
      nil
    (cons (list* (sublis-into-term
                  hyp (doubleton-list-to-alist (caar bindings)))
;;           (bindings-to-lambda (caar bindings) hyp)
           (acl2::msg "case: ~x0" (caar bindings))
           (cadar bindings))
          (param-bindings-to-alist hyp (cdr bindings)))))
(local
 (defthm param-bindings-to-alist-pseudo-term-listp-strip-cars
   (implies (pseudo-termp hyp)
            (pseudo-term-listp (strip-cars (param-bindings-to-alist hyp bindings))))))





(make-event (sublis *glcp-generic-template-subst* *glcp-clause-proc-template*))

(local
 (progn
   ;; What am I doing here?
   (defund glcp-generic-run-parametrized-placeholder (clauses)
     (glcp-generic-geval-ev-theoremp (conjoin-clauses clauses)))

   (defun check-top-level-bind-free (bindings mfc state)
     (declare (ignore state)
              (xargs :stobjs state))
     (and (null (acl2::mfc-ancestors mfc))
          bindings))

   (defthmd glcp-generic-run-parametrized-correct-rw
     (b* (((mv erp (cons clauses out-obligs) &)
           (glcp-generic-run-parametrized
            hyp concl  vars bindings id obligs config st)))
       (implies (and (bind-free (check-top-level-bind-free
                                 '((alist . alist)) acl2::mfc state)
                                (alist))
                     (glcp-generic-geval-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs)))
                     (not erp)
                     (glcp-generic-geval-ev hyp alist)
                     (acl2::interp-defs-alistp obligs)
                     (acl2::interp-defs-alistp (glcp-config->overrides config))
                     (pseudo-termp concl)
                     (pseudo-termp hyp)
                     (equal vars (collect-vars concl))
                     (glcp-generic-geval-ev-meta-extract-global-facts :state state1)
                     (equal (w st) (w state1)))
                (iff (glcp-generic-geval-ev-theoremp (conjoin-clauses clauses))
                     (and (glcp-generic-run-parametrized-placeholder
                           clauses)
                          (glcp-generic-geval-ev concl alist)))))
     :hints(("Goal" :in-theory (enable
                                glcp-generic-run-parametrized-placeholder))))

   (defund glcp-generic-run-cases-placeholder (clauses)
     (glcp-generic-geval-ev-theoremp (conjoin-clauses clauses)))

   (defthmd glcp-generic-run-cases-correct-rw
     (b* (((mv erp (cons clauses out-obligs) &)
           (glcp-generic-run-cases
            param-alist concl  vars obligs config st)))
       (implies (and (bind-free (check-top-level-bind-free
                                 '((alist . alist)) mfc state) (alist))
                     (glcp-generic-geval-ev-theoremp
                      (conjoin-clauses
                       (acl2::interp-defs-alist-clauses out-obligs)))
                     (glcp-generic-geval-ev (disjoin (strip-cars param-alist))
                                      a)
                     (not erp)
                     (acl2::interp-defs-alistp obligs)
                     (acl2::interp-defs-alistp (glcp-config->overrides config))
                     (pseudo-termp concl)
                     (pseudo-term-listp (strip-cars param-alist))
                     (equal vars (collect-vars concl))
                     (glcp-generic-geval-ev-meta-extract-global-facts :state state1)
                     (equal (w st) (w state1)))
                (iff (glcp-generic-geval-ev-theoremp (conjoin-clauses clauses))
                     (and (glcp-generic-run-cases-placeholder clauses)
                          (glcp-generic-geval-ev concl a)))))
     :hints(("Goal" :in-theory (enable glcp-generic-run-cases-placeholder))))))

(local
 (defthm w-state-of-preferred-defs-to-overrides
   (equal (w (mv-nth 2 (preferred-defs-to-overrides table state)))
          (w state))
   :hints(("Goal" :in-theory (enable preferred-defs-to-overrides)))))

(defthm glcp-generic-correct
  (implies (and (pseudo-term-listp clause)
                (alistp alist)
                (glcp-generic-geval-ev-meta-extract-global-facts)
                (glcp-generic-geval-ev
                 (conjoin-clauses
                  (acl2::clauses-result
                   (glcp-generic clause hints state)))
                 (glcp-generic-geval-ev-falsify
                  (conjoin-clauses
                   (acl2::clauses-result
                    (glcp-generic clause hints state))))))
           (glcp-generic-geval-ev (disjoin clause) alist))
  :hints
  (("goal" :do-not-induct
    t
    :in-theory
    (e/d* (glcp-generic-run-cases-correct-rw
           glcp-generic-run-parametrized-correct-rw)
          (glcp-analyze-interp-result-correct
           glcp-generic-geval-alist-gobj-alist-to-param-space
           glcp-generic-geval-gtests-nonnil-correct
           glcp-generic-run-cases-correct
           glcp-generic-run-parametrized-correct
           pseudo-term-listp-cdr
           pseudo-termp-car
           acl2::consp-by-len
           ;; shape-spec-listp-impl-shape-spec-to-gobj-list
           (:rules-of-class :definition :here))
          (gl-cp-hint
           ;; Jared added acl2::fast-alist-free since that's my new name
           ;; for flush-hons-get-hash-table-link
           fast-alist-free
           flush-hons-get-hash-table-link
           acl2::clauses-result
           glcp-generic glcp-error
           assoc-equal pseudo-term-listp))

    :restrict ((glcp-generic-geval-ev-disjoin-append ((a alist)))
               (glcp-generic-geval-ev-disjoin-cons ((a alist)))))
   (and stable-under-simplificationp
        (acl2::bind-as-in-definition
         glcp-generic
         (hyp-clause concl-clause params-cov-term hyp)
         `(:use ((:instance glcp-generic-geval-ev-falsify
                            (x (disjoin ,hyp-clause))
                            (a alist))
                 (:instance glcp-generic-geval-ev-falsify
                            (x (disjoin ,concl-clause))
                            (a alist))
                 (:instance glcp-generic-geval-ev-falsify
                  (x (disjoin (CONS
                               (CONS
                                'NOT
                                (CONS
                                 (CONS 'GL-CP-HINT
                                       (CONS (CONS 'QUOTE (CONS 'CASESPLIT 'NIL))
                                             'NIL))
                                 'NIL))
                               (CONS (CONS 'NOT (CONS ,HYP 'NIL))
                                     (CONS ,PARAMS-COV-TERM 'NIL)))))
                  (a alist)))))))
;  :otf-flg t
  :rule-classes nil)




;; Related clause processor which doesn't run the simulation, but
;; produces all the other necessary clauses.  We define this by
;; using a mock interp-term function that just returns T and no
;; obligs, and also a mock analyze-term
(defun glcp-fake-interp-term (x bindings pathcond clk obligs config state)
  (declare (ignore x bindings pathcond clk config))
  (mv nil obligs t state))

(defun glcp-fake-analyze-interp-result
  (val param-al hyp-bdd id concl config state)
  (declare (ignore val param-al hyp-bdd id concl config)
           (xargs :stobjs state))
  (mv nil '('t) state))

(defconst *glcp-side-goals-subst*
  `((interp-term . glcp-fake-interp-term)
    (run-cases . glcp-side-goals-run-cases)
    (run-parametrized . glcp-side-goals-run-parametrized)
    (clause-proc . glcp-side-goals-clause-proc1)
    (clause-proc-name . 'glcp-side-goals-clause-proc)
    (glcp-analyze-interp-result . glcp-fake-analyze-interp-result)))

(make-event (sublis *glcp-side-goals-subst*
                    *glcp-run-parametrized-template*))

(make-event (sublis *glcp-side-goals-subst* *glcp-run-cases-template*))

(make-event (sublis *glcp-side-goals-subst*
                    *glcp-clause-proc-template*))

(defun glcp-side-goals-clause-proc (clause hints state)
  ;; The cheat: We only allow this clause processor on the trivially
  ;; true clause ('T).
  (b* (((unless (equal clause '('T)))
        (mv "This clause processor can be used only on clause '('T)."
            nil state))
       ((list* & & hyp & concl &) hints))
    (glcp-side-goals-clause-proc1
     `((implies ,hyp ,concl)) hints state)))

(defevaluator glcp-side-ev glcp-side-ev-lst ((if a b c)))

(local (acl2::def-join-thms glcp-side-ev))

(defthm glcp-side-goals-clause-proc-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (glcp-side-ev
                 (conjoin-clauses
                  (acl2::clauses-result
                   (glcp-side-goals-clause-proc clause hints state)))
                 a))
           (glcp-side-ev (disjoin clause) a))
  :hints (("goal" :in-theory
           (e/d** ((:rules-of-class :executable-counterpart :here)
                   acl2::clauses-result glcp-side-goals-clause-proc
                   glcp-side-ev-constraint-2
                   car-cons))))
  :rule-classes :clause-processor)




;; GLCP-UNIVERSAL: an unverifiable version of the clause processor
;; that can apply any symbolic counterpart and execute any function.
;; This is actually somewhat slow because simple-translate-and-eval is
;; slower than an apply function with a reasonable number of cases in
;; the style
;; (case fn
;;   (foo  (foo (nth 0 actuals) (nth 1 actuals)))
;;   (bar  (bar (nth 0 actuals)))
;;   ...)
;; But we do avoid interpreter overhead, which is the real killer.

;; Looks up a function in the gl-function-info table to see if it has
;; a symbolic counterpart, and executes it if so.
(defun gl-universal-run-gified (fn actuals pathcond clk state)
  (declare (xargs :guard (and (symbolp fn)
                              (natp clk))
                  :mode :program))
  (b* ((world (w state))
       (al (table-alist 'gl-function-info world))
       (look (assoc-eq fn al))
       ((unless look) (mv nil nil))
       (gfn (cadr look))
       ((mv er res)
        (acl2::magic-ev-fncall gfn (append actuals (list pathcond clk))
                               state t t))
       ((when er)
        (prog2$ (cw "GL-UNIVERSAL-RUN-GIFIED: error: ~@0~%" er)
                (mv nil nil))))
    (mv t res)))

;; (defun gl-universal-apply-concrete (fn actuals state)
;;   (declare (xargs :guard (true-listp actuals)
;;                   :mode :program))
;;   (b* ((world (w state))
;;        (call (cons fn (acl2::kwote-lst actuals)))
;;        (mvals (len (fgetprop fn 'stobjs-out nil world)))
;;        (term (if (< 1 mvals) `(mv-list ,mvals ,call) call))
;;        ((mv er (cons & val) state)
;;         (acl2::simple-translate-and-eval
;;          term nil nil
;;          (acl2::msg "gl-universal-apply-concrete: ~x0" term)
;;          'gl-universal-apply-concrete world state t))
;;        ((when er)
;;         (prog2$ (cw "GL-UNIVERSAL-APPLY-CONCRETE: error: ~@0~%" er)
;;                 (mv nil nil state))))
;;     (mv t val state)))

(defconst *gl-universal-subst*
  `((interp-term . gl-universal-interp-term)
    (interp-list . gl-universal-interp-list)
    (interp-if . gl-universal-interp-if)
    (rewrite-fncall . gl-universal-rewrite-fncall)
    (rewrite-fncall-apply-rules . gl-universal-rewrite-fncall-apply-rules)
    (rewrite-fncall-apply-rule . gl-universal-rewrite-fncall-apply-rule)
    (relieve-hyps . gl-universal-relieve-hyps)
    (relieve-hyp . gl-universal-relieve-hyp)
    (run-gified . gl-universal-run-gified)
    (apply-concrete . gl-universal-apply-concrete)
    (run-cases . gl-universal-run-cases)
    (run-parametrized . gl-universal-run-parametrized)
    (clause-proc . gl-universal-clause-proc)
    (clause-proc-name . 'gl-universal-clause-proc)))

(program)

(make-event (sublis *gl-universal-subst* *glcp-interp-template*))

(make-event (sublis *gl-universal-subst*
                    *glcp-run-parametrized-template*))

(make-event (sublis *gl-universal-subst* *glcp-run-cases-template*))

(make-event (sublis *gl-universal-subst*
                    *glcp-clause-proc-template*))

(logic)


;; To install this as a clause processor, run the following.  Note
;; that this creates a ttag.
(defmacro allow-gl-universal-clause-processor ()
  '(acl2::define-trusted-clause-processor
    gl-universal-clause-proc
    nil :ttag gl-universal-clause-proc))






;; Symbolic interpreter for translated terms, based on the universal clause
;; processor defined above.  X is the term, ALIST gives a
;; list of bindings of variables to g-objects, hyp is a BDD.

(defun gl-interp-term (x alist pathcond clk state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((world (w state))
       ((er overrides)
        (preferred-defs-to-overrides
         (table-alist 'preferred-defs world) state))
       ((mv er obligs ans state)
        (gl-universal-interp-term
         x alist pathcond clk nil (make-glcp-config :overrides overrides) state))
       ((when er) (mv er nil state))
       (- (flush-hons-get-hash-table-link obligs)))
    (value ans)))




;; Translate the given term, then run the interpreter.
(defmacro gl-interp-raw (x &optional alist (hyp 't) (clk '100000))
  `(acl2::er-let*
    ((trans (acl2::translate ,x t t t 'gl-interp (w state)
                             state)))
    (gl-interp-term trans ,alist ,hyp ,clk state)))



(defdoc gl-interp-raw
  ":Doc-section ACL2::GL
Symbolically interpret a term using GL.~/

Usage:
~bv[]
 (gl-interp-raw term bindings)
~ev[]

The above form runs a symbolic interpretation of ~c[term] on the symbolic input
~c[bindings].  ~c[bindings] should be an association list mapping variables to
symbolic objects (not to shape specifiers, as in ~il[gl-interp].)  Note also
that bindings is a dotted alist, rather than a doubleton list as in
~il[gl-interp]: each pair is ~c[(CONS VAR BINDING)], not ~c[(LIST VAR BINDING)].~/~/")


(defun gl-parametrize-by-hyp-fn (hyp al state)
  (declare (xargs :mode :program))
  (b* ((al (shape-specs-to-interp-al al))
       ((er hyp-pred) (gl-interp-raw hyp al))
       (hyp-test (gtests hyp-pred t))
       (hyp-bdd (bfr-or (gtests-nonnil hyp-test)
                      (gtests-unknown hyp-test))))
    (value (gobj-to-param-space al hyp-bdd))))

(defmacro gl-parametrize-by-hyp (hyp bindings)
  `(gl-parametrize-by-hyp-fn ,hyp ,bindings state))

(defun gl-interp-fn (hyp term al state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* (((er param-al) (gl-parametrize-by-hyp hyp al))
;;        (al (shape-specs-to-interp-al al))
;;        ((er hyp-pred) (gl-interp-raw hyp al))
;;        (hyp-test (gtests hyp-pred t))
;;        (hyp-bdd (q-or (gtests-nonnil hyp-test)
;;                       (gtests-unknown hyp-test)))
;;        (param-al (gobj-to-param-space al hyp-bdd))
       ((er res) (gl-interp-raw term param-al)))
    (value (cons param-al res))))

(defmacro gl-interp (term al &key (hyp 't))
  `(gl-interp-fn ',hyp ',term ,al state))

(defdoc gl-interp
  ":Doc-section ACL2::GL
Symbolically interpret a term using GL, with inputs generated by parametrization.~/

Usage:
~bv[]
 (gl-interp term bindings :hyp hyp)
~ev[]

The above form runs a symbolic interpretation of ~c[term] on the symbolic input
assignment produced by parametrizing ~c[bindings] using ~c[hyp].  The symbolic
execution run by this form is similar to that run by
~bv[]
 (def-gl-thm <name> :hyp hyp :concl term :g-bindings bindings).
~ev[]
~c[bindings] should be a binding list of the same kind as taken by
~il[def-gl-thm], that is, a list of elements ~c[(var val)] such that ~c[var]
is a variable free in ~c[term], and ~c[val] is a shape specifier
(~l[gl::shape-specs].)

Similar to ~c[def-gl-thm], ~c[term] and ~c[hyp] should be the (unquoted)
terms of interest, whereas ~c[bindings] should be something that evaluates to
the binding list (the quotation of that binding list, for example.)~/

In more detail: First, the input bindings are converted to an assignment of
symbolic inputs to variables.  The hyp term is symbolically interpreted using
this variable assignment, yielding a predicate.  The symbolic input assignment is
parametrized using this predicate to produce a new such assignment whose
coverage is restricted to the subset satisfying the hyp.  The term is then
symbolically interpreted using this assignment, and the result is returned.

This macro expands to a function call taking state, and its return value is an
error triple.

The symbolic interpreter used by ~c[gl-interp] is not one introduced by
def-gl-clause-processor as usual, but a special one which can call any function
on concrete values, and any symbolic counterpart function.  (Other interpreters
can call a fixed list of functions on concrete values and a fixed list of
symbolic counterparts.)  However, typically a fixed interpreter is used when
proving theorems (otherwise a ttag is needed.)  This has some
performance-related consequences:

 - ~c[gl-interp] may interpret a term faster than ~c[def-gl-thm].  This
occurs mainly when some function is run concretely by the universal interpreter
but is not in the fixed list of functions callable by the fixed interpreter.
Determine which function is at fault by looking at a backtrace, and then define
your interpreter so that it can call this function.

 - ~c[gl-interp] may interpret a term slower than ~c[def-gl-thm].  The
universal interpreter uses somewhat more overhead on each function call than
fixed interpreters do, so when interpreter overhead is a large portion of the
runtime relative to BDD operations, ~c[gl-interp] may be a constant factor
slower than a fixed interpreter.

See ~il[gl-interp-raw] for a similar function that does not perform
parametrization.~/")




(defun find-counterexamples-fn (hyp concl al state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* (((er (cons param-al concl-pred))
        (gl-interp-fn hyp concl al state))
       (concl-tests (gtests concl-pred t))
       (neg-concl (bfr-and (bfr-not (gtests-nonnil concl-tests))
                         (bfr-not (gtests-unknown concl-tests))))
       (false-al (gobj-to-param-space param-al neg-concl)))
    (value false-al)))

(defmacro find-counterexamples (concl alist &key (hyp 't))
  `(find-counterexamples-fn ,hyp ,concl ,alist state))






(defun max-max-max-depth (x)
  (if (atom x)
      0
    (max (acl2::max-max-depth (car x))
         (max-max-max-depth (cdr x)))))

(defund gobj-max-depth (x)
  (if (atom x)
      0
    (pattern-match x
      ((g-concrete &) 0)
      ((g-boolean b) (max-depth b))
      ((g-number n) (max-max-max-depth n))
      ((g-ite if then else)
       (max (gobj-max-depth if)
            (max (gobj-max-depth then)
                 (gobj-max-depth else))))
      ((g-apply & args) (gobj-max-depth args))
      ((g-var &) 0)
      (& (max (gobj-max-depth (car x))
              (gobj-max-depth (cdr x)))))))




(defun n-random-assignments-fn (n bound obj pred evfn state)
  (declare (xargs :stobjs state
                  :mode :program))
  (if (eq pred nil)
      (er soft 'n-random-assignments-fn
          "Unsatisfiable predicate for n-random-assignments~%")
    (if (zp n)
        (value nil)
      (b* (((er rest) (n-random-assignments-fn
                       (1- n) bound obj pred evfn state))
           ((mv envn state) (acl2::random$ bound state))
           (env (list (to-satisfying-assign (n2v envn) pred))))
        (if evfn
            (b* ((term `(,evfn ',obj ',env))
                 ((er (cons & val))
                  (acl2::simple-translate-and-eval
                   term nil nil
                   (acl2::msg "~
GL evaluation with ~x0 in n-random-assignments-fn" evfn)
                   'n-random-assignments-fn (w state) state t)))
              (value (cons val rest)))
          (value (cons (generic-geval obj env) rest)))))))

(defmacro n-random-assignments (n obj &optional (pred 't) evfn)
  `(n-random-assignments-fn
    ,n 
    (expt 2 (gobj-max-depth ,obj))
    ,obj ,pred ,evfn state))





(defun possibly-true (res)
  (let ((test (gl::gtests res t)))
    (bfr-or (gl::gtests-nonnil test)
          (gl::gtests-unknown test))))

(defun known-true (res)
  (let ((test (gl::gtests res t)))
    (bfr-and (gl::gtests-nonnil test)
           (bfr-not (gl::gtests-unknown test)))))


(defun sim-g-thm-fn (hyp concl g-bindings ctrex-info nexamples erp state)
  (declare (xargs :stobjs state :mode :program))
  (b* ((al (shape-specs-to-interp-al g-bindings))
       ((er hyp-pred) (gl-interp-raw hyp al))
       (hyp-possible (possibly-true hyp-pred))
       ((er hyp-possible)
        (if hyp-possible
            (value hyp-possible)
          (er soft 'sim-g-thm-fn "Impossible hyp~%")))
       (hyp-al (gobj-to-param-space al hyp-possible))
       ((er concl-pred) (gl-interp-raw concl hyp-al))
       (concl-definite (known-true concl-pred)))
    (if (eq concl-definite t)
        (value "OK")
      (b* ((ctrex-bdd (bfr-not concl-definite))
           ((er ctrex-info-res) (gl-interp-raw ctrex-info hyp-al))
           ((er ctrexamples)
            (n-random-assignments nexamples (cons hyp-al ctrex-info-res)
                                  ctrex-bdd)))
        (if erp
            (er soft 'sim-g-thm-fn
                "Counterexamples found: ~x0~%" ctrexamples)
          (value ctrexamples))))))

(defmacro sim-g-thm
  (&key hyp concl g-bindings ctrex-term (nexamples '3) (erp 't))
  `(sim-g-thm-fn ',hyp ',concl ,g-bindings ',ctrex-term ,nexamples ,erp state))



(defun param-al-to-interp-al (al)
  (if (atom al)
      nil
    (if (consp (car al))
        (cons (cons (caar al) (mk-g-concrete (cadar al)))
              (param-al-to-interp-al (cdr al)))
      (param-al-to-interp-al (cdr al)))))


(defun sim-param-coverage (param-hyp param-bindings cov-al state)
  (declare (xargs :stobjs state
                  :mode :program))
  (if (atom param-bindings)
      (value nil)
    (b* (((er rest) (sim-param-coverage
                     param-hyp (cdr param-bindings) cov-al state))
         (curr-al (append (param-al-to-interp-al (caar param-bindings))
                          cov-al))
         ((er res) (gl-interp-raw param-hyp curr-al))
         (res-known (known-true res)))
      (value (bfr-or rest res-known)))))


(defun sim-param-coverage-ok (hyp param-hyp param-bindings cov-bindings
                                  nexamples erp state)
  (declare (xargs :stobjs state
                  :mode :program))
  (b* ((cov-al (shape-specs-to-interp-al cov-bindings))
       ((er hyp-res) (gl-interp-raw hyp cov-al))
       (hyp-possible (possibly-true hyp-res))
       ((er param-cov) (sim-param-coverage
                        param-hyp param-bindings cov-al state))
       (uncov (bfr-and hyp-possible (bfr-not param-cov))))
    (if uncov
        (b* (((er examples)
              (n-random-assignments nexamples cov-al uncov)))
          (if erp
              (er soft 'sim-param-coverage-ok
                  "Coverage gap found. Examples: ~x0~%" examples)
            (value examples)))
      (value "OK"))))

(defun gl-interp-on-alists (term alists state)
  (declare (xargs :stobjs state :mode :program))
  (if (atom alists)
      (value nil)
    (b* (((er rest) (gl-interp-on-alists term (cdr alists) state))
         ((er (cons & first))
                  (acl2::simple-translate-and-eval
                   term (car alists) nil
                   "gl-interp-on-alists"
                   'gl-interp-on-alists (w state) state t))
;;           (gl-interp term (car alists))
          )
      (value (cons (cons (car alists) first) rest)))))

(defun sim-params (param-bindings param-hyp concl ctrex-info nexamples
                                  run-after-cases state)
  (declare (xargs :stobjs state
                  :mode :program))
  (if (atom param-bindings)
      (value "OK")
    (b* ((- (cw "Param bindings: ~x0~%" (caar param-bindings)))
         (al (shape-specs-to-interp-al (cadar param-bindings)))
         (al-with-params (append (param-al-to-interp-al (caar param-bindings)) al))
         ((er hyp) (gl-interp-raw param-hyp al-with-params))
         (hyp-possible (possibly-true hyp))
         ((er &)
          (if hyp-possible
              (b* ((param-al (gobj-to-param-space al hyp-possible))
                   ((er concl-pred) (gl-interp-raw concl param-al))
                   (concl-known (known-true concl-pred)))
                (if (eq concl-known t)
                    (value "OK")
                  (b* ((ctrex-bdd (bfr-not concl-known))
                       ((er ctrex-alists)
                        (n-random-assignments
                         nexamples param-al ctrex-bdd))
                       ((er ctrexamples)
                        (gl-interp-on-alists ctrex-info ctrex-alists state)))
                    (er soft 'sim-params
                        "Counterexamples found at parameters ~x0: ~x1~%" 
                        (caar param-bindings) ctrexamples))))
            (prog2$ (cw "Note: Param hyp is impossible with settings ~x0~%"
                        (caar param-bindings))
                    (value "OK"))))
         ((er &)
          (acl2::simple-translate-and-eval
           run-after-cases nil nil
           (acl2::msg "~
sim-params: ~x0~%" run-after-cases)
           'sim-params (w state) state t)))
      (sim-params (cdr param-bindings) param-hyp concl ctrex-info nexamples
                  run-after-cases state))))


(defun sim-param-thm-fn (hyp param-hyp concl cov-bindings param-bindings
                          ctrex-info nexamples run-after-cases erp state)
  (declare (xargs :stobjs state
                  :mode :program))
  (er-progn
   (sim-param-coverage-ok hyp param-hyp param-bindings cov-bindings
                          nexamples erp state)
   (sim-params param-bindings param-hyp concl ctrex-info nexamples
               run-after-cases state)))

(defmacro sim-param-thm
  (&key hyp param-hyp concl cov-bindings param-bindings ctrex-term
        (nexamples '3) run-after-cases (erp 't))
  `(sim-param-thm-fn ',hyp ',param-hyp ',concl ,cov-bindings ,param-bindings
                     ',ctrex-term ,nexamples ',run-after-cases ,erp state))

