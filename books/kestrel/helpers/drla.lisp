; A tool to conjecture missing hypothesis using counterexamples
;
; Copyright (C) 2023-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Ruben Gamboa (ruben@gamboas.org)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HELP")

;; TODO
;; - limit number of hypotheses suggested
;; - how to subsume hypotheses found
;; - make sure an expression isn't NIL or not-NIL before trying to split on it
;; - tie into ACL2 type-prescriptions, use only boolean predicates for splitting?
;; - use history, e.g., some test patterns that were recently useful

(include-book "acl2s/cgen/top" :dir :system :ttags :all)

(include-book "tools/prove-dollar" :dir :system)

(local (include-book "arithmetic-5/top" :dir :system))

(defconst *DRLA-BUILTIN-PREDICATES*
  '((ACL2::ATOM . 1)
    (ACL2::ACL2-NUMBERP . 1)
    (ACL2::RATIONALP . 1)
    (ACL2::INTEGERP . 1)
    (ACL2::COMPLEX-RATIONALP . 1)
    (ACL2::SYMBOLP . 1)
    (ACL2::BOOLEANP . 1)
    (ACL2::CONSP . 1)
    (ACL2::TRUE-LISTP . 1)
    (ACL2::STRINGP . 1)
    (ACL2::CHARACTERP . 1)
    ))

(defconst *DRLA-COMBINED-BUILTIN-PREDICATES*
    '(((LAMBDA (X) (AND (acl2-numberp x) (not (equal x '0)))) . 1)
      ((LAMBDA (X) (AND (rationalp x) (not (equal x '0)))) . 1)
      ((LAMBDA (X) (AND (rationalp x) (not (< x '0)))) . 1)
      ((LAMBDA (X) (AND (rationalp x) (not (< '0 x)))) . 1)
      ((LAMBDA (X) (AND (integerp x) (not (equal x '0)))) . 1)
      ((LAMBDA (X) (AND (rationalp x) (< '0 x))) . 1)
      ((LAMBDA (X) (AND (rationalp x) (< x '0))) . 1)
      ((LAMBDA (X) (AND (integerp x) (not (< x '0)))) . 1)
      ((LAMBDA (X) (AND (integerp x) (not (< '0 x)))) . 1)
      ((LAMBDA (X) (AND (rationalp x) (not (integerp x)))) . 1)
      ((LAMBDA (X) (AND (rationalp x) (not (integerp x)) (< x '0))) . 1)
      ((LAMBDA (X) (AND (integerp x) (< x '0))) . 1)
      ((LAMBDA (X) (AND (rationalp x) (not (integerp x)) (< '0 x))) . 1)
      ((LAMBDA (X) (AND (integerp x) (< '0 x))) . 1)
      ((LAMBDA (X) (AND (integerp x) (< '1 x))) . 1)
      ((LAMBDA (X) (equal x '0)) . 1)
      ((LAMBDA (X) (equal x '1)) . 1)
      ((LAMBDA (X) (OR  (equal x 't) (equal x 'nil))) . 1)
      ((LAMBDA (X) (AND (consp x) (not (true-listp x)))) . 1)
      ((LAMBDA (X) (AND (consp x) (true-listp x))) . 1)
      ((LAMBDA (X) (AND (symbolp x) (not (equal x 't)) (not (equal x 'nil)))) . 1)
      ((LAMBDA (X) (equal x 't)) . 1)
      ((LAMBDA (X) (equal x 'nil)) . 1)
      ))

(defconst *DRLA-BUILTIN-COMPARISONS*
  '((ACL2::EQUAL . 2)
    (ACL2::<< . 2)
    ))

(defconst *DRLA-SKIP-FNNAMES*
  '(IF
    COERCE
    EQUAL
    <<
    ))

(defconst *DRLA-BUILTIN-CONSTANTS*
  '(0 1 T NIL))

(defun map-cons (e L acc)
  (if (endp L)
      acc
      (map-cons e (cdr L) (cons (cons e (car L)) acc))))

(defun map-list (L acc)
  (if (endp L)
      acc
      (map-list (cdr L)
                (cons (list (car L))
                      acc))))

(defun cross (x y acc)
  (if (endp x)
      acc
      (cross (cdr x) y
             (append (map-cons (car x) y nil)
                     acc))))

(defun cross-n (args n)
  (if (zp n)
      (list nil)
      (if (equal n 1)
          (map-list args nil)
          (cross args (cross-n args (1- n)) nil))))

(defun filter-out (templates do-not-nest)
  (if (endp templates)
      nil
      (if (and (consp (car templates))
               (member-equal (car (car templates))
                             do-not-nest))
          (filter-out (cdr templates) do-not-nest)
          (cons (car templates)
                (filter-out (cdr templates) do-not-nest)))))

(defun make-templates-aux (function-list do-not-nest templates)
  (if (endp function-list)
      nil
      (append (map-cons (car (car function-list))
                        (cross-n (cons nil
                                       (if (member-equal
                                            (car (car function-list))
                                            do-not-nest)
                                           (filter-out templates do-not-nest)
                                           templates))
                                 (cdr (car function-list)))
                        nil)
              (make-templates-aux (cdr function-list) do-not-nest templates))))

(defun make-templates (function-list do-not-nest depth)
  (if (zp depth)
      nil
      (let ((templates (make-templates function-list do-not-nest (1- depth))))
        (union-equal templates
                     (make-templates-aux function-list do-not-nest templates)))))

(defun template-slots (template is-list)
  (if (endp template)
      (if is-list 0 1)
      (if is-list
          (+ (template-slots (car template) nil)
             (template-slots (cdr template) t))
          (template-slots (cdr template) t))))

(defun vars-from-bindings (bindings)
  (if (endp bindings)
      nil
      (cons (car (car bindings))
            (vars-from-bindings (cdr bindings)))))

(defun all-true (term witnesses state)
  (declare (xargs :mode :program
           :stobjs state))
  (if (endp witnesses)
      (mv t state)
      (mv-let (erp stobjs-value state)
          (with-output! :off (acl2::warning acl2::error)
            (trans-eval `(let ,(car witnesses)
                           (declare (ignorable
                                     ,@(vars-from-bindings (car witnesses))))
                           ,term)
                        'drla-ctx state nil))
        (if (or erp (not (cdr stobjs-value)))
            (mv nil state)
            (all-true term (cdr witnesses) state)))))

(defun all-false (term counterexamples state)
  (declare (xargs :mode :program
           :stobjs state))
  (if (endp counterexamples)
      (mv t state)
      (mv-let (erp stobjs-value state)
          (with-output! :off (acl2::warning acl2::error)
            (trans-eval `(let ,(car counterexamples)
                           (declare (ignorable
                                     ,@(vars-from-bindings (car counterexamples))))
                           ,term)
                        'drla-ctx state nil))
        (if (or erp (cdr stobjs-value))
            (mv nil state)
            (all-false term (cdr counterexamples) state)))))

(defun separates (term witnesses counterexamples state)
  (declare (xargs :mode :program
                  :stobjs state))
  (mv-let (goodp state)
      (all-false term counterexamples state)
    (if (not goodp)
        (mv nil state)
        (mv-let (goodp state)
            (all-false term witnesses state)
          (mv (not goodp) state)))))

(defun get-arg-list (base-terms nterms nslots n)
  (if (zp nslots)
      nil
      (cons (nth (mod n nterms) base-terms)
            (get-arg-list base-terms nterms (1- nslots) (floor n nterms)))))

(defun fill-template (template args is-list)
  (if (endp template)
      (if is-list
          (mv nil args)
          (mv (car args) (cdr args)))
      (if is-list
          (mv-let (filled-first remaining-args)
              (fill-template (car template) args nil)
            (mv-let (filled-rest final-args)
                (fill-template (cdr template) remaining-args t)
              (mv (cons filled-first filled-rest)
                  final-args)))
          (mv-let (local-args remaining-args)
              (fill-template (cdr template) args t)
            (mv (cons (car template) local-args)
                remaining-args)))))


(defun redundant-boolean-expr (term all-items state)
  (declare (xargs :mode :program
                  :stobjs state))
  (if (endp term)
      (mv nil state)
      (if (equal (car term) 'not)
          (redundant-boolean-expr (car (cdr term)) all-items state)
          (if (or (equal (car term) 'or) (equal (car term) 'and))
              (let ((x (car (cdr term)))
                    (y (car (cdr (cdr term)))))
                (mv-let (redundantp state)
                    (redundant-boolean-expr x all-items state)
                  (if redundantp
                      (mv t state)
                      (mv-let (redundantp state)
                          (redundant-boolean-expr y all-items state)
                        (if redundantp
                            (mv t state)
                            (mv-let (goodp state)
                                (all-true x all-items state)
                              (if goodp
                                  (mv t state)
                                  (mv-let (goodp state)
                                      (all-false y all-items state)
                                    (if goodp
                                        (mv t state)
                                        (mv-let (goodp state)
                                            (all-true `(implies ,x ,y) all-items state)
                                          (if goodp
                                              (mv t state)
                                              (mv-let (goodp state)
                                                  (all-false `(implies ,x ,y) all-items state)
                                                (if goodp
                                                    (mv t state)
                                                    (mv-let (goodp state)
                                                        (all-true `(implies ,y ,x) all-items state)
                                                      (if goodp
                                                          (mv t state)
                                                          (mv-let (goodp state)
                                                              (all-false `(implies ,y ,x) all-items state)
                                                            (if goodp
                                                                (mv t state)
                                                                (mv (acl2::<< y x)
                                                                    state))))))))))))))))))
              (mv nil state)))))

(defun subst-pairwise (new old term)
  (if (endp new)
      term
      (subst-pairwise (cdr new) (cdr old) (subst (car new) (car old) term))))

; Matt K. mod: Avoid ACL2(p) error.
(set-waterfall-parallelism nil)

(mutual-recursion
 (defun apply-lambdas (term)
   (if (consp term)
       (if (and (consp (car term))
                (equal (car (car term)) 'lambda))
           (let* ((params (car (cdr (car term))))
                  (body (apply-lambdas (car (cdr (cdr (car term))))))
                  (args (cdr term)))
             (subst-pairwise args params body))
           (cons (car term)
                 (apply-lambdas-list (cdr term))))
       term))
 (defun apply-lambdas-list (list)
   (if (endp list)
       nil
       (cons (apply-lambdas (car list))
             (apply-lambdas-list (cdr list)))))
 )

(mutual-recursion

 (defun term-size (term)
   (if (consp term)
       (if (equal (car term) 'quote)
           0
           (1+ (term-list-size (cdr term))))
       1))

 (defun term-list-size (list)
   (if (endp list)
       0
       (+ (term-size (car list))
          (term-list-size (cdr list)))))
 )

(defun simpler-term (x y)
  (< (term-size (apply-lambdas x))
     (term-size (apply-lambdas y))))

(defun more-general (general specific bindings state)
  (declare (xargs :mode :program
                  :stobjs state))
  (mv-let (general->specific state)
      (all-true `(implies ,general ,specific) bindings state)
    (mv-let (specific->general state)
        (all-true `(implies ,specific ,general) bindings state)
      (if general->specific
          (if specific->general
              (if (simpler-term general specific)
                  (mv t state)
                  (mv nil state))
              (mv nil state))
          (if specific->general
              (mv t state)
              (mv nil state))))))

(defun previous-already-more-general (term previous-terms bindings state)
  (declare (xargs :mode :program
                  :stobjs state))
  (if (endp previous-terms)
      (mv nil state)
      (mv-let (more-general-p state)
          (more-general (car previous-terms) term bindings state)
        (if more-general-p
            (mv t state)
            (previous-already-more-general term (cdr previous-terms) bindings
                                           state)))))

(defun filter-less-general-terms (term previous-terms bindings state)
  (declare (xargs :mode :program
                  :stobjs state))
  (if (endp previous-terms)
      (mv nil state)
      (mv-let (more-general-p state)
          (more-general term (car previous-terms) bindings state)
        (mv-let (terms-to-keep state)
            (filter-less-general-terms term
                                       (cdr previous-terms)
                                       bindings
                                       state)
          (if more-general-p
              (mv terms-to-keep state)
              (mv (cons (car previous-terms) terms-to-keep) state))))))

(defun get-terms-separating-template-aux (template base-terms
                                          nterms nslots n
                                          witnesses counterexamples acc state)
  (declare (xargs :mode :program
                  :stobjs state))
  (if (not (natp n))
      (mv acc state)
      (let* ((args (get-arg-list base-terms nterms nslots n)))
        (mv-let (term args)
            (fill-template template args nil)
            (declare (ignorable args))
            (mv-let (goodp state)
                (separates term witnesses counterexamples state)
              (if goodp
                  (mv-let (redundantp state)
                      (redundant-boolean-expr
                       term
                       (append witnesses counterexamples)
                       state)
                    (if redundantp
                        (get-terms-separating-template-aux template base-terms
                                                   nterms nslots (1- n)
                                                   witnesses counterexamples
                                                   acc
                                                   state)
                        (mv-let (previous-more-general-p state)
                            (previous-already-more-general
                             term
                             acc
                             (append witnesses
                                     counterexamples)
                             state)
                          (if previous-more-general-p
                              (get-terms-separating-template-aux template base-terms
                                                   nterms nslots (1- n)
                                                   witnesses counterexamples
                                                   acc
                                                   state)
                              (mv-let (terms-to-keep state)
                                  (filter-less-general-terms
                                   term
                                   acc
                                   (append witnesses counterexamples)
                                   state)
                              (get-terms-separating-template-aux template base-terms
                                                                 nterms nslots (1- n)
                                                                 witnesses counterexamples
                                                                 (cons
                                                                  (apply-lambdas term)
                                                                  terms-to-keep)
                                                                 state))))))
                  (get-terms-separating-template-aux template base-terms
                                                     nterms nslots (1- n)
                                                     witnesses counterexamples
                                                     acc
                                                     state)))))))

(defun get-terms-separating-template (template base-terms
                                      witnesses counterexamples acc state)
  (declare (ignorable state)
           (xargs :mode :program
                  :stobjs state))
  (let ((nslots (template-slots template nil))
        (nterms (len base-terms)))
    (get-terms-separating-template-aux template base-terms
                                       nterms nslots (1- (expt nterms nslots))
                                       witnesses counterexamples acc state)))

(defun get-terms-separating-logical-template-aux (logical-template predicates base-terms
                                                  nterms nslots n
                                                  witnesses counterexamples acc
                                                  state)
  (declare (ignorable state)
           (xargs :mode :program
                  :stobjs state))
  (if (not (natp n))
      (mv acc state)
      (let* ((args (get-arg-list predicates nterms nslots n)))
        (mv-let (template args)
            (fill-template logical-template args nil)
            (declare (ignorable args))
          (mv-let (acc state)
              (get-terms-separating-template
               template base-terms
               witnesses counterexamples acc state)
            (get-terms-separating-logical-template-aux
             logical-template
             predicates
             base-terms
             nterms nslots (1- n)
             witnesses counterexamples acc state))))))

(defun get-terms-separating-logical-template (logical-template predicates base-terms
                                              witnesses counterexamples acc state)
  (declare (ignorable state)
           (xargs :mode :program
                  :stobjs state))
  (let ((nslots (template-slots logical-template nil))
        (nterms (len predicates)))
    (get-terms-separating-logical-template-aux logical-template predicates base-terms
                                               nterms nslots (1- (expt nterms nslots))
                                               witnesses counterexamples acc state)))


(defun get-terms-separating-all-logical-templates (logical-templates
                                                   predicates base-terms
                                                   witnesses counterexamples
                                                   acc state)
  (declare (ignorable state)
           (xargs :mode :program
                  :stobjs state))
  (if (endp logical-templates)
      (mv acc state)
      (mv-let (acc state)
          (get-terms-separating-logical-template
           (car logical-templates) predicates base-terms
           witnesses counterexamples acc state)
        (get-terms-separating-all-logical-templates
         (cdr logical-templates) predicates base-terms
         witnesses counterexamples acc state))))



(defun set-difference (a b)
  (if (endp a)
      nil
      (if (member-equal (car a) b)
          (set-difference (cdr a) b)
          (cons (car a) (set-difference (cdr a) b)))))

(defun get-all-fnnames-used-to-define (fnnames skip-names world)
  (declare (xargs :mode :program))
  (if (endp fnnames)
      nil
      (if (member-equal (car fnnames) skip-names)
          (get-all-fnnames-used-to-define (cdr fnnames)
                                          skip-names
                                          world)
          (union-equal (set-difference
                        (acl2::all-fnnames (acl2::body (car fnnames)
                                                       nil
                                                       world))
                        skip-names)
                       (get-all-fnnames-used-to-define (cdr fnnames)
                                                       skip-names
                                                       world)))))



(defun get-all-fnnames-in-fnnames (fnnames skip-names depth world)
  (declare (xargs :mode :program))
  (if (zp depth)
      (set-difference fnnames skip-names)
      (let ((new-fnnames (get-all-fnnames-used-to-define fnnames
                                                         skip-names
                                                         world)))
        (union-equal fnnames
                     (get-all-fnnames-in-fnnames new-fnnames
                                                 skip-names
                                                 (1- depth)
                                                 world)))))

(defun get-all-fnnames-in-term (term skip-names depth world)
  (declare (xargs :mode :program))
  (get-all-fnnames-in-fnnames (set-difference (acl2::all-fnnames term)
                                              skip-names)
                              skip-names
                              depth
                              world))

(defun get-names (names-and-arities)
  (if (endp names-and-arities)
      nil
      (cons (car (car names-and-arities))
            (get-names (cdr names-and-arities)))))

(defun count-real-args-aux (args)
  (if (endp args)
      0
      (if (member (car args)
                  '(&whole &optional &rest &body &key &allow-other-keys))
          0
          (1+ (count-real-args-aux (cdr args))))))

(defun count-real-args (args)
  (let ((res (count-real-args-aux args)))
    (if (= res 0)
        2
        res)))

(defun get-arities (fnnames world)
  (if (endp fnnames)
      nil
      (if (consp (car fnnames))
          (cons (car fnnames)
                (get-arities (cdr fnnames) world))
          (let ((nargs (acl2::arity (car fnnames) world)))
            (if (not (null nargs))
                (cons (cons (car fnnames)
                            (acl2::arity (car fnnames) world))
                      (get-arities (cdr fnnames) world))
                (let ((args (acl2::getprop
                             (car fnnames)
                             'acl2::macro-args
                             nil
                             'current-acl2-world
                             world)))
                  (if args
                      (cons (cons (car fnnames)
                                  (count-real-args args))
                            (get-arities (cdr fnnames) world))
                      (get-arities (cdr fnnames) world))))))))

(defun get-term-templates (term defn-depth term-depth world)
  (declare (xargs :mode :program))
  (make-templates
   (get-arities (get-all-fnnames-in-term term
                                         (union-equal (get-names *DRLA-BUILTIN-PREDICATES*)
                                                      *DRLA-SKIP-FNNAMES*)
                                         defn-depth
                                         world)
                world)
   nil
   term-depth))

(defun get-boolean-templates (depth)
  (cons nil (make-templates '((OR . 2) (AND . 2) (NOT . 1)) nil depth)))



(defun combine-templates-aux (template base-terms
                              nterms nslots n)
  (declare (xargs :measure (nfix (1+ n))))
  (if (not (natp n))
      nil
      (mv-let (filled-template args)
          (fill-template
           template
           (get-arg-list base-terms nterms nslots n)
           nil)
        (declare (ignorable args))
        (cons filled-template
              (combine-templates-aux template base-terms
                                     nterms nslots (1- n))))))

(defun combine-templates (templates sub-templates)
  (if (endp templates)
      nil
      (let* ((template (car templates))
             (nslots (template-slots template nil))
             (nterms (len sub-templates)))
        (append (combine-templates-aux template sub-templates
                                       nterms nslots (1- (expt nterms nslots)))
                (combine-templates (cdr templates) sub-templates)))))

(defun add-quotes-to-values-aux (l)
  (if (endp l)
      nil
      (cons (list (caar l) `(quote ,(cadar l)))
            (add-quotes-to-values-aux (cdr l)))))

(defun add-quotes-to-values (l)
  (if (endp l)
      nil
      (cons (add-quotes-to-values-aux (car l))
            (add-quotes-to-values (cdr l)))))


(defun get-counterexamples-and-witnesses-from-result (cgen-state)
  (if (endp cgen-state)
      (mv nil nil)
      (let ((s-hist (assoc-eq 'cgen::s-hist cgen-state)))
        (if (null s-hist)
            (mv nil nil)
            (let* ((s-hist-0 (cdadr s-hist))
                   (outcomes (access cgen::s-hist-entry% s-hist-0 :test-outcomes))
                   (cts (access cgen::test-outcomes% outcomes :cts))
                   (wts (access cgen::test-outcomes% outcomes :wts)))
              (mv (add-quotes-to-values cts)
                  (add-quotes-to-values wts)))))))

(defun invoke-cgen-fn (form state)
  (declare (xargs :mode :program
                  :stobjs state))
  (mv-let (res cgen-state state)
      (cgen::prove/cgen
       form
       nil
       (cgen::make-cgen-state-fn
        form
        'gen-hyp
        '(:num-witnesses 50 :num-print-witnesses 50
          :num-counterexamples 50 :num-print-counterexamples 50)
        (w state))
       state)
    (if (or (eq res :falsifiable) (eq res :?))
        (mv-let (cts wts)
            (get-counterexamples-and-witnesses-from-result cgen-state)
          (mv nil cts wts state))
        (mv t form res state))))


(defun strip-constants (lst)
  (if (endp lst)
      nil
      (if (or (acl2-numberp (car lst)) (equal (car lst) t) (equal (car lst) nil))
          (strip-constants (cdr lst))
          (cons (car lst) (strip-constants (cdr lst))))))

(defun real-all-vars (form)
  (strip-constants (all-vars form)))

(defun filter-suggestions (form suggestions state)
  (declare (xargs :mode :program
                  :stobjs state))
  (if (endp suggestions)
      (mv nil nil state)
      (mv-let (erp res state)
          (acl2::prove$ `(implies ,(car suggestions) ,form))
        (mv-let (useful not-useful state)
            (filter-suggestions form (cdr suggestions) state)
          (if (and (not erp) res)
              (mv (cons (car suggestions) useful)
                  not-useful
                  state)
              (mv useful
                  (cons (car suggestions) not-useful)
                  state))))))


(defun display-list-of-suggestions (suggestions state)
  (declare (xargs :mode :program
                  :stobjs state))
  (if (endp suggestions)
      nil
      (prog2$
       (cw "    * ~x0~%" (car suggestions))
       (display-list-of-suggestions (cdr suggestions) state))))

(defun display-missing-hypothesis-result (form hyps state)
  (declare (xargs :mode :program
                  :stobjs state))
  (if (endp hyps)
      (prog2$
       (cw "~%No suggestions found~%")
       (value hyps))
      (prog2$
       (cw "~%~x0 suggestions found~%" (len hyps))
       (mv-let (useful not-useful state)
           (filter-suggestions form hyps state)
          (progn$
           (cw "~%~x0 suggestions succeeded in proving the theorem:~%"
               (if useful (len useful) 'No))
           (display-list-of-suggestions useful state)
           (cw "~%~x0 suggestions failed to prove the theorem:~%"
               (if not-useful (len not-useful) 'No))
           (display-list-of-suggestions not-useful state)
           (cw "~%")
           (value (append useful not-useful)))))))


(defun derive-missing-hypothesis-fn (form boolean-depth
                                     generate-comparisons
                                     predicate-depth
                                     defn-depth
                                     term-depth
                                     extra-predicates
                                     state)
  (declare (xargs :mode :program
                  :stobjs state))
  (mv-let (erp cts wts state)
      (invoke-cgen-fn form state)
    (if erp
        (prog2$
         (cw "~%Cgen found an error~%")
         (mv t 'cgen-error state))
        (if (null cts)
            (prog2$
             (cw "~%Cgen did not find any counterexamples~%")
             (mv t 'no-counterexamples-found state))
            (if (null wts)
                (prog2$
                 (cw "~%Cgen did not find any witnesses~%")
                 (mv t 'no-witnesses-found state))
                (mv-let (hyps state)
                    (get-terms-separating-all-logical-templates
                     (combine-templates (get-boolean-templates boolean-depth)
                                        (make-templates (append
                                                         *DRLA-BUILTIN-PREDICATES*
                                                         (get-arities
                                                          extra-predicates
                                                          (w state))
                                                         (if generate-comparisons
                                                             *DRLA-BUILTIN-COMPARISONS*
                                                             *DRLA-COMBINED-BUILTIN-PREDICATES*))
                                                        (append
                                                         *DRLA-BUILTIN-PREDICATES*
                                                         *DRLA-COMBINED-BUILTIN-PREDICATES*
                                                         (get-arities
                                                          extra-predicates
                                                          (w state)))
                                                        predicate-depth))
                     (cons nil (get-term-templates form defn-depth term-depth (w state)))
                     (if generate-comparisons
                         (append (real-all-vars form)
                                 *DRLA-BUILTIN-CONSTANTS*)
                         (real-all-vars form))
                     wts
                     cts
                     nil
                     state)
                  (display-missing-hypothesis-result form hyps state)))))))

(defmacro derive-missing-hypothesis (form &key (boolean-depth '1)
                                            (generate-comparisons 'nil)
                                            (predicate-depth '1)
                                            (defn-depth '1)
                                            (term-depth '1)
                                            (extra-predicates 'nil))
  `(let* ((gc (f-get-global 'acl2::guard-checking-on state))
          (state (f-put-global 'acl2::guard-checking-on :none state)))
     (mv-let (erp val state)
         (derive-missing-hypothesis-fn ',form ,boolean-depth ,generate-comparisons
          ,predicate-depth
          ,defn-depth ,term-depth ,extra-predicates
          state)
       (let ((state (f-put-global 'acl2::guard-checking-on gc state)))
         (mv erp val state)))))

(defmacro drla (&rest args)
  `(derive-missing-hypothesis ,@args))



#|
(derive-missing-hypothesis (equal (reverse (reverse x)) x))
(derive-missing-hypothesis (equal (+ 0 x) x))
|#
