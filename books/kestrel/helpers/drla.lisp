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
      ((LAMBDA (X) (AND (equal x '0))) . 1)
      ((LAMBDA (X) (AND (equal x '1))) . 1)
      ((LAMBDA (X) (OR  (equal x 't) (equal x 'nil))) . 1)
      ((LAMBDA (X) (AND (consp x) (not (true-listp x)))) . 1)
      ((LAMBDA (X) (AND (consp x) (true-listp x))) . 1)
      ((LAMBDA (X) (AND (symbolp x) (not (equal x 't)) (not (equal x 'nil)))) . 1)
      ((LAMBDA (X) (AND (equal x 't))) . 1)
      ((LAMBDA (X) (AND (equal x 'nil))) . 1)
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

(defun make-templates-aux (function-list templates)
  (if (endp function-list)
      nil
      (append (map-cons (car (car function-list))
                        (cross-n (cons nil templates)
                                 (cdr (car function-list)))
                        nil)
              (make-templates-aux (cdr function-list) templates))))

(defun make-templates (function-list depth)
  (if (zp depth)
      nil
      (let ((templates (make-templates function-list (1- depth))))
        (union-equal templates
                     (make-templates-aux function-list templates)))))

(defun template-slots (template is-list)
  (if (endp template)
      (if is-list 0 1)
      (if is-list
          (+ (template-slots (car template) nil)
             (template-slots (cdr template) t))
          (template-slots (cdr template) t))))

(defun all-true (term witnesses state)
  (declare (xargs :mode :program
           :stobjs state))
  (if (endp witnesses)
      (mv t state)
      (mv-let (erp stobjs-value state)
          (with-output! :off (acl2::warning acl2::error)
            (trans-eval `(let ,(car witnesses) ,term) 'drla-ctx state nil))
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
            (trans-eval `(let ,(car counterexamples) ,term) 'drla-ctx state nil))
        (if (or erp (cdr stobjs-value))
            (mv nil state)
            (all-false term (cdr counterexamples) state)))))

(defun separates (term witnesses counterexamples state)
  (declare (xargs :mode :program
                  :stobjs state))
  (mv-let (goodp state)
      (all-true term witnesses state)
    (if (not goodp)
        (mv nil state)
        (all-false term counterexamples state))))

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
                (get-terms-separating-template-aux template base-terms
                                                   nterms nslots (1- n)
                                                   witnesses counterexamples
                                                   (cons term acc)
                                                   state)
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

(defun get-arities (fnnames world)
  (if (endp fnnames)
      nil
      (let ((nargs (acl2::arity (car fnnames) world)))
        (if (not (null nargs))
            (cons (cons (car fnnames)
                        (acl2::arity (car fnnames) world))
                  (get-arities (cdr fnnames) world))
            (get-arities (cdr fnnames) world)))))

(defun get-term-templates (term defn-depth term-depth world)
  (declare (xargs :mode :program))
  (make-templates
   (get-arities (get-all-fnnames-in-term term
                                         (union-equal (get-names *DRLA-BUILTIN-PREDICATES*)
                                                      *DRLA-SKIP-FNNAMES*)
                                         defn-depth
                                         world)
                world)
   term-depth))

(defun get-boolean-templates (depth)
  (cons nil (make-templates '((OR . 2) (AND . 2) (NOT . 1)) depth)))



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
    (if (eq res :falsifiable)
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

(defun derive-missing-hypothesis-fn (form boolean-depth
                                     generate-comparisons
                                     predicate-depth
                                     defn-depth
                                     term-depth
                                     state)
  (declare (xargs :mode :program
                  :stobjs state))
  (mv-let (erp cts wts state)
      (invoke-cgen-fn form state)
    (if erp
        (mv t 'cgen-error state)
        (mv-let (hyps state)
            (get-terms-separating-all-logical-templates
             (combine-templates (get-boolean-templates boolean-depth)
                                (make-templates (append
                                                 *DRLA-BUILTIN-PREDICATES*
                                                 (if generate-comparisons
                                                     *DRLA-BUILTIN-COMPARISONS*
                                                     *DRLA-COMBINED-BUILTIN-PREDICATES*))
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
          (mv nil hyps state)))))

(defmacro derive-missing-hypothesis (form &key (boolean-depth '1)
                                            (generate-comparisons 'nil)
                                            (predicate-depth '1)
                                            (defn-depth '1)
                                            (term-depth '1))
  `(let* ((gc (f-get-global 'acl2::guard-checking-on state))
          (state (f-put-global 'acl2::guard-checking-on :none state)))
     (mv-let (erp val state)
         (derive-missing-hypothesis-fn ',form ,boolean-depth ,generate-comparisons
          ,predicate-depth
          ,defn-depth ,term-depth
          state)
       (let ((state (f-put-global 'acl2::guard-checking-on gc state)))
         (mv erp val state)))))



#|
(derive-missing-hypothesis (equal (reverse (reverse x)) x))
(derive-missing-hypothesis (equal (+ 0 x) x))
|#
