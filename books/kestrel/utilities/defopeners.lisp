; A utility to build "opener" rules
;
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains a utility for making opener rules for recursive
;; functions.  Using such rules can be faster and more predictable than relying
;; on ACL2's heuristics to decide whether to open calls to recursive functions.
;; (Opener rules are also used by the Axe tool, which lacks such heuristics, for
;; which they help to avoid rewrite loops.)  Essentially, one opener rule is
;; produced for each top-level IF branch in the function (where an IF branch
;; can be considered top-level even if there are lambdas around it).

;; Unlike the tool in books/misc/defopener, this one doesn't do any
;; simplification.

;; Terminology: The "opener" rules for a function include the "unroll" rules
;; and the "base case" rules.

;; TODO: handle ignored let-bound params

;; TODO: ACL2 must do something like this when generating the induction scheme for a function

;; TODO: Add redundancy checking.

;; TODO: Perhaps have this traffic in untranslated terms, to produce nicer
;; theorems (but that might be hard in general).

;; TODO: give an error if there are not base rules and unroll rules (something
;; went wrong trying to analyze the body)

;; TODO: Verify guards

(include-book "world") ; for fn-body
(include-book "kestrel/terms-light/expr-calls-fn" :dir :system)
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(include-book "symbol-term-alistp")
;(include-book "terms")
(include-book "pack")
(include-book "conjunctions")
(include-book "misc/install-not-normalized" :dir :system)
(include-book "user-interface") ;for control-screen-output
(include-book "defthm-forms")
(include-book "kestrel/alists-light/keep-pairs" :dir :system)
(include-book "remove-guard-holders")
(local (include-book "state"))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

(local (in-theory (disable mv-nth
                           w
                           true-listp
                           PLIST-WORLDP)))

;; end of library stuff

(defun some-expr-calls-some-fn (fns exprs)
  (declare (xargs :guard (and (symbol-listp fns)
                              (pseudo-term-listp exprs))))
  (if (atom fns)
      nil
    (or (some-expr-calls-fn (first fns) exprs)
        (some-expr-calls-some-fn (rest fns) exprs))))

(defun expr-calls-some-fn (fns expr)
  (declare (xargs :guard (and (symbol-listp fns)
                              (pseudo-termp expr))))
  (if (atom fns)
      nil
    (or (expr-calls-fn (first fns) expr)
        (expr-calls-some-fn (rest fns) expr))))

;; ;count the number of branches of the ITE nest that are base cases and the number that contain recursive calls
;; ;returns (mv base-case-count recursive-case-count)
;; (defun count-and-recursive-cases-bases-aux (fn term base-case-count recursive-case-count)
;;   (declare (xargs :measure (acl2-count term)
;;                   :verify-guards nil
;;                   :guard (and (symbolp fn)
;;                               (natp base-case-count)
;;                               (natp recursive-case-count)
;;                               (pseudo-termp term))))
;;   (if (and (consp term)
;;            (eq 'if (ffn-symb term)))
;;       (mv-let
;;        (base-case-count recursive-case-count) ;fixme: what if the recursive call is in the IF test?
;;        (count-and-recursive-cases-bases-aux fn (farg2 term) base-case-count recursive-case-count)
;;        (count-and-recursive-cases-bases-aux fn (farg3 term) base-case-count recursive-case-count))
;;     ;;not an if, so just check whether it contains a recursive call:
;;     (if (expr-calls-fn fn term)
;;         (mv base-case-count (+ 1 recursive-case-count))
;;       (mv (+ 1 base-case-count) recursive-case-count))))

;; (defthm natp-of-val-0-of-count-and-recursive-cases-bases-aux
;;   (implies (natp base-case-count)
;;            (natp (mv-nth 0 (count-and-recursive-cases-bases-aux fn term base-case-count recursive-case-count)))))

;; (defthm natp-of-val-1-of-count-and-recursive-cases-bases-aux
;;   (implies (natp recursive-case-count)
;;            (natp (mv-nth 1 (count-and-recursive-cases-bases-aux fn term base-case-count recursive-case-count)))))

;; (verify-guards count-and-recursive-cases-bases-aux)

;; ;returns (mv base-case-count recursive-case-count)
;; (defun count-and-recursive-cases-bases (fn term)
;;   (declare (xargs :guard (and (symbolp fn)
;;                               (pseudo-termp term))))
;;   (count-and-recursive-cases-bases-aux fn term 0 0))

(defund add-hyp-to-claim (hyp claim)
  (declare (xargs :guard t))
  (if (and (consp claim)
           (eq 'implies (ffn-symb claim))
           (consp (cdr claim))
           (consp (cdr (cdr claim))))
        `(implies ,(make-conjunction-from-list (list hyp (farg1 claim)))
                  ,(farg2 claim))
    `(implies ,hyp
              ,claim)))

(defthm pseudo-termp-of-add-hyp-to-claim
  (implies (and (pseudo-termp hyp)
                (pseudo-termp claim))
           (pseudo-termp (add-hyp-to-claim hyp claim)))
  :hints (("Goal" :in-theory (enable add-hyp-to-claim))))

;todo: collect the HYPS into an AND?:
;; (defun add-hyps-to-claim (hyps claim)
;;   (declare (xargs :guard (true-listp hyps)))
;;   (if (endp hyps)
;;       claim
;;     (let ((claim (add-hyp-to-claim (first hyps) claim)))
;;       (add-hyps-to-claim (rest hyps) claim))))

(defun add-hyps-to-claim (hyps claim)
  (declare (xargs :guard (true-listp hyps)))
  (if (endp hyps)
      claim
    (add-hyp-to-claim (first hyps) (add-hyps-to-claim (rest hyps) claim))))

(defthm pseudo-termp-of-add-hyps-to-claim
  (implies (and (pseudo-term-listp hyps)
                (pseudo-termp claim))
           (pseudo-termp (add-hyps-to-claim hyps claim))))

(defund add-hyps-to-claims (hyps claims)
  (declare (xargs :guard (and (true-listp hyps)
                              (true-listp claims))))
  (if (endp claims)
      nil
    (cons (add-hyps-to-claim hyps (first claims))
          (add-hyps-to-claims hyps (rest claims)))))

(defthm len-of-add-hyps-to-claims
  (equal (len (add-hyps-to-claims hyps claims))
         (len claims))
  :hints (("Goal" :in-theory (enable add-hyps-to-claims))))

(defthm pseudo-termp-of-add-hyps-to-claims
  (implies (and (pseudo-term-listp hyps)
                (pseudo-term-listp claims))
           (pseudo-term-listp (add-hyps-to-claims hyps claims)))
  :hints (("Goal" :in-theory (enable add-hyps-to-claims))))

;; ;finds free vars in a term
;; (mutual-recursion
;;  (defun vars-in-term (term)
;;    (if (variablep term)
;;        (list term)
;;      (if (fquotep term)
;;          nil
;;        (if (consp (car (ffn-symb term))) ;; It's a lambda application: ((lambda <formals> <body>) ...<actuals>...)
;;            (let ((lambda-formals (second (ffn-symb term)))
;;                  (lambda-body (third (ffn-symb term)))
;;                  (lambda-actuals (fargs term)))
;;              (union-eq (vars-in-term-lst lambda-actuals)
;;                        ;;fixme is this always nil, since lambda have to be complete?:
;;                        (set-difference-eq (vars-in-term lambda-body)
;;                                           lambda-formals)
;;                        ))
;;          (vars-in-term-lst (fargs term))))))

;;  (defun vars-in-term-lst (term-lst)
;;    (if (endp term-lst)
;;        nil
;;      (union-eq (vars-in-term (car term-lst))
;;                (vars-in-term-lst (cdr term-lst))))))

;; ;fixme think this through
;; ;claim is a nest of implies bottoming out in an (equal <function-call> <body>) where <body> and the conditions of the implies may already have lambdas wrapped around them?
;; ;the point of this is that we don't want to wrap the function call buried deep in the equality
;; ;; TOOD: A nest of implies may no longer be possible here.
;; (defun wrap-lambda-around-claim (claim lambda-formals lambda-actuals)
;;   (declare (xargs :guard (and (pseudo-termp claim)
;;                               (pseudo-term-listp lambda-actuals)
;;                               (symbol-listp lambda-formals)
;;                               (equal (len lambda-formals)
;;                                      (len lambda-actuals)))))
;;   (if (and (call-of 'implies claim)
;;            (consp (cdr claim))       ;for guard proofs
;;            (consp (cdr (cdr claim))) ;for guard proofs
;;            )
;;       ;;fixme: Improve Axe to support hyps that are lambdas.  For now we have to beta reduce here:
;;       `(implies ,(beta-reduce ;(wrap-lambda-around-claim (farg1 claim) lambda-formals lambda-actuals)
;;                   `((lambda ,lambda-formals ,(farg1 claim)) ,@lambda-actuals))
;;                 ,(wrap-lambda-around-claim (farg2 claim) lambda-formals lambda-actuals))
;;     (if (and (call-of 'equal claim)
;;              (consp (cdr claim))       ;for guard proofs
;;              (consp (cdr (cdr claim))) ;for guard proofs
;;              (true-listp claim)
;;              )
;;         (let ((function-call (farg1 claim))
;;               (body (farg2 claim)))
;;           `(equal ,function-call
;;                   ((lambda ,lambda-formals ,body) ,@lambda-actuals)
;;                   ;;,(wrap-lambda-around-claim body lambda-formals lambda-actuals)
;;                   ))
;;       ;;normal case:
;;       `((lambda ,lambda-formals ,claim) ,@lambda-actuals))))

;; (defthm pseudo-termp-of-caddar-of-wrap-lambda-around-claim
;;   (implies (and (pseudo-termp claim))
;;            (pseudo-termp (caddar (wrap-lambda-around-claim claim lambda-formals lambda-actuals)))))

;; (defthm pseudo-termp-of-wrap-lambda-around-claim
;;   (implies (and (pseudo-termp claim)
;;                 (symbol-listp lambda-formals)
;;                 (pseudo-term-listp lambda-actuals)
;;                 (equal (len lambda-formals)
;;                        (len lambda-actuals)))
;;            (pseudo-termp (wrap-lambda-around-claim claim lambda-formals lambda-actuals))))

;; ;; (defthm wrap-lambda-around-claim-type-2
;; ;;   (implies (and (pseudo-termp claim))
;; ;;            (equal (len (car (wrap-lambda-around-claim claim lambda-formals lambda-actuals)))
;; ;;                   3)))

;; (verify-guards wrap-lambda-around-claim :otf-flg t)

;; (defun wrap-lambda-around-claims (claims lambda-formals lambda-actuals)
;;   (declare (xargs :guard (and (pseudo-term-listp claims)
;;                               (PSEUDO-TERM-LISTP LAMBDA-ACTUALS)
;;                               (SYMBOL-LISTP LAMBDA-FORMALS)
;;                               (EQUAL (LEN LAMBDA-FORMALS)
;;                                      (LEN LAMBDA-ACTUALS)))))
;;   (if (endp claims)
;;       nil
;;     (let* ((claim (first claims))
;; ;           (claim-vars (vars-in-term claim))
;;            )
;;       (cons (wrap-lambda-around-claim claim lambda-formals lambda-actuals)
;;             (wrap-lambda-around-claims (rest claims) lambda-formals lambda-actuals)))))

;; (defthm pseudo-term-listp-of-wrap-lambda-around-claims
;;   (implies (and (pseudo-term-listp lambda-actuals)
;;                 (pseudo-term-listp claims)
;;                 (symbol-listp lambda-formals)
;;                 (equal (len lambda-formals)
;;                        (len lambda-actuals)))
;;            (pseudo-term-listp (wrap-lambda-around-claims claims lambda-formals lambda-actuals))))

;; There is already a function call symbol-term-alistp
(defun renamingsp (renamings)
  (declare (xargs :guard t))
  (if (atom renamings)
      (null renamings)
    (and (symbol-term-alistp (first renamings))
         (renamingsp (rest renamings)))))

(local
 (defthm pseudo-term-listp-of-strip-cdrs-when-symbol-term-alistp
   (implies (symbol-term-alistp alist)
            (pseudo-term-listp (strip-cdrs alist)))))

(defthm pseudo-term-listp-of-strip-cdrs-of-keep-pairs
  (implies (pseudo-term-listp (strip-cdrs alist))
           (pseudo-term-listp (strip-cdrs (keep-pairs keys alist)))))

;; Returns (mv term term-vars).  TERM may be untranslated (may contain
;; LETs). TERM-VARS should be the free vars in TERM.
(defun make-let-around-term (term renaming term-vars)
  (declare (xargs :guard (and ;; (pseudo-termp term)
                          (symbol-term-alistp renaming)
                          (symbol-listp term-vars))))
  (let* ((relevant-renaming (keep-pairs term-vars renaming)))
    (if (not relevant-renaming) ; no relevant bindings were present
        (mv term term-vars)
      (mv `(let ,(alist-to-doublets relevant-renaming) ,term)
          ;; new free vars:
          (union-eq
           (set-difference-eq term-vars
                              (strip-cars relevant-renaming))
           (free-vars-in-terms (strip-cdrs relevant-renaming)))))))

;; the renamings come innermost first
(defun make-lets-around-term (term renamings term-vars)
  (declare (xargs :guard (and ;; (pseudo-termp term) ; gets LETs added to it and so is not a pseudo-term
                          (renamingsp renamings)
                          (symbol-listp term-vars))))
  (if (endp renamings)
      term
    (mv-let (term term-vars)
      (make-let-around-term term (first renamings) term-vars)
      (make-lets-around-term term (rest renamings) term-vars))))

(defun make-lets-around-terms (terms renamings)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (renamingsp renamings))))
  (if (endp terms)
      nil
    (cons (make-lets-around-term (first terms) renamings (free-vars-in-term (first terms)))
          (make-lets-around-terms (rest terms) renamings))))

;; The hyps should have already been renamed.
;; Even though the result may contain AND, it is still a pseudo-term.
(defund make-opener-claim (fn-call term rev-hyps renamings)
  (declare (xargs :guard (and (pseudo-termp fn-call)
                              (pseudo-termp term)
                              (true-listp rev-hyps) ; may contain lets
                              (renamingsp renamings))))
  (let* ((term (make-lets-around-term term renamings (free-vars-in-term term)))
         (conclusion `(equal ,fn-call ,term)))
    (if (not rev-hyps)
        conclusion
      (if (equal 1 (len rev-hyps))
          `(implies ,(first rev-hyps)
                    ,conclusion)
        `(implies (and ,@(reverse rev-hyps))
                  ,conclusion)))))

;; (defthm pseudo-termp-of-make-opener-claim
;;   (implies (and (pseudo-termp fn-call)
;;                 (pseudo-termp term)
;;                 (pseudo-term-listp rev-hyps)
;;                 (renamingsp renamings))
;;            (pseudo-termp (make-opener-claim fn-call term rev-hyps renamings)))
;;   :hints (("Goal" :in-theory (enable make-opener-claim))))

;move
;todo name clash if the "2" is removed
(defund remove-trivial-bindings2 (alist)
  (declare (xargs :guard (alistp alist)))
  (if (endp alist)
      nil
    (let* ((pair (first alist))
           (key (car pair))
           (val (cdr pair)))
      (if (equal key val)
          ;; drop this pair
          (remove-trivial-bindings2 (rest alist))
        (cons pair (remove-trivial-bindings2 (rest alist)))))))

(defthm symbol-term-alistp-of-remove-trivial-bindings2
  (implies (symbol-term-alistp alist)
           (symbol-term-alistp (remove-trivial-bindings2 alist)))
  :hints (("Goal" :in-theory (enable symbol-term-alistp
                                     remove-trivial-bindings2))))

;returns (mv base-claims unroll-claims)
(defun make-unroll-and-base-claims-aux (term
                                        fns ;all the functions in the mut-rec nest
                                        fn-call
                                        rev-hyps
                                        renamings ;non-trivial let-bindings, innermost first
                                        )
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbol-listp fns)
                              (pseudo-termp fn-call)
                              (true-listp rev-hyps) ;(pseudo-term-listp rev-hyps)
                              (renamingsp renamings))
                  :verify-guards nil ; done below
                  ))
  (if (call-of 'if term)
      ;; TERM is an IF:
      (let* ((test (farg1 term)) ; apply the overarching LETs to the test
             (renamed-test (make-lets-around-term test renamings (free-vars-in-term test))))
        (mv-let
          (then-base-claims then-unroll-claims)
          ;; the claims from the then-branch get the IF test as a hyp
          (make-unroll-and-base-claims-aux (farg2 term) fns fn-call (cons renamed-test rev-hyps) renamings)
          (mv-let
            (else-base-claims else-unroll-claims)
            ;; the claims from the else-branch get the negated IF test as a hyp
            (make-unroll-and-base-claims-aux (farg3 term) fns fn-call (cons `(not ,renamed-test) rev-hyps) renamings)
            (if (and (not then-base-claims)
                     (not else-base-claims))
                ;; no base cases in either branch, so this whole branch is an -unroll case
                (mv nil ; no base-claims
                    (list (make-opener-claim fn-call term rev-hyps renamings)))
              (if (and (not then-unroll-claims)
                       (not else-unroll-claims))
                  ;; no recursive calls in either branch, so this whole branch is a -base case
                  (mv (list (make-opener-claim fn-call term rev-hyps renamings))
                      nil ; no unroll-claims
                      )
                (mv (append then-base-claims else-base-claims)
                    (append then-unroll-claims else-unroll-claims)))))))
    (if (and (consp term)
             (consp (ffn-symb term)))
        ;; TERM is a lambda application: ((lambda <formals> <body>) ...<actuals>...)
        (let ((lambda-formals (second (ffn-symb term)))
              (lambda-body (third (ffn-symb term)))
              (lambda-actuals (fargs term)))
          ;; FIXME: Think about this:  If there is a recursive call in one of the args, we just consider the whole term a recursive case:
          (if (some-expr-calls-some-fn fns lambda-actuals)
              (mv nil ; no base-claims
                  (list (make-opener-claim fn-call term rev-hyps renamings)))
            (let ((renaming (remove-trivial-bindings2 (pairlis$ lambda-formals lambda-actuals))))
              (mv-let
                (base-claims unroll-claims)
                (make-unroll-and-base-claims-aux lambda-body fns fn-call rev-hyps (cons renaming renamings))
                (if (not base-claims)
                    ;; no base cases, so this whole branch is an -unroll theorem
                    (mv nil ; no base-claims
                        (list (make-opener-claim fn-call term rev-hyps renamings)))
                  (if (not unroll-claims)
                      ;; no recursive calls, so this whole branch is a -base theorem
                      (mv (list (make-opener-claim fn-call term rev-hyps renamings))
                          nil ; no unroll-claims
                          )
                    (mv base-claims
                        unroll-claims)))))))
      ;; TERM is not an IF or LET:
      (if (expr-calls-some-fn fns term)
          ;; a recursive case, so make an unroll rule:
          (mv nil ; no base-claims
              (list (make-opener-claim fn-call term rev-hyps renamings)))
        ;; a base case, so make a base case rule:
        (mv (list (make-opener-claim fn-call term rev-hyps renamings))
            nil ; no unroll-claims
            )))))

;; (defthm pseudo-term-listp-of-mv-nth-0-of-make-unroll-and-base-claims-aux
;;   (implies (and (pseudo-termp fn-call)
;;                 (pseudo-termp term)
;;                 (pseudo-term-listp rev-hyps))
;;            (pseudo-term-listp (mv-nth 0 (make-unroll-and-base-claims-aux term fns fn-call rev-hyps renamings)))))

;; (defthm pseudo-term-listp-of-mv-nth-1-of-make-unroll-and-base-claims-aux
;;   (implies (and (pseudo-termp term)
;;                 (pseudo-termp fn-call)
;;                 (pseudo-term-listp rev-hyps))
;;            (pseudo-term-listp (mv-nth 1 (make-unroll-and-base-claims-aux term fns fn-call rev-hyps renamings)))))

(defthm true-listp-of-mv-nth-0-of-make-unroll-and-base-claims-aux
  (true-listp (mv-nth 0 (make-unroll-and-base-claims-aux term fns fn-call rev-hyps renamings))))

(defthm true-listp-of-mv-nth-1-of-make-unroll-and-base-claims-aux
  (true-listp (mv-nth 1 (make-unroll-and-base-claims-aux term fns fn-call rev-hyps renamings))))

(verify-guards make-unroll-and-base-claims-aux)

;; ;;Result is an untranslated term
;; (defun clean-up-hyps-in-claim (claim)
;;   (declare (xargs :guard (pseudo-termp claim)))
;;   (if (not (and (call-of 'implies claim)
;;                 (= 2 (len (fargs claim)))))
;;       claim
;;     (let ((hyp (farg1 claim))
;;           (body (farg2 claim)))
;;       (let ((hyp-conjuncts (get-conjuncts hyp)))
;;         (if (= 1 (len hyp-conjuncts))
;;             ;; only one conjunct, so no need to insert an AND:
;;             `(implies ,(first hyp-conjuncts)
;;                       ,body)
;;           `(implies (and ,@hyp-conjuncts)
;;                     ,body))))))

(defun make-base-theorems (claims num totalnum defthmnameprefix fn formals disable)
  (declare (xargs :guard (and (natp num)
                              (natp totalnum)
                              (symbolp fn)
                              (true-listp claims)
                              (symbolp defthmnameprefix))))
  (if (endp claims)
      nil
    (let* ((claim (first claims))
           ;;(claim (clean-up-hyps-in-claim claim))
           )
      (cons `(,(if disable 'defthmd 'defthm)
              ,(if (> totalnum 1)
                   (add-suffix defthmnameprefix (concatenate 'string "-" (nat-to-string num)))
                 defthmnameprefix)
              ,claim
              :hints (("Goal" ;:in-theory (enable ,fn)
                       :expand ((,fn ,@formals))
                       :in-theory (union-theories '(,(add-suffix fn "$NOT-NORMALIZED"))
                                                  (theory 'minimal-theory)))))
            (make-base-theorems (rest claims) (+ 1 num) totalnum defthmnameprefix fn formals disable)))))

(defthm defthm-form-listp-of-make-base-theorems
  (implies (symbolp defthmnameprefix)
           (defthm-form-listp (make-base-theorems claims num totalnum defthmnameprefix fn formals disable)))
  :hints (("Goal" :in-theory (enable make-base-theorems defthm-form-listp defthm-formp))))

(defun make-unroll-theorems (claims num totalnum defthmnameprefix fn formals disable)
  (declare (xargs :guard (and (natp num)
                              (natp totalnum)
                              (symbolp fn)
                              (true-listp claims)
                              (symbolp defthmnameprefix))))
  (if (endp claims)
      nil
    (let* ((claim (first claims))
           ;;(claim (clean-up-hyps-in-claim claim))
           )
      (cons `(,(if disable 'defthmd 'defthm)
              ,(if (> totalnum 1)
                   (add-suffix defthmnameprefix (concatenate 'string "-" (nat-to-string num)))
                 defthmnameprefix)
              ,claim
              :hints (("Goal" ;:in-theory (enable ,fn)
                       :expand ((,fn ,@formals))
                       :in-theory (union-theories '(,(add-suffix fn "$NOT-NORMALIZED"))
                                                  (theory 'minimal-theory)))))
            (make-unroll-theorems (rest claims) (+ 1 num) totalnum defthmnameprefix fn formals disable)))))

(defthm defthm-form-listp-of-make-unroll-theorems
  (implies (symbolp defthmnameprefix)
           (defthm-form-listp (make-unroll-theorems claims num totalnum defthmnameprefix fn formals disable)))
  :hints (("Goal" :in-theory (enable make-unroll-theorems defthm-form-listp defthm-formp))))


;;         (mv (cons `(defthm ,(if (> total-unroll-count 1)
;;                                 ;throughout, we use the package of fn for the names of the base and opener rules
;;                                 ;todo: make a version of pack for strings and use it here?
;;                                 (intern-in-package-of-symbol (symbol-name (pack$ fn '-unroll- (nat-to-string unroll-count-acc))) fn)
;;                               (intern-in-package-of-symbol (symbol-name (pack$ fn '-unroll)) fn))
;;                      (implies (and ,@(reverse path-conjuncts))
;;                               (equal (,fn ,@formals)
;;                                      ,term))
;;                      :hints (("Goal" ;:in-theory (enable ,fn)
;;                               ;;sometimes the expand hint doesn't fire (e.g., if one of the params is known to be equal to a constant on this branch):
;;                               :expand ((,fn ,@formals))
;;                               :in-theory (union-theories '(,fn) (theory 'minimal-theory))
;;                               )))
;;                   theorems-acc)
;;             base-count-acc
;;             (+ 1 unroll-count-acc))

;; (defthm natp-of-val-1-of-make-unroll-and-base-theorems-aux
;;   (implies (natp base-count-acc)
;;            (natp (mv-nth 1 (make-unroll-and-base-theorems-aux term fn formals path-conjuncts total-base-count total-unroll-count base-count-acc unroll-count-acc theorems-acc)))))

;; (defthm natp-of-val-2-of-make-unroll-and-base-theorems-aux
;;   (implies (natp unroll-count-acc)
;;            (natp (mv-nth 2 (make-unroll-and-base-theorems-aux term fn formals path-conjuncts total-base-count total-unroll-count base-count-acc unroll-count-acc theorems-acc)))))

;(verify-guards make-unroll-and-base-theorems-aux)

(defun clear-keyword-in-keyword-value-list (key l)
  (declare (xargs :guard (and (symbolp key)
                              (keyword-value-listp l))))
  (if (endp l)
      nil
    (if (eq key (first l)) ;skip the key and its value
        (clear-keyword-in-keyword-value-list key (cddr l))
      (cons key
            (cons (second l)
                  (clear-keyword-in-keyword-value-list key (cddr l)))))))

;; Print theorems with CW (with hints elided)
(defun cw-theorems (thms)
  (declare (xargs :guard (defthm-form-listp thms)
                  :guard-hints (("Goal" :in-theory (enable defthm-form-listp)))))
  (if (endp thms)
      nil
    (let* ((thm (first thms))
           (elided-thm (clean-up-defthm thm)))
      (prog2$ (cw "~x0~%" elided-thm)
              (cw-theorems (rest thms))))))

(defund switch-package (symbol existing-symbol)
  (declare (xargs :guard (and (symbolp symbol)
                              (symbolp existing-symbol))))
  (intern-in-package-of-symbol (symbol-name symbol) existing-symbol))

;; lets us call strip-cadrs on a list of defthms
(defthmd all->=-len-when-defthm-form-listp
  (implies (defthm-form-listp forms)
           (all->=-len forms 2))
  :hints (("Goal" :in-theory (enable defthm-form-listp defthm-formp >=-len))))

;; Returns (mv event generated-names).
(defund make-unroll-and-base-theorems (fn all-fns-in-nest hyps disable suffix verbose wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (not (eq 'quote fn))
                              (symbol-listp all-fns-in-nest)
                              (true-listp hyps)
                              ;;(pseudo-term-listp hyps) ; todo: not necessarily true?
                              (symbolp suffix)
                              (plist-worldp wrld)
                              )
                  :guard-hints (("Goal" :in-theory (enable all->=-len-when-defthm-form-listp)))))
  (let* ((body (fn-body fn t wrld))
         (body (remove-guard-holders-and-clean-up-lambdas body))
         (formals (fn-formals fn wrld)))
    (mv-let (base-claims unroll-claims)
      (make-unroll-and-base-claims-aux body all-fns-in-nest `(,fn ,@formals)
                                       nil ; no hyps (can't pass in user hyps here, since they may not be pseudo-terms)
                                       nil ; no renamings yet
                                       )
      (b* (;; Now add the user hyps to the claims:
           (base-claims (add-hyps-to-claims hyps base-claims))
           (unroll-claims (add-hyps-to-claims hyps unroll-claims))
           (base-theorems-name-root (pack$ fn '-base)) ;todo: use add-suffix to get this in the same package as fn?  also below...
           (base-theorems-name-root (if suffix
                                        (pack$ base-theorems-name-root suffix)
                                      base-theorems-name-root))
           (base-theorems-name-root (switch-package base-theorems-name-root fn))
           (unroll-theorems-name-root (pack$ fn '-unroll))
           (unroll-theorems-name-root (if suffix
                                          (pack$ unroll-theorems-name-root suffix)
                                        unroll-theorems-name-root))
           (unroll-theorems-name-root (switch-package unroll-theorems-name-root fn))
           (base-theorems (make-base-theorems base-claims 1
                                              (len base-claims)
                                              base-theorems-name-root
                                              fn formals disable))
           (unroll-theorems (make-unroll-theorems unroll-claims 1
                                                  (len unroll-claims)
                                                  unroll-theorems-name-root
                                                  fn formals disable))
           (base-theorem-names (strip-cadrs base-theorems))
           (unroll-theorem-names (strip-cadrs unroll-theorems))
           (- (and verbose
                   (progn$ (cw "Base theorems for ~x0:~%" fn)
                           (cw-theorems base-theorems)
                           (cw "Unroll theorems for ~x0:~%" fn)
                           (cw-theorems unroll-theorems)))))
        (mv `(progn (encapsulate ()
                      (local (install-not-normalized ,fn))
                      (set-ignore-ok t)
                      ,@base-theorems
                      ,@unroll-theorems)
                    (value-triple ',(append base-theorem-names unroll-theorem-names)))
            (append base-theorem-names unroll-theorem-names))))))

;TODO: If fn is non-recursive, just make a single rule...    or should it be an error to call defopeners?

;for non-mut-rec.  Returns an event.
;; KEEP IN SYNC WITH DEFOPENERS-NAMES-FN.
(defun defopeners-fn (fn hyps disable suffix verbose state)
  (declare (xargs :guard (and (symbolp fn)
                              (not (eq 'quote fn))
                              (true-listp hyps)
                              (symbolp suffix))
                  :stobjs state))
  (mv-let (event names)
    (make-unroll-and-base-theorems fn (list fn) hyps disable suffix verbose (w state))
    (declare (ignore names))
    event))

;hyps should be a list of terms over the formals of the function (can include syntaxp, etc.)
;; KEEP IN SYNC WITH DEFOPENERS-NAMES.
(defmacro defopeners (fn &key
                         (hyps 'nil)
                         (disable 'nil)
                         (verbose 'nil)
                         (suffix 'nil) ;nil or a symbol to add to the unroll and base rule names
                         )
  (control-screen-output
   (if (member-eq verbose '(t 't)) t nil) ;verbose
   `(make-event (defopeners-fn ',fn ',hyps ',disable ',suffix ',verbose state))))

;for non-mut-rec.  Returns a list of names
;; KEEP IN SYNC WITH DEFOPENERS-FN.
(defun defopeners-names-fn (fn hyps disable suffix verbose state)
  (declare (xargs :guard (and (symbolp fn)
                              (not (eq 'quote fn))
                              (true-listp hyps)
                              (symbolp suffix))
                  :stobjs state))
  (mv-let (event names)
    (make-unroll-and-base-theorems fn (list fn) hyps disable suffix verbose (w state))
    (declare (ignore event))
    names))

;; Returns the list of theorem names that defopeners would introduce.
;; KEEP IN SYNC WITH DEFOPENERS.
(defmacro defopeners-names (fn &key
                               (hyps 'nil)
                               (disable 'nil)
                               (verbose 'nil)
                               (suffix 'nil) ;nil or a symbol to add to the unroll and base rule names
                               )
  `(defopeners-names-fn ',fn ',hyps ',disable ',suffix ',verbose state))

;; Returns an event
(defun defopeners-mut-rec-fn (fn hyps disable suffix verbose state)
  (declare (xargs  :guard (and (symbolp fn)
                               (not (eq 'quote fn))
                               (true-listp hyps)
                               (symbolp suffix))
                   :stobjs state))
  (mv-let (event names)
    (make-unroll-and-base-theorems fn (fn-recursive-partners fn state) hyps disable suffix verbose (w state))
    (declare (ignore names))
    event))

;; TODO: Add defopeners-mut-rec-name, like defopeners-names.
;TODO: Call control-screen-output here, as above?
;TODO: Combine this with the non-mut-rec version (query the world to check whether it's a mut rec and what the other functions are)
(defmacro defopeners-mut-rec (fn &key
                                 (hyps 'nil)
                                 (disable 'nil)
                                 (verbose 'nil)
                                 (suffix 'nil) ;nil or a symbol to add to the unroll and base rule names)
                                 )
  `(make-event (defopeners-mut-rec-fn ',fn ',hyps ',disable ',suffix ',verbose state)))
