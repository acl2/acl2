; Correctness of the functions the rewriter uses to instantiate HIDE terms
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; The rewriter (see the HIDE cases of rewrite, in rewrite.lisp) rewrites a
;; term TERM under a substitution ALIST, and must return a term equal to the
;; instance TERM/ALIST.  It does not rewrite inside calls of HIDE (unless told
;; to expand them), so for (HIDE x) it builds a term equal to (HIDE x)/ALIST:
;;
;;   (HIDE ((lambda formals x) . actuals))
;;
;; where the single frame (formals . actuals) of the stack returned by
;; MAKE-STACK-FROM-ALIST binds the variables of ALIST to their values and any
;; other variables of x to themselves.  MAKE-LAMBDA-APPLICATION then drops
;; unused formals.
;;
;; Similarly, for a nest of lambdas whose innermost body is a call of HIDE
;; (LAMBDA-NEST-HIDEP), it "commutes" the lambdas and the HIDE: it builds
;;
;;   (HIDE <the nest without the HIDE>/ALIST)
;;
;; using LAMBDA-NEST-UNHIDE to remove the HIDE.
;;
;; This book proves that these terms have the right values, using an evaluator
;; that knows only HIDE and, for the connection to SUBLIS-VAR (the usual
;; meaning of TERM/ALIST), one that also knows the primitives that CONS-TERM
;; may evaluate.  It also proves that the frame binds all the variables of the
;; term and that the terms built are well-formed.

(include-book "kestrel/evaluators/defevaluator-plus" :dir :system)
(include-book "kestrel/evaluators/empty-eval" :dir :system)
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(include-book "kestrel/terms-light/lambdas-closed-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-nils-in-termp" :dir :system)
(local (include-book "make-lambda-application"))
(local (include-book "helpers"))
(local (include-book "kestrel/terms-light/empty-eval-helpers" :dir :system))
(local (include-book "kestrel/alists-light/alists-equiv-on" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

;; These functions are in :program mode in the sources.  We put them in
;; :logic mode here.
(verify-termination make-stack-from-alist)
(verify-termination lambda-nest-hidep)
(verify-termination lambda-nest-unhide)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; MAKE-STACK-FROM-ALIST

;; The values of the variables of a term under a substitution ALIST: the vars
;; bound by ALIST get the values of the terms they are bound to, and the others
;; keep their values.  This is the meaning of TERM/ALIST (see the connection
;; to SUBLIS-VAR below).  We state the results below using EMPTY-EVAL, which
;; knows no functions, when we can, since such results hold for every
;; evaluator.

;; Binding vars to their own values
(local
 (defthm cdr-of-assoc-equal-of-pairlis$-of-empty-eval-list-same
   (implies (and (member-equal key keys)
                 (symbolp key)
                 key)
            (equal (cdr (assoc-equal key (pairlis$ keys (empty-eval-list keys a))))
                   (cdr (assoc-equal key a))))
   :hints (("Goal" :in-theory (enable pairlis$ assoc-equal)))))

(local
 (defthm cdr-of-assoc-equal-for-make-stack-from-alist
   (implies (and (member-equal key vars)
                 (symbolp key)
                 key)
            (equal (cdr (assoc-equal key (append (pairlis$ (set-difference-equal vars formals)
                                                           (empty-eval-list (set-difference-equal vars formals) a))
                                                 (pairlis$ formals vals))))
                   (cdr (assoc-equal key (append (pairlis$ formals vals) a)))))))

(local
 (defthm alists-equiv-on-for-make-stack-from-alist
   (implies (and (subsetp-equal keys vars)
                 (symbol-listp keys)
                 (not (member-equal nil keys)))
            (alists-equiv-on keys
                             (append (pairlis$ (set-difference-equal vars formals)
                                               (empty-eval-list (set-difference-equal vars formals) a))
                                     (pairlis$ formals vals))
                             (append (pairlis$ formals vals) a)))
   :hints (("Goal" :in-theory (e/d (alists-equiv-on)
                                   (alists-equiv-on-of-append-arg2
                                    alists-equiv-on-of-append-arg3))))))

(local
 (defthm symbol-listp-of-free-vars-in-term-when-pseudo-termp
   (implies (pseudo-termp term)
            (symbol-listp (free-vars-in-term term)))))

(local
 (defthm subsetp-equal-of-append-of-set-difference-equal-same
   (implies (subsetp-equal x y)
            (subsetp-equal x (append (set-difference-equal y z) z)))
   :hints (("Goal" :in-theory (enable subsetp-equal)))))

;; The frame binds every variable of TERM.  This is the point of
;; make-stack-from-alist (see its comment): TERM can be the body of a closed
;; lambda whose formals are the variables of the frame.
(defthm subsetp-equal-of-free-vars-in-term-and-car-of-car-of-make-stack-from-alist
  (implies alist
           (subsetp-equal (free-vars-in-term term)
                          (car (car (make-stack-from-alist term alist))))))

;; The stack has a single frame, whose formals and actuals have the same
;; length.
(defthm make-stack-from-alist-shape
  (implies alist
           (let ((stack (make-stack-from-alist term alist)))
             (and (consp stack)
                  (not (cdr stack))
                  (equal (len (car (car stack)))
                         (len (cdr (car stack)))))))
  :rule-classes nil)

;; TERM/stack is TERM/ALIST: Evaluating TERM in an alist that binds just the
;; variables of the frame, to the values of the actuals, is like evaluating it
;; under ALIST.
(defthm make-stack-from-alist-correct
  (implies (and alist
                (pseudo-termp term)
                (not (member-equal nil (free-vars-in-term term))))
           (let ((frame (car (make-stack-from-alist term alist))))
             (equal (empty-eval term (pairlis$ (car frame)
                                               (empty-eval-list (cdr frame) a)))
                    (empty-eval term (append (pairlis$ (strip-cars alist)
                                                       (empty-eval-list (strip-cdrs alist) a))
                                             a)))))
  :hints (("Goal" :use ((:instance equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-alt
                                   (keys (free-vars-in-term term))
                                   (alist1 (pairlis$ (car (car (make-stack-from-alist term alist)))
                                                     (empty-eval-list (cdr (car (make-stack-from-alist term alist))) a)))
                                   (alist2 (append (pairlis$ (strip-cars alist)
                                                             (empty-eval-list (strip-cdrs alist) a))
                                                   a))))
           :in-theory (disable equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-alt
                               alists-equiv-on-of-append-arg2
                               alists-equiv-on-of-append-arg3
                               pairlis$-of-append-arg1))))

;; Evaluating a closed term in an extended alist
(local
 (defthm empty-eval-of-append-of-pairlis$-when-closed
   (implies (and (subsetp-equal (free-vars-in-term body) formals)
                 (pseudo-termp body))
            (equal (empty-eval body (append (pairlis$ formals vals) a))
                   (empty-eval body (pairlis$ formals vals))))
   :hints (("Goal" :use (:instance equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-alt
                                   (term body)
                                   (keys formals)
                                   (alist1 (append (pairlis$ formals vals) a))
                                   (alist2 (pairlis$ formals vals)))
            :in-theory (disable equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-alt)))))

;; The term built in the HIDE case of rewrite (inside the HIDE) has the value
;; of TERM/ALIST.
(defthm make-lambda-application-of-make-stack-from-alist-correct
  (implies (and alist
                (pseudo-termp term)
                (not (member-equal nil (free-vars-in-term term))))
           (let ((stack (make-stack-from-alist term alist)))
             (equal (empty-eval (make-lambda-application (car (car stack)) term (cdr (car stack))) a)
                    (empty-eval term (append (pairlis$ (strip-cars alist)
                                                       (empty-eval-list (strip-cdrs alist) a))
                                             a)))))
  :hints (("Goal" :use make-stack-from-alist-correct
           :in-theory (disable make-stack-from-alist-correct
                               make-stack-from-alist
                               make-lambda-application))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; LAMBDA-NEST-UNHIDE

(local (include-book "system/pseudo-termp-lemmas" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))

;; An evaluator that knows only HIDE
(defevaluator+ hide-eval hide)

;; Transfer some results about empty-eval to hide-eval:

(local
 (defthm equal-of-hide-eval-and-hide-eval-when-alists-equiv-on
   (implies (and (alists-equiv-on keys alist1 alist2)
                 (subsetp-equal (free-vars-in-term term) keys)
                 (pseudo-termp term))
            (equal (equal (hide-eval term alist1)
                          (hide-eval term alist2))
                   t))
   :hints (("Goal" :in-theory (e/d (hide-eval-of-fncall-args) (hide-eval-of-fncall-args-back))
            :use (:functional-instance equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-alt
                                       (empty-eval hide-eval)
                                       (empty-eval-list hide-eval-list))))))

(local
 (defthm hide-eval-of-append-of-pairlis$-when-closed
   (implies (and (subsetp-equal (free-vars-in-term body) formals)
                 (pseudo-termp body))
            (equal (hide-eval body (append (pairlis$ formals vals) a))
                   (hide-eval body (pairlis$ formals vals))))
   :hints (("Goal" :use (:instance equal-of-hide-eval-and-hide-eval-when-alists-equiv-on
                                   (term body)
                                   (keys formals)
                                   (alist1 (append (pairlis$ formals vals) a))
                                   (alist2 (pairlis$ formals vals)))
            :in-theory (disable equal-of-hide-eval-and-hide-eval-when-alists-equiv-on)))))

(local
 (defthm hide-eval-of-make-lambda-application
   (implies (and (not (member-equal nil (free-vars-in-term body)))
                 (pseudo-termp body))
            (equal (hide-eval (make-lambda-application formals body actuals) a)
                   (hide-eval body (append (pairlis$ formals (hide-eval-list actuals a)) a))))
   :hints (("Goal" :in-theory (e/d (hide-eval-of-fncall-args)
                                   (hide-eval-of-fncall-args-back
                                    make-lambda-application))
            :use (:functional-instance make-lambda-application-correct
                                       (empty-eval hide-eval)
                                       (empty-eval-list hide-eval-list))))))

(local
 (defthm hide-eval-of-make-lambda-application-of-make-stack-from-alist
   (implies (and alist
                 (pseudo-termp term)
                 (not (member-equal nil (free-vars-in-term term))))
            (let ((stack (make-stack-from-alist term alist)))
              (equal (hide-eval (make-lambda-application (car (car stack)) term (cdr (car stack))) a)
                     (hide-eval term (append (pairlis$ (strip-cars alist)
                                                       (hide-eval-list (strip-cdrs alist) a))
                                             a)))))
   :hints (("Goal" :in-theory (e/d (hide-eval-of-fncall-args)
                                   (hide-eval-of-fncall-args-back
                                    make-lambda-application
                                    make-stack-from-alist))
            :use (:functional-instance make-lambda-application-of-make-stack-from-alist-correct
                                       (empty-eval hide-eval)
                                       (empty-eval-list hide-eval-list))))))

;; Some facts about terms:

(local
 (defthm no-nils-in-termp-of-lambda-body
   (implies (and (no-nils-in-termp term)
                 (consp (car term)))
            (no-nils-in-termp (caddr (car term))))
   :hints (("Goal" :expand (no-nils-in-termp term)))))

(local
 (defthm no-nils-in-termp-of-cadr
   (implies (and (no-nils-in-termp term)
                 (consp (cdr term))
                 (not (equal 'quote (car term))))
            (no-nils-in-termp (cadr term)))
   :hints (("Goal" :expand ((no-nils-in-termp term)
                            (no-nils-in-termsp (cdr term)))))))

;; A nest of lambdas whose innermost body is a call of HIDE, or a call of HIDE.
(local
 (defun hide-nestp (term)
   (if (lambda-applicationp term)
       (hide-nestp (lambda-body (ffn-symb term)))
     (and (consp term)
          (eq 'hide (ffn-symb term))))))

(local
 (defthm hide-nestp-when-lambda-nest-hidep
   (implies (lambda-nest-hidep term)
            (hide-nestp term))))

;; Whether the innermost HIDE has an argument.  The case where it doesn't is
;; uninteresting but is allowed by PSEUDO-TERMP.
(local
 (defun hide-nest-with-argp (term)
   (if (lambda-applicationp term)
       (hide-nest-with-argp (lambda-body (ffn-symb term)))
     (consp (cdr term)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm pseudo-termp-of-lambda-nest-unhide-helper
   (implies (and (pseudo-termp term)
                 (hide-nestp term))
            (pseudo-termp (lambda-nest-unhide term)))
   :hints (("Goal" :in-theory (disable make-lambda-application)))))

;; LAMBDA-NEST-UNHIDE preserves pseudo-termp.
(defthm pseudo-termp-of-lambda-nest-unhide
  (implies (and (pseudo-termp term)
                (lambda-nest-hidep term))
           (pseudo-termp (lambda-nest-unhide term))))

;; The variables of (lambda-nest-unhide term) are among those of TERM (but see
;; below for the degenerate case where the HIDE has no argument).

;; The lambda step
(local
 (defthm subsetp-equal-of-free-vars-in-term-of-make-lambda-application-when-closed
   (implies (and (subsetp-equal (free-vars-in-term new-body) (free-vars-in-term body))
                 (subsetp-equal (free-vars-in-term body) formals)
                 (pseudo-termp new-body)
                 (symbol-listp formals)
                 (equal (len formals) (len args)))
            (subsetp-equal (free-vars-in-term (make-lambda-application formals new-body args))
                           (free-vars-in-terms args)))
   :hints (("Goal" :use ((:instance subsetp-equal-transitive-alt
                                    (x (free-vars-in-term new-body))
                                    (y (free-vars-in-term body))
                                    (z formals))
                         (:instance subsetp-equal-of-free-vars-in-term-of-make-lambda-application
                                    (body new-body)
                                    (actuals args)))
            :in-theory (disable make-lambda-application
                                subsetp-equal-transitive-alt
                                subsetp-equal-of-free-vars-in-term-of-make-lambda-application)))))

(local
 (defthmd free-vars-in-term-when-consp-and-not-quote
   (implies (and (consp term)
                 (not (equal 'quote (car term))))
            (equal (free-vars-in-term term)
                   (free-vars-in-terms (cdr term))))
   :hints (("Goal" :in-theory (enable free-vars-in-term)))))

(local
 (defthm subsetp-equal-of-free-vars-in-term-of-lambda-nest-unhide-helper
   (implies (and (hide-nest-with-argp term)
                 (hide-nestp term)
                 (pseudo-termp term)
                 (lambdas-closed-in-termp term))
            (subsetp-equal (free-vars-in-term (lambda-nest-unhide term))
                           (free-vars-in-term term)))
   :hints (("Goal" :in-theory (e/d (free-vars-in-term-when-consp-and-not-quote)
                                   (make-lambda-application))))))

(local
 (defthm not-member-equal-of-nil-and-free-vars-in-term-of-lambda-nest-unhide
   (implies (and (hide-nest-with-argp term)
                 (hide-nestp term)
                 (pseudo-termp term)
                 (lambdas-closed-in-termp term)
                 (no-nils-in-termp term))
            (not (member-equal nil (free-vars-in-term (lambda-nest-unhide term)))))
   :hints (("Goal" :use (subsetp-equal-of-free-vars-in-term-of-lambda-nest-unhide-helper
                         (:instance member-equal-when-subsetp-equal-1
                                    (x nil)
                                    (lst2 (free-vars-in-term (lambda-nest-unhide term)))
                                    (lst (free-vars-in-term term))))
            :in-theory (disable subsetp-equal-of-free-vars-in-term-of-lambda-nest-unhide-helper
                                member-equal-when-subsetp-equal-1
                                member-equal-when-subsetp-equal-2
                                lambda-nest-unhide
                                hide-nestp
                                hide-nest-with-argp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The degenerate case, where the innermost HIDE has no argument.  Then the
;; term is NIL, and so is the result of lambda-nest-unhide: a nest of lambdas
;; whose innermost body is NIL.

(local
 (defun nil-nestp (term)
   (if (and (consp term)
            (consp (car term)))
       (nil-nestp (lambda-body (ffn-symb term)))
     (equal term nil))))

(local
 (defun induct-nil-nestp (term a)
   (if (and (consp term)
            (consp (car term)))
       (induct-nil-nestp (lambda-body (ffn-symb term))
                         (pairlis$ (lambda-formals (ffn-symb term))
                                   (hide-eval-list (fargs term) a)))
     (list term a))))

(local
 (defthm hide-eval-when-nil-nestp
   (implies (nil-nestp term)
            (equal (hide-eval term a)
                   nil))
   :hints (("Goal" :induct (induct-nil-nestp term a)))))

(local
 (defthm nil-nestp-of-make-lambda-application
   (implies (nil-nestp body)
            (nil-nestp (make-lambda-application formals body actuals)))))

(local
 (defthm nil-nestp-of-lambda-nest-unhide
   (implies (and (hide-nestp term)
                 (not (hide-nest-with-argp term)))
            (nil-nestp (lambda-nest-unhide term)))
   :hints (("Goal" :in-theory (disable make-lambda-application nil-nestp)))))

(local
 (defun induct-hide-nestp (term a)
   (if (lambda-applicationp term)
       (induct-hide-nestp (lambda-body (ffn-symb term))
                          (pairlis$ (lambda-formals (ffn-symb term))
                                    (hide-eval-list (fargs term) a)))
     (list term a))))

(local
 (defthm hide-eval-when-hide-nestp-and-not-hide-nest-with-argp
   (implies (and (hide-nestp term)
                 (not (hide-nest-with-argp term)))
            (equal (hide-eval term a)
                   nil))
   :hints (("Goal" :induct (induct-hide-nestp term a)
            :expand ((:free (x) (hide x)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The main case

(local
 (defun induct-hide-nestp-2 (term a)
   (if (lambda-applicationp term)
       (induct-hide-nestp-2 (lambda-body (ffn-symb term))
                            (append (pairlis$ (lambda-formals (ffn-symb term))
                                              (hide-eval-list (fargs term) a))
                                    a))
     (list term a))))

(local
 (defthm hide-eval-of-lambda-nest-unhide-helper
   (implies (and (hide-nest-with-argp term)
                 (hide-nestp term)
                 (pseudo-termp term)
                 (lambdas-closed-in-termp term)
                 (no-nils-in-termp term))
            (equal (hide-eval (lambda-nest-unhide term) a)
                   (hide-eval term a)))
   :hints (("Goal" :induct (induct-hide-nestp-2 term a)
            :expand ((:free (x) (hide x)))
            :in-theory (disable make-lambda-application)))))

;; Removing the HIDE from a lambda nest whose innermost body is a call of HIDE
;; does not change its value.
(defthm lambda-nest-unhide-correct
  (implies (and (lambda-nest-hidep term)
                (pseudo-termp term)
                (lambdas-closed-in-termp term)
                (no-nils-in-termp term))
           (equal (hide-eval (lambda-nest-unhide term) a)
                  (hide-eval term a)))
  :hints (("Goal" :cases ((hide-nest-with-argp term)))))

;; The lambdas must be closed (as they are in a TERMP): otherwise, a free
;; variable of a lambda body, which always evaluates to NIL there, can be
;; captured from the outside (see lambda-nest-unhide-needs-closed-lambdas in
;; rewrite-hide-tests.lisp).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The two cases of rewrite

;; In the HIDE case of rewrite, TERM is (HIDE x), and the term built has the
;; value of TERM/ALIST.  (When ALIST is NIL, rewrite just uses TERM.)
(defthm rewrite-hide-case-correct
  (implies (and (equal (ffn-symb term) 'hide)
                (pseudo-termp term)
                (no-nils-in-termp term))
           (let* ((stack (make-stack-from-alist (fargn term 1) alist))
                  (inst-term (if alist
                                 (fcons-term* 'hide
                                              (make-lambda-application
                                               (caar stack)
                                               (fargn term 1)
                                               (cdar stack)))
                               term)))
             (equal (hide-eval inst-term a)
                    (hide-eval term (append (pairlis$ (strip-cars alist)
                                                      (hide-eval-list (strip-cdrs alist) a))
                                            a)))))
  :hints (("Goal" :cases ((consp (cdr term)))
           :expand ((:free (x) (hide x)))
           :in-theory (disable make-lambda-application
                               make-stack-from-alist))))

;; In the lambda-hide commuting case of rewrite, TERM is a nest of lambdas
;; whose innermost body is a call of HIDE, and the term built (a call of HIDE)
;; has the value of TERM/ALIST.
(defthm rewrite-lambda-nest-hide-case-correct
  (implies (and (lambda-nest-hidep term)
                (pseudo-termp term)
                (lambdas-closed-in-termp term)
                (no-nils-in-termp term))
           (let* ((new-body (lambda-nest-unhide term))
                  (stack (make-stack-from-alist new-body alist))
                  (inst-term
                   (fcons-term* 'hide
                                (if alist
                                    (make-lambda-application
                                     (caar stack)
                                     new-body
                                     (cdar stack))
                                  new-body))))
             (equal (hide-eval inst-term a)
                    (hide-eval term (append (pairlis$ (strip-cars alist)
                                                      (hide-eval-list (strip-cdrs alist) a))
                                            a)))))
  :hints (("Goal" :cases ((hide-nest-with-argp term))
           :expand ((:free (x) (hide x)))
           :in-theory (disable make-lambda-application
                               make-stack-from-alist
                               lambda-nest-unhide
                               lambda-nest-hidep
                               hide-nestp
                               hide-nest-with-argp
                               nil-nestp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Connection to SUBLIS-VAR

;; The results above say that the terms built have the values of TERM under
;; the alist that binds the variables of ALIST to the values of the terms they
;; are bound to.  That is the value of (sublis-var alist term), the usual
;; meaning of TERM/ALIST, as we now show.  Since sublis-var uses cons-term,
;; which may evaluate calls of primitives on constants, this needs an evaluator
;; that knows those primitives.

(local (include-book "clause-processors/sublis-var-meaning" :dir :system))

(defevaluator+ hide-cterm-eval
  ;; the primitives that cons-term may evaluate (as for cterm-ev):
  acl2-numberp binary-* binary-+ unary-- unary-/ < car cdr char-code characterp code-char
  complex complex-rationalp coerce cons consp denominator equal imagpart integerp
  intern-in-package-of-symbol numerator rationalp realpart stringp symbol-name
  symbol-package-name symbolp if not
  ;; and HIDE:
  hide)

(local
 (defthm hide-cterm-eval-of-sublis-var
   (implies (and (pseudo-termp form)
                 (not (assoc-equal nil alist)))
            (equal (hide-cterm-eval (sublis-var alist form) a)
                   (hide-cterm-eval form (append (pairlis$ (strip-cars alist)
                                                           (hide-cterm-eval-list (strip-cdrs alist) a))
                                                 a))))
   :hints (("Goal" :in-theory (e/d (hide-cterm-eval-of-fncall-args)
                                   (hide-cterm-eval-of-fncall-args-back))
            :use (:instance
                  (:functional-instance eval-of-sublis-var
                                        (cterm-ev hide-cterm-eval)
                                        (cterm-ev-lst hide-cterm-eval-list)
                                        (cterm-ev-alist (lambda (x a)
                                                          (pairlis$ (strip-cars x)
                                                                    (hide-cterm-eval-list (strip-cdrs x) a)))))
                  (x form))))))

;; The HIDE case of rewrite builds a term equal to (sublis-var alist term).
(defthm rewrite-hide-case-correct-sublis-var
  (implies (and (equal (ffn-symb term) 'hide)
                (pseudo-termp term)
                (no-nils-in-termp term)
                (not (assoc-equal nil alist)))
           (let* ((stack (make-stack-from-alist (fargn term 1) alist))
                  (inst-term (if alist
                                 (fcons-term* 'hide
                                              (make-lambda-application
                                               (caar stack)
                                               (fargn term 1)
                                               (cdar stack)))
                               term)))
             (equal (hide-cterm-eval inst-term a)
                    (hide-cterm-eval (sublis-var alist term) a))))
  :hints (("Goal" :in-theory (e/d (hide-cterm-eval-of-fncall-args)
                                  (hide-cterm-eval-of-fncall-args-back
                                   make-lambda-application
                                   make-stack-from-alist))
           :use (:functional-instance rewrite-hide-case-correct
                                      (hide-eval hide-cterm-eval)
                                      (hide-eval-list hide-cterm-eval-list)))))

;; The lambda-hide commuting case of rewrite builds a term equal to
;; (sublis-var alist term).
(defthm rewrite-lambda-nest-hide-case-correct-sublis-var
  (implies (and (lambda-nest-hidep term)
                (pseudo-termp term)
                (lambdas-closed-in-termp term)
                (no-nils-in-termp term)
                (not (assoc-equal nil alist)))
           (let* ((new-body (lambda-nest-unhide term))
                  (stack (make-stack-from-alist new-body alist))
                  (inst-term
                   (fcons-term* 'hide
                                (if alist
                                    (make-lambda-application
                                     (caar stack)
                                     new-body
                                     (cdar stack))
                                  new-body))))
             (equal (hide-cterm-eval inst-term a)
                    (hide-cterm-eval (sublis-var alist term) a))))
  :hints (("Goal" :in-theory (e/d (hide-cterm-eval-of-fncall-args)
                                  (hide-cterm-eval-of-fncall-args-back
                                   make-lambda-application
                                   make-stack-from-alist
                                   lambda-nest-unhide
                                   lambda-nest-hidep))
           :use (:functional-instance rewrite-lambda-nest-hide-case-correct
                                      (hide-eval hide-cterm-eval)
                                      (hide-eval-list hide-cterm-eval-list)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Well-formedness

(include-book "kestrel/terms-light/no-duplicate-lambda-formals-in-termp" :dir :system)
(local (include-book "kestrel/terms-light/termp" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))

;;; Results of LAMBDA-NEST-UNHIDE

;; If the HIDE has the right number of arguments, it has an argument.
(local
 (defthm hide-nest-with-argp-when-termp
   (implies (and (hide-nestp term)
                 (termp term w)
                 (equal (arity 'hide w) 1))
            (hide-nest-with-argp term))
   :hints (("Goal" :expand ((termp term w)
                            (len (cdr term)))))))

(local
 (defthm termp-of-lambda-nest-unhide-helper
   (implies (and (hide-nestp term)
                 (termp term w)
                 (equal (arity 'hide w) 1))
            (termp (lambda-nest-unhide term) w))
   :hints (("Goal" :in-theory (disable make-lambda-application)))))

(defthm termp-of-lambda-nest-unhide
  (implies (and (lambda-nest-hidep term)
                (termp term w)
                (equal (arity 'hide w) 1))
           (termp (lambda-nest-unhide term) w)))

(local
 (defthm lambdas-closed-in-termp-of-lambda-nest-unhide-helper
   (implies (and (hide-nestp term)
                 (pseudo-termp term)
                 (lambdas-closed-in-termp term))
            (lambdas-closed-in-termp (lambda-nest-unhide term)))
   :hints (("Goal" :in-theory (disable make-lambda-application)))))

(defthm lambdas-closed-in-termp-of-lambda-nest-unhide
  (implies (and (lambda-nest-hidep term)
                (pseudo-termp term)
                (lambdas-closed-in-termp term))
           (lambdas-closed-in-termp (lambda-nest-unhide term))))

(local
 (defthm no-duplicate-lambda-formals-in-termp-of-lambda-nest-unhide-helper
   (implies (and (hide-nestp term)
                 (pseudo-termp term)
                 (no-duplicate-lambda-formals-in-termp term))
            (no-duplicate-lambda-formals-in-termp (lambda-nest-unhide term)))
   :hints (("Goal" :in-theory (disable make-lambda-application)))))

(defthm no-duplicate-lambda-formals-in-termp-of-lambda-nest-unhide
  (implies (and (lambda-nest-hidep term)
                (pseudo-termp term)
                (no-duplicate-lambda-formals-in-termp term))
           (no-duplicate-lambda-formals-in-termp (lambda-nest-unhide term))))

;; The variables of (lambda-nest-unhide term) are among those of TERM.
(defthm subsetp-equal-of-free-vars-in-term-of-lambda-nest-unhide
  (implies (and (lambda-nest-hidep term)
                (termp term w)
                (equal (arity 'hide w) 1))
           (subsetp-equal (free-vars-in-term (lambda-nest-unhide term))
                          (free-vars-in-term term))))

(defthm no-nils-in-termp-of-lambda-nest-unhide
  (implies (and (lambda-nest-hidep term)
                (termp term w)
                (equal (arity 'hide w) 1))
           (no-nils-in-termp (lambda-nest-unhide term)))
  :hints (("Goal" :use (:instance no-nils-in-termp-when-termp
                                  (term (lambda-nest-unhide term)))
           :in-theory (disable no-nils-in-termp-when-termp
                               lambda-nest-unhide))))

;; The last two need more than the hyps of the other theorems (here, that the
;; HIDE has an argument, which TERMP ensures): when the HIDE has no argument,
;; NIL appears as a variable in the result (see
;; lambda-nest-unhide-when-hide-has-no-argument in rewrite-hide-tests.lisp).

;;; The frame made by MAKE-STACK-FROM-ALIST

(local (include-book "kestrel/terms-light/all-vars1" :dir :system))
(local (include-book "kestrel/lists-light/list-sets" :dir :system))

;; The formals of the frame are distinct, if the variables bound by ALIST are.
(defthm no-duplicatesp-equal-of-car-of-car-of-make-stack-from-alist
  (implies (no-duplicatesp-equal (strip-cars alist))
           (no-duplicatesp-equal (car (car (make-stack-from-alist term alist))))))

(defthm symbol-listp-of-car-of-car-of-make-stack-from-alist
  (implies (and (pseudo-termp term)
                (symbol-listp (strip-cars alist)))
           (symbol-listp (car (car (make-stack-from-alist term alist))))))

(defthm pseudo-term-listp-of-cdr-of-car-of-make-stack-from-alist
  (implies (and (pseudo-termp term)
                (pseudo-term-listp (strip-cdrs alist)))
           (pseudo-term-listp (cdr (car (make-stack-from-alist term alist))))))

(defthm term-listp-of-cdr-of-car-of-make-stack-from-alist
  (implies (and (termp term w)
                (term-listp (strip-cdrs alist) w))
           (term-listp (cdr (car (make-stack-from-alist term alist))) w)))

(defthm len-of-cdr-of-car-of-make-stack-from-alist
  (equal (len (cdr (car (make-stack-from-alist term alist))))
         (len (car (car (make-stack-from-alist term alist))))))

(local
 (defthm not-member-equal-of-nil-and-car-of-car-of-make-stack-from-alist
   (implies (and (no-nils-in-termp term)
                 (not (member-equal nil (strip-cars alist))))
            (not (member-equal nil (car (car (make-stack-from-alist term alist))))))))

(local
 (defthm no-nils-in-termsp-of-cdr-of-car-of-make-stack-from-alist
   (implies (and (no-nils-in-termp term)
                 (pseudo-termp term)
                 (no-nils-in-termsp (strip-cdrs alist)))
            (no-nils-in-termsp (cdr (car (make-stack-from-alist term alist)))))))

(local
 (defthm lambdas-closed-in-termsp-of-cdr-of-car-of-make-stack-from-alist
   (implies (and (pseudo-termp term)
                 (lambdas-closed-in-termsp (strip-cdrs alist)))
            (lambdas-closed-in-termsp (cdr (car (make-stack-from-alist term alist)))))))

(local
 (defthm no-duplicate-lambda-formals-in-termsp-of-cdr-of-car-of-make-stack-from-alist
   (implies (and (pseudo-termp term)
                 (no-duplicate-lambda-formals-in-termsp (strip-cdrs alist)))
            (no-duplicate-lambda-formals-in-termsp (cdr (car (make-stack-from-alist term alist)))))))

;;; The term built in the HIDE case (inside the HIDE)

(defthm pseudo-termp-of-make-lambda-application-of-make-stack-from-alist
  (implies (and (pseudo-termp term)
                (symbol-listp (strip-cars alist))
                (pseudo-term-listp (strip-cdrs alist)))
           (let ((stack (make-stack-from-alist term alist)))
             (pseudo-termp (make-lambda-application (car (car stack)) term (cdr (car stack))))))
  :hints (("Goal" :in-theory (disable make-lambda-application make-stack-from-alist))))

(defthm termp-of-make-lambda-application-of-make-stack-from-alist
  (implies (and (termp term w)
                (no-duplicatesp-equal (strip-cars alist))
                (term-listp (strip-cdrs alist) w))
           (let ((stack (make-stack-from-alist term alist)))
             (termp (make-lambda-application (car (car stack)) term (cdr (car stack))) w)))
  :hints (("Goal" :in-theory (disable make-lambda-application make-stack-from-alist))))

(defthm no-nils-in-termp-of-make-lambda-application-of-make-stack-from-alist
  (implies (and (no-nils-in-termp term)
                (pseudo-termp term)
                (no-nils-in-termsp (strip-cdrs alist)))
           (let ((stack (make-stack-from-alist term alist)))
             (no-nils-in-termp (make-lambda-application (car (car stack)) term (cdr (car stack))))))
  :hints (("Goal" :in-theory (disable make-lambda-application make-stack-from-alist))))

(defthm lambdas-closed-in-termp-of-make-lambda-application-of-make-stack-from-alist
  (implies (and (lambdas-closed-in-termp term)
                (pseudo-termp term)
                (lambdas-closed-in-termsp (strip-cdrs alist)))
           (let ((stack (make-stack-from-alist term alist)))
             (lambdas-closed-in-termp (make-lambda-application (car (car stack)) term (cdr (car stack))))))
  :hints (("Goal" :in-theory (disable make-lambda-application make-stack-from-alist))))

(defthm no-duplicate-lambda-formals-in-termp-of-make-lambda-application-of-make-stack-from-alist
  (implies (and (no-duplicate-lambda-formals-in-termp term)
                (pseudo-termp term)
                (no-duplicatesp-equal (strip-cars alist))
                (no-duplicate-lambda-formals-in-termsp (strip-cdrs alist)))
           (let ((stack (make-stack-from-alist term alist)))
             (no-duplicate-lambda-formals-in-termp (make-lambda-application (car (car stack)) term (cdr (car stack))))))
  :hints (("Goal" :in-theory (disable make-lambda-application make-stack-from-alist))))

(local (include-book "kestrel/lists-light/remove-duplicates-equal" :dir :system))

(local
 (defthm make-stack-from-alist-of-nil
   (equal (make-stack-from-alist term nil)
          nil)))

(local
 (defthm subsetp-equal-of-free-vars-in-terms-of-cdr-of-car-of-make-stack-from-alist
   (implies (pseudo-termp term)
            (subsetp-equal (free-vars-in-terms (cdr (car (make-stack-from-alist term alist))))
                           (union-equal (set-difference-equal (free-vars-in-term term) (strip-cars alist))
                                        (free-vars-in-terms (strip-cdrs alist)))))
   :hints (("Goal" :in-theory (enable free-vars-in-terms-when-symbol-listp)))))

;; In the following, the variables of the term built are among those of the
;; actuals of the frame and those of TERM not bound by the frame.  The latter
;; are none, unless ALIST is NIL.
(local
 (defthm subsetp-equal-of-set-difference-equal-of-free-vars-in-term-and-car-of-car-of-make-stack-from-alist
   (subsetp-equal (set-difference-equal (free-vars-in-term term) (car (car (make-stack-from-alist term alist))))
                  (union-equal (set-difference-equal (free-vars-in-term term) (strip-cars alist))
                               (free-vars-in-terms (strip-cdrs alist))))
   :hints (("Goal" :cases (alist)
            :in-theory (disable make-stack-from-alist)))))

(local
 (defthmd subsetp-equal-when-subsetp-equal-of-union-equal
   (implies (and (subsetp-equal a (union-equal b c))
                 (subsetp-equal b d)
                 (subsetp-equal c d))
            (subsetp-equal a d))
   :hints (("Goal" :use (:instance subsetp-equal-transitive-alt
                                   (x a)
                                   (y (union-equal b c))
                                   (z d))
            :in-theory (disable subsetp-equal-transitive-alt)))))

;; The variables of the term built are the variables of TERM not bound by
;; ALIST and the variables of the terms they are bound to (that is, those of
;; TERM/ALIST).
(defthm subsetp-equal-of-free-vars-in-term-of-make-lambda-application-of-make-stack-from-alist
  (implies (and (pseudo-termp term)
                (symbol-listp (strip-cars alist)))
           (let ((stack (make-stack-from-alist term alist)))
             (subsetp-equal (free-vars-in-term (make-lambda-application (car (car stack)) term (cdr (car stack))))
                            (union-equal (set-difference-equal (free-vars-in-term term) (strip-cars alist))
                                         (free-vars-in-terms (strip-cdrs alist))))))
  :hints (("Goal" :use ((:instance subsetp-equal-of-free-vars-in-term-of-make-lambda-application
                                   (formals (car (car (make-stack-from-alist term alist))))
                                   (body term)
                                   (actuals (cdr (car (make-stack-from-alist term alist)))))
                        subsetp-equal-of-free-vars-in-terms-of-cdr-of-car-of-make-stack-from-alist
                        subsetp-equal-of-set-difference-equal-of-free-vars-in-term-and-car-of-car-of-make-stack-from-alist
                        (:instance subsetp-equal-when-subsetp-equal-of-union-equal
                                   (a (free-vars-in-term (make-lambda-application (car (car (make-stack-from-alist term alist)))
                                                                                  term
                                                                                  (cdr (car (make-stack-from-alist term alist))))))
                                   (b (free-vars-in-terms (cdr (car (make-stack-from-alist term alist)))))
                                   (c (set-difference-equal (free-vars-in-term term)
                                                            (car (car (make-stack-from-alist term alist)))))
                                   (d (union-equal (set-difference-equal (free-vars-in-term term) (strip-cars alist))
                                                   (free-vars-in-terms (strip-cdrs alist))))))
           :in-theory (union-theories '(symbol-listp-of-car-of-car-of-make-stack-from-alist
                                        len-of-cdr-of-car-of-make-stack-from-alist)
                                      (theory 'minimal-theory)))))

;;; The terms built in the two cases of rewrite are terms (assuming, as
;;; usual for the rewriter, that ALIST binds distinct variables to terms).

(defthm termp-of-rewrite-hide-case-inst-term
  (implies (and (equal (ffn-symb term) 'hide)
                (termp term w)
                (equal (arity 'hide w) 1)
                (no-duplicatesp-equal (strip-cars alist))
                (term-listp (strip-cdrs alist) w))
           (let* ((stack (make-stack-from-alist (fargn term 1) alist))
                  (inst-term (if alist
                                 (fcons-term* 'hide
                                              (make-lambda-application
                                               (caar stack)
                                               (fargn term 1)
                                               (cdar stack)))
                               term)))
             (termp inst-term w)))
  :hints (("Goal" :in-theory (disable make-lambda-application
                                      make-stack-from-alist))))

(defthm termp-of-rewrite-lambda-nest-hide-case-inst-term
  (implies (and (lambda-nest-hidep term)
                (termp term w)
                (equal (arity 'hide w) 1)
                (no-duplicatesp-equal (strip-cars alist))
                (term-listp (strip-cdrs alist) w))
           (let* ((new-body (lambda-nest-unhide term))
                  (stack (make-stack-from-alist new-body alist))
                  (inst-term
                   (fcons-term* 'hide
                                (if alist
                                    (make-lambda-application
                                     (caar stack)
                                     new-body
                                     (cdar stack))
                                  new-body))))
             (termp inst-term w)))
  :hints (("Goal" :in-theory (disable make-lambda-application
                                      make-stack-from-alist
                                      lambda-nest-unhide
                                      lambda-nest-hidep))))
