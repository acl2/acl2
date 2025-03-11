; Axe's representation of rewrite rules
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Axe-rules are created from theorems in the world.  Later, a collection of
;; axe-rules is assembled into a rule-alist for use in rewriting.

;; See also rule-alists.lisp.
;; See also stored-rules.lisp.

(include-book "kestrel/utilities/quote" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/terms-light/lambda-free-termp" :dir :system)
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(include-book "kestrel/lists-light/reverse-list-def" :dir :system)
(include-book "kestrel/lists-light/perm-def" :dir :system)
(include-book "kestrel/lists-light/perm" :dir :system) ;for the fact that perm is an equiv
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/list-sets" :dir :system))

;(local (in-theory (disable all-vars)))

(defund list-of-variables-and-constantsp (items)
  (declare (xargs :guard t))
  (if (atom items)
      (null items)
    (and (or (symbolp (first items))
             (myquotep (first items)))
         (list-of-variables-and-constantsp (rest items)))))

(defthm list-of-variables-and-constantsp-of-take
  (implies (list-of-variables-and-constantsp x)
           (list-of-variables-and-constantsp (take n x)))
  :hints (("Goal" :in-theory (enable list-of-variables-and-constantsp))))

(defthm list-of-variables-and-constantsp-forward-to-pseudo-term-listp
  (implies (list-of-variables-and-constantsp args)
           (pseudo-term-listp args))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable list-of-variables-and-constantsp))))

;; An axe-syntaxp-function-application is an application of a function (a
;; symbol) to arguments that are all either variables or quoted constants.
;; Note that dag-array, if needed, is omitted from args stored in the expr.
;; It will be passed separately to the evaluator.
(defund axe-syntaxp-function-applicationp (expr)
  (declare (xargs :guard (pseudo-termp expr)))
  (and (consp expr)
       (symbolp (ffn-symb expr))
       (not (eq 'quote (ffn-symb expr)))
       ;; todo: consider converting quotep to axe-quotep when we make the
       ;; rule, but we would need different checks before and after
       (not (eq 'quotep (ffn-symb expr))) ; the rule should use axe-quotep instead
       (list-of-variables-and-constantsp (fargs expr))
       ;; special case:
       (implies (eq (ffn-symb expr) 'axe-quotep)
                (variablep (farg1 expr)))))

;; An axe-syntaxp expression is a nest of calls of IF and NOT with constants
;; and axe-syntaxp-function-applications at the leaves.
(defund axe-syntaxp-exprp (expr)
  (declare (xargs :guard (pseudo-termp expr)))
  (if (atom expr)
      nil ; a variable is not allowed
    (if (myquotep expr)
        t ;could check that it is t or nil...
      (if (call-of 'if expr)
          (and (= 3 (len (fargs expr)))
               (axe-syntaxp-exprp (farg1 expr))
               (axe-syntaxp-exprp (farg2 expr))
               (axe-syntaxp-exprp (farg3 expr)))
        (if (call-of 'not expr)
            (and (= 1 (len (fargs expr)))
                 (axe-syntaxp-exprp (farg1 expr)))
          (axe-syntaxp-function-applicationp expr))))))

;; For the second arg of an axe-bind-free, as given by the user.  TODO: Avoid the need for the quoting?
(defun quoted-symbol-listp (item)
  (declare (xargs :guard t))
  (and (true-listp item)
       (eql 2 (len item))
       (eq 'quote (car item))
       (symbol-listp (cadr item))))

(defund axe-bind-free-function-applicationp (expr)
  (declare (xargs :guard (pseudo-termp expr)))
  (and (consp expr)
       (symbolp (ffn-symb expr))
       (not (eq 'quote (ffn-symb expr)))
       (list-of-variables-and-constantsp (fargs expr))))

(defthm axe-bind-free-function-applicationp-forward-to-pseudo-term-listp-of-cdr
  (implies (axe-bind-free-function-applicationp expr)
           (pseudo-term-listp (cdr expr)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-bind-free-function-applicationp))))

(defthm axe-bind-free-function-applicationp-forward-to-list-of-variables-and-constantsp
  (implies (axe-bind-free-function-applicationp expr)
           (list-of-variables-and-constantsp (cdr expr)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-bind-free-function-applicationp))))

(defthm axe-bind-free-function-applicationp-forward-to-true-listp-of-cdr
  (implies (axe-bind-free-function-applicationp expr)
           (true-listp (cdr expr)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-bind-free-function-applicationp))))

(defthm axe-bind-free-function-applicationp-forward-to-true-listp
  (implies (axe-bind-free-function-applicationp expr)
           (true-listp expr))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-bind-free-function-applicationp))))

(defthm axe-bind-free-function-applicationp-forward-to-symbolp-of-car
  (implies (axe-bind-free-function-applicationp expr)
           (symbolp (car expr)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-bind-free-function-applicationp))))

(defthm axe-bind-free-function-applicationp-forward-to-consp
  (implies (axe-bind-free-function-applicationp expr)
           (consp expr))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-bind-free-function-applicationp))))

(defthm axe-bind-free-function-applicationp-forward-to-not-equal-of-quote-and-car
  (implies (axe-bind-free-function-applicationp expr)
           (not (equal 'quote (car expr))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-bind-free-function-applicationp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note that when we talk about free vars in a hyp H, we don't mean variables
;; that are free in H; we mean free variables in H that are not yet bound when
;; H is reached as the hyps are relieved.

;; An axe-rule-hyp (hypothesis of an axe rule) is a special kind of structure
;; that represents an axe-syntaxp hyp, an axe-bind-free hyp, or a lambda-free
;; (currently) function call, which may or may not contain variables that will
;; be free when the hyp is relieved.  TODO: Consider not expanding lambdas in
;; hyps (if they don't have free vars?).  Axe creates these structures by
;; processing hyps in theorems from the world.
(defund axe-rule-hypp (hyp)
  (declare (xargs :guard t))
  (and (consp hyp) ; can't be a variable
       (let ((fn (ffn-symb hyp)))
         (if (eq :axe-syntaxp fn) ; (:axe-syntaxp . <expr>)
             (and (pseudo-termp (cdr hyp))
                  (axe-syntaxp-exprp (cdr hyp)))
           (if (eq :axe-bind-free fn) ; (:axe-bind-free <expr> . <vars>)
               (and (consp (cdr hyp))
                    (pseudo-termp (cadr hyp))
                    (axe-bind-free-function-applicationp (cadr hyp))
                    ;; This list of vars to bind is quoted when supplied by the user but is unquoted when we process the hyp
                    (symbol-listp (cddr hyp)))
             (if (eq :free-vars fn) ; (:free-vars . expr) indicates that the hyp has free vars
                 (let ((expr (cdr hyp)))
                   (and (consp expr)                      ; can't be a var
                        (not (eq 'quote (ffn-symb expr))) ; can't be a quoted constant
                        (pseudo-termp expr)
                        (lambda-free-termp expr)))
               (if (eq :axe-binding-hyp fn) ; (:axe-binding-hyp var . expr) indicates that the hyp binds var to the result of rewriting expr
                   (let ((rest (cdr hyp)))
                     (and (consp rest)
                          (symbolp (car rest))
                          (pseudo-termp (cdr rest))))
                 ;; regular hyp with no free vars (checked by bound-vars-suitable-for-hypp):
                 (and (pseudo-termp hyp)
                      (not (eq 'quote fn)) ; can't be a quoted constant
                      ;; consider relaxing this for efficiency of rewriting:
                      ;; (lambda-free-termp hyp)
                      ))))))))

;drop (see below)?
;; (defthm axe-rule-hypp-when-not-special
;;   (implies (and (consp hyp)
;;                 (not (equal :axe-syntaxp (car hyp)))
;;                 (not (equal :axe-bind-free (car hyp)))
;;                 (not (equal :free-vars (car hyp)))
;;                 (not (equal 'quote (car hyp))))
;;            (equal (axe-rule-hypp hyp)
;;                   (and (pseudo-termp hyp)
;;                        ;; (lambda-free-termp hyp)
;;                        )))
;;   :hints (("Goal" :in-theory (enable axe-rule-hypp)))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0 0 0 0 0))))

;; (defthm axe-rule-hypp-when-equal-of-car-and-work-hard-cheap
;;   (implies (equal 'work-hard (car hyp))
;;            (equal (axe-rule-hypp hyp)
;;                   (and (pseudo-termp hyp)
;;                        ;; (lambda-free-termp hyp)
;;                        )))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0)))
;;   :hints (("Goal" :in-theory (enable axe-rule-hypp))))

(defthm axe-rule-hypp-when-simple
  (implies (and (not (equal :axe-syntaxp (car hyp)))
                (not (equal :axe-bind-free (car hyp)))
                (not (equal :free-vars (car hyp)))
                (not (equal :axe-binding-hyp (car hyp))))
           (equal (axe-rule-hypp hyp)
                  (and (consp hyp)
                       (not (equal 'quote (car hyp)))
                       (pseudo-termp hyp)
                       ;; (lambda-free-termp hyp)
                       )))
  :hints (("Goal" :in-theory (enable axe-rule-hypp))))

(defthm axe-rule-hypp-when-axe-syntaxp
  (implies (equal :axe-syntaxp (car hyp))
           (equal (axe-rule-hypp hyp)
                  (and (pseudo-termp (cdr hyp))
                  (axe-syntaxp-exprp (cdr hyp)))))
;  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable axe-rule-hypp))))

(defthm axe-rule-hypp-when-axe-bind-free
  (implies (equal :axe-bind-free (car hyp))
           (equal (axe-rule-hypp hyp)
                  (and (consp (cdr hyp))
                       (pseudo-termp (cadr hyp))
                       (axe-bind-free-function-applicationp (cadr hyp))
                       (symbol-listp (cddr hyp)))))
;  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable axe-rule-hypp))))

(defthm axe-rule-hypp-when-free-vars
  (implies (equal :free-vars (car hyp))
           (equal (axe-rule-hypp hyp)
                  (let ((expr (cdr hyp)))
                    (and (consp expr)                     ; can't be a var
                         (not (eq 'quote (ffn-symb expr))) ; can't be a quoted constant
                         (pseudo-termp expr)
                         (lambda-free-termp expr)))))
  :hints (("Goal" :in-theory (enable axe-rule-hypp))))

(defthm axe-rule-hypp-when-axe-binding-hyp
  (implies (equal :axe-binding-hyp (car hyp))
           (equal (axe-rule-hypp hyp)
                  (let ((rest (cdr hyp)))
                    (and (consp rest)
                         (symbolp (car rest))
                         (pseudo-termp (cdr rest))))))
;  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable axe-rule-hypp))))

;; Shows that an axe-rule-hyp must be a cons (and so can't be a symbol):
(thm
 (implies (axe-rule-hypp hyp)
          (and (consp hyp)
               (not (symbolp hyp))))
 :hints (("Goal" :in-theory (enable axe-rule-hypp))))

;; Shows that an axe-rule-hyp can't be a quoted constant:
(thm
 (implies (axe-rule-hypp hyp)
          (not (quotep hyp)))
 :hints (("Goal" :in-theory (enable axe-rule-hypp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund axe-rule-hyp-listp (hyps)
  (declare (xargs :guard t))
  (if (atom hyps)
      (null hyps)
    (and (axe-rule-hypp (first hyps))
         (axe-rule-hyp-listp (rest hyps)))))

(defthm axe-rule-hyp-listp-of-reverse-list
  (implies (axe-rule-hyp-listp acc)
           (axe-rule-hyp-listp (reverse-list acc)))
  :hints (("Goal" :in-theory (enable axe-rule-hyp-listp reverse-list))))

(defthm axe-rule-hyp-listp-of-append
  (equal (axe-rule-hyp-listp (append x y))
         (and (axe-rule-hyp-listp (true-list-fix x))
              (axe-rule-hyp-listp y)))
  :hints (("Goal" :in-theory (enable axe-rule-hyp-listp append))))

(defthm axe-rule-hyp-listp-of-cdr
  (implies (axe-rule-hyp-listp x)
           (axe-rule-hyp-listp (cdr x)))
  :hints (("Goal" :in-theory (enable axe-rule-hyp-listp))))

(defthm axe-rule-hyp-listp-forward-to-true-listp
  (implies (axe-rule-hyp-listp hyps)
           (true-listp hyps))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-rule-hyp-listp))))

;; We put this in when a hyp is bad (we also throw a hard error).  This hyp should never be able to be relieved.
(defstub bad-rule-hyp () t)

(defconst *unrelievable-hyp*
  '(bad-rule-hyp))

(defconst *unrelievable-hyps*
  (list *unrelievable-hyp*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Checks whether BOUND-VARS is suitable for the strip-cars of the alist upon
;; reaching HYP and attempting to relieve it.
(defund bound-vars-suitable-for-hypp (bound-vars hyp)
  (declare (xargs :guard (and (symbol-listp bound-vars)
                              (axe-rule-hypp hyp))
                  :guard-hints (("Goal" :in-theory (enable axe-rule-hypp)))))
  (let* ((fn (ffn-symb hyp)))
    (case fn
      (:axe-syntaxp
       (let ((syntaxp-expr (cdr hyp))) ;; strip off the :AXE-SYNTAXP; dag-array formals have been removed from the calls in this
         ;; All vars mentioned must be bound:
         (subsetp-equal (free-vars-in-term syntaxp-expr) bound-vars)))
      (:axe-bind-free
       (let* ((bind-free-expr (cadr hyp)) ;; strip off the :AXE-BIND-FREE
              (vars-to-bind (cddr hyp)))
         (and ;; All vars mentioned must be bound:
          (subsetp-equal (free-vars-in-term bind-free-expr) bound-vars)
          ;; Vars to be bound now must not already be bound:
          (not (intersection-eq vars-to-bind bound-vars)))))
      ;; a hyp marked with :free-vars must have at least 1 free var:
      (:free-vars (let* ((expr (cdr hyp))  ;; (:free-vars . expr)
                         (hyp-vars (free-vars-in-term expr))
                         (free-vars (set-difference-eq hyp-vars bound-vars)))
                    (if free-vars t nil)))
      ;; A binding hyp must have its var free and all vars in its expr already bound:
      (:axe-binding-hyp (let ((var (cadr hyp))
                          (expr (cddr hyp)))
                      (and (not (member-equal var bound-vars))
                           (subsetp-equal (free-vars-in-term expr) bound-vars))))
      ;; a hyp not marked with :free-vars must have no free vars:
      (otherwise (let* ((hyp-vars (free-vars-in-term hyp)))
                   (subsetp-equal hyp-vars bound-vars))))))

(defcong perm equal (bound-vars-suitable-for-hypp bound-vars hyp) 1
  :hints (("Goal" :in-theory (enable bound-vars-suitable-for-hypp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Updates the BOUND-VARS as they will be when HYP is successfully relieved.
(defund bound-vars-after-hyp (bound-vars hyp)
  (declare (xargs :guard (and (symbol-listp bound-vars)
                              (axe-rule-hypp hyp))
                  :guard-hints (("Goal" :in-theory (enable axe-rule-hypp)))))
  (case (ffn-symb hyp)
    (:axe-syntaxp bound-vars) ; no change
    (:axe-bind-free (let ((vars-to-bind (cddr hyp))) ; (:axe-bind-free <expr> . <vars>)
                      ;; some vars get bound:
                      (append vars-to-bind bound-vars)))
    (:free-vars (let* ((expr (cdr hyp)) ; (:free-vars . expr)
                       (hyp-vars (free-vars-in-term expr))
                       (free-vars (set-difference-eq hyp-vars bound-vars)))
                  ;; some vars get bound:
                  (append free-vars bound-vars)))
    ;; The var of the hyp becomes bound:
    (:axe-binding-hyp (let ((var (cadr hyp)))
                    (cons var bound-vars)))
    ;; no vars get bound:
    (otherwise bound-vars)))

(defthm symbol-listp-of-bound-vars-after-hyp
  (implies (and (axe-rule-hypp hyp)
                (symbol-listp bound-vars))
           (symbol-listp (bound-vars-after-hyp bound-vars hyp)))
  :hints (("Goal" :in-theory (enable bound-vars-after-hyp))))

(defthm true-listp-of-bound-vars-after-hyp
  (implies (true-listp bound-vars)
           (true-listp (bound-vars-after-hyp bound-vars hyp)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable bound-vars-after-hyp))))

(defcong perm perm (bound-vars-after-hyp bound-vars hyp) 1
  :hints (("Goal" :in-theory (enable bound-vars-after-hyp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Updates the BOUND-VARS as they will be when the HYPS are successfully relieved.
(defund bound-vars-after-hyps (bound-vars hyps)
  (declare (xargs :guard (and (symbol-listp bound-vars)
                              (axe-rule-hyp-listp hyps))
                  :measure (len hyps)
                  :guard-hints (("Goal" :expand (axe-rule-hyp-listp hyps)
                                 :in-theory (enable axe-rule-hypp)))))
  (if (endp hyps)
      bound-vars
    (let* ((hyp (first hyps))
           (new-bound-vars (bound-vars-after-hyp bound-vars hyp)))
      (bound-vars-after-hyps new-bound-vars (rest hyps)))))

(defthm true-listp-of-bound-vars-after-hyps
  (implies (true-listp bound-vars)
           (true-listp (bound-vars-after-hyps bound-vars hyps)))
  :hints (("Goal" :in-theory (enable bound-vars-after-hyps))))

(defthm bound-vars-after-hyps-of-append
  (equal (bound-vars-after-hyps bound-vars (append hyps1 hyps2))
         (bound-vars-after-hyps (bound-vars-after-hyps bound-vars hyps1) hyps2))
  :hints (("Goal" :in-theory (enable bound-vars-after-hyps))))

(defthm bound-vars-after-hyps-of-cons
  (equal (bound-vars-after-hyps bound-vars (cons hyp hyps))
         (bound-vars-after-hyps (bound-vars-after-hyp bound-vars hyp) hyps))
  :hints (("Goal" :in-theory (enable bound-vars-after-hyps))))

(defthm bound-vars-after-hyps-of-nil
  (equal (bound-vars-after-hyps bound-vars nil)
         bound-vars)
  :hints (("Goal" :in-theory (enable bound-vars-after-hyps))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Checks whether BOUND-VARS is suitable for the strip-cars of the alist upon
;; reaching HYPS and attempting to relieve them.
(defund bound-vars-suitable-for-hypsp (bound-vars hyps)
  (declare (xargs :guard (and (symbol-listp bound-vars)
                              (axe-rule-hyp-listp hyps))
                  :measure (len hyps)
                  :guard-hints (("Goal" :expand (axe-rule-hyp-listp hyps)
                                 :in-theory (enable axe-rule-hypp)))))
  (if (endp hyps)
      t
    (let ((hyp (first hyps)))
      (and (bound-vars-suitable-for-hypp bound-vars hyp)
           (let* ((new-bound-vars (bound-vars-after-hyp bound-vars hyp)))
             (bound-vars-suitable-for-hypsp new-bound-vars (rest hyps)))))))

(defthm bound-vars-suitable-for-hypsp-when-axe-sytaxp-car
  (implies (equal :axe-syntaxp (car (car hyps)))
           (equal (bound-vars-suitable-for-hypsp bound-vars hyps)
                  (and (subsetp-equal (free-vars-in-term (cdr (car hyps))) bound-vars)
                       (bound-vars-suitable-for-hypsp bound-vars (cdr hyps)))))
  :hints (("Goal" :in-theory (enable bound-vars-suitable-for-hypp
                                     bound-vars-after-hyp
                                     bound-vars-suitable-for-hypsp))))

;todo: rename and simplify?  or combine with the above?
(defthm bound-vars-suitable-for-hypsp-when-normal
  (implies (and (equal :axe-syntaxp (car (car hyps)))
                (not (equal :axe-bind-free (car (car hyps))))
                (not (equal :free-vars (car (car hyps))))
                (not (equal :axe-binding-hyp (car (car hyps)))))
           (equal (bound-vars-suitable-for-hypsp bound-vars hyps)
                  (and (subsetp-equal (free-vars-in-term (cdr (car hyps))) bound-vars)
                       (bound-vars-suitable-for-hypsp bound-vars (cdr hyps)))))
  :hints (("Goal" :in-theory (enable bound-vars-suitable-for-hypp
                                     bound-vars-after-hyp
                                     bound-vars-suitable-for-hypsp))))

(defcong perm equal (bound-vars-suitable-for-hypsp bound-vars hyps) 1
  :hints (("Goal" :in-theory (enable bound-vars-suitable-for-hypsp))))

(defthm bound-vars-suitable-for-hypsp-when-free-vars
  (implies (and (equal :free-vars (car (car hyps)))
                (no-duplicatesp-equal bound-vars))
           (equal (bound-vars-suitable-for-hypsp bound-vars hyps)
                  (and (set-difference-equal (free-vars-in-term (cdr (car hyps))) bound-vars) ;at least one free var
                       (bound-vars-suitable-for-hypsp (union-equal (set-difference-equal (free-vars-in-term (cdr (car hyps)))
                                                                                         bound-vars)
                                                                   bound-vars)
                                                      (cdr hyps)))))
  :hints (("Goal" :expand (bound-vars-suitable-for-hypsp bound-vars hyps)
           :in-theory (e/d (bound-vars-suitable-for-hypp
                            bound-vars-after-hyp
                            ;;bound-vars-suitable-for-hypsp
                            ) (no-duplicatesp-equal)))))

(defthm bound-vars-suitable-for-hypsp-when-free-vars-2
  (implies (and (equal :free-vars (car (car hyps)))
;                (no-duplicatesp-equal bound-vars)
                (bound-vars-suitable-for-hypsp bound-vars hyps))
           (bound-vars-suitable-for-hypsp (append (set-difference-equal (free-vars-in-term (cdr (car hyps)))
                                                                        bound-vars)
                                                  bound-vars)
                                          (cdr hyps)))
  :hints (("Goal" :expand (bound-vars-suitable-for-hypsp bound-vars hyps)
           :in-theory (e/d (bound-vars-suitable-for-hypp
                            bound-vars-after-hyp
                            ;;bound-vars-suitable-for-hypsp
                            ) (no-duplicatesp-equal)))))

(defthm bound-vars-suitable-for-hypsp-of-append
  (equal (bound-vars-suitable-for-hypsp bound-vars (append hyps1 hyps2))
         (and (bound-vars-suitable-for-hypsp bound-vars hyps1)
              (bound-vars-suitable-for-hypsp (bound-vars-after-hyps bound-vars hyps1) hyps2)))
  :hints (("Goal" :in-theory (enable bound-vars-suitable-for-hypsp
                                     bound-vars-after-hyps))))

(defthm bound-vars-suitable-for-hypsp-of-cons
  (equal (bound-vars-suitable-for-hypsp bound-vars (cons hyp hyps))
         (and (bound-vars-suitable-for-hypp bound-vars hyp)
              (bound-vars-suitable-for-hypsp (bound-vars-after-hyp bound-vars hyp) hyps)))
  :hints (("Goal" :in-theory (enable bound-vars-suitable-for-hypsp
                                     bound-vars-after-hyps))))

(defthm bound-vars-suitable-for-hypsp-of-nil
  (bound-vars-suitable-for-hypsp bound-vars nil)
  :hints (("Goal" :in-theory (enable bound-vars-suitable-for-hypsp
                                     bound-vars-after-hyps))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Define these later, so they can have axe-rulep as their guards?

;; Extracts the left-hand-side of an axe-rule.
(defund-inline rule-lhs (axe-rule)
  (declare (xargs :guard (equal 4 (len axe-rule))))
  (first axe-rule))

;; Extracts the right-hand-side of an axe-rule.
(defund-inline rule-rhs (axe-rule)
  (declare (xargs :guard (equal 4 (len axe-rule))))
  (second axe-rule))

;; Extracts the name ("rule-symbol") of an axe-rule.
(defund-inline rule-symbol (axe-rule)
  (declare (xargs :guard (equal 4 (len axe-rule))))
  (third axe-rule))

;; Extracts the hypotheses of an axe-rule.
(defund-inline rule-hyps (axe-rule)
  (declare (xargs :guard (equal 4 (len axe-rule))))
  (fourth axe-rule))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The LHS of an Axe rule is a lambda-free pseudo-term that is a function call
;; (i.e., not a variable or constant).
(defund axe-rule-lhsp (lhs)
  (declare (xargs :guard t))
  (and (pseudo-termp lhs)
       (lambda-free-termp lhs)
       (consp lhs)
       (not (eq 'quote (ffn-symb lhs)))))

(defthm axe-rule-lhsp-forward-to-pseudo-termp
  (implies (axe-rule-lhsp lhs)
           (pseudo-termp lhs))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-rule-lhsp))))

(defthm axe-rule-lhsp-forward-to-consp
  (implies (axe-rule-lhsp lhs)
           (consp lhs))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-rule-lhsp))))

(defthm axe-rule-lhsp-of-cons
  (equal (axe-rule-lhsp (cons fn args))
         (and (symbolp fn)
              (not (equal 'quote fn))
              (pseudo-term-listp args)
              (lambda-free-termsp args)))
  :hints (("Goal" :in-theory (enable axe-rule-lhsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An axe-rule is a 4-tuple containing: LHS, RHS, rule name ("rule-symbol"), and hyps.
;; See also stored-axe-rulep.
;; TODO: Make the hyps the final cdr?
(defund axe-rulep (axe-rule)
  (declare (xargs :guard t))
  (and (true-listp axe-rule)
       (= 4 (len axe-rule))
       (symbolp (rule-symbol axe-rule))
       (let ((lhs (rule-lhs axe-rule))
             (rhs (rule-rhs axe-rule))
             (hyps (rule-hyps axe-rule)))
         (and (axe-rule-lhsp lhs)
              (pseudo-termp rhs)
              (axe-rule-hyp-listp hyps)
              (let ((lhs-vars (free-vars-in-term lhs)))
                (and (bound-vars-suitable-for-hypsp lhs-vars hyps)
                     (subsetp-equal (free-vars-in-term rhs)
                                    (bound-vars-after-hyps lhs-vars hyps))))))))

(defthm pseudo-termp-of-rule-rhs
  (implies (axe-rulep axe-rule)
           (pseudo-termp (rule-rhs axe-rule)))
  :hints (("Goal" :in-theory (enable axe-rulep))))

;; Kept disabled to avoid introducing axe-rulep out of nowhere
(defthmd len-when-axe-rulep
  (implies (axe-rulep axe-rule)
           (equal (len axe-rule)
                  4))
  :hints (("Goal" :in-theory (enable axe-rulep))))
