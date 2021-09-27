; Constant-factor unrolling of a function
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;this book contains a tool that takes a function (with one recursive call) and generates a new function that does k repetitions per recursive call.
;also proves them the same (seems to be automatic?)

;FIXME - this doesn't handle MV and MV-LET correctly...
;fixme what about lets?
;FIXME - this should check the input to make sure it's a recursive function

(include-book "kestrel/utilities/quote" :dir :system)
(include-book "kestrel/terms-light/sublis-var-simple" :dir :system)
(include-book "kestrel/utilities/conjunctions" :dir :system)
(include-book "kestrel/utilities/terms" :dir :system) ; for rename-fn
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "kestrel/utilities/printing" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
;(include-book "letify-term") ;; TODO: Try using something from kestrel-acl2/transformations/letify
(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

(mutual-recursion
 (defun expand-function-call (body function-name function-params whole-body)
   (if (variablep body)
       body
     (if (fquotep body)
         body
       ;;function call or lambda
       (let* ((fn (ffn-symb body))
              ;;update fn if it's a lambda
              (fn (if (consp fn)
                      (let* ((lambda-formals (second fn))
                             (lambda-body (third fn))
                             (new-lambda-body (expand-function-call lambda-body function-name function-params whole-body))
                             (new-fn `(lambda ,lambda-formals ,new-lambda-body)))
                        new-fn)
                    fn))
              (args (fargs body)))
         (let ((processed-args (expand-function-call-lst args function-name function-params whole-body)))
           (if (eq function-name fn)
               (sublis-var-simple (pairlis$ function-params
                                        processed-args)
                              whole-body)
             (cons fn processed-args)))))))

 (defun expand-function-call-lst (body-lst function-name function-params whole-body)
   (if (endp body-lst)
       nil
     (cons (expand-function-call (car body-lst) function-name function-params whole-body)
           (expand-function-call-lst (cdr body-lst) function-name function-params whole-body)))))

;; (defun fact (n)
;;   (if (zp n)
;;       1
;;     (* n (fact (+ -1 n)))))

;; (expand-function-call
;;  '(IF (ZP N)
;;       '1
;;       (BINARY-* N (FACT (BINARY-+ '-1 N))))
;;  'fact
;;  '(n)
;;  '(IF (ZP N)
;;       '1
;;       (BINARY-* N (FACT (BINARY-+ '-1 N)))))

;; (find-an-if-to-lift '(a b c (if test d1 d2) e f) 0)
;returns the position of an IF in args, or nil.
(defun find-an-if-to-lift (args num)
  (declare (xargs :guard (and (natp num)
                              (true-listp args))))
  (if (endp args)
      nil
    (let* ((arg (car args)))
      (if (and (consp arg)
               (eq 'if (car arg)))
          num
        (find-an-if-to-lift (cdr args) (+ 1 num))))))

(defthm natp-of-find-an-if-to-lift
  (implies (and (find-an-if-to-lift args num)
                (natp num))
           (natp (find-an-if-to-lift args num))))

(defthm find-an-if-to-lift-type
  (implies (natp num)
           (or (not (find-an-if-to-lift args num))
               (natp (find-an-if-to-lift args num))))
  :rule-classes :type-prescription)

(defthm find-an-if-to-lift-bound-helper
  (implies (and (find-an-if-to-lift args num)
                (natp num))
           (< (find-an-if-to-lift args num)
              (+ num (len args)))))

(defthm find-an-if-to-lift-bound-2
  (implies (and (find-an-if-to-lift args num)
                (natp num))
           (<= num
               (find-an-if-to-lift args num)))
  :rule-classes :linear)

(defthm find-an-if-to-lift-bound
  (implies (find-an-if-to-lift args 0)
           (< (find-an-if-to-lift args 0)
              (len args)))
  :hints (("Goal" :use (:instance find-an-if-to-lift-bound-helper (num 0))
           :in-theory (disable find-an-if-to-lift-bound-helper))))

;; ;; (lift-arg 'foo '(if test d1 d2) 3 '(a b c (if test d1 d2) e f g)) becomes (if test (foo a b c d1 e f g) (foo a b c d2 e f g))
;; ;; arg is an IF
;; (defun lift-arg (function-name arg arg-num args)
;;   (let ((test (second arg))
;;         (then-part (third arg))
;;         (else-part (fourth arg)))
;;     `(if ,test (,function-name ,@(update-nth arg-num then-part args))
;;        (,function-name ,@(update-nth arg-num else-part args)))))

(local (in-theory (disable ACL2-COUNT)))

(defthm <-of-acl2-count-of-update-nth
  (implies (and (< (acl2-count val) (acl2-count (nth n lst)))
                (natp n)
                (< n (len lst))
                )
           (< (acl2-count (update-nth n val lst))
              (acl2-count lst)))
  :hints (("Goal" :in-theory (enable update-nth acl2-count))))

(defthm consp-of-nth-of-find-an-if-to-lift-helper
  (implies (and (find-an-if-to-lift args num)
                (natp num))
           (consp (nth (- (find-an-if-to-lift args num)
                          num)
                       args))))

(defthm consp-of-nth-of-find-an-if-to-lift
  (implies (find-an-if-to-lift args 0)
           (consp (nth (find-an-if-to-lift args 0)
                       args)))
  :rule-classes :type-prescription
  :hints (("Goal" :use (:instance consp-of-nth-of-find-an-if-to-lift-helper (num 0))
           :in-theory (disable consp-of-nth-of-find-an-if-to-lift-helper))))

(defun lift-ifs-in-args (fn args)
  (let ((possible-if-index (find-an-if-to-lift args 0)))
    (if (not possible-if-index)
        (cons fn args)
      (let* ((arg (nth possible-if-index args))
             (test (second arg))
             (then-part (third arg))
             (else-part (fourth arg)))
        `(if ,test
             ,(lift-ifs-in-args fn (update-nth possible-if-index then-part args))
           ,(lift-ifs-in-args fn (update-nth possible-if-index else-part args)))))))

;; (LIFT-IFS '(foo a b c (if test d1 d2) e f))
(mutual-recursion
 (defun lift-ifs (body)
   (declare (xargs :guard (pseudo-termp body)
                   :verify-guards nil
                   :hints (("Goal" :do-not '(generalize eliminate-destructors)))
                   ))
   (if (or (not (mbt (pseudo-termp body))) ;for termination
           (variablep body))
       body
     (if (fquotep body)
         body
       ;;function call or lambda
       (let* ((fn (ffn-symb body))
              ;;update fn if it's a lambda (by lifting IFs in the lambda body); below we lift IFs in the args too, of course
              (fn (if (consp fn)
                      (let* ((lambda-formals (second fn))
                             (lambda-body (third fn))
                             (new-lambda-body (lift-ifs lambda-body))
                             (new-fn `(lambda ,lambda-formals ,new-lambda-body)))
                        new-fn)
                    fn))
              (args (fargs body))
              (processed-args (lift-ifs-lst args)))
         (if (eq 'if fn) ;no need to lift an if over an if (might prevent loops too?)
             (cons 'if processed-args)
           (lift-ifs-in-args fn processed-args))))))

 (defun lift-ifs-lst (body-lst)
   (declare (xargs :guard (pseudo-term-listp body-lst)))
   (if (endp body-lst)
       nil
     (cons (lift-ifs (car body-lst))
           (lift-ifs-lst (cdr body-lst))))))

;how do we lift the ifs for this?
;i guess we lift the if from one param at a time and the recur...
;(foo (if test a b) (if test2 c d))
;(if test (foo a (if test2 c d)) (foo b (if test2 c d)))
;and the we lift the ifs in the args (no need to lift them past the outer if...)

(defun expand-function-call-k-times (k body function-name formals original-body)
  (if (zp k)
      body
    (expand-function-call-k-times (+ -1 k)
                                  (expand-function-call body function-name formals original-body)
                                  function-name formals original-body)))

(mutual-recursion
 (defun function-call-appears (fn body)
   (if (atom body)
       nil
     (if (eq fn (ffn-symb body))
         t
       (function-call-appears-lst fn (fargs body)))))

 (defun function-call-appears-lst (fn body-lst)
   (if (endp body-lst)
       nil
     (or (function-call-appears fn (car body-lst))
         (function-call-appears-lst fn (cdr body-lst))))))

;returns a list of cases, each of which has a body consed onto a list of conditions
(defun extract-cases-for-non-recursive-branches (fn body acc)
  (if (and (consp body)
           (eq 'if
               (ffn-symb body)))
      (append (extract-cases-for-non-recursive-branches fn (third body) (cons (second body) acc))
              (extract-cases-for-non-recursive-branches fn (fourth body) (cons `(not ,(second body)) acc)))
    (if (function-call-appears fn body)
        nil
      (list (cons body acc)))))

(defun generate-theorems-for-cases (call cases tag count fn)
  (if (endp cases)
      nil
    (let* ((case (car cases))
           (body (car case))
           (conditions (cdr case)))
      (cons `(defthm ,(pack$ tag (nat-to-string count))
               (implies ,(make-conjunction-from-list (reverse conditions))
                        (equal ,call
                               ,body))
               :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                                          '(,fn))))
               )
            (generate-theorems-for-cases call (cdr cases) tag (+ 1 count) fn)))))

(defun generate-lemmas-for-non-recursive-branches (fn call body)
  (let* ((cases (extract-cases-for-non-recursive-branches fn body nil)))
    (generate-theorems-for-cases call cases
                                 (pack$ fn '-base-case-lemma-)
                                 0
                                 fn)))

;this could return the unroller-lemma-name..
(defun unroll-events (function-name unrolling-factor expand-hint-terms state)
  (declare (xargs :stobjs state
                  :verify-guards nil))
  (let* ((props (getprops function-name 'current-acl2-world (w state))))
    (if (not props)
        (hard-error 'unroll-events "Can't find the function ~x0" (acons #\0 function-name nil))
      (let* ((body (lookup-eq 'unnormalized-body props))
             (formals (lookup-eq 'formals props))
             (unrolled-body (expand-function-call-k-times (+ -1 unrolling-factor) body function-name formals body))
             ;; fixme what if there are ifs in the original body that we don't want lifted? perhaps we should tag (top-level) ifs introduced in the substitution
             (unrolled-body (lift-ifs unrolled-body))
             (new-function-name (pack$ function-name '-unrolled-by- unrolling-factor))
             (unrolled-body (rename-fn function-name new-function-name unrolled-body))
             )
        `((skip-proofs ;FIXME handle termination better (if the original function terminated, the new function should too)
           (defun ,new-function-name ,formals
             (declare (xargs :normalize nil)) ;this was crucial, since we turn off all rules to prove the unrolling, we don't want any smarts used to transform the body
             ,unrolled-body ;(letify-term unrolled-body) ;Tue Feb 22 17:29:36 2011 ;fixme to put these back we'll need to add support for combining base cases when lets intervene
             ))

          ;; usually is automatic:
          (defthm ,(pack$ function-name '-becomes- new-function-name)
            (equal (,function-name ,@formals)
                   (,new-function-name ,@formals))
            :hints (("Goal" ;;:induct (,new-function-name ,@formals) ;new
                     :induct (,function-name ,@formals) ;things seem to work better with this, though a nested induction is needed yuck!
                     :do-not '(generalize eliminate-destructors)
                     :expand (;(,function-name ,@formals)
                              ;(,new-function-name ,@formals)
                              ,@expand-hint-terms)
                     :in-theory (union-theories '(,function-name ,new-function-name) (theory 'minimal-theory)))))

          ,@(generate-lemmas-for-non-recursive-branches new-function-name `(,new-function-name ,@formals) unrolled-body))))))

(defun unroller-lemma-name (function-name unrolling-factor)
  (let* ((new-function-name (pack$ function-name '-unrolled-by- (nat-to-string unrolling-factor))))
    (pack$ function-name '-becomes- new-function-name)))

;; ;;TODO: Use make-event for this:
;; ;; TODO: Note that the proof requires a nested induction (perhaps to prove that the unrolled function satisfies the definitional axioms [1 for each case] of the original function???)
;; ;;ex: (unroll 'fact 4 state)
;; (defun unroll (function-name unrolling-factor state)
;;   (declare (xargs :stobjs state
;;                   :verify-guards nil))
;;   `(progn ,@(unroll-events function-name unrolling-factor nil state)))

;FIXME may need to simplify the generated body if we want to be able to use a large unrolling factor (otherwise we may have big nests of (+ -1 (+ -1 ...))
;should probably simplify using the dag rewriter
