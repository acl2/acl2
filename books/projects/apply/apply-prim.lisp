; Copyright (C) 2016, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The Maximal Defun of Apply$-Prim

; We define *apply$-primitives*, apply$-primp, and apply$-prim to include all
; functions in the bootstrap world that satisfy the Fundamental Properties.  We
; also introduce a metafunction for simplifying (apply$-prim 'fn args) and
; verify it.

; At some point we may fix these books to work with ACL2(r).
; cert_param: (non-acl2r)

(in-package "ACL2")

; Handling the Primitives

(defun identify-apply$-primitives1 (runes avoid-fns wrld ans)
  (declare (xargs :mode :program))
  (cond
   ((endp runes) ans)
   (t (let ((fn (cadr (car runes))))
        (cond
         ((and (acl2-system-namep fn wrld)
               (not (member-eq fn avoid-fns))
               (all-nils (getprop fn 'stobjs-in nil 'current-acl2-world wrld))
               (equal (length (getprop fn 'stobjs-out nil 'current-acl2-world wrld)) 1)
               (null (car (getprop fn 'stobjs-out nil 'current-acl2-world wrld)))
               (not (member 'STATE-STATE (formals fn wrld))))

; We don't want to think about functions like BOUNDP-GLOBAL1 and
; 32-BIT-INTEGER-STACK-LENGTH1 that use STATE-STATE as a formal preventing
; their execution.

          (identify-apply$-primitives1 (cdr runes) avoid-fns wrld (cons (cons fn (formals fn wrld)) ans)))
         (t (identify-apply$-primitives1 (cdr runes) avoid-fns wrld ans)))))))

(defun identify-apply$-primitives (world)

; Search the world for every single-valued :logic mode function that does not
; traffic in stobjs or state or state-state.  Return an alist pairing each such
; function with its formals.  We accumulate the pairs in reverse order, which
; (it turns out) puts the most basic, familiar ACL2 primitives first.  We do
; not collect certain functions because they are prohibited as per the comments
; below.  Note: Many functions are included that actually have no utility in
; this setting, e.g., does any user really want to call make-wormhole-status
; via apply$?  But if it's legal without a trust tag, we include it, just to
; live up to the name "Maximal".

  (declare (xargs :mode :program))
  (identify-apply$-primitives1 (function-theory :here)
                               '(SYNP ; bad
                                 HIDE ; stupid
                                 MV-LIST ; restricts arguments
                                 WORMHOLE1 ; restricts arguments
                                 WORMHOLE-EVAL ; restricts arguments
;                                 MAKE-WORMHOLE-STATUS
;                                 SET-WORMHOLE-DATA
;                                 SET-WORMHOLE-ENTRY-CODE
;                                 WORMHOLE-DATA
;                                 WORMHOLE-ENTRY-CODE
;                                 WORMHOLE-STATUSP
                                 SYS-CALL ; bad -- requires trust tag
                                 HONS-CLEAR! ; bad -- requires trust tag
                                 HONS-WASH! ; bad -- requires trust tag
;                                 BREAK$
;                                 PRINT-CALL-HISTORY
;                                 NEVER-MEMOIZE-FN
;                                 MEMOIZE-FORM
;                                 CLEAR-MEMOIZE-STATISTICS
;                                 MEMOIZE-SUMMARY
;                                 CLEAR-MEMOIZE-TABLES
;                                 CLEAR-MEMOIZE-TABLE
                                 )
                               world
                               nil
                               #||'((TAMEP . (X))
                                 (TAMEP-FUNCTIONP . (FN))
                                 (SUITABLY-TAMEP-LISTP . (X FLAGS)))||#))

(make-event
 `(defconst *apply$-primitives*
    ',(identify-apply$-primitives (w state))))

(defun apply$-primp (fn)
  (and (assoc-eq fn *apply$-primitives*) t))

(verify-termination car-cadr-caddr-etc)

(defun make-apply$-prim-body-fn (alist)
  (declare (xargs :mode :program))
  (cond
   ((endp alist) nil)
   (t (let ((fn (car (car alist)))
            (formals (cdr (car alist))))
        (cons `(,fn (,fn ,@(car-cadr-caddr-etc formals 'ARGS)))
              (make-apply$-prim-body-fn (cdr alist)))))))

(defmacro make-apply$-prim-body ()
  `(case fn
     ,@(make-apply$-prim-body-fn *apply$-primitives*)
     (otherwise nil)))

(defun apply$-prim (fn args)
  (make-apply$-prim-body))

; The above defun of apply$-prim contains a case statement with about 786
; cases.  Rewriting it causes stack overflow with the nominal rewrite stack
; size of 1000.  For example, we cannot prove: (thm (equal (apply$-prim 'tamep
; (list x)) (tamep x))).  We will therefore temporarily enlarge the stack and
; verify a metafunction which will enable MUCH faster reduction of (apply$-prim
; 'fn args).

(defun meta-apply$-prim (term)
  (cond ((and (consp term)
              (eq (ffn-symb term) 'apply$-prim)
              (quotep (fargn term 1))
              (symbolp (cadr (fargn term 1))))
         (let* ((fn (cadr (fargn term 1)))
                (args (fargn term 2))
                (temp (assoc-eq fn *apply$-primitives*)))
           (cond
            ((null temp) term)
            (t `(,fn ,@(car-cadr-caddr-etc (cdr temp) args))))))
        (t term)))

(make-event
 `(encapsulate
   nil

   (set-rewrite-stack-limit 4000)

; We introduce the relevant evaluator; defevaluator works in a
; very restricted theory (*DEFEVALUATOR-FORM-BASE-THEORY*) and so
; we do not have to worry about disabling all the functions
; involved in the defun of apply$-prim.

   (with-output
    :off (prove event)
    (defevaluator apply$-prim-meta-fn-ev
      apply$-prim-meta-fn-ev-list
      ((apply$-prim fn args)
       ,@*apply$-primitives*)))

; To prove correctness we need to force car-cadr-caddr-etc
; to open.

   (local
    (defthm car-cadr-caddr-etc-opener
      (equal (car-cadr-caddr-etc (cons x y) args)
             (cons (list 'car args)
                   (car-cadr-caddr-etc y (list 'CDR args))))))

; Here's correctness of the apply$-prim simplifier.

   (with-output
    :off (prove event)
    (defthm apply$-prim-meta-fn-correct
      (equal (apply$-prim-meta-fn-ev term alist)
             (apply$-prim-meta-fn-ev (meta-apply$-prim term) alist))
      :hints (("Goal" :in-theory (disable (:executable-counterpart break$))))
      :rule-classes ((:meta :trigger-fns (apply$-prim)))))

   (defthm apply$-primp-implies-symbolp
     (implies (apply$-primp fn)
              (symbolp fn))
     :rule-classes :forward-chaining)

   ))

(in-theory (disable apply$-prim apply$-primp))
