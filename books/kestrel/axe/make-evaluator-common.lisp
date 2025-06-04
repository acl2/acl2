; Utilities for making evaluators
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The book contains utilities used by make-evaluator.lisp and
;; make-evaluator-simple.lisp.

(include-book "interpreted-function-alistp")
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "kestrel/alists-light/lookup" :dir :system)
(include-book "kestrel/typed-lists-light/symbol-alist-listp" :dir :system)
(include-book "kestrel/typed-lists-light/alist-listp" :dir :system)

;dup in books/kestrel/utilities/system/term-function-recognizers.lisp
(DEFUN PSEUDO-LAMBDAP (X)
  (DECLARE (XARGS :GUARD T))
  (LET ((__FUNCTION__ 'PSEUDO-LAMBDAP))
       (DECLARE (IGNORABLE __FUNCTION__))
       (AND (TRUE-LISTP X)
            (= (LEN X) 3)
            (EQ (FIRST X) 'LAMBDA)
            (SYMBOL-LISTP (SECOND X))
            (PSEUDO-TERMP (THIRD X)))))

;; ;move
;; (defthm pseudo-lambdap-of-car
;;   (implies (pseudo-termp form)
;;            (equal (pseudo-lambdap (car form))
;;                   (not (symbolp (car form)))))
;;   :hints (("Goal" :expand ((pseudo-termp form))
;;            :in-theory (enable pseudo-termp pseudo-lambdap))))

;; Generates a list of cases suitable for use with CASE.
;; Each case returns (mv hitp val) or (mv hitp val trace) depending on tracingp.
; ;the alist should have no duplicates
;rename
(defun make-eval-case-for-fns (fn-call-alist current-arity tracingp)
  (declare (xargs :guard (and (symbol-alistp fn-call-alist)
                              (natp current-arity)
                              (booleanp tracingp))))
  (if (endp fn-call-alist)
      ; the "otherwise" case:
      `((t ,(if tracingp
                '(mv nil nil (empty-trace))
              '(mv nil nil))))
    (let* ((entry (first fn-call-alist))
           (fn (car entry))
           (expr (cdr entry)))
      (if (not (and (true-listp expr)
                    ;;(equal current-arity (len (fargs expr))) ; todo: option to put this back? ; might involve a wrapper like eval-in-logic
                    ))
          (er hard? 'make-eval-case-for-fns "Bad entry for fn ~x0 in the fn-call-alist." fn)
        (cons
          `(,fn ,(if tracingp
                    `(mv t ,expr (empty-trace)) ;no trace for this execution
                  `(mv t ,expr)))
          (make-eval-case-for-fns (rest fn-call-alist) current-arity tracingp))))))

;the args are numbered starting at 1
;; TODO: We could speed this up by not repeatedly calling nth
(defund bind-args-to-nths (quoted-argsp n)
  (declare (xargs :guard (natp n)
                  :measure (nfix (+ 1 n))))
  (if (zp n)
      nil
    (cons `(,(pack$ 'arg (nat-to-string n))
            ,(if quoted-argsp
                 `(unquote (nth ,(+ -1 n) args))
               `(nth ,(+ -1 n) args)))
          (bind-args-to-nths quoted-argsp (+ -1 n)))))

;; (defun arg-names (n)
;;   (declare (xargs :measure (nfix (+ 1 n))))
;;   (if (zp n)
;;       nil
;;     (cons (pack$ 'arg (nat-to-string n))
;;           (arg-names (+ -1 n)))))

;only used for simple evaluators
;the generated term returns (mv hitp val) or (mv hitp val trace) depending on tracingp
(defun make-apply-cases-for-arities-simple (current-arity arity-fn-call-alist-alist quoted-argsp innermost-callp tracingp acc)
  (declare (xargs :guard (and (integerp current-arity)
                              (<= -1 current-arity)
                              (alistp arity-fn-call-alist-alist)
                              (nat-listp (strip-cars arity-fn-call-alist-alist))
                              (symbol-alist-listp (strip-cdrs arity-fn-call-alist-alist))
                              (booleanp quoted-argsp)
                              (booleanp innermost-callp)
                              (booleanp tracingp))
                  :measure (nfix (+ 1 current-arity))))
  (if (not (natp current-arity))
      acc
    (let* ((calls-for-this-arity (lookup current-arity arity-fn-call-alist-alist)))
      (make-apply-cases-for-arities-simple (+ -1 current-arity)
                                           arity-fn-call-alist-alist
                                           quoted-argsp
                                           nil ;not innermost-call
                                           tracingp
                                           `(if (endp args-to-walk-down)
                                                ,(if (not calls-for-this-arity)
                                                     '(mv nil ;no hit
                                                       nil)
                                                   `(let (,@(bind-args-to-nths quoted-argsp current-arity))
                                                      (case fn
                                                        ,@(make-eval-case-for-fns calls-for-this-arity
                                                                                  current-arity
                                                                                  tracingp))))
                                              ,(if innermost-callp ;leave off the let:
                                                   acc
                                                 `(let ((args-to-walk-down (cdr args-to-walk-down)))
                                                    ,acc)))))))

(defun strip-cars-list (items)
  (declare (xargs :guard (alist-listp items)))
  (if (endp items)
      nil
    (append (strip-cars (first items))
            (strip-cars-list (rest items)))))
