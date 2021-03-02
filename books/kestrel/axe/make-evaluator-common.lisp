; Utilities for making evaluators
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

;; The book contains utilities used by make-evaluator.lisp and
;; make-evaluator-simple.lisp.

(include-book "interpreted-function-alistp")
(include-book "kestrel/alists-light/lookup" :dir :system)

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

;the generated term returns (mv hitp val) or (mv hitp val trace) depending on tracingp
;do the fns get tested in reverse order??
;the alist should have no duplicates
(defun make-eval-case-for-fns (fn-call-alist current-arity tracingp acc)
;;  (declare (xargs :guard (and (symbol-alistp fn-call-alist))))
  (if (endp fn-call-alist)
      acc
    (let* ((entry (car fn-call-alist))
           (fn (first entry))
           (expr (cdr entry)))
      (if (not (equal current-arity (len (cdr expr))))
          (er hard 'make-eval-case-for-fns "Bad entry for fn ~x0 in the fn-call-alist." fn)
      (make-eval-case-for-fns (cdr fn-call-alist)
                              current-arity
                              tracingp
                              `(if (eq ',fn fn)
                                   ,(if tracingp
                                        `(mv t ,expr (empty-trace)) ;no trace for this execution
                                      `(mv t ,expr))
                                 ,acc))))))

;the args are numbered starting at 1
;; TODO: We could speed this up by not repeatedly calling nth
(defun bind-args-to-nths (quoted-argsp n)
  (declare (xargs :measure (nfix (+ 1 n))))
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

;the generated term returns (mv hitp val) or (mv hitp val trace) depending on tracingp
(defun make-apply-cases-for-arities (current-arity arity-fn-call-alist-alist quoted-argsp innermost-callp tracingp acc)
  (declare (xargs :measure (nfix (+ 1 current-arity))))
  (if (not (natp current-arity))
      acc
    (let* ((calls-for-this-arity (lookup current-arity arity-fn-call-alist-alist)))
      (make-apply-cases-for-arities (+ -1 current-arity)
                                    arity-fn-call-alist-alist
                                    quoted-argsp
                                    nil ;not innermost-call
                                    tracingp
                                    `(if (endp args-to-walk-down)
                                         ,(if (not calls-for-this-arity)
                                              '(mv nil ;no hit
                                                   nil)
                                            `(let (,@(bind-args-to-nths quoted-argsp current-arity))
                                               ,@(let ((eval-case-for-this-arity (make-eval-case-for-fns calls-for-this-arity
                                                                                                         current-arity
                                                                                                         tracingp
                                                                                                         '(mv nil ;no hit
                                                                                                              nil))))
                                                   (if (and (= current-arity 4)
                                                            (= (len calls-for-this-arity) 2))
                                                       ;; special cases for arity 4 and 8 if we only have self-functions to eval, since arg4/arg8 is overwritten by the array-depth param
                                                       `((declare (ignore arg4)) ;todo: don't even let bind it
                                                         ,eval-case-for-this-arity)
                                                     (if (and (= current-arity 8) ;todo: don't even let bind it
                                                              (= (len calls-for-this-arity) 1))
                                                         `((declare (ignore arg8))
                                                           ,eval-case-for-this-arity)
                                                       ;; normal case:
                                                       `(,eval-case-for-this-arity))))))
                                       ,(if innermost-callp ;leave off the let:
                                            acc
                                          `(let ((args-to-walk-down (cdr args-to-walk-down)))
                                             ,acc)))))))

(defun strip-cars-list (items)
  (if (endp items)
      nil
    (append (strip-cars (first items))
            (strip-cars-list (rest items)))))
