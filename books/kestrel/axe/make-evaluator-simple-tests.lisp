; Tests of make-evaluator-simple
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

(include-book "make-evaluator-simple")
(include-book "kestrel/utilities/erp" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)
(include-book "std/testing/eval" :dir :system)

(deftest
  (make-evaluator-simple test
                         '(consp stringp)))


(deftest
;todo: what about guards?
  (make-evaluator-simple for-len
                         '(len
                           consp
                           cdr
                           binary-+)
                         :verify-guards nil)

  ;; Expected result:
  (must-be-redundant
   (MUTUAL-RECURSION
    ;; Returns (mv erp result) where erp is nil (no error), :unknown-function, or :count-exceeded.
    (defund apply-axe-evaluator-for-len (fn args interpreted-function-alist count)
      (declare (type (unsigned-byte 60) count)
               (xargs :measure (make-ord 2 (+ 1 (nfix count)) (make-ord 1 2 0))
                      :verify-guards nil
                      :guard (and (or (symbolp fn) (pseudo-lambdap fn))
                                  (true-listp args)
                                  (interpreted-function-alistp interpreted-function-alist)
                                  (natp count))))
      (if (consp fn)
          ;; lambda case:
          (let* ((formals (second fn))
                 (body (third fn))
                 (alist (pairlis$-fast formals args)))
            (eval-axe-evaluator-for-len alist body interpreted-function-alist count))
        (let ((args-to-walk-down args))
          (mv-let
            (hit val)
            (if (endp args-to-walk-down)
                (mv nil nil)
              (let ((args-to-walk-down (cdr args-to-walk-down)))
                (if (endp args-to-walk-down)
                    (let ((arg1 (nth 0 args)))
                      (if (eq 'cdr fn)
                          (mv t (cdr arg1))
                        (if (eq 'consp fn)
                            (mv t (consp arg1))
                          (if (eq 'len fn)
                              (mv t (len arg1))
                            (mv nil nil)))))
                  (let ((args-to-walk-down (cdr args-to-walk-down)))
                    (if (endp args-to-walk-down)
                        (let ((arg2 (nth 1 args))
                              (arg1 (nth 0 args)))
                          (if (eq 'binary-+ fn)
                              (mv t (binary-+ arg1 arg2))
                            (mv nil nil)))
                      (mv nil nil))))))
            (if hit
                (mv (erp-nil) val)
              (let ((match (assoc-eq fn interpreted-function-alist)))
                (if (not match)
                    ;; Unknown function: ~x0 applied to args ~x1.  Consider passing it as an interpreted function, or adding it to the list of built-ins for the evaluator ~x2.  (This error also occurs when a function appears with an incorrect number of arguments.)
                    (progn$ ;; ...
                     (mv :unknown-function nil))
                  (let* ((fn-info (cdr match))
                         (formals (first fn-info))
                         (body (second fn-info))
                         (alist (pairlis$-fast formals args)) ;todo: avoid this consing?
                         )
                    (eval-axe-evaluator-for-len alist body interpreted-function-alist count)))))))))

    ;; Returns (mv erp result).
    (defun eval-axe-evaluator-for-len (alist form interpreted-function-alist count)
      (declare (type (unsigned-byte 60) count)
               (xargs :measure (make-ord 2 (+ 1 (nfix count)) (make-ord 1 1 (acl2-count form)))
                      :guard (and (symbol-alistp alist)
                                  (pseudo-termp form)
                                  (interpreted-function-alistp interpreted-function-alist)
                                  (natp count))))
      (if (or (not (mbt (natp count)))
              (= 0 count))
          (mv :count-exceeded nil)
        (cond ((variablep form)
               (mv (erp-nil) (lookup-eq form alist)))
              ((fquotep form)
               (mv (erp-nil) (unquote form)))
              (t
               (let ((fn (ffn-symb form)))
                 (if (and (or (eq fn 'if) (eq fn 'myif))
                          (= 3 (len (fargs form))))
                     (b* ((test-form (second form))
                          ((mv erp test-result)
                           (eval-axe-evaluator-for-len alist
                                               test-form interpreted-function-alist
                                               count))
                          ((when erp) (mv erp nil)))
                       (eval-axe-evaluator-for-len alist
                                           (if test-result
                                               (third form)
                                             (fourth form))
                                           interpreted-function-alist count))
                   (b* (((mv erp args)
                         (eval-list-axe-evaluator-for-len alist (fargs form)
                                                  interpreted-function-alist
                                                  count))
                        ((when erp) (mv erp nil)))
                     (apply-axe-evaluator-for-len fn args interpreted-function-alist (+ -1 count)))))))))

    ;; returns (mv erp result).
    (defun eval-list-axe-evaluator-for-len (alist form-lst interpreted-function-alist count)
      (declare (type (unsigned-byte 60) count)
               (xargs :measure (make-ord 2 (+ 1 (nfix count)) (make-ord 1 1 (acl2-count form-lst)))
                      :guard (and (symbol-alistp alist)
                                  (pseudo-term-listp form-lst)
                                  (interpreted-function-alistp interpreted-function-alist)
                                  (natp count))))
      (if (endp form-lst)
          (mv (erp-nil) nil)
        (b* (((mv erp car-res)
              (eval-axe-evaluator-for-len alist (car form-lst) interpreted-function-alist count))
             ((when erp) (mv erp nil))
             ((mv erp cdr-res)
              (eval-list-axe-evaluator-for-len alist (cdr form-lst) interpreted-function-alist count))
             ((when erp) (mv erp nil)))
          (mv (erp-nil) (cons car-res cdr-res)))))
    ) ;end of mut-rec



   ;; Returns (mv erp result).
   (defun apply-axe-evaluator-for-len-to-quoted-args (fn args interpreted-function-alist)
     (declare (xargs :guard (and (or (symbolp fn) (pseudo-lambdap fn))
                                 (true-listp args)
                                 (all-myquotep args)
                                 (interpreted-function-alistp interpreted-function-alist))
                     :verify-guards nil))
     (if (consp fn)
         (let* ((formals (second fn))
                (body (third fn))
                (alist (pairlis$-fast formals (unquote-list args))))
           (eval-axe-evaluator-for-len alist body interpreted-function-alist *max-fixnum*))
       (let ((args-to-walk-down args))
         (mv-let
           (hit val)
           (if (endp args-to-walk-down)
               (mv nil nil)
             (let ((args-to-walk-down (cdr args-to-walk-down)))
               (if (endp args-to-walk-down)
                   (let ((arg1 (unquote (nth 0 args))))
                     (if (eq 'cdr fn)
                         (mv t (cdr arg1))
                       (if (eq 'consp fn)
                           (mv t (consp arg1))
                         (if (eq 'len fn)
                             (mv t (len arg1))
                           (mv nil nil)))))
                 (let ((args-to-walk-down (cdr args-to-walk-down)))
                   (if (endp args-to-walk-down)
                       (let ((arg2 (unquote (nth 1 args)))
                             (arg1 (unquote (nth 0 args))))
                         (if (eq 'binary-+ fn)
                             (mv t (binary-+ arg1 arg2))
                           (mv nil nil)))
                     (mv nil nil))))))
           (if hit
               (mv (erp-nil) val)
             (let ((match (assoc-eq fn interpreted-function-alist)))
               (if (not match)
                   (mv :unknown-function nil)
                 (let* ((fn-info (cdr match))
                        (formals (first fn-info))
                        (body (second fn-info))
                        (alist (pairlis$-fast formals (unquote-list args))))
                   (eval-axe-evaluator-for-len alist body interpreted-function-alist *max-fixnum*))))))))))

  ;; Apply LEN to a single, argument, the list (a b c).  The result is 3 and no
  ;; error is signalled.
  (defthm axe-evaluator-for-len-test
    (equal (apply-axe-evaluator-for-len 'len '((a b c)) nil *max-fixnum*)
           (mv (erp-nil) 3)))

  (defun myplus (x y)
    (+ x y))

  ;; Make sure we can evaluate an interpreted function:
  (defthm axe-evaluator-for-len-test2
    (equal (eval-axe-evaluator-for-len (acons 'x 17 nil)
                               '(myplus '2 x)
                               '((MYPLUS (X Y) (BINARY-+ X Y))) ;;(make-interpreted-function-alist '(myplus) (w state))
                               *max-fixnum*)
           (mv (erp-nil) 19)))

  ;;todo: add more tests!
  )

(deftest
  (must-fail
   (make-evaluator-simple for-len2
                          '((cons car) ;; car is not equivalent to cons!
                            ))))
