; A tool to generate substution code that calls a given evaluator
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book provides a tool that, given the name of an evaluator, makes a
;; version of my-sublis-var-and-eval that uses it.

(include-book "kestrel/alists-light/maybe-replace-var" :dir :system)
(include-book "all-dargp-less-than")
(include-book "axe-trees")

(defun make-substitution-code-simple-fn (suffix evaluator-base-name)
  (declare (xargs :guard (and (symbolp suffix)
                              (symbolp evaluator-base-name))))
  (let ((my-sublis-var-and-eval-name (pack$ 'my-sublis-var-and-eval- suffix))
        (my-sublis-var-and-eval-lst-name (pack$ 'my-sublis-var-and-eval- suffix '-lst))
        (apply-axe-evaluator-to-quoted-args-name (pack$ 'apply- evaluator-base-name '-to-quoted-args)))
    `(encapsulate ()
       (local (include-book "kestrel/axe/replace-var-rules" :dir :system))
       (local (include-book "kestrel/lists-light/len" :dir :system))
       (local (include-book "kestrel/utilities/pseudo-termp" :dir :system))

       ;; This handles lambda applications correctly (by handling their args) but does not beta reduce.
       (mutual-recursion
        ;; Returns a new term.
        (defund ,my-sublis-var-and-eval-name (alist ;maps vars to nodenums/quoteps
                                              term interpreted-function-alist)
          (declare (xargs :verify-guards nil ;done below
                          :guard (and (symbol-alistp alist)
                                      (all-dargp (strip-cdrs alist))
                                      (pseudo-termp term)
                                      (interpreted-function-alistp interpreted-function-alist))))
          (cond ((variablep term)
                 (maybe-replace-var term alist))
                ((fquotep term) term)
                (t (let ((fn (ffn-symb term)))
                     (if (and (eq fn 'if) ;; TODO: consider also handling bvif, boolif, myif, maybe boolor and booland...
                              (= 3 (len (fargs term))))
                         (let* ((test (second term))
                                (test-result (,my-sublis-var-and-eval-name alist test interpreted-function-alist)))
                           (if (quotep test-result)
                               (,my-sublis-var-and-eval-name alist (if (unquote test-result) ;if the test is not nil
                                                                       (third term) ;then part
                                                                     (fourth term) ;else part
                                                                     )
                                                             interpreted-function-alist)
                             ;;couldn't resolve if-test:
                             (list 'if
                                   test-result
                                   (,my-sublis-var-and-eval-name alist (third term) interpreted-function-alist) ;then part
                                   (,my-sublis-var-and-eval-name alist (fourth term) interpreted-function-alist) ;else part
                                   )))
                       ;;regular function call or lambda
                       ;; Substitute in the args:
                       (mv-let (ground-termp args)
                         (,my-sublis-var-and-eval-lst-name alist (fargs term) interpreted-function-alist)
                         (if ground-termp
                             (mv-let (erp res)
                               (,apply-axe-evaluator-to-quoted-args-name fn args interpreted-function-alist)
                               (if erp
                                   (progn$ ;; This failure can be due to a sub-function not being in the interpreted-function-alist
                                    (cw "Failed to apply ~x0 (or one of its subfunctions) to constant args.~%" fn) ;; Shows messages about ground calls that we cannot evaluate
                                    ;; (cw "sub: Failed to apply ~x0 to constant args (er:~x1,ifns:~x2).~%" fn erp (strip-cars interpreted-function-alist) ;(len interpreted-function-alist))
                                    (cons fn args))
                                 (enquote res)))
                           (cons fn args))))))))

        ;; Returns (mv ground-termp args).
        (defund ,my-sublis-var-and-eval-lst-name (alist terms interpreted-function-alist)
          (declare (xargs
                    :verify-guards nil
                    :guard (and (symbol-alistp alist)
                                (all-dargp (strip-cdrs alist)) ;gen?  really just need that things whose cars are 'quote are myquoteps
                                (pseudo-term-listp terms)
                                (interpreted-function-alistp interpreted-function-alist))))
          (if (atom terms)
              (mv t nil)
            (let ((new-car (,my-sublis-var-and-eval-name alist (first terms) interpreted-function-alist)))
              (mv-let (cdr-ground-termp new-cdr)
                (,my-sublis-var-and-eval-lst-name alist (rest terms) interpreted-function-alist)
                (mv (and cdr-ground-termp (quotep new-car))
                    (cons new-car new-cdr)))))))

       (make-flag ,my-sublis-var-and-eval-name)

       (defthm ,(pack$ 'len-of-mv-nth-1-of- my-sublis-var-and-eval-lst-name)
         (equal (len (mv-nth 1 (,my-sublis-var-and-eval-lst-name alist terms interpreted-function-alist)))
                (len terms))
         :hints (("Goal" :induct (len terms) :in-theory (enable ,my-sublis-var-and-eval-lst-name (:i len)))))

       (defthm ,(pack$ 'true-listp-of-mv-nth-1-of- my-sublis-var-and-eval-lst-name)
         (true-listp (mv-nth 1 (,my-sublis-var-and-eval-lst-name alist terms interpreted-function-alist)))
         :hints (("Goal" :induct (len terms) :in-theory (enable ,my-sublis-var-and-eval-lst-name (:i len)))))

       (,(pack$ 'defthm-flag- my-sublis-var-and-eval-name)
         (defthm ,(pack$ 'myquotep-of- my-sublis-var-and-eval-name)
           (implies (and (eq 'quote (car (,my-sublis-var-and-eval-name alist term interpreted-function-alist)))
                         (all-dargp (strip-cdrs alist))
                         (pseudo-termp term))
                    (myquotep (,my-sublis-var-and-eval-name alist term interpreted-function-alist)))
           :flag ,my-sublis-var-and-eval-name)
         (defthm ,(pack$ 'all-myquotep-of-mv-nth-1-of- my-sublis-var-and-eval-lst-name)
           (implies (and (mv-nth 0 (,my-sublis-var-and-eval-lst-name alist terms interpreted-function-alist)) ;means ground term
                         (all-dargp (strip-cdrs alist))
                         (pseudo-term-listp terms))
                    (all-myquotep (mv-nth 1 (,my-sublis-var-and-eval-lst-name alist terms interpreted-function-alist))))
           :flag ,my-sublis-var-and-eval-lst-name)
         :hints (("Goal" :in-theory (e/d (,my-sublis-var-and-eval-name ,my-sublis-var-and-eval-lst-name
                                                                       myquotep-when-dargp)
                                         (myquotep)))))

       (verify-guards ,my-sublis-var-and-eval-name
         :hints (("Goal"
                  :use (:instance ,(pack$ 'myquotep-of- my-sublis-var-and-eval-name)
                                  (term (cadr term)))
                  :in-theory (disable myquotep symbol-alistp strip-cdrs ,(pack$ 'myquotep-of- my-sublis-var-and-eval-name)))))

       (,(pack$ 'defthm-flag- my-sublis-var-and-eval-name)
         (defthm ,(pack$ 'axe-treep-of- my-sublis-var-and-eval-name)
           (implies (and ;(eq 'quote (car (,my-sublis-var-and-eval-name alist term interpreted-function-alist)))
                     (all-dargp (strip-cdrs alist))
                     (pseudo-termp term))
                    (axe-treep (,my-sublis-var-and-eval-name alist term interpreted-function-alist)))
           :flag ,my-sublis-var-and-eval-name)
         (defthm ,(pack$ 'all-axe-treep-of-mv-nth-1-of- my-sublis-var-and-eval-lst-name)
           (implies (and ;(mv-nth 0 (,my-sublis-var-and-eval-lst-name alist terms interpreted-function-alist))
                     (all-dargp (strip-cdrs alist))
                     (pseudo-term-listp terms))
                    (all-axe-treep (mv-nth 1 (,my-sublis-var-and-eval-lst-name alist terms interpreted-function-alist))))
           :flag ,my-sublis-var-and-eval-lst-name)
         :hints (("Goal" :in-theory (e/d (,my-sublis-var-and-eval-name ,my-sublis-var-and-eval-lst-name)
                                         (myquotep ,(pack$ 'myquotep-of- my-sublis-var-and-eval-name) axe-treep)))))

       (,(pack$ 'defthm-flag- my-sublis-var-and-eval-name)
         (defthm ,(pack$ 'bounded-axe-treep-of- my-sublis-var-and-eval-name)
           (implies (and ;(eq 'quote (car (,my-sublis-var-and-eval-name alist term interpreted-function-alist)))
                     (all-dargp-less-than (strip-cdrs alist) dag-len)
                     (pseudo-termp term))
                    (bounded-axe-treep (,my-sublis-var-and-eval-name alist term interpreted-function-alist) dag-len))
           :flag ,my-sublis-var-and-eval-name)
         (defthm ,(pack$ 'all-bounded-axe-treep-of-mv-nth-1-of- my-sublis-var-and-eval-lst-name)
           (implies (and ;(mv-nth 0 (,my-sublis-var-and-eval-lst-name alist terms interpreted-function-alist))
                     (all-dargp-less-than (strip-cdrs alist) dag-len)
                     (pseudo-term-listp terms))
                    (all-bounded-axe-treep (mv-nth 1 (,my-sublis-var-and-eval-lst-name alist terms interpreted-function-alist)) dag-len))
           :flag ,my-sublis-var-and-eval-lst-name)
         :hints (("Goal" :in-theory (e/d (,my-sublis-var-and-eval-name
                                          ,my-sublis-var-and-eval-lst-name
                                          bounded-axe-treep-when-dargp-less-than
                                          ;;bounded-axe-treep-when-natp
                                          ;;bounded-axe-treep-when-not-consp
                                          )
                                         (myquotep ,(pack$ 'myquotep-of- my-sublis-var-and-eval-name)
                                                   bounded-axe-treep
                                                   natp))))))))
(defmacro make-substitution-code-simple (suffix
                                         evaluator-base-name)
  (make-substitution-code-simple-fn suffix
                                    evaluator-base-name))
