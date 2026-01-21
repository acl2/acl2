; A tool to generate substitution code that calls a given evaluator
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

;; This book provides a tool that, given the name of an evaluator, makes a
;; version of sublis-var-and-eval that uses it.

;; See also make-subcor-var-and-eval-simple.lisp.

(include-book "kestrel/alists-light/maybe-replace-var" :dir :system)
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "bounded-darg-listp")
(include-book "axe-trees")

(defun make-sublis-var-and-eval-simple-fn (suffix evaluator-base-name)
  (declare (xargs :guard (and (symbolp suffix)
                              (symbolp evaluator-base-name))))
  (let ((sublis-var-and-eval-name (pack$ 'sublis-var-and-eval- suffix))
        (sublis-var-and-eval-lst-name (pack$ 'sublis-var-and-eval- suffix '-lst))
        (apply-axe-evaluator-to-quoted-args-name (pack$ 'apply- evaluator-base-name '-to-quoted-args)))
    `(encapsulate ()
       (local (include-book "kestrel/axe/replace-var-rules" :dir :system))
       (local (include-book "kestrel/lists-light/len" :dir :system))
       (local (include-book "kestrel/utilities/pseudo-termp" :dir :system))

       ;; for speed:
       (local (in-theory (disable pseudo-termp
                                  member-equal
                                  default-cdr
                                  default-car
                                  ;; quote-lemma-for-bounded-darg-listp-gen-alt ; not always defined
                                  ;car-of-car-when-pseudo-termp
                                  consp-from-len-cheap
                                  ;; len-of-cdr
                                  pseudo-term-listp
                                  ;; quotep
                                  ;;car-cdr-elim
                                  mv-nth
                                  )))

       (local (defthm myquotep-when-pseudo-termp
                (implies (pseudo-termp term)
                         (equal (myquotep term)
                                (quotep term)))
                :hints (("Goal" :in-theory (enable pseudo-termp quotep myquotep)))))

       (local (defthm pseudo-termp-of-car-when-pseudo-term-listp
                (implies (pseudo-term-listp terms)
                         (pseudo-termp (car terms)))
                :hints (("Goal" :in-theory (enable pseudo-termp pseudo-term-listp)))))

       (local (defthm pseudo-termp-of-cadr-when-pseudo-term-listp
                (implies (pseudo-term-listp terms)
                         (pseudo-termp (cadr terms)))
                :hints (("Goal" :in-theory (enable pseudo-termp pseudo-term-listp)))))

       (local (defthm pseudo-termp-of-caddr-when-pseudo-term-listp
                (implies (pseudo-term-listp terms)
                         (pseudo-termp (caddr terms)))
                :hints (("Goal" :in-theory (enable pseudo-termp pseudo-term-listp)))))

       (local (defthm pseudo-termp-of-cdr-when-pseudo-term-listp
                (implies (pseudo-term-listp terms)
                         (pseudo-term-listp (cdr terms)))
                :hints (("Goal" :in-theory (enable pseudo-term-listp)))))

       ;; This handles lambda applications correctly (by handling their args) but does not beta reduce.
       (mutual-recursion
         ;; Applies the substitution represented by ALIST to TERM.
         ;; Returns an axe-tree.
        (defund ,sublis-var-and-eval-name (alist ;maps vars to nodenums/quoteps
                                              term interpreted-function-alist)
          (declare (xargs :guard (and (symbol-alistp alist)
                                      (darg-listp (strip-cdrs alist))
                                      (pseudo-termp term)
                                      (interpreted-function-alistp interpreted-function-alist))
                          :verify-guards nil ;done below
                          ))
          (cond ((variablep term)
                 ;; todo: can we do something faster when we know all the vars are bound?:
                 (maybe-replace-var term alist))
                ((fquotep term) term)
                (t (let ((fn (ffn-symb term)))
                     (if (and (eq fn 'if) ;; TODO: consider also handling bvif, boolif, myif, bv-array-if, maybe boolor and booland...
                              (consp (cddr (fargs term))) ;; for guards
                              )
                         (let* ((test (first (fargs term)))
                                (test-result (,sublis-var-and-eval-name alist test interpreted-function-alist)))
                           (if (quotep test-result)
                               ;; Resolved the test, so continue with just the relevant branch:
                               (,sublis-var-and-eval-name alist (if (unquote test-result) ;if the test is not nil
                                                                    (second (fargs term)) ;then part
                                                                  (third (fargs term)) ;else part
                                                                  )
                                                             interpreted-function-alist)
                             ;;couldn't resolve if-test:
                             (list 'if
                                   test-result
                                   (,sublis-var-and-eval-name alist (second (fargs term)) interpreted-function-alist) ;then part
                                   (,sublis-var-and-eval-name alist (third (fargs term)) interpreted-function-alist) ;else part
                                   )))
                       ;;regular function call or lambda
                       ;; Substitute in the args:
                       (mv-let (ground-termp args)
                         (,sublis-var-and-eval-lst-name alist (fargs term) interpreted-function-alist)
                         (if ground-termp
                             (mv-let (erp res)
                               (,apply-axe-evaluator-to-quoted-args-name fn args interpreted-function-alist)
                               (if erp
                                   (progn$ ;; This failure can be due to a sub-function not being in the interpreted-function-alist
                                    ;; (cw "Can't eval ~x0 (or a subfunction).~%" fn) ;; Shows messages about ground calls that we cannot evaluate
                                    ;; (cw "sub: Failed to apply ~x0 to constant args (er:~x1,ifns:~x2).~%" fn erp (strip-cars interpreted-function-alist) ;(len interpreted-function-alist))
                                    (cons fn args))
                                 (enquote res)))
                           ;; No special treatment for lambda (does not touch the lambda body):
                           (cons fn args))))))))

        ;; Returns (mv ground-termsp args).
        (defund ,sublis-var-and-eval-lst-name (alist terms interpreted-function-alist)
          (declare (xargs :guard (and (symbol-alistp alist)
                                      (darg-listp (strip-cdrs alist)) ;gen?  really just need that things whose cars are 'quote are myquoteps
                                      (pseudo-term-listp terms)
                                      (interpreted-function-alistp interpreted-function-alist))))
          (if (atom terms)
              (mv t nil)
            (let ((new-car (,sublis-var-and-eval-name alist (first terms) interpreted-function-alist)))
              (mv-let (cdr-ground-termsp new-cdr)
                (,sublis-var-and-eval-lst-name alist (rest terms) interpreted-function-alist)
                (mv (and cdr-ground-termsp (quotep new-car))
                    (cons new-car new-cdr)))))))

       (make-flag ,sublis-var-and-eval-name)

       (defthm ,(pack$ 'len-of-mv-nth-1-of- sublis-var-and-eval-lst-name)
         (equal (len (mv-nth 1 (,sublis-var-and-eval-lst-name alist terms interpreted-function-alist)))
                (len terms))
         :hints (("Goal" :induct (len terms) :in-theory (enable ,sublis-var-and-eval-lst-name (:i len))
                  :expand (,sublis-var-and-eval-lst-name alist terms interpreted-function-alist))))

       (defthm ,(pack$ 'true-listp-of-mv-nth-1-of- sublis-var-and-eval-lst-name)
         (true-listp (mv-nth 1 (,sublis-var-and-eval-lst-name alist terms interpreted-function-alist)))
         :hints (("Goal" :induct (len terms) :in-theory (enable ,sublis-var-and-eval-lst-name (:i len))
                  :expand (,sublis-var-and-eval-lst-name alist terms interpreted-function-alist))))

       (,(pack$ 'defthm-flag- sublis-var-and-eval-name)
         (defthm ,(pack$ 'myquotep-of- sublis-var-and-eval-name)
           (implies (and (eq 'quote (car (,sublis-var-and-eval-name alist term interpreted-function-alist)))
                         (darg-listp (strip-cdrs alist))
                         (pseudo-termp term))
                    (myquotep (,sublis-var-and-eval-name alist term interpreted-function-alist)))
           :flag ,sublis-var-and-eval-name)
         (defthm ,(pack$ 'all-myquotep-of-mv-nth-1-of- sublis-var-and-eval-lst-name)
           (implies (and (mv-nth 0 (,sublis-var-and-eval-lst-name alist terms interpreted-function-alist)) ;means ground term
                         (darg-listp (strip-cdrs alist))
                         (pseudo-term-listp terms))
                    (all-myquotep (mv-nth 1 (,sublis-var-and-eval-lst-name alist terms interpreted-function-alist))))
           :flag ,sublis-var-and-eval-lst-name)
         :hints (("Goal" :expand (pseudo-termp term) ; why?
                  :in-theory (e/d (,sublis-var-and-eval-name
                                          ,sublis-var-and-eval-lst-name
                                          myquotep-when-dargp
                                          pseudo-termp-when-not-consp-cheap)
                                         (myquotep)))))

       (verify-guards ,sublis-var-and-eval-name
         :hints (("Goal"
                  :use (:instance ,(pack$ 'myquotep-of- sublis-var-and-eval-name)
                                  (term (cadr term)))
                  :in-theory (disable myquotep symbol-alistp strip-cdrs ,(pack$ 'myquotep-of- sublis-var-and-eval-name)))))

       (,(pack$ 'defthm-flag- sublis-var-and-eval-name)
         (defthm ,(pack$ 'axe-treep-of- sublis-var-and-eval-name)
           (implies (and (darg-listp (strip-cdrs alist))
                         (pseudo-termp term))
                    (axe-treep (,sublis-var-and-eval-name alist term interpreted-function-alist)))
           :flag ,sublis-var-and-eval-name)
         (defthm ,(pack$ 'axe-tree-listp-of-mv-nth-1-of- sublis-var-and-eval-lst-name)
           (implies (and (darg-listp (strip-cdrs alist))
                         (pseudo-term-listp terms))
                    (axe-tree-listp (mv-nth 1 (,sublis-var-and-eval-lst-name alist terms interpreted-function-alist))))
           :flag ,sublis-var-and-eval-lst-name)
         :hints (("Goal" :in-theory (e/d (,sublis-var-and-eval-name ,sublis-var-and-eval-lst-name
                                                                    pseudo-termp-when-not-consp-cheap)
                                         (myquotep ,(pack$ 'myquotep-of- sublis-var-and-eval-name) axe-treep)))))

       (,(pack$ 'defthm-flag- sublis-var-and-eval-name)
         (defthm ,(pack$ 'bounded-axe-treep-of- sublis-var-and-eval-name)
           (implies (and (bounded-darg-listp (strip-cdrs alist) dag-len)
                         (pseudo-termp term))
                    (bounded-axe-treep (,sublis-var-and-eval-name alist term interpreted-function-alist) dag-len))
           :flag ,sublis-var-and-eval-name)
         (defthm ,(pack$ 'bounded-axe-tree-listp-of-mv-nth-1-of- sublis-var-and-eval-lst-name)
           (implies (and (bounded-darg-listp (strip-cdrs alist) dag-len)
                         (pseudo-term-listp terms))
                    (bounded-axe-tree-listp (mv-nth 1 (,sublis-var-and-eval-lst-name alist terms interpreted-function-alist)) dag-len))
           :flag ,sublis-var-and-eval-lst-name)
         :hints (("Goal" :in-theory (e/d (,sublis-var-and-eval-name
                                          ,sublis-var-and-eval-lst-name
                                          bounded-axe-treep-when-dargp-less-than
                                          ;;bounded-axe-treep-when-natp
                                          ;;bounded-axe-treep-when-not-consp
                                          pseudo-termp-when-not-consp-cheap
                                          )
                                         (myquotep ,(pack$ 'myquotep-of- sublis-var-and-eval-name)
                                                   bounded-axe-treep
                                                   natp))))))))

;; Makes "substitute and eval" functions for the evaluator with the given
;; evaluator-base-name.  Uses SUFFIX when creating the names of the new
;; functions.
(defmacro make-sublis-var-and-eval-simple (suffix evaluator-base-name)
  (make-sublis-var-and-eval-simple-fn suffix
                                    evaluator-base-name))
