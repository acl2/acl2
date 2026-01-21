; A tool to generate substitution code (like subcor-var) that calls a given evaluator
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
;; version of subcor-var-and-eval that uses it.  This is for use when instead
;; of an alist you have the list of vars and the list of values as separate
;; lists.

;; See also make-sublis-var-and-eval-simple.lisp.

(include-book "kestrel/alists-light/maybe-replace-var" :dir :system)
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "bounded-darg-listp")
(include-book "axe-trees")

(defun make-subcor-var-and-eval-simple-fn (suffix evaluator-base-name)
  (declare (xargs :guard (and (symbolp suffix)
                              (symbolp evaluator-base-name))))
  (let ((subcor-var-and-eval-name (pack$ 'subcor-var-and-eval- suffix))
        (subcor-var-and-eval-lst-name (pack$ 'subcor-var-and-eval- suffix '-lst))
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

       ;; we put the VAR param last to match subcor-var
       (defund subcor-var1-with-dargs (vars dargs var)
         (declare (xargs :guard (and (symbol-listp vars)
                                     (darg-listp dargs)
                                     (equal (len vars) (len dargs))
                                     (symbolp var))))
         (if (atom vars)
             var ; sometimes this can't happen (when var is among the vars)
           (if (eq var (first vars))
               (first dargs)
             (subcor-var1-with-dargs (rest vars) (rest dargs) var))))

       (local
        (defthm dargp-of-subcor-var1-with-dargs
          (implies (and (not (symbolp (subcor-var1-with-dargs vars dargs var)))
                        ;; (symbol-listp vars)
                        (darg-listp dargs)
                        ;(equal (len vars) (len dargs))
                        (symbolp var))
                   (dargp (subcor-var1-with-dargs vars dargs var)))
          :hints (("Goal" :induct (subcor-var1-with-dargs vars dargs var)
                   :in-theory (enable subcor-var1-with-dargs)))))

       (local
        (defthm myquotep-of-subcor-var1-with-dargs
          (implies (and (equal 'quote (car (subcor-var1-with-dargs vars dargs var)))
                        ;; (symbol-listp vars)
                        (darg-listp dargs)
                        ;(equal (len vars) (len dargs))
                        (symbolp var))
                   (myquotep (subcor-var1-with-dargs vars dargs var)))
          :hints (("Goal" :use dargp-of-subcor-var1-with-dargs
                   :in-theory (disable dargp-of-subcor-var1-with-dargs)))))

       (local
        (defthm axe-treep-of-subcor-var1-with-dargs
          (implies (and ;(not (symbolp (subcor-var1-with-dargs vars dargs var)))
                        ;; (symbol-listp vars)
                        (darg-listp dargs)
                        ;(equal (len vars) (len dargs))
                        (symbolp var))
                   (axe-treep (subcor-var1-with-dargs vars dargs var)))
          :hints (("Goal" :induct (subcor-var1-with-dargs vars dargs var)
                   :in-theory (enable subcor-var1-with-dargs)))))

       (local
        (defthm bounded-axe-treep-of-subcor-var1-with-dargs
          (implies (and (bounded-darg-listp dargs dag-len)
                        (symbolp var))
                   (bounded-axe-treep (subcor-var1-with-dargs vars dargs var) dag-len))
          :hints (("Goal" :induct (subcor-var1-with-dargs vars dargs var)
                   :in-theory (enable subcor-var1-with-dargs bounded-axe-treep-when-symbolp)))))

       ;; This handles lambda applications correctly (by handling their args) but does not beta reduce.
       (mutual-recursion
         ;; Applies the substitution represented by VARS and DARGS to TERM.
        ;; Returns an axe-tree.
        (defund ,subcor-var-and-eval-name (vars dargs term interpreted-function-alist)
          (declare (xargs :guard (and (symbol-listp vars)
                                      (darg-listp dargs)
                                      (equal (len vars) (len dargs))
                                      (pseudo-termp term)
                                      (interpreted-function-alistp interpreted-function-alist))
                          :verify-guards nil ;done below
                          ))
          (cond ((variablep term)
                 ;; I can't think of a way to be faster here even if we know var is among the vars:
                 (subcor-var1-with-dargs vars dargs term))
                ((fquotep term) term)
                (t (let ((fn (ffn-symb term)))
                     (if (and (eq fn 'if) ;; TODO: consider also handling bvif, boolif, myif, bv-array-if, maybe boolor and booland...
                              (consp (cddr (fargs term))) ;; for guards
                              )
                         (let* ((test (first (fargs term)))
                                (test-result (,subcor-var-and-eval-name vars dargs test interpreted-function-alist)))
                           (if (quotep test-result)
                               ;; Resolved the test, so continue with just the relevant branch:
                               (,subcor-var-and-eval-name vars dargs (if (unquote test-result) ;if the test is not nil
                                                                    (second (fargs term)) ;then part
                                                                  (third (fargs term)) ;else part
                                                                  )
                                                             interpreted-function-alist)
                             ;;couldn't resolve if-test:
                             (list 'if
                                   test-result
                                   (,subcor-var-and-eval-name vars dargs (second (fargs term)) interpreted-function-alist) ;then part
                                   (,subcor-var-and-eval-name vars dargs (third (fargs term)) interpreted-function-alist) ;else part
                                   )))
                       ;;regular function call or lambda
                       ;; Substitute in the args:
                       (mv-let (ground-termp args)
                         (,subcor-var-and-eval-lst-name vars dargs (fargs term) interpreted-function-alist)
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
        (defund ,subcor-var-and-eval-lst-name (vars dargs terms interpreted-function-alist)
          (declare (xargs :guard (and (symbol-listp vars)
                                      (darg-listp dargs)
                                      (equal (len vars) (len dargs))
                                      (pseudo-term-listp terms)
                                      (interpreted-function-alistp interpreted-function-alist))))
          (if (atom terms)
              (mv t nil)
            (let ((new-car (,subcor-var-and-eval-name vars dargs (first terms) interpreted-function-alist)))
              (mv-let (cdr-ground-termsp new-cdr)
                (,subcor-var-and-eval-lst-name vars dargs (rest terms) interpreted-function-alist)
                (mv (and cdr-ground-termsp (quotep new-car))
                    (cons new-car new-cdr)))))))

       (make-flag ,subcor-var-and-eval-name)

       (defthm ,(pack$ 'len-of-mv-nth-1-of- subcor-var-and-eval-lst-name)
         (equal (len (mv-nth 1 (,subcor-var-and-eval-lst-name vars dargs terms interpreted-function-alist)))
                (len terms))
         :hints (("Goal" :induct (len terms) :in-theory (enable ,subcor-var-and-eval-lst-name (:i len))
                  :expand (,subcor-var-and-eval-lst-name vars dargs terms interpreted-function-alist))))

       (defthm ,(pack$ 'true-listp-of-mv-nth-1-of- subcor-var-and-eval-lst-name)
         (true-listp (mv-nth 1 (,subcor-var-and-eval-lst-name vars dargs terms interpreted-function-alist)))
         :hints (("Goal" :induct (len terms) :in-theory (enable ,subcor-var-and-eval-lst-name (:i len))
                  :expand (,subcor-var-and-eval-lst-name vars dargs terms interpreted-function-alist))))

       (,(pack$ 'defthm-flag- subcor-var-and-eval-name)
         (defthm ,(pack$ 'myquotep-of- subcor-var-and-eval-name)
           (implies (and (eq 'quote (car (,subcor-var-and-eval-name vars dargs term interpreted-function-alist)))
                         (darg-listp dargs)
                         (pseudo-termp term))
                    (myquotep (,subcor-var-and-eval-name vars dargs term interpreted-function-alist)))
           :flag ,subcor-var-and-eval-name)
         (defthm ,(pack$ 'all-myquotep-of-mv-nth-1-of- subcor-var-and-eval-lst-name)
           (implies (and (mv-nth 0 (,subcor-var-and-eval-lst-name vars dargs terms interpreted-function-alist)) ;means ground term
                         (darg-listp dargs)
                         (pseudo-term-listp terms))
                    (all-myquotep (mv-nth 1 (,subcor-var-and-eval-lst-name vars dargs terms interpreted-function-alist))))
           :flag ,subcor-var-and-eval-lst-name)
         :hints (("Goal" :expand (pseudo-termp term) ; why?
                  :in-theory (e/d (,subcor-var-and-eval-name
                                   ,subcor-var-and-eval-lst-name
                                   myquotep-when-dargp
                                   pseudo-termp-when-not-consp-cheap)
                                  (myquotep)))))

       (verify-guards ,subcor-var-and-eval-name
         :hints (("Goal"
                  :use (:instance ,(pack$ 'myquotep-of- subcor-var-and-eval-name)
                                  (term (cadr term)))
                  :in-theory (disable myquotep symbol-alistp strip-cdrs ,(pack$ 'myquotep-of- subcor-var-and-eval-name)))))

       (,(pack$ 'defthm-flag- subcor-var-and-eval-name)
         (defthm ,(pack$ 'axe-treep-of- subcor-var-and-eval-name)
           (implies (and (darg-listp dargs)
                         (pseudo-termp term))
                    (axe-treep (,subcor-var-and-eval-name vars dargs term interpreted-function-alist)))
           :flag ,subcor-var-and-eval-name)
         (defthm ,(pack$ 'axe-tree-listp-of-mv-nth-1-of- subcor-var-and-eval-lst-name)
           (implies (and (darg-listp dargs)
                         (pseudo-term-listp terms))
                    (axe-tree-listp (mv-nth 1 (,subcor-var-and-eval-lst-name vars dargs terms interpreted-function-alist))))
           :flag ,subcor-var-and-eval-lst-name)
         :hints (("Goal" :in-theory (e/d (,subcor-var-and-eval-name ,subcor-var-and-eval-lst-name
                                                                    pseudo-termp-when-not-consp-cheap)
                                         (myquotep ,(pack$ 'myquotep-of- subcor-var-and-eval-name) axe-treep)))))

       (,(pack$ 'defthm-flag- subcor-var-and-eval-name)
         (defthm ,(pack$ 'bounded-axe-treep-of- subcor-var-and-eval-name)
           (implies (and (bounded-darg-listp dargs dag-len)
                         (pseudo-termp term))
                    (bounded-axe-treep (,subcor-var-and-eval-name vars dargs term interpreted-function-alist) dag-len))
           :flag ,subcor-var-and-eval-name)
         (defthm ,(pack$ 'bounded-axe-tree-listp-of-mv-nth-1-of- subcor-var-and-eval-lst-name)
           (implies (and (bounded-darg-listp dargs dag-len)
                         (pseudo-term-listp terms))
                    (bounded-axe-tree-listp (mv-nth 1 (,subcor-var-and-eval-lst-name vars dargs terms interpreted-function-alist)) dag-len))
           :flag ,subcor-var-and-eval-lst-name)
         :hints (("Goal" :in-theory (e/d (,subcor-var-and-eval-name
                                          ,subcor-var-and-eval-lst-name
                                          bounded-axe-treep-when-dargp-less-than
                                          ;;bounded-axe-treep-when-natp
                                          ;;bounded-axe-treep-when-not-consp
                                          pseudo-termp-when-not-consp-cheap
                                          )
                                         (myquotep ,(pack$ 'myquotep-of- subcor-var-and-eval-name)
                                                   bounded-axe-treep
                                                   natp))))))))

;; Makes "subcor and eval" functions for the evaluator with the given
;; evaluator-base-name.  Uses SUFFIX when creating the names of the new
;; functions.
(defmacro make-subcor-var-and-eval-simple (suffix evaluator-base-name)
  (make-subcor-var-and-eval-simple-fn suffix evaluator-base-name))
