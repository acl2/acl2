; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

(in-package "ACL2")

; Note: Modified by J Moore, 12/28/2015, to add comments below and to change
; syn::defevaluator-form accordingly.

; This version of defevaluator-form is exactly what is in the ACL2 sources
; except that we skip local in-theory (commented out below) that puts us in a
; minimal theory.

(defun syn::defevaluator-form (evfn evfn-lst namedp fn-args-lst)
  (declare (xargs :mode :program))
  (let* ((fns-clauses (defevaluator-form/fns-clauses fn-args-lst))
         (defthms (defevaluator-form/defthms evfn evfn-lst namedp
                    (namedp-prefix evfn namedp)
                    0
                    (evaluator-clauses evfn evfn-lst fn-args-lst))))
    `(encapsulate
      (((,evfn * *) => *)
       ((,evfn-lst * *) => *))
      (set-inhibit-warnings "theory")
;     (local (in-theory *defevaluator-form-base-theory*))
      . ,(sublis
          (list (cons 'evfn evfn)
                (cons 'evfn-lst evfn-lst)
                (cons 'fns-clauses fns-clauses)
                (cons 'defthms defthms))
          '((local (defun-nx apply-for-defevaluator (fn args)
                     (declare (xargs :verify-guards nil
                                     :normalize nil))
                     (cond . fns-clauses)))
            (local
             (mutual-recursion
              (defun-nx evfn (x a)
                (declare
                 (xargs :verify-guards nil
                        :measure (acl2-count x)
                        :well-founded-relation o<
                        :normalize nil
                        :hints (("goal" :in-theory
                                 (enable (:type-prescription
                                          acl2-count))))
                        :mode :logic))
                (cond
                 ((symbolp x) (and x (cdr (assoc-eq x a))))
                 ((atom x) nil)
                 ((eq (car x) 'quote) (car (cdr x)))
                 (t (let ((args (evfn-lst (cdr x) a)))
                      (cond
                       ((consp (car x))
                        (evfn (car (cdr (cdr (car x))))
                              (pairlis$ (car (cdr (car x)))
                                        args)))
                       ((not (symbolp (car x))) nil)
                       (t (apply-for-defevaluator (car x) args)))))))
                (defun-nx evfn-lst (x-lst a)
                  (declare (xargs :measure (acl2-count x-lst)
                                  :well-founded-relation o<))
                  (cond ((endp x-lst) nil)
                        (t (cons (evfn (car x-lst) a)
                                 (evfn-lst (cdr x-lst) a)))))))
            (local (in-theory (disable evfn evfn-lst apply-for-defevaluator)))
            ;; Mihir M. mod: this is one of a small number of unusual books
            ;; which use true-list fix (enabled by default) while also
            ;; including books which bring in list-fix and disable the
            ;; underlying function true-list-fix. It needs this theory hint for
            ;; proofs to succeed.
            (local
             (defthm eval-list-kwote-lst
               (equal (evfn-lst (kwote-lst args) a)
                      (fix-true-list args))
               :hints (("goal"
                        :expand ((:free (x y) (evfn-lst (cons x y) a))
                                 (evfn-lst nil a)
                                 (:free (x)
                                        (evfn (list 'quote x) a)))
                        :in-theory (enable true-list-fix)
                        :induct (true-list-fix args)))))
            (local
             (defthm true-list-fix-ev-lst
               (equal (true-list-fix (evfn-lst x a))
                      (evfn-lst x a))
               :hints (("goal" :induct (len x)
                        :in-theory (e/d ((:induction len)))
                        :expand ((evfn-lst x a)
                                 (evfn-lst nil a))))))
            (local
             (defthm ev-commutes-car
               (equal (car (evfn-lst x a))
                      (evfn (car x) a))
               :hints (("goal" :expand ((evfn-lst x a)
                                        (evfn nil a))
                        :in-theory (enable default-car)))))
            (local
             (defthm ev-lst-commutes-cdr
               (equal (cdr (evfn-lst x a))
                      (evfn-lst (cdr x) a))
               :hints (("Goal" :expand ((evfn-lst x a)
                                        (evfn-lst nil a))
                        :in-theory (enable default-cdr)))))
            . defthms)))))

; Note that :namedp is an allowed keyword arg but is not mentioned in the error
; msg.

(defmacro syn::defevaluator (&whole x evfn evfn-lst fn-args-lst &key namedp)
  (cond
   ((not (and (symbolp evfn)
              (symbolp evfn-lst)
              (symbol-list-listp fn-args-lst)))
    `(er soft '(defevaluator . ,evfn)
	       "The form of a defevaluator event is (defevaluator evfn ~
          evfn-lst fn-args-lst), where evfn and evfn-lst are symbols ~
          and fn-args-lst is a true list of lists of symbols.  ~
          However, ~x0 does not have this form."
	       ',x))
   (t
    (syn::defevaluator-form evfn evfn-lst namedp fn-args-lst))))

#||
(defun syn::defevaluator-form (evfn evfn-lst fn-args-lst)
  (declare (xargs :mode :program))
  (let* ((clauses (evaluator-clauses evfn evfn-lst fn-args-lst))
         (fns-clauses (defevaluator-form/fns-clauses fn-args-lst))
         (defthms (defevaluator-form/defthms
                    evfn
                    evfn-lst
                    nil
                    (namedp-prefix evfn nil)
                    0
                    clauses)))
    `(encapsulate
      (((,evfn * *) => *)
       ((,evfn-lst * *) => *))
      (set-inhibit-warnings "theory")

      ,@(sublis
         (list (cons 'evfn evfn)
               (cons 'evfn-lst evfn-lst)
               (cons 'fns-clauses fns-clauses)
               (cons 'defthms defthms))
         '((local
            (mutual-recursion
             (defun evfn (x a)
               (declare (xargs :verify-guards nil
                               :measure (acl2-count x)
                               :well-founded-relation o<
			       :hints (("goal" :do-not '(preprocess) :in-theory (disable o< acl2-count)))
                               :mode :logic))
               (cond
                ((symbolp x) (and x (cdr (assoc-eq x a))))
                ((atom x) nil)
                ((eq (car x) 'quote) (car (cdr x)))
                ((consp (car x))
                 (evfn (car (cdr (cdr (car x))))
                       (pairlis$ (car (cdr (car x)))
                                 (evfn-lst (cdr x) a))))
                .
                fns-clauses))
             (defun evfn-lst (x-lst a)
               (declare (xargs :measure (acl2-count x-lst)
                               :well-founded-relation o<))
               (cond ((endp x-lst) nil)
                     (t (cons (evfn (car x-lst) a)
                              (evfn-lst (cdr x-lst) a)))))))
	   (local (in-theory *defevaluator-form-base-theory*))
	   (local (in-theory (enable evfn evfn-lst)))
           (local
            (defthm eval-list-kwote-lst
              (equal (evfn-lst (kwote-lst args) a)
                     (fix-true-list args))))
           . defthms)))))

(defmacro syn::defevaluator (&whole x evfn evfn-lst fn-args-lst)

  (cond
   ((not (and (symbolp evfn)
              (symbolp evfn-lst)
              (symbol-list-listp fn-args-lst)))
    `(er soft '(defevaluator . ,evfn)
	       "The form of a defevaluator event is (defevaluator evfn ~
          evfn-lst fn-args-lst), where evfn and evfn-lst are symbols ~
          and fn-args-lst is a true list of lists of symbols.  ~
          However, ~x0 does not have this form."
	       ',x))
   (t
    (syn::defevaluator-form evfn evfn-lst fn-args-lst))))
||#


(defthm o<-acl2-count-car
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CAR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-cdr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CDR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-cadr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-caar
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CAAR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-caddr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADDR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-caadr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CAaDR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-cadar
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADaR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-cadddr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADDDR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-caaddr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CAaDDR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-cadadr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADaDR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-caddar
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADDaR x))
	       (ACL2-COUNT x))))

(defthm o<-acl2-count-caddddr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADDDR (cdr x)))
	       (ACL2-COUNT x))))


(defthm o<-acl2-count-caadddr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CAaDDR (cdr x)))
	       (ACL2-COUNT x))))


(defthm o<-acl2-count-cadaddr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADaDR (cdr x)))
	       (ACL2-COUNT x))))


(defthm o<-acl2-count-caddadr
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADDaR (cdr x)))
	       (ACL2-COUNT x))))


(defthm o<-acl2-count-cadddar
  (IMPLIES (consp x)
	   (O< (ACL2-COUNT (CADDDR (car x)))
	       (ACL2-COUNT x))))
