; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "kestrel/utilities/defmacroq" :dir :system)

(program)
(set-state-ok t)

(defun make-termination-theorem-subst (fns)
  (cond ((endp fns) nil)
        (t (cons (list (car fns)
                       (add-suffix (car fns) "$STUB"))
                 (make-termination-theorem-subst (cdr fns))))))

(defun make-termination-theorem-defstub-events (subst wrld)
  (cond ((endp subst) nil)
        (t (cons `(defstub ,(cadar subst)
                    ,(formals (caar subst) wrld)
                    t)
                 (make-termination-theorem-defstub-events (cdr subst) wrld)))))

(defun make-termination-theorem-fn (fn subst subst-p thm-name rule-classes
                                       verbose wrld ctx state)
  (let ((fn-nest (and (symbolp fn)
                      (getpropc fn 'recursivep nil wrld)))
        (thm-name (or thm-name (add-suffix fn "$TTHM"))))
    (cond
     ((null fn-nest)
      (er soft ctx
          "The first argument, ~x0, is not a recursively defined function ~
           symbol."
          fn))
     ((and subst-p
           (not (doublet-style-symbol-to-symbol-alistp subst)))
      (er soft ctx
          "The :subst argument, is not a list of pairs of the form (old-sym ~
           new-sym)"
          subst))
     ((and subst-p
           (not (subsetp-eq (strip-cars subst) fn-nest)))
      (cond
       ((null (cdr fn-nest))
        (er soft ctx
            "The :subst argument has key ~x0, which should be ~x1."
            (caar subst)
            fn))
       (t
        (er soft ctx
            "The :subst argument has~#0~[a key, ~&0, that is~/keys ~&0 that ~
             are not~] function symbol~#0~[~/s~] introduced in the same ~
             mutual-recursion as ~x0."
            (set-difference-eq (strip-cars subst) fn-nest)))))
     (t (let* ((subst (if subst-p
                          subst
                        (make-termination-theorem-subst fn-nest)))
               (tformula (sublis-fn-simple (pairlis$ (strip-cars subst)
                                                     (strip-cadrs subst))
                                           (termination-theorem fn wrld)))
               (formula (untranslate tformula t wrld))
               (thm `(defthm ,thm-name
                       ,formula
                       :hints (("Goal"
                                :use (:termination-theorem ,fn ,subst)
                                :in-theory (theory 'minimal-theory)))
                       :rule-classes ,rule-classes)))
          (value `(with-output
                    :off :all
                    :on error
                    :stack :push
                    (progn
                      ,@(make-termination-theorem-defstub-events subst wrld)
                      ,(if verbose `(with-output :stack :pop ,thm) thm)
                      (value-triple ',thm)))))))))

(defmacroq make-termination-theorem (fn &key
                                        (subst 'nil subst-p)
                                        thm-name rule-classes
                                        verbose show-only)
  `(make-event (er-let* ((event (make-termination-theorem-fn
                                 ,fn ,subst ,subst-p ,thm-name ,rule-classes
                                        ,verbose (w state)
                                        'make-termination-theorem state)))
                 (if ,show-only
                     (value `(value-triple ',event))
                   (value event)))))

; Example

(local (progn

(defun my-car (x)
  (car x))
(defun my-cdr (x)
  (cdr x))

(mutual-recursion
 (defun f1 (x)
   (if (consp x) (and (f1 (my-car x)) (f2 (my-cdr x))) x))
 (defun f2 (x)
   (if (consp x) (and (f2 (my-car x)) (f1 (my-cdr x))) x)))

(in-theory (disable my-car my-cdr))

(make-termination-theorem f1)

(mutual-recursion
 (defun g1 (x)
   (declare (xargs :hints
                   (("Goal" :use ((:functional-instance f1$tthm
                                                        (f1$stub g1)
                                                        (f2$stub g2)))))))
   (if (consp x) (and (g1 (my-car x)) (g2 (my-cdr x))) x))
 (defun g2 (x)
   (if (consp x) (and (g2 (my-car x)) (g1 (my-cdr x))) x)))

))
