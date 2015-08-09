; evalable-printing.lisp - Implements a "beginner-friendly" way of printing
; objects such that evaluating the printed result gives that same result.
;
; Nuances of the printing are controlled with the state global
; EVALABLE-PRINTING-ABSTRACTIONS, which should be a list containing some
; subset of (LIST LIST*-MULTIPLE LIST* CONS) in that order.  Each
; abstraction is tried in the order specified, falling back on quotation
; if none apply:
;   LIST - If a non-empty true list, use (LIST ...)
;   LIST*-MULTIPLE - If a cons whose cdr is a cons, use (LIST* ...)
;          maximally (such that last parameter is an atom).
;   LIST* - If a cons, use (LIST* ...) maximally.
;   CONS - If a cons, use (CONS ... ...).
;
; It only makes sense to specify them in the order given because, with
; the exception of LIST*-MULTIPLE, each subsumes all those preceding it.
;
; The function-like macro MAKE-EVALABLE constructs the modified object,
; which can be printed with a standard printing function.  (MAKE-EVALABLE
; needs access to STATE but does not modify it.)
;
; Beginning languages of DrScheme implement a printing scheme like this.
;
; Peter C. Dillinger, Northeastern University, 2008


(in-package "ACL2")

(program)
(set-state-ok t)


(defun quote-as-needed (expr)
  (declare (xargs :guard t))
  (if (or (consp expr)
          (and (symbolp expr)
               (not (booleanp expr))
               (not (keywordp expr))))
    (list 'quote expr)
    expr))

(defun quote-as-needed-list (expr-lst)
  (declare (xargs :guard (true-listp expr-lst)))
  (if (endp expr-lst)
    expr-lst
    (cons (quote-as-needed (car expr-lst))
          (quote-as-needed-list (cdr expr-lst)))))


(defun quote-as-needed-with-stobj (val stobj)
  (if stobj
    stobj
    (quote-as-needed val)))

(defun quote-as-needed-with-stobj-list (valx stobjs)
  (if (or (endp valx)
          (endp stobjs))
    nil
    (cons (quote-as-needed-with-stobj (car valx) (car stobjs))
          (quote-as-needed-with-stobj-list (cdr valx) (cdr stobjs)))))


(defconst *evalable-printing-abstractions*
  '(list list*-multiple list* cons))

(defconst *default-evalable-printing-abstractions*
  '(list list*-multiple cons))

;;; Modification by Matt K. for after ACL2 3.6.1 for early loading of compiled
;;; files, where the make-event expansion process cannot be assumed to take
;;; place (rather, we just load the expansion).

(defun get-evalable-printing-abstractions (state)
  (if (f-boundp-global 'evalable-printing-abstractions state)
      (f-get-global 'evalable-printing-abstractions state)
    *default-evalable-printing-abstractions*))

(defun lastcdr (x)
  (if (atom x)
    x
    (lastcdr (cdr x))))


(mutual-recursion
(defun make-evalable-how (val abstractions)
  (if (consp val)
    (cond ((and (member-eq 'list abstractions)
                (true-listp val))
           (cons 'list
                 (make-evalable-lst-how val abstractions)))
          ((or (and (member-eq 'list*-multiple abstractions)
                    (consp (cdr val)))
               (member-eq 'list* abstractions))
           (append (list 'list*)
                   (make-evalable-lst-how val abstractions)
                   (list (make-evalable-how (lastcdr val) abstractions))))
          ((member-eq 'cons abstractions)
           (list 'cons
                 (make-evalable-how (car val) abstractions)
                 (make-evalable-how (cdr val) abstractions)))
          (t
           (list 'quote val)))
    (quote-as-needed val)))

(defun make-evalable-lst-how (val-lst abstractions)
  (if (atom val-lst)
    nil
    (cons (make-evalable-how (car val-lst) abstractions)
          (make-evalable-lst-how (cdr val-lst) abstractions)))))

(defun make-evalable-with-stobj-how (val stobj abstractions)
  (if stobj
    stobj
    (make-evalable-how val abstractions)))

(defun make-evalable-with-stobj-list-how (valx stobjs abstractions)
  (if (or (endp valx)
          (endp stobjs))
    nil
    (cons (make-evalable-with-stobj-how (car valx) (car stobjs) abstractions)
          (make-evalable-with-stobj-list-how (cdr valx) (cdr stobjs) abstractions))))


(defmacro make-evalable (x)
  `(make-evalable-how ,x (get-evalable-printing-abstractions state)))

(defmacro make-evalable-with-stobjs (valx stobjs)
  `(make-evalable-with-stobj-list-how
    ,valx
    ,stobjs
    (get-evalable-printing-abstractions state)))
