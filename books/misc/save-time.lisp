; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann, January, 2012
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Thanks to Sarah Weissman for the idea of this book and helpful discussions.

;;; Table of contents
;;; 1. The simplest way to use the save-time utility
;;; 2. How to use this utility to save many times and produce a report
;;; 3. How to save times when certifying a book

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 0. Introduction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; While the ACL2 utility time$ provides a way to time evaluation of a form, it
; doesn't provide a way to get your hands within ACL2 on the time that taken to
; do that evaluation.  The utility save-time puts that time into the ACL2
; state, where it can be retrieved with the macro (last-time) or viewed with
; the macro (print-last-time).  Moreover, you can save a sequence of timings,
; for example for several forms in a book, and display all the times at the end
; using the macro (saved-times).

; Please feel free to extend this book to have additional capabilities that you
; need, and to ask Matt Kaufmann (kaufmann@cs.utexas.edu) for assistance if you
; get stuck when trying to do so.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 1. Saving the time for a single form
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (save-time <form>)
; THEN:
; (print-last-time) ; formatted output of runtime elapsed
;   or
; (last-time) ; runtime elapsed as a rational number

; Example:
;   ACL2 !>(save-time (mini-proveall))
;   [.. output omitted ..]
;   ACL2 !>(print-last-time)
;   0.48 seconds
;   ACL2 !>(last-time)
;   480643/1000000
;   ACL2 !>

; If you want to call save-time in an event context, such as within a book or
; as in (progn ... (save-time ...) ...), use keyword argument :eventp t, for
; example as follows.

; (progn ... (save-time <form> :eventp t) ...)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 2. How to use this utility to save many times and produce a report
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (save-time <form>)
; or
; (save-time <form> :name <name>)
; or add :eventp t if you want the save-time form to be an event:
; (save-time <event> :eventp t)
; or
; (save-time <event> :name <name> :eventp t)

; Normally you don't need to supply the :name argument, which by default is the
; cadr of a form except in the case of (local <form>) in which case it is
; (recursively) the name of <form>.  But there are times where two forms have
; the same name, as with (defun foo ...) and (verify-guards foo ...).  And
; there may be times when (cadr form) isn't suitable, as is typically an issue
; for a make-event call.  In any such cases, supply :name to be a symbol.

; Ultimately, the times will be printed using the macro call (saved-times).

; Example:

; ACL2 !>(with-output
;         :off :all
;         (progn
;           (save-time (defthm thm1
;                        (equal (revappend (revappend x y) z)
;                               (revappend y (append x z))))
;                      :eventp t)
;           (save-time (local (include-book "arithmetic/top-with-meta" :dir :system))
;                      :eventp t)
;           (save-time (defthm thm2
;                        (equal (nth n (append x y))
;                               (let ((n (nfix n)))
;                                 (if (< n (len x))
;                                     (nth n x)
;                                   (nth (- n (len x)) y))))
;                        :hints (("Goal" :induct (nth n x))))
;                      :eventp t)))
;  :SAVE-TIME-STOPPED
; ACL2 !>(saved-times)
;
; arithmetic/top-with-meta: 0.15
; THM2: 0.02
; THM1: 0.00
;  :TIMES-PRINTED
; ACL2 !>(saved-times :raw t)
;
; arithmetic/top-with-meta: 957/6250
; THM2: 5027/250000
; THM1: 2449/500000
;  :TIMES-PRINTED
; ACL2 !>

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 3. How to save times when certifying a book
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; If you want to see the times for some events in a book, here's a suggestion.

; Wrap each form of interest in (save-time form :eventp t), supplying a :name
; argument when necessary (as explained above).  Then later in the book (say,
; at the end), put (saved-times) or (saved-times :raw t).  The output from
; certify-book will include a report on saved times, such as shown above, where
; the saved-times form is evaluated.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defmacro save-time-init ()
  '(make-event
    (pprogn (f-put-global 'save-time-alist nil state)
            (f-put-global 'save-time-temp-stack nil state)
            (value '(value-triple nil)))
    :check-expansion t))

(save-time-init)

(defmacro save-time-start (eventp)
  (let ((form '(mv-let (start-time state)
                       (read-run-time state)
                       (f-put-global
                        'save-time-temp-stack
                        (cons start-time
                              (cond
                               ((eql 0 (f-get-global 'make-event-debug-depth state))
                                nil)
                               (t (f-get-global 'save-time-temp-stack
                                                state))))
                        state))))
    (cond (eventp
           `(local
             (make-event
              (pprogn
               ,form
               (value '(value-triple :SAVE-TIME-STARTED
                                     :on-skip-proofs t))))))
          (t `(pprogn ,form (value nil))))))

(defmacro save-time-stop (name eventp)
  (let* ((last-form
          (cond (eventp '(value '(value-triple
                                  :SAVE-TIME-STOPPED
                                  :on-skip-proofs t)))
                (t `(value ',name))))
         (form
          `(let ((stack (f-get-global 'save-time-temp-stack state)))
             (mv-let (stop-time state)
                     (read-run-time state)
                     (pprogn (f-put-global
                              'save-time-alist
                              (put-assoc ',name
                                         (- stop-time (car stack))
                                         (f-get-global 'save-time-alist
                                                       state)
                                         :test 'eq)
                              state)
                             (f-put-global 'save-time-temp-stack
                                           (cdr stack)
                                           state)
                             ,last-form)))))
    (cond (eventp
           `(local (make-event ,form)))
          (t form))))

(defun save-time-name (form)
  (let ((er-string "The form ~x0  is not of the form (_ s ...) where s is a ~
                    symbol.  Supply a :NAME argument for save-time."))
    (case-match form
      (('local f)
       (save-time-name f))
      ((& name . &)
       (cond ((atom name) name)
             (t (er hard 'save-time er-string form))))
      (& nil))))

(defmacro save-time (form &key name eventp)
  (let ((prog (if eventp 'progn 'er-progn)))
    `(,prog (save-time-start ,eventp)
            ,form
            (save-time-stop ,(or name (save-time-name form))
                            ,eventp))))

(defun merge-cdr-> (l1 l2)
  (declare (xargs :mode :program))
; from ACL2 sources (but conditional there on #+acl2-rewrite-meter)
  (cond ((null l1) l2)
        ((null l2) l1)
        ((> (cdr (car l1)) (cdr (car l2)))
         (cons (car l1) (merge-cdr-> (cdr l1) l2)))
        (t (cons (car l2) (merge-cdr-> l1 (cdr l2))))))

(defun merge-sort-cdr-> (l)
; from ACL2 sources (but conditional there on #+acl2-rewrite-meter)
  (declare (xargs :mode :program))
  (cond ((null (cdr l)) l)
        (t (merge-cdr-> (merge-sort-cdr-> (evens l))
                        (merge-sort-cdr-> (odds l))))))

(defun print-saved-times-alist (raw alist ch state)
  (declare (xargs :mode :program :stobjs state))
  (cond ((endp alist) (newline ch state))
        (t (pprogn (newline ch state)
                   (princ$ (caar alist) ch state)
                   (princ$ ": " ch state)
                   (if raw
                       (princ$ (cdar alist) ch state)
                     (print-rational-as-decimal (cdar alist) ch state))
                   (print-saved-times-alist raw (cdr alist) ch state)))))

(defmacro saved-times (&key (sort ':times) channel raw)
  (let ((channel (or channel '*standard-co*)))
    `(with-output
      :off summary
      (make-event
       (let ((alist (f-get-global 'save-time-alist state))
             (sort ,sort))
         (pprogn (print-saved-times-alist
                  ,raw
                  (cond ((eq sort :names) (merge-sort-lexorder alist))
                        ((eq sort :times) (merge-sort-cdr-> alist))
                        (t alist))
                  ,channel
                  state)
                 (value (list 'value-triple :times-printed))))))))

(defmacro last-time ()
  `(let ((alist (f-get-global 'save-time-alist state)))
     (cond (alist (cdar alist))
           (t nil))))

(defmacro print-last-time ()
  `(let ((alist (f-get-global 'save-time-alist state)))
     (cond (alist
            (pprogn (print-rational-as-decimal (cdar alist)
                                               (standard-co state)
                                               state)
                    (princ$ " seconds" (standard-co state) state)
                    (newline (standard-co state) state)
                    (value :invisible)))
           (t (er soft 'print-last-time
                  "There is no last-time to print!  Use SAVE-TIME first.")))))

