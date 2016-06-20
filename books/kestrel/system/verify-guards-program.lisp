; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; To do:

; - Document verify-guards-program with xdoc.

; - Control the output, perhaps simply by turning it off unless a :verbose
;   option is supplied.  Notice for example the error message currently
;   produced for f5p in the example (verify-guards-program f6p) below.

; - For each system utilities used below, either document it in :doc
;   system-utilities or replace it below with a corresponding documented system
;   utility.

; - Perhaps store functions in a table when they are "guard-verified" in this
;   sense, and insist that all supporters (ancestors) are in that table before
;   applying verify-guards-program to a given function symbol.

; - Consider causing an error if the argument to verify-guards-program is
;   already a guard-verified function symbol, and maybe even if it's already in
;   :logic mode (since then perhaps verify-guards would be more appropriate).

; - Consider adding an option that proves both termination and guards for the
;   given function, rather than skipping the termination proof.

; - Consider including the book misc/eval.lisp and use must-fail and perhaps
;   must-succeed to incorporate the tests at the end, below.  Perhaps the
;   successes could simply be local encapsulates.

(program)

(defun verify-termination-form (f wrld)
  (cond ((ffnnamep f (body f nil wrld))

; Initially, the test above was (getpropc f 'recursivep nil wrld).  But that's
; only a suitable test if f is in :logic mode.  The point here is that for
; recursive functions, ACL2 might not be able to guess a measure when no
; measure is supplied, so the first verify-termination form below might fail;
; see f5p below for an example.  Our solution to that problem is simply to try
; again in that case, supplying an explicit measure arbitrarily based on the
; first formal.  (If the formals are nil this might or might not work, but the
; formals are very unlikely to be nil for a recursively defined function.)

         `(make-event
           '(:or (skip-proofs
                  (verify-termination ,f
                    (declare (xargs :verify-guards nil))))
                 (skip-proofs
                  (verify-termination ,f
                    (declare (xargs :measure
                                    (:? ,@(formals f wrld))
                                    :verify-guards nil)))))))
        (t `(skip-proofs (verify-termination ,f
                           (declare (xargs :verify-guards nil)))))))

(defun verify-guards-program-forms-1 (fn-list fn wrld acc)

; We accumulate into acc a pair (num . form) for each function g in fn-list,
; where num is the absolute event number of g and form is the form we want to
; evaluate for g.  Finally we sort by num and return the sorted list of such
; forms.

  (cond ((endp fn-list)
         (strip-cdrs (merge-sort-car-< acc)))
        (t (verify-guards-program-forms-1
            (cdr fn-list) fn wrld
            (let* ((g (car fn-list))
                   (class (getpropc g 'symbol-class nil wrld)))
              (cond
               ((eq class :common-lisp-compliant) acc)
               (t (cons
                   (let ((num (getpropc g 'absolute-event-number nil wrld))
                         (form (cond ((eq class :ideal)
                                      `(verify-guards ,g))
                                     (t ; (eq class :program)
                                      `(progn
                                         ,(verify-termination-form g wrld)
                                         (verify-guards ,g))))))
                     (cons num
                           (if (eq fn g) form `(skip-proofs ,form))))
                   acc))))))))

(defun verify-guards-program-forms (fn wrld)
  (cond ((not (and (symbolp fn)
                   (function-symbolp fn wrld)))
         `((value-triple (er hard 'verify-guards-program
                             "Not a function symbol: ~x0"
                             ',fn))))
        (t (let* ((ancs (instantiable-ancestors (list fn) wrld nil)))
             (verify-guards-program-forms-1 ancs fn wrld nil)))))

(defmacro verify-guards-program (fn)
  `(make-event (mv-let (erp val state)
                 (ld (cons '(logic)
                           (verify-guards-program-forms ',fn (w state)))
                     :ld-error-action :error)
                 (declare (ignore val))
                 (value (list 'value-triple
                              (if erp :FAILED :SUCCESS))))))

; Examples:
#||

(logic)

(progn
  (defun f1p (x) (declare (xargs :mode :program)) x)
  (defun f2p (x)
    (declare (xargs :mode :program))
    (if (consp x) (f2p (cdr x)) x))
  (defun f3 (x) x)
  (defun f4p (x)
    (declare (xargs :mode :program))
    (list (f1p x) (f2p x) (f3 x)))
  (verify-guards-program f4p))

; No measure guessed:
(progn
  (defun f5p (x y)
    (declare (xargs :mode :program))
    (if (consp x)
        (f5p (cdr x) y)
      (if (consp y)
          (f5p x (cdr y))
        (list x y))))
  (defun f6p (x y)
    (declare (xargs :mode :program))
    (list (f4p x) (f5p x y)))
  (verify-guards-program f6p))

; Fails
(defun f7p (x)
  (declare (xargs :mode :program))
  (car (f1p x)))
(verify-guards-program f7p)

; Fails (tests that verify-termination doesn't skip-proofs in guard
; verification).
(defun f8p (x)
  (declare (xargs :mode :program :guard (not (acl2-numberp x))))
  (car (f1p x)))
(verify-guards-program f8p)

; Succeeds
(defun f9p (x)
  (declare (xargs :mode :program :guard (consp x)))
  (car (f1p x)))
(verify-guards-program f9p)

; Fails
(verify-guards-program f0)

||#
