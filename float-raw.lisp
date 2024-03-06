; ACL2 Version 8.5 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2024, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

(in-package "ACL2")

; The Common Lisp HyperSpec
; (http://www.lispworks.com/documentation/HyperSpec/Body/12_aaaa.htm), Section
; 12.1.1.1.1 "Examples of Associativity and Commutativity in Numeric
; Operations", makes it clear that nothing can be deduced about the order of
; operations.  So we convert all operations with more than two arguments to
; right-associated binary operations; for example, (df+ x y z) is treated
; identically to (df+ x (df+ y z)).

; For ACL2, transcendental functions traffic completely in double-floatas.  For
; example, if x is of double-float type, (sqrt x) is also of double-float type
; even if x and its square root both have rational mathemmatical values.  See
; also the CL HyperSpec Section 12.1.4.4.  Of course, we need guards checked in
; some cases before calling such functions.  For example, if x is negative then
; we can (or must?) get a complex float for (expt x y) when y is not an
; integer; but ACL2 doesn't recognize complex floats.

(defmacro df-signal? (form op)

; Form should return a single numeric value in ACL2.  We ensure that if there
; is no error then the result is truly a floating-point number that represents
; a rational number -- not an infinity or NaN.  Actually we don't need to worry
; about NaN in guard-verified code; it's simple to include that test in Allegro
; CL with a documented function (rather than just testing against
; #.*infinity-double* and #.*negative-infinity-double*), so we do so, but we
; don't bother testing for Nan in LispWorks.

; We return form unchanged in other than Allegro CL and LispWorks, because we
; already know that an error is signalled on overflow for other Lisps that host
; ACL2; see break-on-overflow-and-nan.

  #-(or allegro lispworks)
  (declare (ignore op))
  #-(or allegro lispworks)
  form
  #+allegro
  `(let ((result ,form))
     (when (excl:exceptional-floating-point-number-p result)
       (error "Floating-point exception for a call of ~s"
              ',op))
     result)
  #+lispworks
  `(let ((result ,form))
     (when (or (= result +1D++0) (= result -1D++0))
       (error "Floating-point overflow for a call of ~s"
              ',op))
     result))

(defmacro defun-df-binary (name op)

; We can perhaps avoid calling df-signal? in cases where overflow is
; impossible, but we don't; see defun-df-unary.

  `(progn
     (defun ,name (x y)
       (declare (type double-float x y))
       (the double-float
            (df-signal? (,op (the double-float x)
                             (the double-float y))
                        ,op)))))

(defmacro defun-df-unary (name op)

; We can perhaps avoid calling df-signal? in cases where overflow is
; impossible, e.g., if op is sin.  But since df-signal? is needed on most df
; operations, so we already likely have slowdown from df-signal? in LispWorks
; and Allegro CL, we keep things simple and apply df-signal? unconditionally.
; That could change if there are complaints.

  `(progn
     (defun ,name (x)
       (declare (type double-float x))
       (the double-float
            (df-signal? (,op (the double-float x))
                        ,op)))))

(defun-df-binary binary-df+ +)
(defun-df-binary binary-df* *)
(defun-df-binary binary-df/ /)
(defun-df-binary binary-df-log log)
(defun-df-binary df-expt-fn expt)

(defun-df-unary unary-df- -)
(defun-df-unary unary-df/ /)
(defun-df-unary df-exp-fn exp)
(defun-df-unary df-sqrt-fn sqrt)
(defun-df-unary unary-df-log log)
(defun-df-unary df-abs-fn abs)
(defun-df-unary df-sin-fn sin)
(defun-df-unary df-cos-fn cos)
(defun-df-unary df-tan-fn tan)
(defun-df-unary df-asin-fn asin)
(defun-df-unary df-acos-fn acos)
(defun-df-unary df-atan-fn atan)
(defun-df-unary df-sinh-fn sinh)
(defun-df-unary df-cosh-fn cosh)
(defun-df-unary df-tanh-fn tanh)
(defun-df-unary df-asinh-fn asinh)
(defun-df-unary df-acosh-fn acosh)
(defun-df-unary df-atanh-fn atanh)

(defun df-pi ()
  pi)

(defun df-string (x)
  (the string (cond ((typep x 'double-float)

; We make some effort to make the result independent of what is printed by the
; host Lisp.  Some lisps use "e" for the exponent while others use "E", and
; some use the "+" sign in the exponent but others do not.  We choose "E+"
; (like CCL) but it would be fine to use "e" and/or to omit the "+".

                     (let* ((s (princ-to-string x))
                            (p1 (position #\E s))
                            (p2 (and (not p1) ; optimization
                                     (position #\e s)))
                            (p (or p1 p2)))
                       (cond
                        ((and p
                              (not (member (char s (1+ p))
                                           '(#\+ #\-))))
                         (cond (p1
                                (concatenate 'string
                                             (subseq s 0 (1+ p1))
                                             "+"
                                             (subseq s (1+ p1) (length s))))
                               (t ; p2
                                (concatenate 'string
                                             (subseq s 0 p2)
                                             "E+"
                                             (subseq s (1+ p2) (length s))))))
                        (p2 (concatenate 'string
                                         (subseq s 0 p2)
                                         "E"
                                         (subseq s (1+ p2) (length s))))
                        (t s))))
                    (t (error "~s called on non-df value, ~s"
                              'df-string
                              x)
                       ""))))

; Now we define *1* functions.  They always return ordinary ACL2 objects, never
; floats.  The idea is that in *1* evaluation we only encounter floats at the
; top level.  Of course, printing in the top-level loop is expected to write
; out floats based on the stobjs-out, just as stobjs are printed using the
; stobjs-out.  (Note that binding *read-default-float-format* to 'double-float
; will cause the exponent to be E rather than D, so that the result can be read
; back in.)

(defun make-df (x)

; If there is a double-float corresponding to x, return it; else return nil.
; Note that although we expect that *1* functions are normally not handed
; dfs, an exception is when ec-call is invoked from raw Lisp.

  (cond ((typep x 'double-float) x) ; See note above about ec-call.
        ((rationalp x)
         (let ((xf (to-df x)))
           (and (= xf x)
                xf)))
        (t nil)))

(defmacro defun-df-*1*-unary (fn &rest more-guard-conjuncts)
  `(defun-*1* ,fn (x)
     (the rational
          (let ((xf (make-df x)))
            (cond ((and xf
; If there are more conjuncts, apply each to the double-float corresponding to
; x, for efficiency.
                        ,@(and more-guard-conjuncts
                               `((let ((x xf))
                                   ,@more-guard-conjuncts))))
                   (rational (,fn xf)))
                  (t (gv ,fn (x)
                         ,(cond
                           ((eq fn 'unary-df-)
                            `(df-round (funcall ',(*1*-symbol 'unary--) x)))
                           ((eq fn 'unary-df/)
                            `(df-round (funcall ',(*1*-symbol 'unary-/) x)))

; If there is a guard violation during a proof or when guard-checking is off,
; the constrained function will be called, which will have the usual effect of
; calling a constrained function, and that's entirely appropriate here.

                           (t `(,(packn (list 'constrained- fn)) x))))))))))

(defmacro defun-df-*1*-binary (fn &rest more-guard-conjuncts)
  `(defun-*1* ,fn (x y)
     (the rational
          (let ((xf (make-df x))
                (yf (make-df y)))
            (declare (type (or double-float null) xf yf))
            (cond ((and xf yf
                        ,@(and more-guard-conjuncts

; The raw Lisp versions of the conjuncts expect dfs, but x and y are probably
; rational.  So we replace x and y by numerically equal values of double-float
; type.

                               `((let ((x xf)
                                       (y yf))
                                   (declare (ignorable x y))
                                   ,@more-guard-conjuncts))))
                   (rational (,fn xf yf)))
                  (t (gv ,fn (x y)
                         ,(cond
                           ((eq fn 'binary-df+)
                            `(df-round (funcall ',(*1*-symbol 'binary-+) x y)))
                           ((eq fn 'binary-df*)
                            `(df-round (funcall ',(*1*-symbol 'binary-*) x y)))
                           ((eq fn 'binary-df/)
                            `(df-round
                              (funcall ',(*1*-symbol 'binary-*)
                                       x
                                       (funcall ',(*1*-symbol 'unary-/)
                                                y))))
                           (t

; If there is a guard violation during a proof or when guard-checking is off,
; the constrained function will be called, which will have the usual effect of
; calling a constrained function, and that's entirely appropriate here.

                            `(,(packn (list 'constrained- fn)) x y))))))))))

(defun-*1* from-df (x)
  (cond ((typep x 'double-float) ; impossible?
         (rational x))
        ((dfp x) x)
        (t (gv from-df (x)
; Logically, (from-df x) = x.  We don't want (from-df x) here because that
; would probably cause a raw Lisp error if x is not a number.
               x))))

(defun-*1* dfp (x)
  (dfp x))

(defconstant rational-pi
  (rational pi))

(defun-*1* df-pi ()
  rational-pi)

(defun-*1* to-df (x)
  (rational (cond ((typep x 'double-float)
                   (rational x))
                  ((rationalp x)
                   (rational (to-df x)))
                  (t (gv to-df (x)
                         (constrained-to-df x))))))

(defun-*1* df-string (x)
  (cond ((typep x 'double-float)
         (df-string x))
        ((rationalp x)
         (df-string (to-df x)))
        (t (gv df-string (x)
               (constrained-df-string x)))))

(defmacro defun-df-*1*-from-function-sigs ()
  (cons
   'progn
   (loop with tmp
         for tuple in *df-function-sigs-exec*
         as fn = (car tuple)
         as args = (cadr tuple)
         when (setq tmp (cond ((null args) ; df-pi
                               nil)
                              ((null (cdr args))
                               `(defun-df-*1*-unary ,fn
                                  ,@(cddr tuple)))
                              ((null (cddr args))
                               `(defun-df-*1*-binary ,fn
                                  ,@(cddr tuple)))
                              (t (error "Unexpected: ~s has ~s arguments, ~
                                        which is more than 2."
                                        fn (length args)))))
         collect tmp)))

(defun-df-*1*-from-function-sigs)

(defun-df-*1*-unary unary-df-)
(defun-df-*1*-unary unary-df/)
(defun-df-*1*-unary df-rationalize)

(defun-df-*1*-binary binary-df+)
(defun-df-*1*-binary binary-df*)
(defun-df-*1*-binary binary-df/ (not (= y 0)))
