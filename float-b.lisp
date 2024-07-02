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

; Here we continue the development in float-a.lisp, now that set-w has been
; defined during the boot-strap (by processing history-management.lisp first).

(defun install-df-basic-primitives (state)
  (declare (xargs :mode :program))
  (if (global-val 'boot-strap-pass-2 (w state)) ; then this was already done
      state
    (set-w 'extension
           (install-df-basic-primitives-1 *df-basic-primitives* (w state))
           state)))

#+acl2-loop-only
(pprogn (install-df-basic-primitives state)

; The invariant on command blocks, which is checked by function
; good-command-blocksp1 defined in books/system/pseudo-good-worldp.lisp,
; requires that every command block contain at least one event-landmark.  So we
; lay one down here by adding a harmless deflabel event.

        (deflabel df-basic-primitives-installed))

(defun to-df?-fn (x)

; We want to support expressions like (df* 1/4 x) or (df-sin *df-pi*), where
; there is a constant argument whose value is a dfp (i.e., a rational that is
; representable as a double-float), yet the operation expects a double-float.
; This utilitity applies to-df to numeric constants, since those cannot be of
; type :DF.  This optimization applies not only to numbers but also constant
; symbols, to allow an expression like (df-sin *df-pi*), since *df-pi* is a
; rational.

  (declare (xargs :guard t))
  (let ((x (cond ((and (consp x)
                       (consp (cdr x))
                       (null (cddr x))
                       (eq (car x) 'quote)
                       (acl2-numberp (cadr x)))
                  (cadr x))
                 (t x))))
    (cond ((acl2-numberp x)

; Translate will check that numeric arguments of a df primitive are 

           (cond ((dfp x)

; It might be reasonable to return the double-float (to-df x) when we are in
; raw Lisp.  However, we choose to avoid that special case after observing with
; disassemble that (to-df n) is inlined for a rational, n.

                  `(to-df ,x))
                 (t

; In this case we simply let translate complain about passing the wrong type of
; object.

                  x)))
          ((and (symbolp x)
                (legal-constantp1 x)
                (not (member-eq x '(t nil))))

; Comments in the previous case apply here.

           `(let ((c ,x))
              (assert$ (dfp c)
                       (to-df c))))
          (t x))))

(defun to-df?-args (lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        (t (cons (to-df?-fn (car lst))
                 (to-df?-args (cdr lst))))))

(defun defun-df-events (fn-name macro-name formals rest)
  (declare (xargs :guard (and (symbolp macro-name) ; can be nil
                              (symbolp fn-name))))
  (let ((dfp-thm-name (packn-pos (list 'dfp- fn-name) fn-name))
        (rationalp-thm-name (packn-pos (list 'rationalp- fn-name) fn-name)))
    `((defun ,fn-name ,formals
        ,@(and formals `((declare (type double-float ,@formals))))
        ,@rest)
      (defthm ,dfp-thm-name
        (dfp (,fn-name ,@formals)))
      (defthm ,rationalp-thm-name
        (rationalp (,fn-name ,@formals))
        :rule-classes :type-prescription)
      ,@(and macro-name
             `((defmacro ,macro-name ,formals
                 (cons ',fn-name (to-df?-args (list ,@formals))))
               ,(if (eq macro-name 'df-log)

; We don't support having df-log stand for both binary-df-log and unary-df--log
; when used in theory functions.

                    `(table untrans-table ',fn-name '(,macro-name))
                  `(add-macro-fn ,macro-name ,fn-name))
               (value-triple ',macro-name))))))

(defmacro defun-df (fn formals &rest rest)
  (let* ((fn-fn (packn-pos (list fn '-FN) fn))
         (events (defun-df-events fn-fn fn formals rest))
         (defun-ev (car events))
         (rest-evs (cdr events)))
    `(with-output
       :stack :push
       :off :all
       :on error
       (progn (with-output
                :stack :pop
                ,defun-ev)
              ,@rest-evs))))

; In the following comparison functions df<, df=, and df/=, we can simply call
; the usual arithmetic comparitors, since numeric comparisons are based on the
; mathematical value regardless of the type of the number (including rational
; vs. double-float).

(defun df<-fn (x y)
  (declare (type double-float x y))
  #+acl2-loop-only
  (< (from-df x) (from-df y))
  #-acl2-loop-only
  (< x y))
(defmacro df< (x y)
  `(df<-fn ,(to-df?-fn x) ,(to-df?-fn y)))
(add-macro-fn df< df<-fn)

(defun df=-fn (x y)
  (declare (type double-float x y))
  #+acl2-loop-only
  (= (from-df x) (from-df y))
  #-acl2-loop-only
  (= x y))
(defmacro df= (x y)
  `(df=-fn ,(to-df?-fn x) ,(to-df?-fn y)))
(add-macro-fn df= df=-fn)

(defun df/=-fn (x y)
  (declare (type double-float x y))
  #+acl2-loop-only
  (/= (from-df x) (from-df y))
  #-acl2-loop-only
  (/= x y))
(defmacro df/= (x y)
  `(df/=-fn ,(to-df?-fn x) ,(to-df?-fn y)))
(add-macro-fn df/= df/=-fn)

(defmacro df<= (x y)
  `(not (df< ,y ,x)))

(defmacro df>= (x y)
  `(not (df< ,x ,y)))

(defmacro df> (x y)
  `(df< ,y ,x))

(defun df0 ()
  (declare (xargs :guard t))
  (to-df 0))

(defun df1 ()
  (declare (xargs :guard t))
  (to-df 1))

(defun df-minus-1 ()
  (declare (xargs :guard t))
  (to-df -1))

(defun df-function-sigs (flg)

; This is a list of "signatures" -- in quotes because each entry is actually
; either (fn formals) or (fn formals guard), where guard is an untranslated
; guard.  In the former case, the guard is implicitly t.

; Support for arithmetic functions (+, -, *, /) is handled separately.

; Flg is non-nil if and only if these signatures are used for generating events
; for the partial-encapsulate that introduces the constrained-F function for
; each signature function F below.

; Each of these signature functions except df-pi has a macro version that
; applies to-df? to each argument.  We use the "-FN" suffix to distinguish
; the function from the macro except when there is already a "BINARY-" or
; "UNARY-" prefix to serve that purpose (and except for df-pi).

  (declare (xargs :guard t))
  `((df-expt-fn (x y)
                
; We cannot allow x to be negative, since te CL HyperSpec says that "expt is
; defined as b^x = e^x log b" (here b is our x and x is our y), and ACL2 does
; not support complex floats.  Here are a couple of relevant examples in CCL.

;   ? (expt -1 1/2)
;   #C(6.123234S-17 1.0S0)
;   ? (expt -2.0 3.0)
;   #C(-7.999999999999998 2.9391523179536467E-15)
;   ? 

; Also, we don't want the base and exponent to both be (df0), because the CL
; HyperSpec entry on expt says that "the consequences are undefined if
; base-number is zero when power-number is zero and not of type integer."  And
; of course 0^y is a non-starter when y is negative.


                (or (df< 0 x)
                    (and (df= 0 x) (df< 0 y))))
    (df-exp-fn (x))
    (df-sqrt-fn (x)
                (df<= 0 x))
    (binary-df-log (x y)
                   (and (df< 0 x) (df<= 0 y)))
    (unary-df-log (x)
                  (df< 0 x))
    (df-abs-fn (x))
    (df-sin-fn (x))
    (df-cos-fn (x))
    (df-tan-fn (x) 

; It seems possible that (tan x) could be undefined because (cos x) is 0.  But
; that might be rare; for example, in CCL (tan (acos 0.0D0)) =
; 1.633123935319537D+16.  Even if an error occurred, we can live with that,
; just as we can live with overflow and underflow errors.

               (not (df= (,(if flg
                               'constrained-df-cos-fn
                             'df-cos-fn)
                          x)
                         0)))
    (df-asin-fn (x)
                (df<= (df-abs-fn x) 1))
    (df-acos-fn (x)
                (df<= (df-abs-fn x) 1))
    (df-atan-fn (x))
    (df-sinh-fn (x))
    (df-cosh-fn (x))
    (df-tanh-fn (x) 
                (not (df= (,(if flg
                                'constrained-df-cosh-fn
                              'df-cosh-fn)
                           x)
                          0)))
    (df-asinh-fn (x))
    (df-acosh-fn (x)
                 (df<= 1 x))
    (df-atanh-fn (x)
                 (df< (df-abs x) 1))
    (df-pi ())))

(defconst *df-function-sigs-exec*
  (df-function-sigs nil))

(verify-termination-boot-strap substring-p) ; and guards
(verify-termination-boot-strap string-suffixp) ; and guards

(defun df-macro-name (fn)

; This utility creates a macro name corresponding to fn when fn ends in "-FN".
; For example, (df-macro-name 'df-sin-fn) evaluates to the symbol, df-sin.

; Thus, if fn is a or the form unary-xxx or binary-xxx, we return nil, as we
; handle those in another way.  We don't even create a macro corresponding to
; the zero-ary function, df-pi.

  (declare (type symbol fn))
  (let ((name (symbol-name fn)))
    (and (string-suffixp "-FN" name)
         (intern-in-package-of-symbol (subseq name 0 (- (length name) 3))
                                      fn))))

(defconst *df-primitives* ; See add-trip and compile-uncompiled-*1*-defuns.

; This constant is used in two ways: to exempt its function symbols from being
; given *1* function definitions in the usual way, hence they should have
; custom *1* function definitions; and to be added to *acl2-exports*, together
; with corresponding macros (when they exist; see df-macro-name).

; Note that the list below does not include the following built-in functions
; that operate on dfs.

; df<-fn
; df=-fn
; df/=-fn
; df-rationalize
; rize (based on df-rationalize but actually operates on rationals)

  (cons 'dfp
        (append-strip-cars *df-basic-primitives*
                           (strip-cars *df-function-sigs-exec*))))

(defun df-events-1 (sig flg)

; Sig is a signature, for example like the following (though it can be for a
; unary function and have additional :guard conjuncts).

; ((fn * *) => *
;  :formals (x y) :guard (and (dfp x) (dfp y)))

; Flg is t if we are generating these events for the partial-encapsulate that
; introduces the constrained- functions; otherwise flg is nil for the
; corresponding events about non-constrained macros and functions.

  (declare (xargs :guard (and (<= 2 (len sig))
                              (symbolp (car sig))
                              (symbol-listp (cadr sig)))))
  (let* ((name (car sig))
         (formals (cadr sig))
         (guard (if (consp (cddr sig)) (caddr sig) t))
         (constrained-name (packn (list 'constrained- name)))
         (name (if flg constrained-name name))
         (macro-name (and (null flg) (df-macro-name name)))
         (rest ; irrelevant if flg is true
          `((declare (xargs :guard ,guard))
            (to-df (non-exec (,constrained-name ,@formals)))))
         (events (defun-df-events name macro-name formals rest)))
    (if flg
        (cons `(local (defun ,name ,formals 0))
              (cdr events))
      events)))

(defun df-events (sigs flg)

; Flg is non-nil if and only we are generating events for constrained versions
; of the df operations.

  (declare (xargs :guard (and (symbol-alistp sigs)
                              (all->=-len sigs 2)
                              (symbol-list-listp (strip-cadrs sigs)))))
  (cond ((endp sigs) nil)
        (t (append (df-events-1 (car sigs) flg)
                   (df-events (cdr sigs) flg)))))

(defun prefix-sigs-with-constrained (sigs)
  (declare (xargs :guard (and (alistp sigs)
                              (symbol-alistp sigs)
                              (true-list-listp sigs))))
  (cond ((endp sigs) nil)
        (t (cons (let* ((sig (car sigs)) ; (fn formals &optional guard)
                        (fn (car sig))
                        (formals (cadr sig)))
                   (list (packn (list 'constrained- fn))
                         formals
                         t))
                 (prefix-sigs-with-constrained (cdr sigs))))))

(defmacro df-constrained-functions-intro ()
  (let ((sigs (df-function-sigs t)))
    `(encapsulate
       ()
; We do it this way (instead of putting (logic) inside the partial-encapsulate)
; to support redundancy in pass 2.
       (logic)
       (partial-encapsulate
        ,(prefix-sigs-with-constrained sigs)
        nil
        (set-ignore-ok t)             ; local to this partial-encapsulate
        (set-irrelevant-formals-ok t) ; local to this partial-encapsulate
        ,@(df-events sigs t)))))

(defun df-non-constrained-functions-events ()
  (declare (xargs :guard t))
  (df-events *df-function-sigs-exec* nil))

(defmacro df-non-constrained-functions-intro ()
  (cons 'progn (df-non-constrained-functions-events)))

(df-constrained-functions-intro)

(df-non-constrained-functions-intro)

(defun df-rationalize (x)

; Warning: it may be important to define the #-acl2-loop-only version of this
; function before rize is defined, since df-rationalize is inlined in
; float-a.lisp, so for example deferring the #-acl2-loop-only definition to a
; later file such as float-raw.lisp may cause problems for evaluating calls of
; rize.

  (declare (xargs :mode :logic)
           (type double-float x))
  #+acl2-loop-only
  (constrained-df-rationalize (from-df x))
  #-acl2-loop-only
  (the rational (rationalize x)))

(defthm rationalp-df-rationalize
   (rationalp (df-rationalize x))
   :rule-classes :type-prescription)

(defthm to-df-of-df-rationalize
; This theorem is justified by the CL HyperSpec:
; http://www.lispworks.com/documentation/HyperSpec/Body/f_ration.htm
  (implies (dfp x)
           (equal (to-df (df-rationalize x))
                  x)))

(in-theory (disable (:definition df-rationalize)))

(defun rize (x)

; This function is in the spirit of Common Lisp rationalize, except that it
; takes a rational rather than a double-float.

  (declare (type rational x))
  (df-rationalize (to-df x)))

(defthm to-dfp-of-rize
; This is a variant of to-df-of-df-rationalize
  (implies (dfp x)
           (equal (to-dfp (rize x))
                  x)))

(defthm stringp-df-string
   (stringp (df-string x))
   :rule-classes :type-prescription)

(in-theory (disable (:definition df-string)))

(defmacro df+ (&rest rst)
  (let ((rst (to-df?-args rst)))
    (if rst
        (if (cdr rst)
            (xxxjoin 'binary-df+ rst)
          (cons 'binary-df+ (cons '(df0) (cons (car rst) nil))))
      '(df0))))

(defmacro df- (x &optional (y 'nil yp))
  (cond (yp
         `(binary-df+ ,(to-df?-fn x)
                      (unary-df- ,(to-df?-fn y))))
        (t
         `(unary-df- ,(to-df?-fn x)))))

(defmacro df* (&rest rst)
  (let ((rst (to-df?-args rst)))
    (cond ((null rst) '(df1))
          ((null (cdr rst)) (list 'binary-df* '(df1) (car rst)))
          (t (xxxjoin 'binary-df* rst)))))

(defmacro df/ (x &optional (y 'nil yp))
  (cond (yp
         `(binary-df/ ,(to-df?-fn x)
                      ,(to-df?-fn y)))
        (t
         `(unary-df/ ,(to-df?-fn x)))))

(defmacro df-log (x &optional (y 'nil yp))
  (if yp
      `(binary-df-log ,(to-df?-fn x) ,(to-df?-fn y))
    `(unary-df-log ,(to-df?-fn x))))

(add-macro-fn df+ binary-df+ t)
(add-macro-fn df* binary-df* t)
(table untrans-table 'unary-df- '(df-))
(table untrans-table 'unary-df/ '(df/))
(table untrans-table 'binary-df/ '(df/))
(table untrans-table 'unary-df-log '(df-log))
(table untrans-table 'binary-df-log '(df-log))

(in-theory (set-difference-theories (current-theory :here)
                                    (strip-cars *df-function-sigs-exec*)))
