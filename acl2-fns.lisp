; ACL2 Version 8.4 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Regents of the University of Texas

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

(proclaim-optimize)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            PRELIMINARIES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro qfuncall (fn &rest args)

; Avoid noise in CCL about undefined functions, not avoided by funcall alone.
; But this doesn't help in ANSI GCL or CMU CL 19e on Linux, and even has broken
; on CMU CL 18d on Solaris, so we just punt on this trick for those Lisps.

  (if (not (symbolp fn))
      (error "~s requires a symbol, not ~s" 'qfuncall fn)
    #+(and cltl2 (not cmu) (not gcl))
    `(let () (declare (ftype function ,fn)) (,fn ,@args))
    #-(and cltl2 (not cmu) (not gcl))
    `(funcall ',fn ,@args)))

(defmacro defun-one-output (&rest args)

; Use this for raw Lisp functions that are known to return a single value in
; raw Lisp, since make-defun-declare-form uses that assumption to make an
; appropriate declaration.

  (cons 'defun args))

; The following alist associates package names with Common Lisp packages, and
; is used in function find-package-fast, which is used by princ$ in place of
; find-package in order to save perhaps 15% of the print time.
(defparameter *package-alist* nil)
(defparameter *find-package-cache* nil)
(defun-one-output find-package-fast (string)
    (if (equal string (car *find-package-cache*))
        (cdr *find-package-cache*)
      (let ((pair (assoc string *package-alist* :test 'equal)))
        (cond (pair (setq *find-package-cache* pair) (cdr pair))
              (t (let ((pkg (find-package string)))
                   (push (cons string pkg) *package-alist*)
                   pkg))))))

(defvar *global-symbol-key* (make-symbol "*GLOBAL-SYMBOL-KEY*"))

(defun global-symbol (x)
  (or (get x *global-symbol-key*)
      (setf (get x *global-symbol-key*)
            (intern (symbol-name x)
                    (find-package-fast
                     (concatenate 'string
                                  *global-package-prefix*
                                  (symbol-package-name x)))))))

(defmacro live-state-p (x)
  (list 'eq x '*the-live-state*))

#-acl2-loop-only
(defun get-global (x state-state)

; Keep this in sync with the #+acl2-loop-only definition of get-global (which
; doesn't use qfuncall).

  (cond ((live-state-p state-state)
         (return-from get-global
                      (symbol-value (the symbol (global-symbol x))))))
  (cdr (assoc x (qfuncall global-table state-state))))

(defmacro f-get-global (x st)
  (cond ((and (consp x)
              (eq 'quote (car x))
              (symbolp (cadr x))
              (null (cddr x)))

; The cmulisp compiler complains about unreachable code every (perhaps) time
; that f-get-global is called in which st is *the-live-state*.  The following
; optimization is included primarily in order to eliminate those warnings;
; the extra efficiency is pretty minor, though a nice side effect.

         (if (eq st '*the-live-state*)
             `(let ()
                (declare (special ,(global-symbol (cadr x))))
                ,(global-symbol (cadr x)))
           (let ((s (gensym)))
             `(let ((,s ,st))
                (declare (special ,(global-symbol (cadr x))))
                (cond ((live-state-p ,s)
                       ,(global-symbol (cadr x)))
                      (t (get-global ,x ,s)))))))
        (t `(get-global ,x ,st))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            SUPPORT FOR NON-STANDARD ANALYSIS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Amazingly, some lisps do not have a definition for realp.  In those
; implementations (apparently including at least one early version of GCL), we
; will use rationalp as a poor substitute which however suffices for ACL2
; objects.

#+:non-standard-analysis
(defun acl2-realp (x)
  (rationalp x))

#+(and :non-standard-analysis CLTL2)
(if (not (fboundp 'common-lisp::realp))
    (setf (symbol-function 'common-lisp::realp) (symbol-function 'acl2-realp)))

#+(and :non-standard-analysis (not CLTL2))
(if (not (fboundp 'lisp::realp))
    (setf (symbol-function 'lisp::realp) (symbol-function 'acl2-realp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                         GCL VERSION QUERIES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+gcl
(defun gcl-version-> (major minor extra &optional weak)

; When true, this guarantees that the current GCL version is greater than
; major.minor.extra (or if weak is non-nil, than greater than or equal to).
; The converse holds for versions of GCL past perhaps 2.0.

  (and (boundp 'si::*gcl-major-version*)
       (integerp si::*gcl-major-version*)
       (if (= si::*gcl-major-version* major)
           (and (boundp 'si::*gcl-minor-version*)
                (integerp si::*gcl-minor-version*)
                (if (= si::*gcl-minor-version* minor)
                    (and (boundp 'si::*gcl-extra-version*)
                         (integerp si::*gcl-extra-version*)
                         (if weak
                             (>= si::*gcl-extra-version* extra)
                           (> si::*gcl-extra-version* extra)))
                  (if weak
                      (>= si::*gcl-minor-version* minor)
                    (> si::*gcl-minor-version* minor))))
         (if weak
             (>= si::*gcl-major-version* major)
           (> si::*gcl-major-version* major)))))

#+gcl
(defun gcl-version->= (major minor extra)
  (gcl-version-> major minor extra t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            PROCLAIMING
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Essay on Proclaiming

; The variable acl2::*do-proclaims* determines whether or not we proclaim ACL2
; function types before compiling them.  The intent of proclaiming is to
; improve performance, though we once observed proclaiming to have had the
; opposite effect for some combination of ACL2 and Allegro CL; see a comment in
; proclaim-file.  It might be worthwhile to revisit, from time to time,
; proclaiming in more Lisps, especially those used heavily in the community.

; During the boot-strap we avoid any activity related to proclaiming types
; except, perhaps, by generating or loading file acl2-proclaims.lisp.  At one
; time we did some proclaiming on a file-by-file basis, but this approach
; requires a lot of care to be done right.  For example with *do-proclaims*
; true, compile-acl2 had by default used a file-by-file load/proclaim/compile
; process, while load-acl2 had proclaimed all files after loading the compiled
; files.  We believe that this process allowed load-acl2 to come up with more
; specific function types during load-acl2 than had been used by compile-acl2
; We may have this change in types lead to buggy behavior.

; So in order to proclaim during the boot-strap, we use steps as shown below.
; First, here is the general process, which is currently unused.  But we could
; try it for any Lisp other than GCL; see below for what we do in GCL.  We note
; that GNUmakefile orchestrates both versions of these steps for "make".

; --- COMPILE: ---
; (1) In a fresh Lisp, call compile-acl2 without any proclaiming.
; --- OPTIONALLY PROCLAIM: ---
; (2) In a fresh Lisp, call generate-acl2-proclaims, which does these steps if
;     *do-proclaims* is true (currently, GCL only), and otherwise is a no-op.
;     (a) load-acl2;
;     (b) initialize-acl2;
;     (c) proclaim-files, to write out file "acl2-proclaims.lisp".
; --- OPTIONALLY RECOMPILE: ---
; (3) In a fresh Lisp, if *do-proclaims* is true (also see (2) above), load the
;     generated file "acl2-proclaims.lisp" and then recompile.
; --- SAVE EXECUTABLE: ---
; (4) In a fresh Lisp, call save-acl2, which does these steps:
;     (a) load "acl2-proclaims.lisp" if *do-proclaims* is true;
;     (b) load-acl2;
;     (c) initialize-acl2;
;     (d) save an executable.

; In GCL, we modify this process to utilize GCL's own ability to proclaim
; function types.  Note that this process doesn't proclaim types for defconst
; forms; from a Lisp perspective, that wouldn't make sense, since defconst
; symbols are variables, not constants.

; --- COMPILE: ---
; (1) In a fresh Lisp, call compile-acl2 without any proclaiming, as follows.
;     (compiler::emit-fn t)
;     (acl2::compile-acl2)
;     (compiler::make-all-proclaims "*.fn")
; --- OPTIONALLY PROCLAIM: ---
; (2) In a fresh Lisp, call generate-acl2-proclaims, which does only the following
;     if *do-proclaims* is true, and otherwise is a no-op.
;     Rename sys-proclaim.lisp to acl2-proclaims.lisp.
; --- OPTIONALLY RECOMPILE: ---
; (3) In a fresh Lisp, if *do-proclaims* is true (also see (2) above), load the
;     generated file "acl2-proclaims.lisp" and then recompile.
; --- SAVE EXECUTABLE: ---
; (4) In a fresh Lisp, call save-acl2, which does these steps:
;     (a) load "acl2-proclaims.lisp" if *do-proclaims* is true;
;     (b) load-acl2;
;     (c) initialize-acl2;
;     (d) save an executable.

; At one time we proclaimed for CCL, but one profiling run of a
; compute-intensive include-book form showed that this was costing us some 10%
; of the time.  After checking with Gary Byers we decided that there was little
; if any benefit in CCL for proclaiming functions, so we no longer do it.
; Perhaps we should reconsider some time.  See also comments below in
; *do-proclaims*.

; We considered adding &OPTIONAL to the end of every VALUES form (see comments
; below), based on output (since forgotten) from SBCL.  But GCL has issued
; several dozen warnings during the build when this happened, so for now, since
; we are only proclaiming functions for GCL, we omit the &optional.

(defvar *do-proclaims*

; We may want to experiment for proclaiming with other Lisps besides GCL.  But
; this might not be a good idea, in particular for Allegro CL and CCL (see
; above).

; In fact we experimented with CCL and ACL2(h) on 8/9/2013, by temporarily
; setting this variable to T.  We got these results from "time" for make -j 8
; with target regression-fresh on dunnottar.cs.utexas.edu.  The results are
; inconclusive, so we keep things simple (and avoid stepping on the possibility
; of future CCL improvements) by the skipping of function proclaiming in CCL.

; Built as follows (not showing here the setting PREFIX=):
;   make ACL2_HONS=h LISP=ccl-trunk ACL2_SIZE=3000000
; 27815.314u 1395.775s 1:09:03.35 705.0%        0+0k 2008+1736952io 34pf+0w

; Built as follows (not showing here the setting PREFIX=):
;   make ACL2_HONS=h LISP=ccl-trunk ACL2_SIZE=3000000 \
;     ACL2_PROCLAIMS_ACTION=generate_and_reuse
; 27272.420u 1401.555s 1:09:11.18 690.7%        0+0k 333088+1750384io 303pf+0w

  #+gcl

; The special value of :gcl says to use GCL's automatic mechanism during the
; boot-strap (but use ACL2's during normal execution).  But it also should work
; to use t instead.  Experiments may lead us to prefer one over the other.

  :gcl
  #-gcl nil)

(defun macroexpand-till (form sym)

; In order to find the THEs that we want to find to do automatic proclaiming of
; the output types of functions, we need to do macroexpansion at proclaim-time.
; It is possible that a given implementation of Common Lisp will macroexpand
; THE forms further.  Hence we gently do the macroexpansion we need, one
; expansion at a time, looking for the THE we want to find.

  (loop (cond ((and (consp form) (eq (car form) sym))
               (return form))
              (t (multiple-value-bind
                  (new-form flg)
                  (macroexpand-1 form)
                  (cond ((null flg) (return form))
                        (t (setq form new-form))))))))

(defun get-type-from-dcls (var dcls)
  (cond ((endp dcls) t)
        ((and (consp (car dcls))
              (eq 'type (caar dcls))
              (member var (cddr (car dcls))))
         (cadr (car dcls)))
        (t (get-type-from-dcls var (cdr dcls)))))

(defun arg-declarations (formals dcls)
  (cond ((endp formals) nil)
        (t (cons (get-type-from-dcls (car formals) dcls)
                 (arg-declarations (cdr formals) dcls)))))

(defun collect-types (l)
  (cond ((null (cdr l)) nil)
        ((stringp (car l))
         (collect-types (cdr l)))
        ((consp (car l))
         (let ((exp (car l)))
           (cond ((and (consp exp) (eq (car exp) 'declare))
                  (append (cdr exp) (collect-types (cdr l))))
                 (t nil))))
        (t nil)))

(defun convert-type-to-integer-pair (typ)

; Typ is (integer i j), (signed-byte i), or (unsigned-byte i).  We return an
; equivalent type (integer i' j').

  (case (car typ)
    (integer (cdr typ))
    (signed-byte (let ((n (expt 2 (1- (cadr typ)))))
                   (list (- n) (1- n))))
    (unsigned-byte (list 0 (1- (expt 2 (cadr typ)))))
    (t (error
        "Unexpected type for convert-to-integer-type ~s"
        typ))))

(defvar *acl2-output-type-abort* nil)

(defun min-integer-* (x y)
  (cond ((and (integerp x) (integerp y))
         (min x y))
        (t '*)))

(defun max-integer-* (x y)
  (cond ((and (integerp x) (integerp y))
         (max x y))
        (t '*)))

(defun max-output-type-for-declare-form (type1 type2)

; We return a supertype of type1 and type2, preferably as small as possible,
; else nil.  We assume that each typei that is not null is (values ...) or is
; some sort of integer type.

  (cond
   ((equal type1 type2)
    type1)
   ((or (eq type1 '*)
        (eq type2 '*))
    '*)
   ((not (equal (and (consp type1)
                     (eq (car type1) 'values))
                (and (consp type2)
                     (eq (car type2) 'values))))
    '*)
   ((and (or (eq type1 'integer)
             (and (consp type1)
                  (eq (car type1) 'integer)
                  (or (null (cddr type1))
                      (member '* (cdr type1) :test 'eq))))
         (or (eq type2 'integer)
             (and (consp type2)
                  (eq (car type2) 'integer)
                  (or (null (cddr type2))
                      (member '* (cdr type2) :test 'eq)))))
    'integer)
   ((or (atom type1) (atom type2)) ; so, type is t since neither is *
    t)
   ((cdr (last type1)) ; (not (true-listp type1))
    (error
     "Non-atom, non-true-listp type for max-output-type-for-declare-form: ~s"
     type1))
   ((cdr (last type2)) ; (not (true-listp type2))
    (error
     "Non-atom, non-true-listp type for max-output-type-for-declare-form: ~s"
     type2))
   (t (let ((sym1 (car type1))
            (sym2 (car type2)))
        (cond
         ((eq sym1 sym2)
          (case sym1
            ((signed-byte unsigned-byte)
             (if (< (cadr type1) (cadr type2))
                 type2
               type1))
            (integer
             (list 'integer
                   (min-integer-*  (cadr type1)  (cadr type2))
                   (max-integer-* (caddr type1) (caddr type2))))
            (values
             (cons 'values (max-output-type-for-declare-form-lst (cdr type1)
                                                                 (cdr type2))))
            (otherwise
             (error
              "Unexpected type for max-output-type-for-declare-form: ~s"
              type1))))
         ((or (eq sym1 'values) (eq sym2 'values)) ; but not both
          '*)
         (t (let* ((pair1 (convert-type-to-integer-pair type1))
                   (pair2 (convert-type-to-integer-pair type2))
                   (lower1 (car pair1))
                   (upper1 (cadr pair1))
                   (lower2 (car pair2))
                   (upper2 (cadr pair2))
                   (lower-min (min-integer-* lower1 lower2))
                   (upper-max (max-integer-* upper1 upper2)))
              (cond
               ((and (eql lower1 lower-min) (eql upper1 upper-max))
                type1)
               ((and (eql lower2 lower-min) (eql upper2 upper-max))
                type2)
               (t
                (list 'integer lower-min upper-max))))))))))

(defun max-output-type-for-declare-form-lst (type-list1 type-list2)

; Type-list1 and type-list2 are known to be true lists (nil-terminated
; lists).

  (cond ((or (null type-list1) (null type-list2))
         (cond
          ((and (null type-list1) (null type-list2))
           nil)
          ((and *acl2-output-type-abort*
                (or (atom type-list1) (atom type-list2)))
           (cons '*
                 (max-output-type-for-declare-form-lst
                  (cdr type-list1) (cdr type-list2))))
          (t
           (error "Implementation error:~%~
                   max-output-type-for-declare-form-lst called on lists of~%~
                   different length:~%~
                   ~s~%  ~s~%~
                   Please contact the ACL2 implementors."
                  type-list1 type-list2))))
        (t (cons (max-output-type-for-declare-form
                  (car type-list1) (car type-list2))
                 (max-output-type-for-declare-form-lst
                  (cdr type-list1) (cdr type-list2))))))

(declaim (ftype (function (t t)
                          (values t) ; see comment above about &optional
                          )
                output-type-for-declare-form-rec))
(declaim (ftype (function (t t)
                          (values t) ; see comment above about &optional
                          )
                output-type-for-declare-form-rec-list))

(defun output-type-for-declare-form-rec (form flet-alist)

; We return either nil or *, or else a type for form that ideally is as small
; as possible.

; Note that this isn't complete.  In particular, ACL2's proclaiming mechanism
; for GCL produces a return type of * for RETRACT-WORLD, because it can return
; what RETRACT-WORLD1 returns, and below we don't account for defined raw Lisp
; functions like RETRACT-WORLD1.  This could presumably be remedied by doing a
; sort of iterative computation of return types till we reach a fixed point,
; but that's for another day.

  (cond
   ((integerp form)
    `(integer ,form ,form))
   ((characterp form)
    'character)
   ((atom form)
    t)
   ((and (eq (car form) 'quote)
         (consp (cdr form)))
    (cond ((integerp (cadr form))
           `(integerp ,(cadr form) ,(cadr form)))
          ((rationalp (cadr form))
           `rational)
          ((numberp (cadr form))
           'number)
          ((characterp (cadr form))
           'character)
          ((null (cadr form))
           'null)
          ((symbolp (cadr form))
           'symbol)
          ((stringp (cadr form))
           'string)
          ((consp (cadr form))
           'cons)
          (t ; impossible?
           t)))
   ((and (eq (car form) 'setq)   ; always returns a single value
         (equal (length form) 3) ; avoid considering aborts from other values
         )
    (let ((x (output-type-for-declare-form-rec (car (last form))
                                               flet-alist)))
      (cond (*acl2-output-type-abort* '*)
            ((and (consp x)
                  (eq (car x) 'values))
             (cadr x))
            ((eq x '*) t)
            (t x))))
   ((and (eq (car form) 'setf)
         (equal (length form) 3) ; avoid considering aborts from other values
         )
    (output-type-for-declare-form-rec (car (last form))
                                      flet-alist))
   ((eq (car form) 'return-last)
    (cond ((equal (cadr form) ''mbe1-raw)
           (output-type-for-declare-form-rec (caddr form) flet-alist))
          ((and (equal (cadr form) ''progn)
                (consp (caddr form))
                (eq (car (caddr form)) 'throw-nonexec-error))
           (setq *acl2-output-type-abort* '*))
          (t (output-type-for-declare-form-rec (car (last form)) flet-alist))))
   ((eq (car form) 'return-from)
    (output-type-for-declare-form-rec (car (last form)) flet-alist))
   ((eq (car form) 'when)
    (let ((tmp (output-type-for-declare-form-rec (car (last form))
                                                 flet-alist)))
      (cond (*acl2-output-type-abort* '*)
            ((or (atom tmp)
                 (not (eq (car tmp) 'values)))
             t)
            (t '*))))
   ((assoc (car form) flet-alist :test 'eq)
    (cdr (assoc (car form) flet-alist :test 'eq)))
   ((member (car form) '(values
                         mv
; Note: for swap-stobjs, cadr and caddr have the same type.
                         swap-stobjs)
            :test 'eq)
    (cond ((null (cdr form))
           (setq *acl2-output-type-abort* '*))
          ((null (cddr form)) ; (values &), or (mv &) if mv is values
           (let* ((*acl2-output-type-abort* nil)
                  (tmp (output-type-for-declare-form-rec (cadr form)
                                                         flet-alist)))
             (cond ((and (symbolp tmp)
                         (not (eq tmp '*))
                         (not *acl2-output-type-abort*))
                    tmp)
                   (t t))))
          (t
           (cons 'values
                 (loop for x in (cdr form)
                       collect
                       (let* ((*acl2-output-type-abort* nil)
                              (tmp
                               (output-type-for-declare-form-rec x
                                                                 flet-alist)))
                         (cond ((and (symbolp tmp)
                                     (not (eq tmp '*))
                                     (not *acl2-output-type-abort*))
                                tmp)
                               (t t))))))))
   ((member (car form) '(flet labels)
            :test 'eq) ; (flet bindings val)
    (let ((temp flet-alist))
      (dolist (binding (cadr form))
        (let ((fn (car binding))
              (body (car (last binding)))
              *acl2-output-type-abort*)
          (let ((typ (output-type-for-declare-form-rec body flet-alist)))
            (push (cons fn
                        (if *acl2-output-type-abort*
                            '*
                          typ))
                  temp))))
      (output-type-for-declare-form-rec (car (last form)) temp)))
   ((eq (car form) 'the)
    (let ((typ (cadr form)))
      (cond ((member typ '(integer fixnum character) :test 'eq)
             typ)
            ((and (consp typ)
                  (member (car typ)
                          '(integer signed-byte unsigned-byte values)
                          :test 'eq))
             typ)
            (t t))))
   ((eq (car form) 'if)
    (cond
     ((eq (cadr form) t) ; as generated for final cond branch in CCL
      (output-type-for-declare-form-rec (caddr form) flet-alist))
     ((eq (cadr form) nil) ; perhaps not necessary
      (output-type-for-declare-form-rec (cadddr form) flet-alist))
     (t (let ((type1 (output-type-for-declare-form-rec (caddr form) flet-alist)))
          (if (eq type1 '*) ; optimization
              '*
            (max-output-type-for-declare-form
             type1
             (output-type-for-declare-form-rec (cadddr form) flet-alist)))))))
   ((member (car form) '(let let*) :test 'eq)
    (cond ((cddr form)
           (output-type-for-declare-form-rec (car (last form)) flet-alist))
          (t t)))
   ((eq (car form) 'multiple-value-bind)
    (cond ((cdddr form)
           (output-type-for-declare-form-rec (car (last form)) flet-alist))
          (t t)))
   ((eq (car form) 'unwind-protect)
    (output-type-for-declare-form-rec (cadr form) flet-alist))
   ((member (car form) '(time progn ec-call) :test 'eq)
    (output-type-for-declare-form-rec (car (last form)) flet-alist))
   ((member (car form)
            '(tagbody ; e.g., ld-fn
              throw-raw-ev-fncall ; e.g., from defchoose
              throw-nonexec-error
              eval
              error
              )
            :test 'eq)
    (setq *acl2-output-type-abort* '*))
   ((member (car form)

; Feel free to add any symbol to the following list that, when called, is
; guaranteed to yield a single value.

            '(* + - / 1+ 1-
                = /= < <= > >=
                append assoc
                concatenate format import list list* make-hash-table member
                mv-list nreverse position rassoc remove subsetp
; (strip-cars *ca<d^n>r-alist*)
                CADR CDAR CAAR CDDR
                CAADR CDADR CADAR CDDAR CAAAR CDAAR CADDR CDDDR
                CAAADR CADADR CAADAR CADDAR CDAADR CDDADR CDADAR CDDDAR
                CAAAAR CADAAR CAADDR CADDDR CDAAAR CDDAAR CDADDR CDDDDR)
            :test 'eq)
    t)
   (t (multiple-value-bind
       (new-form flg)
       (macroexpand-1 form)
       (cond ((null flg)
              (cond ((atom form) t)
                    ((eq (car form) 'multiple-value-prog1)
                     (and (consp (cdr form))
                          (output-type-for-declare-form-rec (cadr form) flet-alist)))
; Note: We don't expect multiple-value-setq to show up in ACL2.
                    ((and (consp (car form))
                          (eq (caar form) 'lambda))
                     (output-type-for-declare-form-rec (caddr (car form)) flet-alist))
                    ((not (symbolp (car form))) ; should always be false
                     '*)
                    (t (let ((x (and ; check that (w *the-live-state*) is bound
                                 (boundp 'ACL2_GLOBAL_ACL2::CURRENT-ACL2-WORLD)
                                 (fboundp 'get-stobjs-out-for-declare-form)
                                 (qfuncall get-stobjs-out-for-declare-form
                                           (car form)))))
                         (cond ((consp (cdr x))
                                (cons 'values
                                      (make-list (length x)
                                                 :initial-element
                                                 t)))
                               (x t)
                               (t (setq *acl2-output-type-abort* '*)))))))
             (t (output-type-for-declare-form-rec new-form flet-alist)))))))

(defun output-type-for-declare-form-rec-list (forms flet-alist)
  (cond ((atom forms)
         nil)
        (t (cons (let ((tp (output-type-for-declare-form-rec (car forms)
                                                             flet-alist)))
                   (if (member tp '(nil *) :test 'eq)
                       t
                     tp))
                 (output-type-for-declare-form-rec-list (cdr forms)
                                                        flet-alist)))))

(defun output-type-for-declare-form (fn form)

; We return a list of output types, one per value.

  (let* ((*acl2-output-type-abort* nil) ; protect for call on next line
         (result (output-type-for-declare-form-rec form nil))
         (stobjs-out (and
                      (not (member fn (symbol-value '*stobjs-out-invalid*)
                                   :test #'eq))
; check that (w *the-live-state*) is bound
                      (boundp 'ACL2_GLOBAL_ACL2::CURRENT-ACL2-WORLD)
                      (fboundp 'get-stobjs-out-for-declare-form)
                      (qfuncall get-stobjs-out-for-declare-form fn))))
    (when (and stobjs-out
               (not (eq (and (consp result)
                             (eq (car result) 'values))
                        (consp (cdr stobjs-out))))
               (not *acl2-output-type-abort*))
      (error "Implementation error in ~s:~%~
              stobjs-out and result don't mesh.~%~
              Stobjs-out = ~s~%~
              Result = ~s~%~
              Please contact the ACL2 implementors."
             (list 'output-type-for-declare-form fn '|defun...|)
             stobjs-out result))
    (cond
     ((and (consp result)
           (eq (car result) 'values))
      result ; see comment above about &optional
      )
     ((or *acl2-output-type-abort*
          (eq result '*))
      '*)
     (t
      (list 'values result) ; see comment above about &optional
      ))))

(defun make-defun-declare-form (fn form
                                   &optional
                                   (output-type nil output-type-p))

; See the comment in proclaim-file for why we don't proclaim in more lisps.

  (when *do-proclaims*
    (let* ((output-type
            (if output-type-p
                output-type
              (output-type-for-declare-form fn (car (last form))))))
      (let ((formals (caddr form)))
        (cond
         ((null (intersection formals lambda-list-keywords
                              :test 'eq))
          `(declaim (ftype (function
                            ,(arg-declarations
                              formals
                              (collect-types (cdddr form)))
                            ,output-type)

; WARNING: Do not replace (cadr form) by fn below.  These can differ!  Fn is
; passed to output-type-for-declare-form in order to get its 'stobjs-out, but
; (cadr form) can be the *1* function for fn.  The mistaken placement of fn
; below caused a factor of 4 slowdown in GCL in the first lemma5 in community
; book books/unicode/utf8-decode.lisp, because the proclaim for function
; utf8-combine4-guard was overwritten by a subsequent weaker proclaimed type
; that was supposed to be generated for the *1* function, but instead was
; generated for utf8-combine4-guard.

                           ,(cadr form))))
         (t nil))))))

(defun make-defconst-declare-form (form)

; We assume that the form has already been evaluated.

  (when *do-proclaims*
    (let* ((output (macroexpand-till (caddr form) 'the))
           (output-type (cond ((and (consp output)
                                    (eq 'the (car output)))
                               (cadr output))
                              (t nil))))
      (cond
       (output-type
        `(declaim (type ,output-type ,(cadr form))))
       (t (let ((val (symbol-value (cadr form))))
            (if (integerp val)
                `(declaim (type (integer ,val ,val) ,(cadr form)))
              nil)))))))

(defun make-defstobj-declare-form (form)
  (when *do-proclaims*
    (let* ((name (cadr form))
           (args (cddr form))

; The loss of efficiency caused by using symbol-value below should be more than
; compensated for by the lack of a warning here when building the system.

           (template (qfuncall defstobj-template name args nil))
           (raw-defs (qfuncall defstobj-raw-defs name template

; We do not want to rely on having the world available here, so we pass in nil
; for the final argument of defstobj-raw-defs.  The only effect of using nil
; instead of a world in such a context is that additional checking by
; translate-declaration-to-guard is missing.  We also pass in nil for
; congruent-to, since we don't think it makes any difference in the resulting
; declare form.

                               nil nil)))
      (cons 'progn
            (mapcar (function
                     (lambda (def) (if (member (symbol-value
                                                '*stobj-inline-declare*)
                                               def
                                               :test (function equal))
                                       nil
                                     (make-defun-declare-form
                                      (car def)
                                      (cons 'defun def)))))
                    raw-defs)))))

(defmacro eval-or-print (form stream)
  `(let ((form ,form)
         (stream ,stream))
     (when form
       (if stream
           (format stream "~s~%" form)
         (eval form)))))

(defun proclaim-form (form &optional stream)

; We assume that this function is called under proclaim-file, which binds
; *package*.  See the comment below for the in-package case.

  (when *do-proclaims*
    (cond ((consp form)
           (case (car form)
             ((in-package)
              (eval-or-print form stream)
              (when stream

; We make sure that when we're merely printing, nevertheless we are in the
; correct package as we read the rest of the file.

                (eval form))
              nil)
             ((defmacro defvar defparameter) nil)
             ((defconst)
              (eval-or-print (make-defconst-declare-form form) stream)
              nil)
             ((defstobj)
              (eval-or-print (make-defstobj-declare-form form) stream))
             ((eval-when)
              (dolist (x (cddr form))
                (proclaim-form x stream))
              nil)
             ((progn mutual-recursion)
              (dolist (x (cdr form))
                (proclaim-form x stream))
              nil)
             ((defun defund)
; debugging code:
;             (let ((decl-form (make-defun-declare-form (cadr form) form)))
;               (when (null decl-form)
;                 (format t "@@ Failed: ~s~%" (cadr form)))
;               (eval-or-print decl-form stream))
; non-debugging code:
              (eval-or-print (make-defun-declare-form (cadr form) form)
                             stream)
              nil)
             (defun-one-output
               (eval-or-print (make-defun-declare-form
                               (cadr form)
                               form
                               '(values t) ; see comment above about &optional
                               )
                              stream)
               nil)
             (otherwise nil)))
          (t nil))))

(defun proclaim-file (name &optional stream)

; Proclaims the functions in the file name that are either at the top-level, or
; within a progn, mutual-recursion, or eval-when.  IMPORTANT: This function
; assumes that the defconst forms in the given file have already been
; evaluated.  One way to achieve this state of affairs, of course, is to load
; the file first.

; Just before creating Version_2.5 we decided to consider proclaiming for
; Lisps other than GCL.  However, our tests in Allegro suggested that this may
; not help.  The comment below gives some details.  Perhaps we will proclaim
; for MCL in the future.  At any rate, CCL (OpenMCL) is supported starting with
; Version_2.8.  We tried proclaiming for that Lisp, but no longer do so; see
; Section "PROCLAIMING" above.

; Here is a summary of three comparable user times from certifying all the ACL2
; books in June 2000, just before Version_2.5 is complete.  The first column,
; labeled "Comp", is the one to be looked at for comparison purposes.  These are
; all done on the same Sun workstation, using Allegro 5.0.1.  The meanings of
; these numbers are explained below.
;
;                                Comp     Actual   Comments
; Recent ACL2 without proclaim:  5:41     5:36:42  no meta
; Recent ACL2 *with*  proclaim:  5:54     5:53:58
; April ACL2 (before non-std.):  5:48     5:35:58  missing some pipeline and ~40
;                                                  sec. user time on powerlists
;
; The "Comp" column estimates how long the run would have taken if all books had
; certified, except that no run gets past book batcher-sort in the powerlists/
; directory.  (The April run bogs down even slightly earlier.)  The first row is
; adjusted by about 4 minutes because the run started with book meta-plus-lessp.
; The April run broke on book basic-def from case-studies/pipeline and hence
; missed the rest of that directory's books.  The above points account for the
; addition of time from "Actual" to the appropriate comparison time in the first
; column.

  (when *do-proclaims*
    (format t "Note: Proclaiming file ~s.~%" name)
    (with-open-file
     (file name :direction :input)
     (let ((eof (cons nil nil))
           (*package* *package*))
       (loop
        (let ((form (read file nil eof)))
          (cond ((eq eof form) (return nil))
                (t (proclaim-form form stream)))))
       nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;          ACL2's Implementation of the Backquote Readmacro
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *comma* (make-symbol "COMMA")
  "*comma* is used by the backquote reader.  When the reader
encounters <,foo>, it returns (list *comma* read:<foo>>).")

(defparameter *comma-atsign* (make-symbol "COMMA-ATSIGN")
  "*comma-atsign* is used by the backquote reader.  When the reader
encounters <,@foo>, it returns (list *comma-atsign* read:<foo>).")

(defparameter *backquote-counter* 0
  "READ cannot handle a comma or comma-atsign unless there is a
pending backquote that will eliminate the *comma* or *comma-atsign*.
In the SPECIAL variable *backquote-counter* we keep track of the number of
backquotes that are currently pending.  It is crucial that this variable
be SPECIAL.")

(defun backquote (x)

  "The two functions BACKQUOTE and BACKQUOTE-LST implement backquote
as described on pp. 349-350 of CLTL1 except that (a) use of vector
notation causes an error and (b) the use of ,. is not permitted."

; It must be emphasized that the ACL2 implementation of backquote is
; only one of many implementations that are consistent with the Common
; Lisp specification of backquote.  That spec requires only that
; backquote produce a form that when evaluated will produce a
; designated object.  We impose the requirement that *acl2-readtable*
; be used both when checking files with ACL2 and when later compiling
; or using those files.  This requirement guarantees that we obtain
; the same behavior of backquote across all Common Lisps.  For
; example, it is an ACL2 theorem, across all Common Lisps that

;   (equal (car '`(,a)) 'cons)

; This theorem is definitely not true about the implementation of
; backquote provided by the implementors of each Common Lisp.  In
; fact, the lefthand side of this theorem represents an informal
; misuse of the backquote notation because one is intended to consider
; the effects of evaluating backquoted forms, not the forms
; themselves.  (In some Common Lisps, the lefthand side might even
; evaluate to a symbol in a nonstandard package.)  Nevertheless,
; because we inflict our definition of backquote on the ACL2 user at
; all times, the above equation is a theorem throughout, so no harm is
; done.  On the other hand, if we used the local implementation of
; backquote of each particular Common Lisp, we would get different
; ACL2 theorems in different Common Lisps, which would be bad.

; Unlike most implementors of backquote, we do no serious
; optimization.  We feel this inattention to efficiency is justified
; at the moment because in the usage we expect, the only serious costs
; will be small ones, during compilation.

; Our backquote always returns a cons-expression on a cons.  In
; particular, '`(a) returns (CONS 'A 'NIL) and not '(a), which would
; be legal in any backquote that produces a constant, e.g., one
; containing no commas.  We rely on the fact that the backquote of a
; cons is a cons-expression in our documentation of methods of
; bypassing the restrictions translate puts on LAMBDA objects in :FN
; slots.  For example, see :DOC gratuitous-lambda-object-restrictions.

  (cond ((and (vectorp x) (not (stringp x)))
         (error "ACL2 does not handle vectors in backquote."))
        ((atom x) (list 'quote x))
        ((eq (car x) *comma*) (cadr x))
        ((eq (car x) *comma-atsign*) (error "`,@ is an error"))
        (t (backquote-lst x))))

(defun backquote-lst (l)
  (cond ((atom l) (list 'quote l))
        ((eq (car l) *comma*)
         (cadr l))
        ((eq (car l) *comma-atsign*)
         (error ". ,@ is illegal."))
        ((and (consp (car l))
              (eq (caar l) *comma*))
         (list 'cons
               (cadr (car l))
               (backquote-lst (cdr l))))
        ((and (consp (car l))
              (eq (caar l) *comma-atsign*))
         (cond ((null (cdr l))
                (cadr (car l)))
               (t (list 'append (cadr (car l)) (backquote-lst (cdr l))))))
        (t
         (list 'cons
               (backquote (car l))
               (backquote-lst (cdr l))))))

(defvar *read-object-comma-count* nil)

(defun acl2-comma-reader (stream)
  (when *read-object-comma-count*
    (incf *read-object-comma-count*))
  (when (< *backquote-counter* 0)
    (let* ((pathname (and (typep stream 'file-stream)
                          (pathname stream)))
           (posn (and pathname
                      (file-position stream))))
      (clear-input stream)
      (cond
       (posn
        (error "Illegal comma encountered by READ: file ~a, position ~s."
               pathname posn))
       (*read-object-comma-count*
        (error
         "Illegal comma: ~:r comma processed while reading top-level form."
         *read-object-comma-count*))
       (t (error "Illegal comma encountered by READ.")))))
  (case (peek-char nil stream t nil t)
    (#\@ (read-char stream t nil t)
     (list *comma-atsign* (read stream t nil t)))
    (#\. (error ",. not allowed in ACL2 backquote forms."))
    (otherwise (list *comma* (read stream t nil t)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            PACKAGES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following function used to be defined in axioms.lisp (with
; #-acl2-loop-only), but we need it here.

(defun symbol-package-name (x)

; Warning: This function assumes that x is not a bad-lisp-objectp.  In
; particular, see the Invariant on Symbols in the Common Lisp Package,
; discussed in a comment in bad-lisp-objectp, which allows us to assume that if
; x resides in the "COMMON-LISP" package and does not have its
; *initial-lisp-symbol-mark* property set, then its symbol-package is the
; *main-lisp-package*.

  (cond ((get x *initial-lisp-symbol-mark*))
        ((let ((p (symbol-package x)))
           (cond ((eq p *main-lisp-package*)

; We could just return *main-lisp-package-name-raw* in this case (but do not
; skip this case, since in non-ANSI GCL, (package-name *main-lisp-package*) is
; "LISP", not "COMMON-LISP" (which is what we need here).  But we go ahead and
; set *initial-lisp-symbol-mark* in order to bypass this code next time.

                  (setf (get x *initial-lisp-symbol-mark*)
                        *main-lisp-package-name-raw*))
                 (t (and p (package-name p))))))

; We use ERROR now because we cannot print symbols without packages
; with ACL2 functions.

        (t (error
            "The symbol ~a, which has no package, was encountered~%~
             by ACL2.  This is an inconsistent state of affairs, one that~%~
             may have arisen by undoing a defpkg but holding onto a symbol~%~
             in the package being flushed, contrary to warnings printed.~%~%"
            x))))

(defvar *defpkg-virgins* nil)

(defun maybe-make-package (name)

; We formerly had a long comment here explaining that this definition CMU
; Common Lisp 19e.  At that time, maybe-make-package was a macro with a #+cmu
; body of `(defpackage ,name (:use)).  But CMU Common Lisp 21a does not have
; this problem, so we have changed maybe-make-package from a macro to a
; function, which allows its callers to be functions as well.  That, in turn,
; may avoid compilation required for macro calls in some Lisps, including CCL.

  (when (not (find-package name))
    (make-package name :use nil)))

(defun maybe-make-three-packages (name)
  (maybe-make-package name)
  (maybe-make-package (concatenate 'string
                                   acl2::*global-package-prefix*
                                   name))
  (maybe-make-package (concatenate 'string
                                   acl2::*1*-package-prefix*
                                   name)))

(defmacro maybe-introduce-empty-pkg-1 (name)

; It appears that GCL requires a user::defpackage (non-ANSI case) or
; defpackage (ANSI case; this may be the same as user::defpackage) form near
; the top of a file in order to read the corresponding compiled file.  For
; example, an error occurred upon attempting to load the community books file
; books/data-structures/defalist.o after certifying the corresponding book
; using GCL, because the form (MAYBE-INTRODUCE-EMPTY-PKG-1 "U") near the top of
; the file was insufficient to allow reading a symbol in the "U" package
; occurring later in the corresponding source file.

; On the other hand, the CL HyperSpec does not pin down the effect of
; defpackage when a package already exists.  Indeed, the defpackage approach
; that we use for GCL does not work for LispWorks 6.0.

; So, we have quite a different definition of this macro for GCL as opposed to
; the other Lisps.

  #-gcl
  `(eval-when
    #+cltl2 (:load-toplevel :execute :compile-toplevel)
    #-cltl2 (load eval compile) ; though probably #-gcl implies #+cltl2
    (maybe-make-three-packages ,name))
  #+gcl
  (let ((defp #+cltl2 'defpackage #-cltl2 'user::defpackage))
    `(progn
       (,defp ,name
         (:use))
       (,defp ,(concatenate 'string
                            acl2::*global-package-prefix*
                            name)
         (:use))
       (,defp ,(concatenate 'string
                            acl2::*1*-package-prefix*
                            name)
         (:use)))))

(defvar *ever-known-package-alist* ; to be redefined in axioms.lisp
  nil)

(defun package-has-no-imports (name)
  (let ((pkg (find-package name)))
    (do-symbols (sym pkg)
                (when (not (eq (symbol-package sym) pkg))
                  (return-from package-has-no-imports nil))))
  t)

(defun maybe-introduce-empty-pkg-2 (name)
  (when (and (not (member name *defpkg-virgins*
                          :test 'equal))
             (not (assoc name *ever-known-package-alist*
                         :test 'equal))
             (package-has-no-imports name))
    (push name *defpkg-virgins*)))

; The GCL proclaim mechanism puts symbols in package "ACL2-PC" into file
; acl2-proclaims.lisp.  So Lisp needs to know about that package when it loads
; that file.  We introduce that package in a harmless way here.  Although we
; only need to do so for GCL, we do so for every Lisp, for uniformity.
(maybe-make-package "ACL2-PC")
(maybe-introduce-empty-pkg-2 "ACL2-PC")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            SUPPORT FOR ACL2 CHARACTER READER
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rev1@ (x acc)

; A strange version of linear reverse, which treats the final cdr of x
; as the final element of x.

  (cond
   ((atom x)
    (cons x acc))
   (t (rev1@ (cdr x) (cons (car x) acc)))))

(defun acl2-read-character-string (s acc)

; The reason we're so picky about what we allow as readable character notation
; is the existence of certain restrictions imposed by dpANS.  From the
; documentation for Sharpsign Backslash in dpANS:

;   When the token x is more than one character long, the x must have
;   the syntax of a symbol with no embedded package markers.  In this
;   case, the sharpsign backslash notation parses as the character
;   whose name is (string-upcase x); see *See Character Names::.

; And from the documentation for char-name in dpANS:

;   Returns a string that is the name of the character, or nil if the
;   character has no name.

; However, in akcl for example, (char-name #\\346) evaluates to NIL.  Even if
; it didn't, surely different lisps will define char-name differently.  So,
; we can't allow notation such as #\\346.

  (let* ((ch (read-char s nil nil)))
    (cond ((or (null ch)
               (member ch *acl2-read-character-terminators*))
           (when ch (unread-char ch s))
           (cond
            ((characterp acc)
             acc)
            (t (let ((x (coerce (rev1@ acc nil) 'string)))
                 (cond
                  ((string-equal x "SPACE")
                   #\Space)
                  ((string-equal x "TAB")
                   #\Tab)
                  ((string-equal x "NEWLINE")
                   #\Newline)
                  ((string-equal x "PAGE")
                   #\Page)
                  ((string-equal x "RUBOUT")
                   #\Rubout)
                  ((string-equal x "RETURN")
                   #\Return)
                  #+clisp

; Currently we only allow #\Null in CLISP.  We have to allow it there in some
; fashion because it is written to compiled (.fas) files.  The current approach
; seems to avoid any soundness issue: presumably #\Null is the same in every
; CLISP, and if one tries then to use a book containing #\Null that was
; certified using CLISP, then one will simply get an error.

                  ((string-equal x "NULL")
                   #\Null)
                  #+(and cmu18 solaris)

; We have seen code with #\Newline generate #\Linefeed in CMU CL 18d on
; Sun/Solaris, so here we allow #\Linefeed in order to avoid an error during
; the ACL2 build.  This would seem a harmless fix, for the sort of reason
; described above in the case of NULL.

                  ((and (string-equal x "LINEFEED")
                        (eql #\Newline #\Linefeed))
                   #\Newline)
                  (t (funcall
                      (if (fboundp 'interface-er)
                          'interface-er
                        'error)

                      "When the ACL2 reader tries to read #\\x, then x must ~
                       either be a single character or one of Space, Tab, ~
                       Newline, Page, Rubout, or Return (where case is ~
                       ignored).  What follows x must be a character in the ~
                       list:~|~X01.~|However, ~s2 is neither a single ~
                       character nor one of Space, Tab, Newline, Page, ~
                       Rubout, or Return (where case is ignored)."
                      *acl2-read-character-terminators*
                      nil
                      x)))))))
          (t (acl2-read-character-string s (cons ch acc))))))

(defun acl2-character-reader (s c n)
  (declare (ignore n c))
  (let ((ch (read-char s)))
    (acl2-read-character-string s ch)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            SUPPORT FOR #.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar *inside-sharp-dot-read* nil)

(defvar *inside-sharp-u-read* nil)

(defun sharp-dot-read (stream char n)
  (declare (ignore char n))
  (let ((whitespace-chars '(#\Backspace #\Tab #\Newline #\Linefeed #\Page
                            #\Return #\Space)))
    (when (member (peek-char nil stream nil nil t)
                  whitespace-chars)
      (error "#. must be followed immediately by a non-whitespace character.~%~
              See :DOC sharp-dot-reader.")))
  (let* ((*inside-sharp-dot-read*
          (or (not *inside-sharp-dot-read*)
              (error "Recursive attempt to read a sharp-dot (#.)~%expression ~
                      while inside a sharp-dot expression.  This is not~%~
                      allowed in ACL2.")))
         (sym (read stream t nil t))
         (val (and (symbolp sym)
                   (qfuncall fgetprop sym 'const nil
                             (qfuncall w *the-live-state*)))))
    (cond
     (val
      (cond ((and (consp val)
                  (eq (car val) 'quote)
                  (consp (cdr val))
                  (null (cddr val)))
             (cadr val))
            (t (clear-input stream)
               (error "(Implementation error) Found non-quotep 'const ~%~
                       property for ~s."
                      sym))))
     (sym
      (clear-input stream)
      (error "ACL2 supports #. syntax only for #.*a*, where *a* has been ~%~
              defined by ~s.  Thus the form #.~s is illegal.  See :DOC ~%~
              sharp-dot-reader~a."
             'defconst
             sym
             (cond ((eval '(f-get-global 'certify-book-info *the-live-state*))
                    (format nil ", in particular Remark (2)"))
                   (t ""))))
     (t ; surprising case
      (clear-input stream)
      (error "ACL2 supports #. syntax only for #.*a*, where *a* has been ~%~
              defined by ~s."
             'defconst)))))

(defun sharp-bang-read (stream char n)

; Thanks to Pascal J. Bourguignon for suggesting this approach.

  (declare (ignore char n))
  (let* ((package-name (read stream t nil t))
         (package-string (cond ((symbolp package-name)
                                (symbol-name package-name))
                               ((stringp package-name)
                                package-name)
                               (t nil)))
         (*package* (cond
                     (*read-suppress* *package*)
                     ((assoc package-string
                             (qfuncall known-package-alist *the-live-state*)
                             :test 'equal)
                      (qfuncall find-package-fast package-string))
                     (t
                      (error "There is no package named ~S that is known to ~
                              ACL2 in this context."
                             package-name)))))
    (read stream t nil t)))

(defun sharp-u-read (stream char n)
  (declare (ignore char n))
  (let* ((*inside-sharp-u-read*
          (or (not *inside-sharp-u-read*)
              (error "Recursive attempt to read a sharp-u (#u)~%expression ~
                      while inside a sharp-u expression.  This is not~%~
                      allowed.")))
         (x (read stream t nil t)))
    (cond
     ((numberp x) x)
     ((not (symbolp x))
      (error "Failure to read #u expression:~%~
              #u was not followed by a symbol."))
     (t (let* ((name (symbol-name x))
               (c (and (not (equal name ""))
                       (char name 0))))
          (cond ((member c '(#\B #\O #\X))
                 (values ; seems necessary in GCL to return a single value
                  (read-from-string
                   (concatenate 'string "#" (remove #\_ name)))))
                (t (let ((n (read-from-string (remove #\_ name))))
                     (cond ((numberp n) n)
                           (*read-suppress* nil)
                           (t (error "Failure to read #u expression:~%~
                                      Result ~s is not a numeral."
                                     n)))))))))))

(defun read-digits (stream base-16-p)
  (declare (special *hex-array* *base-10-array*))
  (let ((base-array (if base-16-p *hex-array* *base-10-array*))
        (sign (read-char stream nil :eof t))
        tmp lst)
    (cond ((eq sign :eof)
           (return-from read-digits
                        (values 0 nil :eof)))
          ((not (member sign '(#\+ #\-)))
           (unread-char sign stream)))
    (loop (setq tmp (read-char stream nil :eof t))
          (cond ((eq tmp :eof) (return))
                ((eql tmp #\_)) ; discard underscore
                ((aref base-array (char-code tmp))
                 (push tmp lst))
                (t (return))))
    (let ((len (length lst))) ; computed before destructive nreverse call
      (values len
              (eql sign #\-)
              (cond ((null lst) 0)
                    (t (let ((*read-base* (if base-16-p 16 10)))
                         (read-from-string
                          (coerce (nreverse lst) 'string)))))
              tmp))))

(defun sharp-f-read (stream char n)
  (declare (ignore char n))
  (flet ((read-exp (stream)
                   (multiple-value-bind
                    (len negp exp next-char)
                    (read-digits stream nil)
                    (when (eql len 0)
                      (cond (*read-suppress* (return-from sharp-f-read nil))
                            (t (clear-input stream)
                               (error "Empty exponent in #f expression."))))
                    (unread-char next-char stream)
                    (if negp (- exp) exp))))
    (let* ((tmp (read-char stream nil :eof t))
           (base-16-p (cond
                       ((member tmp '(#\x #\X)) t)
                       ((eq tmp :eof)
                        (cond (*read-suppress* (return-from sharp-f-read nil))
                              (t (error "End of file encountered after #f."))))
                       (t (unread-char tmp stream)
                          nil)))
           (exp-chars (if base-16-p '(#\p #\P) '(#\e #\E))))
      (multiple-value-bind
       (len negp before-dot next-char)
       (read-digits stream base-16-p)
       (declare (ignore len))
       (cond ((eq next-char :eof)
              (if negp (- before-dot) before-dot))
             ((member next-char exp-chars)
              (let* ((exp (read-exp stream)))
                (* (if negp (- before-dot) before-dot)
                   (expt (if base-16-p 2 10) exp))))
             ((eql next-char #\.)
              (multiple-value-bind
               (len negp-after-dot after-dot next-char)
               (read-digits stream base-16-p)
               (when negp-after-dot
                 (cond
                  (*read-suppress* (return-from sharp-f-read nil))
                  (t (clear-input stream)
                     (error "Illegal sign after point in #f expression."))))
               (let ((significand
                      (+ before-dot (/ after-dot
                                       (expt (if base-16-p 16 10) len)))))
                 (cond ((member next-char exp-chars)
                        (let* ((exp (read-exp stream)))
                          (* (if negp (- significand) significand)
                             (expt (if base-16-p 2 10) exp))))
                       (t (unread-char next-char stream)
                          (if negp (- significand) significand))))))
             (t (unread-char next-char stream)
                (if negp (- before-dot) before-dot)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            SUPPORT FOR #@
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; See interface-raw.lisp, as sharp-atsign-read uses several functions defined
; in the sources and we want to avoid compiler warnings.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            SUPPORT FOR #{"""
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun fancy-string-reader-escape-check (acc)

; Checks whether acc consists of any number of backslashes followed by three
; doublequotes.

  (if (atom acc)
      nil
    (if (eql (car acc) #\\)
        (fancy-string-reader-escape-check (cdr acc))
      (and (eql (first acc) #\")
           (eql (second acc) #\")
           (eql (third acc) #\")))))

(defun fancy-string-reader-macro-aux (stream acc)

; See fancy-string-reader-macro.

  (let ((char ; error on EOF is appropriate here
         (read-char stream)))
    (if (and (eql char #\})
             (fancy-string-reader-escape-check acc))
        (if (eql (car acc) #\\)

; We have three doublequotes followed by 1 or more backslashes and followed by
; a close brace.  Just remove one of the backslashes and continue.

            (fancy-string-reader-macro-aux stream (cons #\} (cdr acc)))

; No backslashes, so we have """} -- we're at the end of the fancy string.  We
; haven't accumulated the } yet, but throw away the """ since those end the
; string and aren't part of its content.

          (cdddr acc))

; Otherwise just accumulate the char.

      (fancy-string-reader-macro-aux stream (cons char acc)))))

(defun fancy-string-reader-macro (stream subchar arg)

; Initial implementation contributed by Jared Davis.  See community book
; books/system/fancy-string-reader-test.lisp for how this is used.

  (declare (ignorable subchar arg))

; This is the reader macro for #{.  When it is called the #{ part has already
; been read.

; First, require that there are three starting quotes.  This is intended to
; leave room to grow, i.e., if someone else wants to add some other kind of
; special #{... syntax, they can do so as long as it's not """.

  (let ((quote1 (read-char stream)))
    (unless (eql quote1 #\")
      (error "Undefined reader macro: #{~c" quote1)))
  (let ((quote2 (read-char stream)))
    (unless (eql quote2 #\")
      (error "Undefined reader macro: #{\"~c" quote2)))
  (let ((quote3 (read-char stream)))
    (unless (eql quote3 #\")
      (error "Undefined reader macro: #{\"\"~c" quote3)))

; Now read all the characters until """}, reverse them, and turn them into a
; string.

  (let ((rchars (fancy-string-reader-macro-aux stream nil)))
    (nreverse (coerce rchars 'string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            SUPPORT FOR FAST #n= and #n#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The handling of #n= in CCL 1.4, and we suspect some other Lisp
; implementations as well, can be quite slow because of the need to handle
; circular objects and to check for illegal use of #n=(... #n=... ...).  But
; ACL2 controls how it writes out certain files, notably expansion files (see
; the Essay on Hash Table Support for Compilation).  In those cases, we are
; willing to take responsibility that such illegal uses of #n= do not occur,
; and that #n# is used only after the "definition" of n with #n=.  (It is easy
; to take such responsibility, since we print each form of the file in a legal
; manner.  We cannot similarly take responsibility for user books, which can be
; hand-edited.)

(defvar *sharp-reader-array-size*

; While this is initially 65536, it may increase, each time by a factor of
; *sharp-reader-array-size-multiplier*.  It never decreases.

  (expt 2 16))

(defvar *sharp-reader-array*
  (make-array *sharp-reader-array-size*))

(defvar *sharp-reader-array-size-multiplier*

; Resize *sharp-reader-array* by this factor each time its size limit is hit,
; but never to a size past most-positive-fixnum.

  2)

(defconstant *sharp-reader-max-array-size*

; We keep this a fixnum in all reasonable Lisps, to guarantee in particular
; that the expression (1+ *sharp-reader-max-index*) in with-reckless-read will
; always evaluate to a fixnum.

  (1- (expt 2 29)))

(defvar *sharp-reader-max-index*

; We hold the maximum index assigned to *sharp-reader-array* in this variable.
; (It is also OK if this variable exceeds that index; initially, its value is 0
; even though no index has been assigned.)  We use this value to wipe clean the
; *sharp-reader-array* after its use (see with-reckless-read), so that it
; doesn't defeat potential garbage collection of its elements.  We were tempted
; to use a one-element array so that Lisps like GCL can avoid boxing, but a
; little experimentation seems to suggest that GC for even 1,000,000 fixnums is
; very fast compared to what we might expect from reading that many objects.

  0)

(defun update-sharp-reader-max-index (index)
  (when (< *sharp-reader-max-index* index)
    (when (>= index *sharp-reader-array-size*)

; Grow the array.

      (when (>= index *sharp-reader-max-array-size*)
        (error "Lisp reader encountered #=~s (maximum index is ~s)."
               index
               (1- *sharp-reader-max-array-size*)))
      (let* ((new-sharp-reader-array-size
              (max (1+ index)
                   (min (* *sharp-reader-array-size-multiplier*
                           *sharp-reader-array-size*)
                        *sharp-reader-max-array-size*)))
             (new-sharp-reader-array
              (make-array new-sharp-reader-array-size))
             (bound (the (unsigned-byte 29) (1+ *sharp-reader-max-index*))))
        (do ((i 0 (the (unsigned-byte 29) (1+ i)))) ((eql i bound))
          (declare (type (unsigned-byte 29) i))
          (setf (svref new-sharp-reader-array i)
                (svref *sharp-reader-array* i)))
        (setq *sharp-reader-array* new-sharp-reader-array
              *sharp-reader-array-size* new-sharp-reader-array-size)))

; End growing of the array.

    (setq *sharp-reader-max-index* index)))

(defun reckless-sharp-sharp-read (stream char arg)
  (declare (ignore stream char))
  (cond
   (*read-suppress* nil)
   (t (svref *sharp-reader-array* arg))))

(defun reckless-sharp-equal-read (stream char arg)
  (declare (ignore char))
  (cond (*read-suppress* (values)) ; as for CCL, but unlikely to arise in ACL2
        (t (let ((val (read stream t nil t)))
             (update-sharp-reader-max-index arg)
             (setf (svref *sharp-reader-array* arg)
                   val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            ENVIRONMENT SUPPORT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Getenv$ is first used in acl2-init.lisp, so we define it here.

#+cmu
(defvar *cmucl-unix-setenv-fn*

; Jared Davis has pointed us to the following from
; https://common-lisp.net/project/cmucl/doc/cmu-user/unix.html#toc235:

;   You probably won't have much cause to use them, but all the Unix system
;   calls are available. The Unix system call functions are in the Unix
;   package. The name of the interface for a particular system call is the name
;   of the system call prepended with unix-. The system usually defines the
;   associated constants without any prefix name. To find out how to use a
;   particular system call, try using describe on it. If that is unhelpful,
;   look at the source in unix.lisp or consult your system maintainer.

; As Jared has also suggested, unix:unix-setenv is presumably a wrapper for the
; C function setenv, described for example here:

;   http://pubs.opengroup.org/onlinepubs/009695399/functions/setenv.html
;   http://linux.die.net/man/3/setenv

; Also see *cmucl-unix-getenv-fn*.

  (and (find-package "UNIX")
       (let ((fn (ignore-errors (intern "UNIX-SETENV" "UNIX"))))
         (and (fboundp fn) fn))))

#+cmu
(defvar *cmucl-unix-getenv-fn*

; Also see *cmucl-unix-setenv-fn*.

  (and *cmucl-unix-setenv-fn* ; so that getenv$ respects setenv$
       (let ((fn (ignore-errors (intern "UNIX-GETENV" "UNIX"))))
         (and (fboundp fn) fn))))

(defun getenv$-raw (string)

; The following either returns the value of the given environment variable or
; returns nil (in lisps where we do not yet know how to get that value).
; Except, it causes an error if the computed value is an illegal ACL2 string.

; WARNING: Keep this in sync with the #-acl2-loop-only definition of setenv$.

  (let* ((val
          #+cmu
          (cond (*cmucl-unix-getenv-fn*
                 (funcall *cmucl-unix-getenv-fn* string))
                ((boundp 'ext::*environment-list*)
                 (cdr (assoc (intern string :keyword)
                             ext::*environment-list*
                             :test #'eq))))
          #+(or gcl allegro lispworks ccl sbcl clisp)
          (let ((fn
                 #+gcl       'si::getenv
                 #+allegro   'sys::getenv
                 #+lispworks 'hcl::getenv
                 #+ccl       'ccl::getenv
                 #+sbcl      'sb-ext::posix-getenv
                 #+clisp     'ext:getenv))
            (and (fboundp fn)
                 (funcall fn string))))
         (msg (and val
                   (fboundp 'bad-lisp-stringp) ; false early in boot-strap
                   (qfuncall bad-lisp-stringp val))))
    (cond (msg ; It's not clear that this case is possible, at least in CCL.
           (qfuncall
            interface-er
            "The value of environment variable ~x0 is ~x1, which is not a ~
             legal ACL2 string.~%~@2"
            string val msg))
          (t val))))

#+sbcl
(defmacro define-our-sbcl-putenv ()

; Jared Davis found sb-posix::putenv and the necessary require form (below) for
; using it.  We aren't finding much documentation about this function on the
; web, but we also aren't particularly relying on any properties of it.  Our
; function defined below is a wrapper (if the REQUIRE form succeeds without
; error), for use in the raw Lisp definition of setenv$.

; But we don't define our-sbcl-putenv here -- instead we define the present
; macro to be called after starting up ACL2.  The reason is that during the
; build, environment variable SBCL_HOME might not yet be set; we set it in our
; function, save-acl2-in-sbcl-aux, so that it's set when ACL2 starts up.

  '(ignore-errors
    (require :sb-posix)
    (defun our-sbcl-putenv (var value)
      (funcall (intern "PUTENV" "SB-POSIX") ; avoid sb-posix package prefix
               (concatenate 'string var "=" value)))))

(defun get-os ()

; The following are in priority order.

  #+unix (return-from get-os :unix)
  #+mswindows (return-from get-os :mswindows)
  #-(or unix mswindows) nil)

(defmacro our-ignore-errors (x)
  #+cltl2 `(ignore-errors ,x)
  #-cltl2 x)

(defmacro safe-open (filename &rest args &key direction &allow-other-keys)
  (assert (member direction ; might later support :io and :probe
                  '(:input :output)
                  :test #'eq))
  `(our-ignore-errors
    (progn ,@(when (eq direction :output)
               `((ensure-directories-exist ,filename)))
           (open ,filename ,@args))))

(defvar *check-namestring* t)

(defun our-truename (filename &optional namestringp)

; Filename can be a pathname, in which case we treat it as its namestring.
; Both filename and the result of this function are OS filenames, which might
; have characters that disqualify them from being ACL2 strings.

; For now, assume that namestringp is nil (or not supplied).

; This function is intended to return nil if filename does not exist.  We thus
; rely on the CL HyperSpec, where it says of truename that "An error of type
; file-error is signaled if an appropriate file cannot be located within the
; file system for the given filespec"; and we also rely on the Allegro CL
; documentation for function pathname-resolve-symbolic-links, which says: "When
; pathname names a non-existent pathname, an error is signaled...."

; We return (ignore-errors (truename x)) instead of (probe-file x) because we
; have seen CLISP 2.48 cause an error when probe-file is called on a directory
; name.  Unfortunately, we can't do that with GCL 2.6.7, which doesn't have
; ignore-errors.  Also unfortunately, Allegro CL 8.0 (also probably earlier
; versions, and maybe later versions) does not fully resolve symbolic links
; using truename, even with value T for keyword :follow-symlinks.

; Finally, consider namestringp.  If nil, then as above we either return nil or
; the truename (a pathname object).  Otherwise, we return the namestring of
; such a truename, with the following treatment if that truename is nil: return
; nil if namestringp is :safe, else cause an error, where if namestringp is a
; msgp then incorporate it into the error message.

  (when (pathnamep filename)
    (setq filename (namestring filename)))
  (let* ((truename
          (cond
           #+allegro
           ((fboundp 'excl::pathname-resolve-symbolic-links)
            (ignore-errors
              (qfuncall excl::pathname-resolve-symbolic-links
                        filename)))
           #+(and gcl (not cltl2))
           ((fboundp 'si::stat) ; try to avoid some errors
            (and (or (qfuncall si::stat filename)

; But filename might be a directory, in which case the si::stat call above
; could return nil; so we try again.

                     (and (or (equal filename "")
                              (not (eql (char filename (1- (length filename)))
                                        #\/)))
                          (qfuncall si::stat
                                    (concatenate 'string filename "/"))))
                 (truename filename)))
           #+(and gcl (not cltl2))
           (t (truename filename))
           #-(and gcl (not cltl2))
           (t

; Here we also catch the case of #+allegro if
; excl::pathname-resolve-symbolic-links is not defined.

            (ignore-errors (truename filename)))))
         (namestring (and truename (namestring truename))))
    (cond ((null namestringp)
           truename)
          ((null truename)
           (cond ((eq namestringp :safe) nil)
                 (t (qfuncall
                     interface-er
                     "Unable to obtain the truename of file ~x0.~@1"
                     filename
                     (if (qfuncall msgp namestringp)

; It is tempting to write (qfuncall msg "  ~@0" namestringp) just below, but
; msg is a macro, so we construct the appropriate message ourselves.

                         (list "  ~@0" (cons #\0 namestringp))
                       "")))))
          (t namestring))))

(defun unix-full-pathname (name &optional extension)

; Unlike truename and our-truename, unix-full-pathname does not assume that any
; particular file exists.

; We formerly used Common Lisp function merge-pathnames.  But with CCL
; (probably quite an old version), merge-pathnames has inserted an extra
; backslash (\), as follows:

;  ? (MERGE-PATHNAMES "foo.xxx.lx86cl64" "/u/kaufmann/temp/")
;  #P"/u/kaufmann/temp/foo\\.xxx.lx86cl64"
;  ?

; Gary Byers has explained that while this behavior may not be ideal, it is
; legal for Common Lisp.  So we avoid merge-pathnames here.

  (let* ((*check-namestring* t)
         (os (get-os))
         (state *the-live-state*)
         (name (qfuncall pathname-os-to-unix
                         (if extension
                             (concatenate 'string
                                          name
                                          "."
                                          extension)
                           name)
                         os state)))
    (qfuncall
     cancel-dot-dots
     (cond ((qfuncall absolute-pathname-string-p name nil os)
            name)
           (t
            (concatenate 'string (qfuncall our-pwd) name))))))

(defun our-user-homedir-pathname ()

; For ACL2 Version_4.2, Hanbing Liu reported the following error using Allegro
; CL Enterprise Edition 8.0 for Linux, apparently printed before printing the
; optimization settings.

;     An unhandled error occurred during initialization:
;     There is no file named /home/rcash/

; The error was likely caused by our calling user-homedir-pathname without a
; host, for a user without a home directory.  Quoting the Common Lisp Hyperspec
; on (user-homedir-pathname &optional host):

;   If it is impossible to determine the user's home directory on host, then
;   nil is returned. user-homedir-pathname never returns nil if host is not
;   supplied.

; It's not clear that there is a meaningful notion of host on Linux.  So we
; play it safe and define our own, error-free (for CLtL2) version of
; user-homedir-pathname.

; For GCL, Camm Maguire has told us that calling user-homedir-pathname should
; work on GCL 2.6.8 or later, at least if there is a proper home directory and
; password entry.  But if that fails for some reason, one can use the
; commented-out alternative code below instead.

; (let ((home (si::getenv "HOME")))
;   (and home
;        (pathname (concatenate 'string home "/"))))

  (our-ignore-errors (user-homedir-pathname)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;             SUPPORT FOR SERIALIZE INTEGRATION INTO ACL2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following definitions might seem to belong serialize-raw.lisp, and
;; that's where they lived when we only built ACL2(h) with CCL.  But Jared
;; Davis noticed that SBCL 1.0.46 didn't let him add undefined functions into
;; the readtable.  Note also that it doesn't seem sufficient to give the
;; function symbols temporary definitions and redefine them later: the
;; readtable still uses the old functions.  So to solve this, we move the
;; functions over from serialize-raw.lisp to here.

(declaim (ftype (function (t t t) (values t))
                ser-decode-from-stream))

(defun ser-cons-reader-macro (stream subchar arg)
  (declare (ignorable subchar arg))
  ;; This is the reader macro for #Y.  When it is called the #Z part has
  ;; already been read, so we just want to read the serialized object.
  (ser-decode-from-stream nil :never stream))

(defun ser-hons-reader-macro (stream subchar arg)
  (declare (ignorable subchar arg))
  ;; This is the reader macro for #Z.  When it is called the #Z part has
  ;; already been read, so we just want to read the serialized object.
  (ser-decode-from-stream nil :smart stream))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            MISCELLANY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following definition was originally in interface-raw.lisp.  But it was
; also needed in hons-raw.lisp, which is compiled earlier, and CCL (at least)
; needs to know that we indeed have a macro here -- so the definition can't be
; put off until loading interface-raw.lisp.  In Version_3.2, hons-raw.lisp was
; only included in special builds, so we did't want to put this definition
; there; thus, we put it here.  (Even in August 2021, we saw no reason to move
; it.)

(defmacro special-form-or-op-p (name)

; At one time we thought that special-operator-p does not work in all Lisps.
; But if that was true, it no longer seems to be the case in October 2011.

  `(special-operator-p ,name))

(defvar *startup-package-name* "ACL2")

(defmacro save-def (def-form)

; WARNING: We assume in function mf-len-outputs that the body of def-form (see
; below) evaluates to a single value.

; Consider a definition (save-def (defun name formals ... body)), where defun
; could be replaced by other macros that take the same arguments (like
; defun-one-output or defn1), and where body evaluates to a single value.  Then
; this macro executes the definition and saves (name formals ... body) as the
; 'acl2-saved-def property of name.  We use this property to obtain the raw
; Lisp definition of name for memoize-fn.

; This macro is intended only for raw Lisp definitions.  For definitions in the
; loop, we expect that cltl-def-from-name will give us the definition.

  (let ((name (cadr def-form))) ; (defunxxx name ...)
    `(progn ,def-form
            (setf (get ',name 'acl2-saved-def)
                  ',def-form))))

(defmacro defg (&rest r)

  "DEFG is a short name for DEFPARAMETER.  However, in Clozure Common
  Lisp (CCL) its use includes two promises: (1) never to locally bind
  the variable, e.g., with LET or LAMBDA, and (2) never to call
  MAKUNBOUND on the variable.  CCL uses fewer machine instructions to
  reference such a variable than an ordinary special, which may have a
  per-thread binding that needs to be locked up."

  #-ccl
  `(defparameter ,@r)
  #+ccl
  `(ccl::defstatic ,@r))

(defmacro defv (&rest r)

  "DEFV is a short name for DEFVAR.  However, in Clozure Common Lisp (CCL) its
  use includes two promises: (1) never to locally bind the variable, e.g., with
  LET or LAMBDA, and (2) never to call MAKUNBOUND on the variable.  CCL uses
  fewer machine instructions to reference such a variable than an ordinary
  special, which may have a per-thread binding that needs to be locked up.
  Unlike for DEFVAR, the second argument of DEFV is not optional.  But quoting
  the CCL documentation string for DEFSTATICVAR: ``Like DEFVAR, the initial
  value form is not evaluated if the variable is already BOUNDP.''"

  #-ccl
  `(defvar ,@r)
  #+ccl
  `(ccl::defstaticvar ,@r))

#+allegro
(setq excl::*warn-smp-usage*

; We turn off warnings for excl:without-interrupts, as per:
; Section 2.0, Deprecated macros,
; https://franz.com/support/documentation/current/doc/smp.htm.

      nil)

(defmacro without-interrupts (&rest forms)

; This macro prevents, in raw Lisp for underlying Common Lisp implementations
; where we know how to do this, the interrupting of evaluation of any of the
; given forms.  We expect this behavior to take priority over any enclosing
; call of with-interrupts.

; "Without-interrupts" typically means that there will be no interrupt from the
; Lisp system, including ctrl+c from the user or an interrupt from another
; thread/process.  (However, in GCL it may mean that one can still enter a
; break, although :q is disabled and :r should be issued in order to continue.)
; For an ACL2(p) example: if *thread1* is running (progn (without-interrupts
; (process0)) (process1)), then execution of (interrupt-thread *thread1*
; (lambda () (break))) will not interrupt (process0).

; But note that "without-interrupts" does not guarantee atomicity; for example,
; it does not mean "without-setq".

; Thanks to David Rager for initially contributing this function.

  #+ccl
  `(ccl:without-interrupts ,@forms)
  #+sbcl
  `(sb-sys:without-interrupts ,@forms)
  #+gcl
  (if (fboundp 'si::without-interrupts)
      `(si::without-interrupts ,@forms) ; Camm Maguire suggestion
    `(progn ,@forms))
  #+lispworks

; Lispworks decided to remove "without-interrupts" from their system, because
; its use has changed from meaning "atomic" to meaning "can't be interrupted by
; other threads or processes".  Thus, we use the new primitive,
; "with-interrupts-blocked".

  `(mp:with-interrupts-blocked ,@forms)
  #+allegro

; Excl:with-interrupts is deprecated in Allegro CL.  However, the documentation
; suggests (Section 2.0, Deprecated macros,
; https://franz.com/support/documentation/current/doc/smp.htm) that this is
; fine to use in single-process applications.

  `(excl:without-interrupts ,@forms)
  #+cmucl
  `(system:without-interrupts ,@forms)
  #-(or allegro ccl cmucl gcl lispworks sbcl)
  '(error "This Lisp implementation does not support ~s, which is used, for~%~
           example, to support certain atomic operations when installing an~%~
           ACL2 logical world.  One could define (without-interrupts ...) ~%~
           to be (progn ...), but think about whether that provides enough~%~
           support for those operations!"
          'without-interrupts))

(defmacro with-interrupts (&rest forms)

; This macro allows, in raw Lisp for underlying Common Lisp implementations
; where we know how to do this, the interrupting of evaluation of any of the
; given forms.  We expect this behavior to take priority over any enclosing
; call of without-interrupts.

  #+ccl
  `(ccl:with-interrupts-enabled ,@forms)
  #+sbcl
  `(sb-sys:with-interrupts ,@forms)
  #-(or ccl sbcl)

; Note that in GCL, si::without-interrupts (when implemented) disables :q but
; does not disable control-c.  So although there is no si::with-interrupts,
; probably no such utility is needed.

  `(progn ,@forms))

(defmacro unwind-protect-disable-interrupts-during-cleanup
  (body-form &rest cleanup-forms)

; As the name suggests, this is unwind-protect but with a guarantee that
; cleanup-form cannot be interrupted.  Note that CCL's implementation already
; disables interrupts during cleanup: here we quote CCL developer Gary Byers,
; from
; http://lists.clozure.com/pipermail/openmcl-devel/2013-September/010291.html.

;   Since UNWIND-PROTECT cleanup forms are effectively run with interrupts
;   disabled in CCL by default ....

; Thanks to David Rager for initially contributing this function.

  #+ccl
  `(unwind-protect ,body-form ,@cleanup-forms)
  #+lispworks
; See http://www.lispworks.com/documentation/lw60/LW/html/lw-808.htm for why we
; don't just use without-interrupts in the cleanup form here.
  `(hcl:unwind-protect-blocking-interrupts-in-cleanups ,body-form
                                                       ,@cleanup-forms)
  #-(or ccl lispworks)
  `(unwind-protect ,body-form (without-interrupts ,@cleanup-forms)))

(defvar *load-compiled-verbose* nil)

(defun load-compiled (filename &optional verbose)

; It may be useful to implement the maybe-verbose argument for Lisps that do
; not print a "loading" message.  For now, we comment out code below that would
; do this.

  (when (and verbose
             *load-compiled-verbose*)
    (eval `(format t "~&Note: loading file ~s.~&" ',filename)))
  #+clisp
  (let ((*readtable* *acl2-readtable-clisp-fas*))
    (declare (special *acl2-readtable-clisp-fas*))
    (load filename))
  #-clisp
  (load filename))

(defun make-lock (&optional lock-name)

; See also deflock.

; If lock-name is supplied, it must be nil or a string.

; Even though CCL nearly always uses a FIFO for threads blocking on a lock,
; it does not guarantee so: no such promise is made by the CCL
; documentation or implementor (in fact, we are aware of a race condition that
; would violate FIFO properties for locks).  Thus, we make absolutely no
; guarantees about ordering; for example, we do not guarantee that the
; longest-blocked thread for a given lock is the one that would enter a
; lock-guarded section first.  However, we suspect that this is usually the
; case for most implementations, so assuming such an ordering property is
; probably a reasonable heuristic.  We would be somewhat surprised to find
; significant performance problems in our own application to ACL2's parallelism
; primitives due to the ordering provided by the underlying system.

  #-(or ccl sb-thread lispworks)
  (declare (ignore lock-name))
  #+ccl (ccl:make-lock lock-name)
  #+sb-thread (sb-thread:make-mutex :name lock-name)
  #+lispworks (mp:make-lock :name lock-name)
  #-(or ccl sb-thread lispworks)

; We return nil in the uni-threaded case in order to stay in sync with lockp.

  nil)

(defmacro with-lock-raw (bound-symbol &rest forms)

; Grab the lock, blocking until it is acquired; evaluate forms; and then
; release the lock.  This macro guarantees mutual exclusion.

  #-(or ccl sb-thread lispworks)
  (declare (ignore bound-symbol))
  (let ((forms

; We ensure that forms is not empty because otherwise, in CCL alone,
; (with-lock some-lock) evaluates to t.  We keep the code simple and consistent
; by modifying forms here for all cases, not just CCL.

         (or forms '(nil))))
    #+ccl
    `(ccl:with-lock-grabbed (,bound-symbol) nil ,@forms)
    #+sb-thread
    `(sb-thread:with-recursive-lock (,bound-symbol) nil ,@forms)
    #+lispworks
    `(mp:with-lock (,bound-symbol) nil ,@forms)
    #-(or ccl sb-thread lispworks)
    `(progn ,@forms)))

; Through ACL2 Version_6.5, acl2-gentemp was defined in interface-raw.lisp.
; But since it is used in parallel-raw.lisp, we have moved it here in support
; of the toothbrush.
(defvar *acl2-gentemp-counter* 0)
(defun-one-output acl2-gentemp (root)
  (let ((acl2-pkg (find-package "ACL2")))
    (loop
     (let ((name (coerce (qfuncall packn1 (list root *acl2-gentemp-counter*))
                         'string)))
       (if (not (find-symbol name acl2-pkg))
           (return (let ((ans (intern name acl2-pkg)))
; See comment in intern-in-package-of-symbol for an explanation of this trick.
                     ans))
         (incf *acl2-gentemp-counter*))))))

; Subsection: type mfixnum

; We use the type mfixnum for counting things that are best counted in the
; trillions or more.  Mfixnums happen to coincide with regular fixnums on
; 64-bit CCL, and may be fixnums in other Lisps (e.g. SBCL 1.1.8 and, as
; confirmed by Camm Maguire Sept. 2014, in 64-bit GCL where fixnums are 64 bits
; long).

(defconstant most-positive-mfixnum

; Warning: In function internal-real-ticks, we rely on this value having a
; binary representation as a sequence of ones.

; This is more than 10^18, that is, more than a billion billions.  It seems
; reasonable to assume (at least in 2014 and for some years beyond) that any
; integer quantities that we accumulate, such as call counts, are less than
; that.  This number is also more than the (2*500,000,000)^2, which is the size
; of *memoize-call-array* when we have approximately 500 million memoized
; functions.  [Note: if a countable event, like a call, took just the time of
; the fastest single instruction on a 100GHz (!) machine, then counting up
; most-positive-mfixnum of them would take over 4 months.]

  (1- (expt 2 60)))

(deftype mfixnum ()
  `(integer ,(- -1 most-positive-mfixnum)
            ,most-positive-mfixnum))

(defmacro the-mfixnum (x)

; This silly macro may help someday in debugging, using code such as is found
; in the comment just below.  Of course, by adding an optional argument that
; specifies some sort of location for this call, we can get more specific
; debugging information.  Debugging could also be aided by replacing this with
; a corresponding defun, which could be traced.

; `(let ((x ,x))
;    (cond ((not (typep x 'fixnum))
;           (error "OUCH")))
;    (the mfixnum x))

  `(the mfixnum ,x))

(defun our-pwd ()

; This function was moved here from basis-a.lisp, in order to avoid a build
; error.

; Warning: Do not be tempted to use (getenv$-raw "PWD").  The PWD environment
; variable is not necessarily maintained, for example in Solaris/SunOS as one
; make invokes another make in a different directory.

  (qfuncall pathname-os-to-unix
            (our-truename "" "Note: Calling OUR-TRUENAME from OUR-PWD.")
            (get-os)
            *the-live-state*))

; The forms below were sent to us by Camm Maguire in February 2017, to fix an
; issue with GCL 2.6.12.  We use the progn wrapper to avoid breaking the reader
; in other Lisps.

#+gcl
(progn
compiler::
(defun c2funcall-new (funob args &optional loc info)

  ;;; Usually, ARGS holds a list of forms, which are arguments to the
  ;;; function.  If, however, the arguments are already pushed on the stack,
  ;;; ARGS should be set to the symbol ARGS-PUSHED.
  (case (car funob)
    (call-global (c2call-global (caddr funob) args loc t))
    (call-local (c2call-local (cddr funob) args))
    (call-lambda (c2call-lambda (caddr funob) args))
    (ordinary           ;;; An ordinary expression.  In this case, if
                        ;;; arguments are already pushed on the stack, then
                        ;;; LOC cannot be NIL.  Callers of C2FUNCALL must be
                        ;;; responsible for maintaining this condition.
      (let ((*vs* *vs*) (form (caddr funob)))
           (declare (object form))
           (cond ((and (listp args)
                       (< (length args) 12) ;FIXME fcalln1 limitation
                       *use-sfuncall*
                       ;;Determine if only one value at most is required:
                       (or
                        (member *value-to-go* '(return-object trash))
                        (and (consp *value-to-go*)
                             (member (car *value-to-go*) '(var cvar jump-false jump-true)))
                        (and info (equal (info-type info) '(values t)))
                        ))
                  (c2funcall-sfun form args info)
                  (return-from c2funcall-new nil)))
           (unless loc
             (unless (listp args) (baboon))
             (cond ((eq (car form) 'LOCATION) (setq loc (caddr form)))
                   ((and (eq (car form) 'VAR)
                         (not (args-info-changed-vars (caaddr form) args)))
                    (setq loc (cons 'VAR (caddr form))))
                   (t
                    (setq loc (list 'vs (vs-push)))
                    (let ((*value-to-go* loc)) (c2expr* (caddr funob))))))
           (push-args args)
           (if *compiler-push-events*
               (wt-nl "super_funcall(" loc ");")
             (if *super-funcall*
                 (funcall *super-funcall* loc)
               (wt-nl "super_funcall_no_event(" loc ");")))
           (unwind-exit 'fun-val)))
    (otherwise (baboon))
    ))

(when (or (< si::*gcl-major-version* 2)
          (and (= si::*gcl-major-version* 2)
               (or (< si::*gcl-minor-version* 6)
                   (and (= si::*gcl-minor-version* 6)
                        (<= si::*gcl-extra-version* 12)))))
  (setf (symbol-function 'compiler::c2funcall)
        (symbol-function 'compiler::c2funcall-new))))

#+gcl
(eval-when
    (compile load eval)
  (proclaim '(ftype (function (t t *) t) compiler::c2funcall-new)))
