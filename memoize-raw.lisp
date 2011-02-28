; ACL2 Version 4.2 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2011  University of Texas at Austin

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic
; NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

; memoize-raw.lisp -- Raw lisp definitions for memoization functions, only to
; be included in the experimental HONS version of ACL2.

; The original version of this file was contributed by Bob Boyer and
; Warren A. Hunt, Jr.  The design of this system of Hash CONS,
; function memoization, and fast association lists (applicative hash
; tables) was initially implemented by Boyer and Hunt.

(in-package "ACL2")


;; FEATURES

(eval-when (:execute :compile-toplevel :load-toplevel)

#-hons
(error "memoize-raw.lisp should only be included when #+hons is set.")

#+Clozure
(unless (> (parse-integer ccl::*openmcl-svn-revision* :junk-allowed t)
            13296)
  (fresh-line)
  (princ "Better use a version of CCL past revision 13295."))

(defparameter *faking-batch-flag* nil)

(defun live-terminal-p ()

  "(LIVE-TERMINAL-P) attempts to determine whether there
  is an active user terminal for this Lisp."

  #+Clozure
  (and (null (or *faking-batch-flag* ccl::*batch-flag*))
       (not (search "FILE"
                    (with-standard-io-syntax
                     (write-to-string *terminal-io*
                                      :escape nil
                                      :readably nil)))))
    #-Clozure t)

; #+Clozure (pushnew :parallel *features*)

; #+Clozure (pushnew :Sol *features*)

; One may comment out the following PUSHNEW and rebuild to get
; profiling times not based upon the curious and wondrous RDTSC
; instruction of some x86 processors.  On a machine with several
; cores, the RDTSC values returned by different cores may be slightly
; different, which could lead one into such nonsense as instructions
; apparently executing in negative time, when timing starts on one
; core and finishes on another.  To some extent we ignore such RDTSC
; nonsense, but we still can report mysterious results since we have
; no clue about which core we are running on in CCL.

  #+Clozure
  (when (fboundp 'ccl::rdtsc) (pushnew :RDTSC *features*))

)


;;;;;;;; UTILITIES ;;;;;;;; UTILITIES ;;;;;;;; UTILITIES
;;;;;;;; UTILITIES ;;;;;;;; UTILITIES ;;;;;;;; UTILITIES


; DEFG

(defmacro defg (&rest r)

  "DEFG is a short name for DEFPARAMETER.  However, in Clozure Common
  Lisp (CCL) its use includes two promises: (1) never to locally bind
  the variable, e.g., with LET or LAMBDA, and (2) never to call
  MAKUNBOUND on the variable.  CCL uses fewer machine instructions to
  reference such a variable than an ordinary special, which may have a
  per-thread binding that needs to be locked up."

  #-Clozure
  `(defparameter ,@r)
  #+Clozure
  `(ccl::defstatic ,@r))


(defmacro defv (&rest r)

  "DEFV is a short name for DEFVAR.  However, in Clozure Common Lisp
  (CCL) its use includes two promises: (1) never to locally bind the
  variable, e.g., with LET or LAMBDA, and (2) never to call MAKUNBOUND
  on the variable.  CCL uses fewer machine instructions to reference
  such a variable than an ordinary special, which may have a
  per-thread binding that needs to be locked up.  Unlike for DEFVAR,
  the second argument of DEFV is not optional."

  #-Clozure
  `(defparameter ,@r)
  #+Clozure
  `(ccl::defstaticvar ,@r))


; PROFILER-IF

; See also comments in SETUP-SMASHED-IF.

(defg *form-ht* (make-hash-table :test 'eq))

(defg *ignore-form-ht* (make-hash-table :test 'eq))

(declaim (hash-table *form-ht* *ignore-form-ht*))

(defmacro profiler-if (test true &optional false)

  "Semantically, PROFILER-IF is the same as IF.  However, the
  execution of the PROFILER-IF macro also puts the IF form into
  *IGNORE-FORM-HT* so that the compiler macro for IF will not consider
  'fixing' it with code to monitor which branch of the IF is taken.
  We use PROFILER-IF to avoid monitoring of code that we have
  introduced into the user's code for the purpose of profiling."

  (let ((val `(if ,test ,true ,false)))
    #+Clozure (setf (gethash val *ignore-form-ht*) t)
    val))

(defmacro profiler-cond (&rest r)
  (cond ((null r) nil)
        (t `(profiler-if ,(caar r)
                     (progn ,@(cdar r))
                     (profiler-cond ,@(cdr r))))))

(defmacro profiler-and (&rest r)
  (cond ((null r) t)
        ((null (cdr r)) (car r))
        (t `(profiler-if ,(car r)
                     (profiler-and ,@(cdr r))
                     nil))))

(defmacro profiler-or (&rest r)
  (cond ((null r) nil)
        ((null (cdr r)) (car r))
        (t (let ((temp (make-symbol "TEMP")))
             `(let ((,temp ,(car r)))
                (profiler-if ,temp
                         ,temp
                         (profiler-or ,@(cdr r))))))))

(defmacro profiler-when (test &rest r)
  `(profiler-if ,test (progn ,@r)))

(defmacro profiler-unless (test &rest r)
  `(profiler-if (not ,test) (progn ,@r)))

; PRINL

(defmacro prinl (&rest r)

  "PRINL is for debugging.  In general, PRINL PRIN1s the members of r
  followed by their values to *STANDARD-OUTPUT*.  The values are first
  followed by =>, to indicate evaluation.

  For example, (prinl a b (+ a b)) might print:  
    A => 1
    B => 2
    (+ A B) => 3
  PRINL returns the principal value of the last member of r.  PRINL
  does not evaluate the members of r that are neither symbols nor
  conses, but it does PRINC those members.  PRINL evalutes (oft ...)
  forms, but does not do the printing twice."

  (let ((tem (make-symbol "TEM"))
        (tem2 (make-symbol "TEM2")))
    `(our-syntax-nice
      (let ((,tem nil) (,tem2 nil))
        (declare (ignorable ,tem2))
        ,@(loop for x in r collect
                (cond
                 ((or (symbolp x)
                      (and (consp x) (not (eq (car x) 'oft))))
                  `(progn (oft "~&~:a =>~40t" ',x)
                          (setq ,tem ,x)
                          (cond ((integerp ,tem)
                                 (setq ,tem2 (ofn "~20:d" ,tem)))
                                ((floatp ,tem)
                                 (setq ,tem2 (ofn "~20,4f" ,tem)))
                                ((hash-table-p ,tem)
                                 (let ((l nil))
                                   (maphash (lambda (k v)
                                              (push (cons k v) l))
                                            ,tem)
                                   (setq l (nreverse l))
                                   (setq l (list* 'hash-table-size
                                                  (hash-table-size
                                                   ,tem)
                                                  l))
                                   (setq ,tem l)))
                                (t (setq ,tem2 (ofn "~a" ,tem))))
                          (cond ((and (stringp ,tem2)
                                      (< (length ,tem2) 40))
                                 (oft "~a" ,tem2))
                                (t (oft "~%  ")
                                   (prin1 ,tem *terminal-io*)))))
                 ((and (consp x) (eq (car x) 'oft)) x)
                 (t `(oft "~&~a" (setq ,tem ',x)))))
        ,tem))))

(defv *number-of-arguments-and-values-ht*
  (let ((ht (make-hash-table)))
    (declare (hash-table ht))
    (loop for pair in
      '((bad-lisp-objectp . (1 . 1))
        (apropos . (nil . 0))
        (aref . (nil . 1))
        (array-displacement . (1 . 2))
        (decode-float . (1 . 3))
        (expansion-alist-pkg-names-memoize . (1 . 1))
        (fchecksum-obj . (1 . 1))
        (worse-than . (2 . 1))
        (find-symbol . (nil . 2))
        (function . (nil . 1))
        (get-properties . (2 . 3))
        (gethash . (nil . 2))
        (integer-decode-float (1 . 3))
        (intern . (nil . 2))
        (lambda . (nil . 1))
        (list . (nil . 1))
        (list* . (nil . 1))
        (macroexpand . (nil . 2))
        (macroexpand-1 . (nil . 2))
        (pprint-dispatch  . (nil . 2))
        (prog1 . (nil . 1))
        (prog2 . (nil . 1))
        (quote . (1 . 1))) do
      (setf (gethash (car pair) ht)
            (cdr pair)))
    (loop for sym in
          '(car cdr caar cadr cdar cddr caaar cadar cdaar
            cddar caadr caddr cdadr cdddr caaaar cadaar cdaaar cddaar
            caadar caddar cdadar cdddar caaadr cadadr cdaadr cddadr
            caaddr cadddr cdaddr cddddr) do
            (setf (gethash sym ht) '(1 . 1)))
    ht)

  "The hash table *NUMBER-OF-ARGUMENTS-AND-VALUES-HT* maps a symbol fn
  to a cons pair (a . d), where a is the number of inputs and d is the
  number of outputs of fn.  NIL for a or d indicates 'don't know'.")

(declaim (hash-table *number-of-arguments-and-values-ht*))

(defun make-list-t (n) (make-list n :initial-element t))

(defmacro defn1 (f a &rest r)
  (when (intersection a lambda-list-keywords)
    (error "DEFN1: ** In the defintion of ~s, the argument list ~s ~
            contains a member of lambda-list-keywords so do not ~
            use defn1."
           f a))
  `(progn
     (setf (gethash ',f *number-of-arguments-and-values-ht*)
           (cons ,(length a) 1))
     (declaim (ftype (function ,(make-list-t (len a)) (values t)) ,f))
     (defun ,f ,a (declare (xargs :guard t)) ,@r)))

(defmacro defn1-one-output (f a &rest r)
  (when (intersection a lambda-list-keywords)
    (error "DEFN1-ONE-OUTPUT:  *** In the definition of ~s, the ~
            argument list ~s contains a member of ~
            lambda-list-keywords so do not use defn1-one-output."
           f a))
  `(progn
     (setf (gethash ',f *number-of-arguments-and-values-ht*)
           (cons ,(length a) 1))
     (declaim (ftype (function ,(make-list-t (len a)) (values t)) ,f))
     (defun-one-output ,f ,a (declare (xargs :guard t)) ,@r)))

(defmacro defn2 (f a &rest r)
  (when (intersection a lambda-list-keywords)
    (error "defn2: In the definition of ~s, the argument list ~s ~
               contains a member of lambda-list-keywords, so do ~
               not use defn2."
           f a))
  `(progn
     (setf (gethash ',f *number-of-arguments-and-values-ht*)
           (cons ,(length a) 2))
     (declaim (ftype (function ,(make-list-t (len a)) (values t t)) ,f))
     (defun ,f ,a (declare (xargs :guard t)) ,@r)))

(defmacro globlet (bindings &rest rest)

  "GLOBLET is reminiscent of LET.  It is intended to be used in CCL
  with variables that are introduced via DEFG or DEFV, i.e., may not
  be LET or LAMBDA bound.  UNWIND-PROTECT is used to try to make sure
  that the old value, which is assumed to exist, is restored."

  (unless
      (and (symbol-alistp bindings)
           (loop for pair in bindings always
                 (let ((var (car pair))
                       (d (cdr pair)))
                   (and (consp d)
                        (null (cdr d))
                        (not (constantp var))))))
    (ofe "GLOBLET: ** bad bindings ~a." bindings))
  (let ((vars (loop for b in bindings collect
                    (make-symbol (symbol-name (car b))))))
    `(let ,(loop for b in bindings as v in vars collect
                  (list v (car b)))
          (unwind-protect
              (progn (psetq
                      ,@(loop for b in bindings nconc
                              (list (car b) (cadr b))))
                     ,@rest)
            (psetq ,@(loop for b in bindings as v in vars nconc
                           (list (car b) v)))))))


; MFIXNUM

; We use the type mfixnum for counting things that are best counted in
; the trillions or more.

(defconstant most-positive-mfixnum (1- (expt 2 60)))

(deftype mfixnum ()
  `(integer ,(- -1 most-positive-mfixnum)
            ,most-positive-mfixnum))


; TIMING UTILITIES

; *float-ticks/second* is set correctly by HONS-INIT.

(defg *float-ticks/second* 1.0)

(defg *float-internal-time-units-per-second*
  (float internal-time-units-per-second))

(declaim (float *float-ticks/second*
                *float-internal-time-units-per-second*))

(defabbrev internal-real-time ()
  #+(and RDTSC (not 32-bit-target)) ; faster for 64
  (the mfixnum (ccl::rdtsc))
  #+(and RDTSC 32-bit-target) ; slower for 32
  (the mfixnum (mod (ccl::rdtsc64) most-positive-mfixnum))
  #-RDTSC (the mfixnum (mod (get-internal-real-time)
                            most-positive-fixnum)))

(defn1 float-ticks/second-init ()
  (setq *float-ticks/second*
        #+RDTSC
        (let ((i1 (ccl::rdtsc64))
              (i2 (progn (sleep .01) (ccl::rdtsc64))))
          (if (>= i2 i1)
              (* 100 (float (- i2 i1)))
            (error "(float-ticks/second-init).")))
        #-RDTSC
        *float-internal-time-units-per-second*)
  (check-type *float-ticks/second*
              (and float (satisfies plusp))))


; VERY-UNSAFE-INCF

(defmacro very-unsafe-incf (x inc &rest r)

; returns NIL !

  (declare (ignore r))
  (unless (symbolp x)
    (error "Do not use very-unsafe-incf on conses: ~a" x))
  `(locally (declare (type mfixnum ,x))
            (setq ,x
                  (the mfixnum (+ ,x
                                 (the mfixnum ,inc))))
            nil))

(defmacro very-very-unsafe-aref-incf (ar loc)
 `(setf (aref (the (simple-array mfixnum (*)) ,ar) ,loc)
        (the mfixnum (1+ (aref (the (simple-array mfixnum (*)) ,ar)
                              ,loc)))))


; WATCH

(defg *watch-file* nil
  "If *WATCH-FILE* is not NIL, it is a string that names the 'watch
  file', to which (WATCH-DUMP) prints.")

(defg *watch-string*
  (let ((ws (make-array 0 :element-type 'character
                        :adjustable t :fill-pointer t)))
    (setf (fill-pointer ws) 0)
    ws)
  "WATCH-DUMP first writes to the adjustable string *WATCH-STRING*
  and then prints to the *WATCH-FILE*.")

(declaim (type (array character (*)) *watch-string*))


; SAFE-INCF

(defmacro safe-incf (x inc &optional where)

  "SAFE-INCF is a raw Lisp macro that behaves the same as INCF when
  both X and INC are nonnegative MFIXNUMs and their sum is a
  nonnegative MFIXNUM.  In a call of (SAFE-INCF x inc), X must be a
  place that holds an MFIXNUM.  INC must evaluate to an MFIXNUM.  Both
  X and INC must evaluate without side effects, so that it is
  impossible to tell which was executed first or whether only one or
  both were executed.  If INC is not positive, no update takes place
  at all.  Otherwise, if the sum of the values of X and INC is not an
  MFIXNUM, which is tested without causing an error, a run-time error
  will be caused.  Else, if the sum is an MFIXNUM then, as with INCF,
  the place X will be set to hold the sum of the old value of that
  place and the value of INC.  The value returned by SAFE-INCF is NIL.
  Caution:  INC may be evaluated first, which is why side effects are
  prohibited.

  An optional third parameter is merely to help with error location
  identification.

  In (SAFE-INCF (AREF A (FOO)) INC), (FOO) is only evaluted once.
  Same for SVREF."

  (cond ((integerp inc)
         (if (<= inc 0)
             nil
           `(safe-incf-aux ,x ,inc ,where)))
        ((symbolp inc)
         `(profiler-if (>= 0 (the mfixnum ,inc))
                   nil
                   (safe-incf-aux ,x ,inc ,where)))
        (t (let ((incv (make-symbol "INCV")))
             `(let ((,incv (the mfixnum ,inc)))
                (declare (type mfixnum ,incv))
                (profiler-if (>= 0 ,incv)
                         nil
                         (safe-incf-aux ,x ,incv ,where)))))))

(defn1 safe-incf-aux-error (x inc where)
  (error "~%; SAFE-INCF-AUX: ** Error: ~a."
         (list :x x :inc inc :where where)))

(defmacro safe-incf-aux (x inc where)
  (profiler-cond
   ((not (or (symbolp inc)
             (profiler-and (< inc most-positive-mfixnum)
                           (> inc 0))))
    (safe-incf-aux-error x inc where))
   ((profiler-and (true-listp x)
              (equal (len x) 3)
              (member (car x) '(aref svref))
              (symbolp (nth 1 x))
              (consp (nth 2 x)))
    (let ((idx (make-symbol "IDX")))
      `(let ((,idx (the fixnum ,(nth 2 x))))
         (declare (type fixnum ,idx))
         (safe-incf (,(nth 0 x)
                     ,(nth 1 x)
                     ,idx)
                    ,inc
                    ',where))))
   (t (let ((v (make-symbol "V")))
        `(let ((,v (the mfixnum ,x)))
           (declare (type mfixnum ,v))
           (profiler-cond ((<= ,v (the mfixnum
                                    (- most-positive-mfixnum
                                       (the mfixnum ,inc))))
                  
                       (setf (the mfixnum ,x)
                             (the mfixnum (+ ,v (the mfixnum ,inc))))
                       nil)
                      (t (safe-incf-aux-error ',x ',inc
                                              ',where))))))))


;                               PARALLEL

; (pushnew :parallel *features*) causes a lot of locking that is of no
; value in a sequentially executing system.

; We have attempted to make honsing, memoizing, and Emod-compilation
; 'thread safe', whatever in hell that means, but we have no idea what
; we are really doing and are simply coding based upon what we feel is
; intuitive common sense.  Very subtle stuff.

(declaim (hash-table *compiled-module-ht* *memoize-info-ht*))

(defmacro unwind-mch-lock (&rest forms)

; Returns NIL.

  #+parallel
  (let ((v (make-symbol "V")))
    `(let ((,v nil))
       (unwind-protect
         (progn
           (ccl::lock-hash-table *compiled-module-ht*)
           (ccl::lock-hash-table *memoize-info-ht*)
           ,@forms
           (setq ,v t)
           nil)
         (ccl::unlock-hash-table *memoize-info-ht*)
         (ccl::unlock-hash-table *compiled-module-ht*)
         (unless ,v (error "unwind-mch-lock failure.")))))
  #-parallel
  `(progn ,@forms nil))

#+parallel
(unless (member :Clozure *features*)
  (error "We use CCL primitives for parallelism."))

; We limit our efforts at thread-safedness to locking/unlocking some
; hash tables.

(declaim (special *compiled-module-ht* *memoize-info-ht*))

; Lock order.  To avoid deadlock, we always lock HONS before COMPILED
; and COMPILED before MEMOIZE; we unlock in the exact reverse order.

; If there is a pons table for a memoized function, it may be locked
; and unlocked during the execution of that memoized function, to
; ponsing together new arguments to a multiple argument function.  It
; would be DEADLY if PONS could result in honsing, memoizing, or
; Emod-compiling.

(defmacro our-lock-unlock-ht1 (ht &rest r)
  (declare (ignorable ht))
  #+parallel
  `(progn (ccl::lock-hash-table ,ht)
          (prog1 ,@r
                 (ccl::unlock-hash-table ,ht)))
  #-parallel `(prog1 ,@ r))

(defmacro our-lock-unlock-hons1 (&rest r)
  ;; Was `(our-lock-unlock-ht1 *hons-str-ht* ,@r))
  `(progn ,@r))

(defmacro our-lock-unlock-compile1 (&rest r)
  `(our-lock-unlock-hons1
    (our-lock-unlock-ht1 *compiled-module-ht* ,@r)))

(defmacro our-lock-unlock-memoize1 (&rest r)
  `(our-lock-unlock-compile1
    (our-lock-unlock-ht1 *memoize-info-ht* ,@r)))

(defmacro our-lock-unlock-htmv1 (ht &rest r)
  (declare (ignorable ht))
  #+parallel
  `(progn (ccl::lock-hash-table ,ht)
     (multiple-value-prog1 ,@r
                           (ccl::unlock-hash-table ,ht)))
  #-parallel `(multiple-value-prog1 ,@r))

(defmacro our-lock-unlock-honsmv1 (&rest r)
  ;; Was `(our-lock-unlock-htmv1 *hons-str-ht* ,@r))
  `(progn ,@r))

(defmacro our-lock-unlock-compilemv1 (&rest r)
  `(our-lock-unlock-honsmv1
    (our-lock-unlock-htmv1 *compiled-module-ht* ,@r)))

(defmacro our-lock-unlock-memoizemv1 (&rest r)
  `(our-lock-unlock-compilemv1
    (our-lock-unlock-htmv1 *memoize-info-ht* ,@r)))


;  OUR-SYNTAX

(defg *print-pprint-dispatch-orig* *print-pprint-dispatch*)

(defmacro our-syntax (&rest args)

  "OUR-SYNTAX is similar to Common Lisp's WITH-STANDARD-IO-SYNTAX.
  The settings in OUR-SYNTAX are oriented towards reliable, standard,
  vanilla, mechanical reading and printing, and less towards human
  readability.

  Please, before changing the following, consider existing uses of
  this macro insofar as the changes might impact reliable, standard,
  vanilla, mechanical printing.  Especially consider
  COMPACT-PRINT-FILE.  Consider using OUR-SYNTAX-NICE."

; We use the *ACL2-PACKAGE* and the *ACL2-READTABLE* because we use
; them almost all the time in our code.

; Keep in sync with COMPACT-PRINT-STREAM.

  `(with-standard-io-syntax
    (setq *package*   *acl2-package*)
    (setq *readtable* *acl2-readtable*)
    ,@args))

(defmacro our-syntax-nice (&rest args)

; OUR-SYNTAX-NICE offers slightly more pleasant human readabilty.

  `(our-syntax
    (setq *print-case*                 :downcase)
    (setq *print-pretty*               t)
    (setq *print-readably*             nil)
    (setq *print-right-margin*         70)
    (setq *print-miser-width*          100)
    ,@args))

(defmacro our-syntax-brief (&rest args)

; Within OUR-SYNTAX-BRIEF printing may be greatly abbreviated.

  `(our-syntax-nice
    (setq *print-length* 10)
    (setq *print-level* 5)
    (setq *print-lines* 10)
    ,@args))

(defmacro ofd (&rest r) ; For writing to *debug-io*.
  `(progn (format *debug-io* ,@r) (force-output *debug-io*)))

(defv *hons-verbose* t)
(defg *ofv-note-printed* nil)
(defg *ofv-msg-list* nil)
(defg *ofe-msg-list* nil)
(defg *ofb-msg-list* nil)

(defun ofe (&rest r)  ; For writing to *error-output*; calls (error).
  (our-syntax-nice
   (format *error-output* "~%; ** Error:  ")
   (let ((*print-pretty* t)
         (*print-level* 4)
         (*print-length* 10)
         (*print-lines*  10))
     (apply #'format *error-output*
            (loop for x in r collect (abbrev x)))
     (force-output *terminal-io*)
     (force-output *error-output*)
     (force-output *standard-output*)
     (force-output *debug-io*)
     (clear-input *terminal-io*)
     (clear-input *standard-input*)
     (clear-input *debug-io*)
     (push (cons 'ofe r) *ofe-msg-list*)
     (error "~%; See *ofe-msg-list*."))))

(defun ofv (&rest r) ; For verbose but helpful info.
  (our-syntax-nice
   (when *hons-verbose*
     (format *debug-io* "~%; Aside:  ")
     (let ((*print-level* 3)
           (*print-length* 5)
           (*print-lines* 5))
       (let ((ab (loop for x in r collect (abbrev x))))
         (apply #'format *debug-io* ab)
         (when (loop for x in ab as y in r thereis (not (eq x y)))
           (push (cons 'ofv r) *ofv-msg-list*)
           (format *debug-io* "~%; See *ofv-msg-list*."))
         (unless *ofv-note-printed*
           (format *debug-io*
                   "~%; Aside:  (setq acl2::*hons-verbose* nil) to ~
                    suppress asides.")
           (setq *ofv-note-printed* t))))
     (force-output *debug-io*))))

(defun ofvv (&rest r) ; For very verbose but helpful info.
  (our-syntax-nice
   (when (and (integerp *hons-verbose*) (> *hons-verbose* 1))
     (format *debug-io* "~%; Aside:  ")
     (let ((*print-level* 3) (*print-length* 5) (*print-lines* 5))
       (let ((ab (loop for x in r collect (abbrev x))))
         (apply #'format *debug-io* ab)
         (when (loop for x in ab as y in r thereis (not (eq x y)))
           (push (cons 'ofv r) *ofv-msg-list*)
           (format *debug-io* "~%; See *ofv-msg-list*."))
         (unless *ofv-note-printed*
           (format *debug-io*
                   "~%; Aside:  (setq acl2::*hons-verbose* nil) ~
                    to suppress asides.")
           (setq *ofv-note-printed* t))))
     (force-output *debug-io*))))

(defmacro ofg (&rest r) ; For verbose gc info.
    `(when *hons-verbose*
       (format *debug-io* ,@r)
       (force-output *debug-io*)))

(defun ofw (&rest r) ; For writing to *debug-io*, with a warning.
  (our-syntax-nice
   (format *debug-io* "~%; ** Warning:  ")
   (apply #'format *debug-io* r)
   (force-output *debug-io*)))

(defun ofb (&rest r) ; For writing to *debug-io* and breaking.
  (our-syntax-nice
   (format *debug-io* "~%; ** Warning and break:  ")
   (let ((*print-level* 3) (*print-length* 5) (*print-lines* 6))
     (let ((ab (loop for x in r collect (abbrev x))))
       (apply #'format *debug-io* ab)
       (when (loop for x in ab as y in r thereis (not (eq x y)))
         (push (cons 'ofe r) *ofb-msg-list*)
         (format *error-output* "~%; See *ofb-msg-list*."))
       (force-output *debug-io*)
       (error "")))
   (break "ofb")))

(defmacro ofn (&rest r) ; For forming strings.
  `(our-syntax (format nil ,@r)))

(defn1 ofnum (n) ; For forming numbers.
  (check-type n number)
  (if (= n 0) (setq n 0))
  (our-syntax
   (cond ((typep n '(integer -99 999))
          (format nil "~8d" n))
         ((or (< -1000 n -1/100)
              (< 1/100 n 1000))
          (format nil "~8,2f" n))
         (t (format nil "~8,2e" n)))))

(defmacro ofni (&rest r) ; For forming symbols in package ACL2.
  `(our-syntax (intern (format nil ,@r) *acl2-package*)))

(defmacro ofnm (&rest r) ; For forming uninterned symbols.
  `(our-syntax (make-symbol (format nil ,@r))))

(defmacro oft (&rest r) ; For writing to *standard-output*.
  `(progn (format t ,@r) (force-output *standard-output*)))

(defmacro ofto (&rest r) ; For writing to *terminal-io*
  `(progn (format *terminal-io* ,@r)
          (force-output *terminal-io*)))

(defmacro oftr (&rest r) ; For writing to *trace-output*.
  `(progn (format *trace-output* ,@r) (force-output *trace-output*)))

(defn1 suffix (str sym)
  (check-type str string)
  (check-type sym symbol)
  (let ((spkn (package-name (symbol-package sym)))
        (sn (symbol-name sym)))
    (ofn "~s,~s,~s" str spkn sn)))

(defn looking-at (str1 str2 &key (start1 0) (start2 0))

;  (LOOKING-AT str1 str2 :start1 s1 :start2 s2) is non-NIL if and only
;  if string STR1, from location S1 to its end, is an initial segment
;  of string STR2, from location S2 to its end.

  (unless (typep str1 'simple-base-string)
    (ofe "looking at:  ~a is not a string." str1))
  (unless (typep str2 'simple-base-string)
    (ofe "looking at:  ~a is not a string." str2))
  (unless (typep start1 'fixnum)
    (ofe "looking at:  ~a is not a fixnum." start1))
  (unless (typep start2 'fixnum)
    (ofe "looking at:  ~a is not a fixnum." start2))
  (locally
    (declare (simple-base-string str1 str2)
             (fixnum start1 start2))
    (let ((l1 (length str1)) (l2 (length str2)))
      (declare (fixnum l1 l2))
      (loop
       (when (>= start1 l1) (return t))
       (when (or (>= start2 l2)
                 (not (eql (char str1 start1)
                           (char str2 start2))))
         (return nil))
       (incf start1)
       (incf start2)))))

(defn1 meminfo (pat)

;  General comment about PROBE-FILE.  PROBE-FILE, according to Gary
;  Byers, may reasonably cause an error.  He is undoubtedly right.  In
;  such cases, however, Boyer generally thinks and wishes that it
;  returned NIL, and generally, therefore, ensconces a PROBE-FILE
;  within an IGNORE-ERROR in his code.

  (or
   (and
    (ignore-errors (probe-file "/proc/meminfo"))
    (with-standard-io-syntax
     (with-open-file (stream "/proc/meminfo")
       (let (line)
         (loop while (setq line (read-line stream nil nil)) do
               (when (looking-at pat line)
                 (return
                  (values
                   (read-from-string line nil nil
                                     :start (length pat))))))))))
   0))

(defn1 physical-memory () (meminfo "MemTotal:"))


; NUMBER OF ARGS AND RETURN VALUES

(defn1 input-output-number-warning (fn)
  (ofn "What is the number of inputs and output of ~a, please? ~
        ~%; To assert that ~a takes, say, 2 inputs and returns 1 ~
        output, do ~% (setf (gethash '~a ~
        acl2::*number-of-arguments-and-values-ht*) (cons 2 1))."
       fn fn fn))

(defn1 input-output-number-error (fn)
  (ofd (input-output-number-warning fn))
  (ofe "input-output-number-error: **: ~a" fn))

(defn1 number-of-arguments (fn)

; A NIL value returned by NUMBER-OF-ARGUMENTS means 'don't know'.

  (let* ((state *the-live-state*)
         (w (w state))
         (pair (gethash fn *number-of-arguments-and-values-ht*)))
    (cond
     ((not (symbolp fn)) nil)
     ((and (consp pair) (integerp (car pair))) (car pair))
     ((let ((formals (getprop fn 'formals t 'current-acl2-world w)))
        (and (not (eq t formals))
             (length formals))))
     ((not (fboundp fn)) nil)
     ((macro-function fn) nil)
     ((special-operator-p fn) nil)
     #+Clozure
     ((multiple-value-bind (req opt restp keys)
          (ccl::function-args (symbol-function fn))
        (and (null restp)
             (null keys)
             (integerp req)
             (eql opt 0)
             req)))
     (t nil))))

(defn1 number-of-return-values (fn)

; A NIL value returned by NUMBER-OF-RETURN-VALUES means 'don't know'.

  (let*
    ((pair (gethash fn *number-of-arguments-and-values-ht*))
     (state *the-live-state*)
     (w (w state)))
    (cond
     ((not (symbolp fn)) nil)
     ((and (consp pair) (integerp (cdr pair))) (cdr pair))
     ((member fn '(let let* mv-let progn if return-last))
      (ofe "number-of-return-values: It is curious to ask about ~
            'the' number of return values of ~a because the answer ~
            is that it depends."
           fn))
     ((not (eq t (getprop fn 'formals t 'current-acl2-world w)))
      (len (stobjs-out fn w))))))

(defn1 event-number (fn)
  (cond ((symbolp fn)
         (fgetprop fn 'absolute-event-number t (w *the-live-state*)))
        (t (ofe "EVENT-NUMBER: ** ~a is not a symbol ~s." fn))))

;;;;;;;; HONS ;;;;;;;; HONS ;;;;;;;; HONS ;;;;;;;; HONS ;;;;;;;; HONS
;;;;;;;; HONS ;;;;;;;; HONS ;;;;;;;; HONS ;;;;;;;; HONS ;;;;;;;; HONS


(defconstant *empty-ht* (make-hash-table)
  
  "Sometimes when a variable, say V, has been declared to be a hash
  table and we are about to rebuild it, we may temporarily set V to
  *EMPTY-HT* for purposes of garbage collection.")

(declaim (hash-table *empty-ht*))

; HONS VARIABLES, MACROS, AND DATA STRUCTURES

; Gary Byers recalls Lisp folklore that alists are faster than hash
; tables up to length 18.

(defconstant *start-car-ht-size*            18)

; The following DEFV for *MHT-DEFAULT-SIZE* may seem to duplicate what
; is in hons.lisp for *MHT-DEFAULT-SIZE*, but the DEFV makes
; *MHT-DEFAULT-SIZE* 'static' in CCL, so access is faster than to
; an ordinary special, such as DEFPARAMETER introduces.

(defv *mht-default-size* 60)

(defv *mht-default-rehash-size*             1.5)

(defv *mht-default-rehash-threshold*        0.7)

(defv *mht-default-shared* nil)

(declaim (type fixnum *start-car-ht-size* *mht-default-size*))
(declaim (float *mht-default-rehash-size* *mht-default-rehash-threshold*))

(defn mht (&key (test         'eql)
                (size         *mht-default-size*)
                (shared       *mht-default-shared*)
                (rehash-size  *mht-default-rehash-size*)
                (rehash-threshold *mht-default-rehash-threshold*)
                (weak         nil))
  (declare (ignorable shared weak))
  (make-hash-table :test             test
                   :size             size
                   :rehash-size      rehash-size
                   :rehash-threshold rehash-threshold
                   #+Clozure :weak
                   #+Clozure weak
                   #+Clozure :shared
                   #+Clozure *mht-default-shared*))

(defparameter *count-pons-calls*                   t
  "If *COUNT-PONS-CALLS*, then each call of PONS increments
  *PONS-CALL-COUNTER* by 1, and each call of PONS that does not find
  the desired PONS to already exist increments *PONS-MISSES-COUNTER*
  by 1.

  Warning:  because the hons and/or pons call and hit counters may not
  be protected by locks, hons and/or pons call/hit info is remotely
  possibly somewhat low.")

(defparameter *hons-report-discipline-failure* 'break)

(declaim (hash-table *compact-print-file-ht*))
(declaim (type mfixnum *pons-call-counter* *pons-misses-counter*))

(defg *hons-call-counter* 0)
(defg *hons-misses-counter* 0)

; Definition. ***** means 'Do not call this function unless you are
; sure that a superior caller in this thread has the lock on
; *HONS-STR-HT*.



(defun hons-report-discipline-failure-message ()
  (ofd
   "
          You may ignore this 'discipline' warning.

   There is nothing wrong except that some calls to HONS-GET may be
   executing slower than you would like or might assume.  You may do

      (setq *hons-report-discipline-failure* nil)

   in raw Lisp to avoid seeing such messages.  Why the warning?  When
   a concrete alist, say X, has been formed with calls to HONS-ACONS,
   and is currently secretly backed by a hash table, and then some new
   concrete object, say Y, is formed by HONS-ACONSing something
   concrete on to X, the hash table of X is 'stolen' to support Y.
   HONS-GET on X will then be possibly much slower, calling
   ASSOC-EQUAL instead of a GETHASH.

   "))

(defmacro maybe-report-discipline-failure (fn args)
  (cond
   (*hons-report-discipline-failure*
    `(cond
      ((eq *hons-report-discipline-failure* 't)
       (ofd "~&; Warning: ~s discipline failure on args:~% ~s~%"
            ',fn ,args)
       (hons-report-discipline-failure-message))
      ((eq *hons-report-discipline-failure* 'break)
       (hons-report-discipline-failure-message)
       (break "~&; Break: ~s discipline failure on args:~% ~s~%"
              ',fn ,args)
       nil)))))


;  WATCH-IF

(defg *if-counter* -1)

(declaim (type (integer -1 1152921504606846975) *if-counter*))

(defg *if-true-array* (make-array 2000
                                  :element-type
                                  '(integer -1 1152921504606846975)
                                  :initial-element -1))

(defg *if-false-array* (make-array 2000
                                   :element-type
                                   '(integer -1 1152921504606846975)
                                   :initial-element -1))

(declaim (type (simple-array (integer -1 1152921504606846975) (*))
               *if-true-array* *if-false-array*))


; HONS INVARIANTS

; If A and B are consp+honsp, then (eq A B) iff (equal A B).  The car
; of a consp+honsp is an atom or a consp+honsp.  The cdr of a
; consp+honsp is an atom or a consp+honsp.  No consp+honsp is
; circular.  If a string occurs in any consp+honsp, then no other
; EQUAL but not EQ version of that string occurs in any consp+honsp.

; Here are some basic data structures for honsing and memoizing.  Some
; of these are significantly expanded in size later by hons-init, but
; there is no reason to clog up saved images with large empty versions
; of them.

; HONS FUNCTIONS

(defn1 assoc-no-error-at-end (x l)

; We assume that every element of L is CONSP.

  (if (typep x '(or cons symbol (and array string)))
      (loop (if (consp l)
                (let ((al (car l)))
                  (if (eq x (car al))
                      (return al)
                    (setq l (cdr l))))
              (return nil)))
    (loop (if (consp l)
              (let ((al (car l)))
                (if (eql x (car al))
                    (return al)
                  (setq l (cdr l))))
            (return nil)))))

(defn1 too-long (x n)
  (declare (type fixnum n))

; (TOO-LONG x n) == (> (LENGTH x) n) provided x a noncircular list and
; n is a nonnegative fixnum.  TOO-LONG is perhaps faster than LENGTH
; because (a) LENGTH has to worry about its argument being a circular
; list, (b) LENGTH may worry about the answer exceeding
; MOST-POSITIVE-FIXNUM, and (c) LENGTH must consider the possibility
; that its argument is a vector.
  
  (loop (cond ((atom x) (return nil))
              ((eql n 0) (return t))
              (t (setq x (cdr x))
                 (setq n (the fixnum (1- n)))))))

#+Clozure
(defn1 mis-ordered-commutative-args (x y)
  (cond ((eql x y) nil)
        (t (let ((idx (or (ccl::%staticp x)
                          (and (typep x 'fixnum) x))))
             (cond (idx
                    (let ((idy (or (ccl::%staticp y)
                                   (and (typep y 'fixnum) y))))
                      (cond (idy (< (the fixnum idy)
                                    (the fixnum idx)))
                            ((rationalp y)
                             (< y (the fixnum idx))))))
                   ((rationalp x)
                    (let ((idy (or (ccl::%staticp y)
                                   (and (typep y 'fixnum) y))))
                      (cond (idy (< (the fixnum idy)
                                    x))
                            ((rationalp y)
                             (< y x))))))))))

(defn1 integer-pair (x y)
  (let ((z (+ x y)))
    (+ (/ (* z (1+ z)) 2) y)))



(defn1 our-gc ()

  "At least in Clozure Common Lisp, (OUR-GC) does not return until the
  garbage collection invoked, via GC$, is finished.  This is important
  for WASH-HONSES.  In Clozure, a call of CCL::GC may not complete a
  garbage collection, but merely request one, which is then carried
  out later on, by a separate process."

  #+Clozure
  (let ((current-gcs (ccl::full-gccount)))
    (gc$)
    (loop (when (> (ccl::full-gccount) current-gcs) (return))
          (sleep 1)
          (ofvv "Sleeping while waiting for a GC to finish.")))
  #+Closure
  (gc$))




;;;;;;;;;; MEMOIZE ;;;;;;;;;; MEMOIZE ;;;;;;;;;; MEMOIZE ;;;;;;;;;;
;;;;;;;;;; MEMOIZE ;;;;;;;;;; MEMOIZE ;;;;;;;;;; MEMOIZE ;;;;;;;;;;

;  MEMOIZE VARIABLES, MACROS, AND DATA STRUCTURES

(defv *never-profile-ht*
  (let ((h (make-hash-table :test 'eq)))
    (loop for x in
          '(bytes-used
            memoize-summary
            memoize-summary-after-compute-calls-and-times
            watch-dump
            #+rdtsc ccl::rdtsc
            * 
            + 
            - 
            < 
            <= 
            = 
            > 
            >= 
            abort 
            adjoin 
            adjust-array 
            allocate-instance 
            append 
            apply 
            apropos 
            apropos-list 
            aref 
            arrayp 
            assoc 
            assoc-if 
            assoc-if-not 
            atan 
            atom 
            bit 
            bit-and 
            bit-andc1 
            bit-andc2 
            bit-eqv 
            bit-ior 
            bit-nand 
            bit-nor 
            bit-not 
            bit-orc1 
            bit-orc2 
            bit-xor 
            break 
            butlast 
            car 
            cdr 
            ceiling 
            cerror 
            change-class 
            char-equal 
            char-greaterp 
            char-lessp 
            char-not-equal 
            char-not-greaterp 
            char-not-lessp 
            char/= 
            char< 
            char<= 
            char= 
            char> 
            char>= 
            clear-input 
            clear-memoize-tables 
            clear-output 
            compile 
            compile-file 
            compile-file-pathname 
            compiler-macro-function 
            complex 
            compute-restarts 
            concatenate 
            continue 
            copy-pprint-dispatch 
            copy-readtable 
            copy-symbol 
            count 
            count-if 
            count-if-not 
            decode-universal-time 
            delete 
            delete-duplicates 
            delete-if 
            delete-if-not 
            describe 
            digit-char 
            digit-char-p 
            directory 
            dribble 
            ed 
            encode-universal-time 
            enough-namestring 
            ensure-directories-exist 
            ensure-generic-function 
            eq 
            eql 
            error 
            eval 
            every 
            export 
            fboundp 
            fceiling 
            ffloor 
            file-position 
            fill 
            find 
            find-class 
            find-if 
            find-if-not 
            find-method 
            find-restart 
            find-symbol 
            finish-output 
            fixnum-to-symbol 
            float 
            float-sign 
            floor 
            force-output 
            format 
            fresh-line 
            fround 
            ftruncate 
            funcall 
            gensym 
            gentemp 
            get 
            get-dispatch-macro-character 
            get-internal-real-time 
            get-internal-run-time 
            get-macro-character 
            get-properties 
            get-setf-expansion 
            getf 
            gethash 
            if 
            import 
            initialize-instance 
            intern 
            internal-real-time 
            intersection 
            invalid-method-error 
            invoke-restart 
            last 
            ld-fn 
            len 
            len1 
            length 
            lisp-implementation-type 
            list 
            list* 
            listen 
            load 
            log 
            macro-function 
            macroexpand 
            macroexpand-1 
            make-array 
            make-broadcast-stream 
            make-concatenated-stream 
            make-condition 
            make-dispatch-macro-character 
            make-hash-table 
            make-instance 
            make-list 
            make-load-form 
            make-load-form-saving-slots 
            make-package 
            make-pathname 
            make-random-state 
            make-sequence 
            make-string 
            make-string-input-stream 
            make-string-output-stream 
            map 
            map-into 
            mapc 
            mapcan 
            mapcar 
            mapcon 
            mapl 
            maplist 
            max 
            member 
            member-if 
            member-if-not 
            memoize-call-array-grow 
            memoize-eval-compile 
            memoize-fn 
            merge 
            merge-pathnames 
            method-combination-error 
            mf-1st-warnings 
            mf-2nd-warnings 
            mf-warnings 
            mismatch 
            muffle-warning 
            nbutlast 
            nconc 
            nintersection 
            no-applicable-method 
            no-next-method 
            not 
            notany 
            notevery 
            nset-difference 
            nset-exclusive-or 
            nstring-capitalize 
            nstring-downcase 
            nstring-upcase 
            nsublis 
            nsubst 
            nsubst-if 
            nsubst-if-not 
            nsubstitute 
            nsubstitute-if 
            nsubstitute-if-not 
            null 
            nunion 
            open 
            pairlis 
            parse-integer 
            parse-namestring 
            pathname-device 
            pathname-directory 
            pathname-host 
            pathname-name 
            pathname-type 
            peek-char 
            position 
            position-if 
            position-if-not 
            pprint 
            pprint-dispatch 
            pprint-fill 
            pprint-indent 
            pprint-linear 
            pprint-newline 
            pprint-tab 
            pprint-tabular 
            prin1 
            princ 
            princ-to-string 
            print 
            print-object 
            profile 
            profile-acl2 
            profile-all 
            random 
            rassoc 
            rassoc-if 
            rassoc-if-not 
            read 
            read-byte 
            read-char 
            read-char-no-hang 
            read-delimited-list 
            read-from-string 
            read-line 
            read-preserving-whitespace 
            read-sequence 
            reduce 
            reinitialize-instance 
            remove 
            remove-duplicates 
            remove-if 
            remove-if-not 
            rename-file 
            rename-package 
            replace 
            require 
            room 
            round 
            sbit 
            search 
            set-difference 
            set-dispatch-macro-character 
            set-exclusive-or 
            set-macro-character 
            set-pprint-dispatch 
            set-syntax-from-char 
            shadow 
            shadowing-import 
            shared-initialize 
            signal 
            signum 
            slot-missing 
            some 
            sort 
            stable-sort 
            store-value 
            string-capitalize 
            string-downcase 
            string-equal 
            string-greaterp 
            string-lessp 
            string-not-equal 
            string-not-greaterp 
            string-not-lessp 
            string-upcase 
            string/= 
            string< 
            string<= 
            string= 
            string> 
            string>= 
            stringp 
            sublis 
            subseq 
            subsetp 
            subst 
            subst-if 
            subst-if-not 
            substitute 
            substitute-if 
            substitute-if-not 
            subtypep 
            svref 
            symbol-to-fixnum 
            symbol-to-fixnum-create 
            symbolp 
            sync-memoize-call-array 
            sync-watch-array 
            terpri 
            time-of-last-watch-update
            time-since-watch-start
            translate-logical-pathname
            translate-pathname 
            tree-equal 
            true-listp 
            truncate 
            typep 
            unexport 
            unintern 
            union 
            unread-char 
            unuse-package 
            update-instance-for-different-class 
            update-instance-for-redefined-class 
            upgraded-array-element-type 
            upgraded-complex-part-type 
            use-package 
            use-value 
            user-homedir-pathname 
            values 
            vector-push-extend 
            warn 
            watch-array-grow 
            wild-pathname-p 
            write 
            write-byte 
            write-char 
            write-line 
            write-sequence 
            write-string 
            write-to-string 
            y-or-n-p 
            yes-or-no-p)
          do (setf (gethash x h) t))
    h))

(declaim (hash-table *never-profile-ht*))

;  recording vars

; To minimize metering overhead costs, one may set these "*RECORD-"
; variables to NIL before memoizing.

; *RECORD-BYTES* and other *RECORD-...* variables are bound in
; REMEMOIZE-ALL, so we use DEFPARAMETER rather than DEFG.

(defparameter *record-bytes*
  (and (member :Clozure *features*)
       (> most-positive-fixnum (expt 2 32)))
  "In 64-bit Clozure Common Lisp, if *RECORD-BYTES* is not NIL when a
  function is memoized, we keep track of heap bytes allocated during
  calls of that function.")

(defparameter *record-calls* t
  "If *RECORD-CALLS* when a function is memoized,
  we count all calls of the function.")

(defparameter *record-hits* t
  "If *RECORD-HITS* is not NIL when a function is memoized, we count
  the number of times that a previously computed answer is used
  again.")

(defparameter *record-hons-calls* t
  "If *RECORD-HONS-CALLS* in not NIL a function is memoized, HONS
  calls are counted.")

(defparameter *record-mht-calls* t
  "If *RECORD-HONS-CALLS* is not NIL at the time a function is
  memoized, we record the number of times that a memo hash-table for
  the function was is counted.")

(defparameter *record-pons-calls* t
  "If *RECORD-PONS-CALLS* is not NIL at the time a function is
  memoized, pons calls are counted.")

(defparameter *record-time* t
  "If *RECORD-TIME* is not NIL the time a function is memoized, we
  record the elapsed time for each outermost call of the function.")


;  reporting vars

(defv *report-bytes* #+Clozure t #-Clozure nil
  "If *REPORT-BYTES* is not NIL, then MEMOIZE-SUMMARY prints the
  number of bytes allocated on the heap.")

(defv *report-calls* t
  "If *REPORT-CALLS* is not NIL, MEMOIZE-SUMMARY prints the number of
  calls.")

(defv *report-calls-from* t
  "If *REPORT-CALLS-FROM* is not NIL, MEMOIZE-SUMMARY prints which
functions called a function, how many times, and how long the calls
took.")

(defv *report-calls-to* t
  "If *REPORT-CALLS-TO* is not NIL, MEMOIZE-SUMMARY prints which
functions were called by given function, how many times, and how long
the calls took.")

(defv *report-hits* t
  "If *REPORT-HITS* is not NIL, MEMOIZE-SUMMARY prints the number of
  times that a previously computed answer was reused.")

(defv *report-hons-calls* t
  "If *REPORT-HONS-CALLS* is not NIL, then MEMOIZE-SUMMARY prints the
  number of times that hons was called.")

(defv *report-mht-calls* t
  "If *REPORT-MHT-CALLS* is not NIL, then MEMOIZE-SUMMARY prints the
  number of times that a memo hash-table for the function was created.
  This may be of interest to those who memoize functions that deal in
  changing stobjs; the memoization machinery sometimes 'forgets' an
  entire memoization hash table out of an abundance of caution, and
  then may later need to create it afresh.")

(defv *report-pons-calls* t
  "If *REPORT-PONS-CALLS* is not NIL, MEMOIZE-SUMMARY prints the
  number of calls of PONS.")

(defv *report-time* t
  "If *REPORT-TIME* is not NIL, MEMOIZE-SUMMARY prints the total time
  used to compute the outermost calls.")

(defv *report-on-memo-tables* t
  "If *REPORT-ON-MEMO-TABLES* is not NIL, MEMOIZE-SUMMARY prints
  information about memo tables.")

(defv *report-on-pons-tables* t
  "If *REPORT-ON-PONS-TABLES* is not NIL, MEMOIZE-SUMMARY prints
  information about pons tables.")

(defv *report-ifs* t
  "If *REPORT-ON-IFS* is not NIL, information about IF coverage is
  printed for those functions memoized with :WATCH-IFS option T.")

; counters

(defg *pons-call-counter* 0)

(defg *pons-misses-counter* 0)

(defmacro maybe-count-pons-calls ()
  (and *count-pons-calls*
       '(safe-incf *pons-call-counter* 1 maybe-count-pons-calls)))

(defmacro maybe-count-pons-misses ()
  (and *count-pons-calls*
       '(safe-incf *pons-misses-counter* 1 maybe-count-pons-misses)))

; array and hash-tables

(defg *memoize-info-ht* (mht))

(defg *memoize-call-array*
  (make-array 1 :element-type 'mfixnum :initial-element 0)
  
  "*MEMOIZE-CALL-ARRAY*, 'ma' for short, is used for storage of the
  monitoring information for memoized functions.  ma has as its length
  4 times the square of the maximum number of memoized functions.

  ma is initialized in MEMOIZE-INIT.  Think of ma as a two dimensional
  array with dimensions (twice the max number of memoized functions) x
  (twice the max number of memoized functions).  Each 'column'
  corresponds to info about a memoized function, but the first five
  columns are 'special'.  We count rows and columns starting at 0.
  Column 0 is used as scratch space by COMPUTE-CALLS-AND-TIMES for
  sums across all functions.  Columns 1, 2, and 3 are not currently
  used at all.  Column 4 is for the anonymous 'outside caller'.
  Column 5 is for the first memoized function.  In columns 5 and
  greater, row 0 is used to count 'bytes', 1 'hits', 2 MHT calls, 3
  HONS calls, and 4 PONS calls.

  The elements of an ma column starting at row 10 are for counting and
  timing info.  Suppose column 7 corresponds to the memoized function
  FOO and column 12 corresponds to the memoized function BAR.
  Whenever FOO calls BAR, element 2*12 of column 7 will be incremented
  by 1, and the total elapsed time for the call will be added to
  element 2*12+1 of column 7.

  Though ma may 'grow', it may not grow while any memoized function is
  running, and here is why: every memoized function has a cached
  opinion about the size of ma.  To avoid an abort during a call of
  MEMOIZE one may call (MEMOIZE-HERE-COME n) to assure that ma has
  room for at least n more memoized functions.")

(defg *compute-array* (make-array 0)
  
  "*COMPUTE-ARRAY*, ca for short, is an array of proper lists.  At the
  end of a call of COMPUTE-CALLS-AND-TIMES, which is called by
  MEMOIZE-SUMMARY, (aref ca n) will contain the numbers of the
  functions that have called the function numbered n.")

(declaim (type (simple-array t (*)) *compute-array*))

(eval-when
 #-cltl2
 (load eval)
 #+cltl2
 (:load-toplevel :execute)
 (proclaim `(type (simple-array mfixnum
                                (*)) *memoize-call-array*)))

(defv *initial-max-memoize-fns* 500)

(defg *2max-memoize-fns* (* 2 *initial-max-memoize-fns*))

(defconstant *ma-bytes-index*       0)

(defconstant *ma-hits-index*        1)

(defconstant *ma-mht-index*         2)

(defconstant *ma-hons-index*        3)

(defconstant *ma-pons-index*        4)

(defconstant *ma-initial-max-symbol-to-fixnum* 4)

(defg *max-symbol-to-fixnum* *ma-initial-max-symbol-to-fixnum*)

(declaim (type fixnum
               *max-symbol-to-fixnum*
               *initial-2max-memoize-fns*
               *ma-initial-max-symbol-to-fixnum*
               *2max-memoize-fns*))

; for initialization

(defg *memoize-init-done* nil)


; locals used in memoize-on and memoize-off

(defconstant *mo-f* (make-symbol "F"))

(defconstant *mo-h* (make-symbol "H"))

(defconstant *mo-o* (make-symbol "O"))


; locals used in functions generated by memoize-fn

(defconstant *mf-old-caller* (make-symbol "OLD-CALLER"))

(defconstant *mf-start-hons* (make-symbol "START-HONS"))

(defconstant *mf-start-pons* (make-symbol "START-PONS"))

(defconstant *mf-start-bytes* (make-symbol "START-BYTES"))

(defconstant *mf-ans* (make-symbol "ANS"))

(defconstant *mf-ans-p* (make-symbol "ANS-P"))

(defconstant *mf-ma* (make-symbol "MA"))

(defconstant *mf-args* (make-symbol "ARGS"))

(defconstant *mf-2mmf* (make-symbol "MF-2MMF"))

(defconstant *mf-2mmf-fnn* (make-symbol "MF-2MMF-FNN"))

(defconstant *mf-count-loc* (make-symbol "MF-COUNT-LOC"))

(defconstant *mf-cl-error-msg*
  "~%; Redefining a function in the COMMON-LISP package ~
   is forbidden.")

(defg *caller* (* *ma-initial-max-symbol-to-fixnum*
                  *2max-memoize-fns*)
  "When memoized functions are executing in parallel, the value of
  *CALLER* and of statistics derived therefrom may be meaningless and
  random.")

(declaim (type fixnum *caller*))

; The :CONDITION parameter of MEMOIZE-FN can either be T, or a
; function symbol defined by the user within the ACL2 loop, or a LISTP
; (CONSP or NIL).  In the last case we think of the condition as an
; expression in the formals of FN.  If the :INLINE parameter T, then
; the body of FN is placed inline in the memoized definition;
; otherwise, a funcall of the original function is placed there.

(defv *profile-reject-ht*
  (let ((ht (mht :test 'eq)))
    (loop for sym in
          '(ld-fn0
            protected-eval
            hons-read-list-top
            hons-read-list
            raw-ev-fncall
            read-char$
            1-way-unify
            hons-copy1
            grow-static-conses
            bytes-used
            lex->
            gc-count
            outside-p
            shorten
            date-string
            strip-cars1
            short-symbol-name
            hons-calls
            memoize-condition
            1-way-unify-top
            absorb-frame
            access-command-tuple-number
            access-event-tuple-depth
            access-event-tuple-form
            access-event-tuple-number
            accumulate-ttree-into-state
            acl2-macro-p
            acl2-numberp
            add-car-to-all
            add-cdr-to-all
            add-command-landmark
            add-event-landmark
            add-g-prefix
            add-literal
            add-literal-and-pt
            add-name
            add-new-fc-pots
            add-new-fc-pots-lst
            add-timers
            add-to-pop-history
            add-to-set-eq
            add-to-set-equal
            add-to-tag-tree
            advance-fc-activations
            advance-fc-pot-lst
            all-args-occur-in-top-clausep
            all-calls
            all-fnnames1
            all-nils
            all-ns
            all-quoteps
            all-runes-in-ttree
            all-vars
            all-vars1
            all-vars1-lst
            alphorder
            ancestors-check
            and-macro
            and-orp
            apply-top-hints-clause
            approve-fc-derivations
            aref1
            aref2
            arglistp
            arglistp1
            arith-fn-var-count
            arith-fn-var-count-lst
            arity
            assoc-eq
            assoc-equal
            assoc-equal-cdr
            assoc-equiv
            assoc-equiv+
            assoc-keyword
            assoc-no-error-at-end
            assoc-type-alist
            assume-true-false
            assume-true-false1
            atoms
            augment-ignore-vars
            backchain-limit
            bad-cd-list
            not-pat-p
            basic-worse-than
            being-openedp-rec
            big-n
            binary-+
            binary-append
            bind-macro-args
            bind-macro-args-after-rest
            bind-macro-args-keys
            bind-macro-args-keys1
            bind-macro-args-optional
            bind-macro-args1
            binding-hyp-p
            binop-table
            body
            boolean-listp
            booleanp
            boundp-global
            boundp-global1
            brkpt1
            brkpt2
            built-in-clausep
            built-in-clausep1
            bytes-allocated
            bytes-allocated/call
            call-stack
            canonical-representative
            car-cdr-nest
            case-list
            case-split-limitations
            case-test
            change-plist
            change-plist-first-preferred
            character-listp
            chars-for-int
            chars-for-num
            chars-for-pos
            chars-for-pos-aux
            chars-for-rat
            chase-bindings
            chk-acceptable-defuns
            chk-acceptable-ld-fn
            chk-acceptable-ld-fn1
            chk-acceptable-ld-fn1-pair
            chk-all-but-new-name
            chk-arglist
            chk-assumption-free-ttree
            chk-dcl-lst
            chk-declare
            chk-defun-mode
            chk-defuns-tuples
            chk-embedded-event-form
            chk-free-and-ignored-vars
            chk-free-and-ignored-vars-lsts
            chk-irrelevant-formals
            chk-just-new-name
            chk-just-new-names
            chk-legal-defconst-name
            chk-length-and-keys
            chk-no-duplicate-defuns
            chk-table-guard
            chk-table-nil-args
            chk-xargs-keywords
            chk-xargs-keywords1
            clausify
            clausify-assumptions
            clausify-input
            clausify-input1
            clausify-input1-lst
            clean-type-alist
            clear-memoize-table
            clear-memoize-tables
            cltl-def-from-name
            coerce-index
            coerce-object-to-state
            coerce-state-to-object
            collect-assumptions
            collect-dcls
            collect-declarations
            collect-non-x
            comm-equal
            complementaryp
            complex-rationalp
            compute-calls-and-times
            compute-inclp-lst
            compute-inclp-lst1
            compute-stobj-flags
            cond-clausesp
            cond-macro
            conjoin
            conjoin-clause-sets
            conjoin-clause-to-clause-set
            conjoin2
            cons-make-list
            cons-ppr1
            cons-term
            cons-term2
            const-list-acc
            constant-controller-pocketp
            constant-controller-pocketp1
            contains-guard-holdersp
            contains-guard-holdersp-lst
            contains-rewriteable-callp
            controller-complexity
            controller-complexity1
            controller-pocket-simplerp
            controllers
            convert-clause-to-assumptions
            csh
            current-package
            dcls
            def-body
            default-defun-mode
            default-hints
            default-print-prompt
            default-verify-guards-eagerness
            defconst-fn
            defined-constant
            defn-listp
            defnp
            defun-fn
            defuns-fn
            defuns-fn0
            delete-assumptions
            delete-assumptions-1
            digit-to-char
            disjoin
            disjoin-clause-segment-to-clause-set
            disjoin-clauses
            disjoin-clauses1
            disjoin2
            distribute-first-if
            doc-stringp
            doubleton-list-p
            dumb-assumption-subsumption
            dumb-assumption-subsumption1
            dumb-negate-lit
            dumb-negate-lit-lst
            dumb-occur
            dumb-occur-lst
            duplicate-keysp
            eapply
            enabled-numep
            enabled-xfnp
            ens
            eoccs
            eqlable-listp
            eqlablep
            equal-mod-alist
            equal-mod-alist-lst
            er-progn-fn
            ev
            ev-fncall
            ev-fncall-rec
            ev-for-trans-eval
            ev-rec
            ev-rec-lst
            eval-bdd-ite
            eval-event-lst
            eval-ground-subexpressions
            eval-ground-subexpressions-lst
            evens
            every-occurrence-equiv-hittablep1
            every-occurrence-equiv-hittablep1-listp
            eviscerate
            eviscerate-stobjs
            eviscerate-stobjs1
            eviscerate1
            eviscerate1-lst
            eviscerate1p
            eviscerate1p-lst
            evisceration-stobj-marks
            expand-abbreviations
            expand-abbreviations-lst
            expand-abbreviations-with-lemma
            expand-and-or
            expand-any-final-implies1
            expand-any-final-implies1-lst
            expand-clique-alist
            expand-clique-alist-term
            expand-clique-alist-term-lst
            expand-clique-alist1
            expand-permission-result
            expand-some-non-rec-fns
            expand-some-non-rec-fns-lst
            explode-atom
            extend-car-cdr-sorted-alist
            extend-type-alist
            extend-type-alist-simple
            extend-type-alist-with-bindings
            extend-type-alist1
            extend-with-proper/improper-cons-ts-tuple
            extract-and-clausify-assumptions
            f-and
            f-booleanp
            f-ite
            f-not
            fc-activation
            fc-activation-lst
            fc-pair-lst
            fc-pair-lst-type-alist
            fetch-from-zap-table
            ffnnamep
            ffnnamep-hide
            ffnnamep-hide-lst
            ffnnamep-lst
            ffnnamep-mod-mbe
            ffnnamep-mod-mbe-lst
            ffnnamesp
            ffnnamesp-lst
            fgetprop
            filter-geneqv-lst
            filter-with-and-without
            find-abbreviation-lemma
            find-alternative-skip
            find-alternative-start
            find-alternative-start1
            find-alternative-stop
            find-and-or-lemma
            find-applicable-hint-settings
            find-clauses
            find-clauses1
            find-mapping-pairs-tail
            find-mapping-pairs-tail1
            find-rewriting-equivalence
            find-subsumer-replacement
            first-assoc-eq
            first-if
            fix-declares
            flpr
            flpr1
            flpr11
            flsz
            flsz-atom
            flsz-integer
            flsz1
            flush-hons-get-hash-table-link
            fms
            fmt
            fmt-char
            fmt-ctx
            fmt-hard-right-margin
            fmt-ppr
            fmt-soft-right-margin
            fmt-symbol-name
            fmt-symbol-name1
            fmt-var
            fmt0
            fmt0&v
            fmt0*
            fmt1
            fn-count-1
            fn-count-evg-rec
            fn-rune-nume
            fnstack-term-member
            formal-position
            formals
            free-varsp
            free-varsp-lst
            function-symbolp
            gatom
            gatom-booleanp
            gen-occs
            gen-occs-list
            geneqv-lst
            geneqv-lst1
            geneqv-refinementp
            geneqv-refinementp1
            general
            gentle-binary-append
            gentle-atomic-member
            gentle-caaaar
            gentle-caaadr
            gentle-caaar
            gentle-caadar
            gentle-caaddr
            gentle-caadr
            gentle-caar
            gentle-cadaar
            gentle-cadadr
            gentle-cadar
            gentle-caddar
            gentle-cadddr
            gentle-caddr
            gentle-cadr
            gentle-car
            gentle-cdaaar
            gentle-cdaadr
            gentle-cdaar
            gentle-cdadar
            gentle-cdaddr
            gentle-cdadr
            gentle-cdar
            gentle-cddaar
            gentle-cddadr
            gentle-cddar
            gentle-cdddar
            gentle-cddddr
            gentle-cdddr
            gentle-cddr
            gentle-cdr
            gentle-getf
            gentle-length
            gentle-revappend
            gentle-reverse
            gentle-strip-cars
            gentle-strip-cdrs
            gentle-take
            genvar
            get-and-chk-last-make-event-expansion
            get-declared-stobj-names
            get-doc-string
            get-docs
            get-global
            get-guards
            get-guards1
            get-guardsp
            get-ignorables
            get-ignores
            get-integer-from
            get-level-no
            get-package-and-name
            get-stobjs-in-lst
            get-string
            get-timer
            get-unambiguous-xargs-flg
            get-unambiguous-xargs-flg1
            get-unambiguous-xargs-flg1/edcls
            getprop-default
            gify
            gify-all
            gify-file
            gify-list
            global-set
            global-val
            good-defun-mode-p
            gsal
            gtrans-atomic
            guard
            guard-clauses
            guard-clauses-for-clique
            guard-clauses-for-fn
            guard-clauses-lst
            guess-and-putprop-type-prescription-lst-for-clique
            guess-and-putprop-type-prescription-lst-for-clique-step
            guess-type-prescription-for-fn-step
            hide-ignored-actuals
            hide-noise
            hits/calls
            hons
            hons-acons
            hons-acons!
            hons-acons-summary
            hons-copy-restore
            hons-copy2-consume
            hons-copy3-consume
            hons-copy1-consume
            hons-copy1-consume-top
            hons-copy2
            hons-copy3
            hons-copy1
            hons-copy1-top
            hons-copy
            hons-copy-list-cons
            hons-copy-r
            hons-copy-list-r
            hons-copy
            hons-dups-p
            hons-dups-p1
            hons-gentemp
            hons-get-fn-do-hopy
            hons-get-fn-do-not-hopy
            hons-int1
            hons-intersection
            hons-intersection2
            hons-len
            hons-member-equal
            hons-normed
            hons-put-list
            hons-sd1
            hons-set-diff
            hons-set-diff2
            hons-set-equal
            hons-shrink-alist
            hons-shrink-alist!
            hons-subset
            hons-subset2
            hons-union1
            hons-union2
            if-compile
            if-compile-formal
            if-compile-lst
            if-interp
            if-interp-add-clause
            if-interp-assume-true
            if-interp-assumed-value
            if-interp-assumed-value-x
            if-interp-assumed-value1
            if-interp-assumed-value2
            ignorable-vars
            ignore-vars
            in-encapsulatep
            increment-timer
            induct-msg/continue
            initialize-brr-stack
            initialize-summary-accumulators
            initialize-timers
            inst
            install-event
            install-global-enabled-structure
            intern-in-package-of-symbol
            intersection-eq
            intersectp-eq
            irrelevant-non-lambda-slots-clique
            keyword-param-valuep
            keyword-value-listp
            known-package-alist
            known-whether-nil
            kwote
            lambda-nest-hidep
            latch-stobjs
            latch-stobjs1
            ld-error-triples
            ld-evisc-tuple
            ld-filter-command
            ld-fn-alist
            ld-fn-body
            ld-loop
            ld-post-eval-print
            ld-pre-eval-filter
            ld-pre-eval-print
            ld-print-command
            ld-print-prompt
            ld-print-results
            ld-prompt
            ld-read-command
            ld-read-eval-print
            ld-skip-proofsp
            ld-verbose
            legal-case-clausesp
            legal-constantp
            legal-variable-or-constant-namep
            legal-variablep
            len
            let*-macro
            lexorder
            list*-macro
            list-fast-fns
            list-macro
            list-to-pat
            listify
            listlis
            locn-acc
            look-in-type-alist
            lookup-hyp
            lookup-world-index
            lookup-world-index1
            loop-stopperp
            macro-args
            macroexpand1
            main-timer
            make-bit
            make-clique-alist
            make-event-ctx
            make-event-debug-post
            make-event-debug-pre
            make-event-fn
            make-fmt-bindings
            make-list-of-symbols
            make-list-with-tail
            make-occs-map1
            make-slot
            make-symbol-with-number
            map-type-sets-via-formals
            match-free-override
            max-absolute-command-number
            max-absolute-event-number
            max-form-count
            max-form-count-lst
            max-level-no
            max-level-no-lst
            max-width
            may-need-slashes
            maybe-add-command-landmark
            maybe-add-space
            maybe-gify
            maybe-reduce-memoize-tables
            maybe-str-hash
            maybe-zify
            member-complement-term
            member-complement-term1
            member-eq
            member-equal
            member-equal-+-
            member-symbol-name
            member-term
            memoizedp-raw
            mer-star-star
            merge-runes
            merge-sort
            merge-sort-car->
            merge-sort-length
            merge-sort-runes
            most-recent-enabled-recog-tuple
            mv-atf
            mv-nth
            mv-nth-list
            n2char
            nat-list-to-list-of-chars
            nat-to-list
            nat-to-string
            nat-to-v
            natp
            new-backchain-limit
            newline
            next-absolute-event-number
            next-tag
            next-wires
            nfix
            nmake-if
            nmerge
            no-duplicatesp
            no-duplicatesp-equal
            no-op-histp
            nominate-destructor-candidates
            non-linearp
            non-stobjps
            normalize
            normalize-lst
            normalize-with-type-set
            not-instance-name-p
            not-pat-receiving
            dubious-to-profile
            not-safe-for-synthesis-list
            not-to-be-rewrittenp
            not-to-be-rewrittenp1
            nth-update-rewriter
            nth-update-rewriter-target-lstp
            nth-update-rewriter-targetp
            nu-rewriter-mode
            num-0-to-9-to-char
            num-to-bits
            number-of-arguments
            number-of-calls
            number-of-hits
            number-of-memoized-entries
            number-of-mht-calls
            number-of-return-values
            number-of-strings
            obfb
            obj-table
            odds
            ofe
            ofnum
            ofv
            ofvv
            ofw
            ok-to-force
            oncep
            one-way-unify
            one-way-unify-restrictions
            one-way-unify1
            one-way-unify1-equal
            one-way-unify1-equal1
            one-way-unify1-lst
            open-input-channel
            open-output-channel
            open-output-channel-p
            or-macro
            output-ignored-p
            output-in-infixp
            pairlis$
            pairlis2
            pal
            partition-according-to-assumption-term
            permute-occs-list
            pons
            pons-calls
            pop-accp
            pop-clause
            pop-clause-msg
            pop-clause-msg1
            pop-clause1
            pop-timer
            pop-warning-frame
            posp
            ppr
            ppr1
            ppr1-lst
            ppr2
            ppr2-column
            ppr2-flat
            prefix
            preprocess-clause
            preprocess-clause-msg1
            prin1$
            princ$
            print-alist
            print-base-p
            print-call-stack
            print-defun-msg
            print-defun-msg/collect-type-prescriptions
            print-defun-msg/type-prescriptions
            print-defun-msg/type-prescriptions1
            print-prompt
            print-rational-as-decimal
            print-redefinition-warning
            print-rules-summary
            print-summary
            print-time-summary
            print-timer
            print-verify-guards-msg
            print-warnings-summary
            profile-g-fns
            progn-fn
            progn-fn1
            program-term-listp
            program-termp
            proofs-co
            proper/improper-cons-ts-tuple
            prove
            prove-guard-clauses
            prove-loop
            prove-loop1
            pseudo-term-listp
            pseudo-termp
            pseudo-variantp
            pseudo-variantp-list
            pt-intersectp
            pt-occur
            pts-to-ttree-lst
            puffert
            push-accp
            push-ancestor
            push-io-record
            push-lemma
            push-timer
            push-warning-frame
            put-assoc-eq
            put-global
            put-ttree-into-pspv
            putprop
            putprop-defun-runic-mapping-pairs
            quickly-count-assumptions
            quote-listp
            quotep
            qzget-sign-abs
            raw-mode-p
            read-acl2-oracle
            read-object
            read-run-time
            read-standard-oi
            recompress-global-enabled-structure
            recompress-stobj-accessor-arrays
            record-accessor-function-name
            recursive-fn-on-fnstackp
            redundant-or-reclassifying-defunsp1
            relevant-slots-call
            relevant-slots-clique
            relevant-slots-clique1
            relevant-slots-def
            relevant-slots-term
            relevant-slots-term-lst
            relieve-hyp
            relieve-hyps
            relieve-hyps1
            remove-evisc-marks
            remove-evisc-marks-al
            remove-invisible-fncalls
            remove-keyword
            remove-one-+-
            remove-strings
            replace-stobjs
            replace-stobjs1
            replaced-stobj
            ret-stack
            return-type-alist
            rewrite
            rewrite-args
            rewrite-fncall
            rewrite-fncallp
            rewrite-fncallp-listp
            rewrite-if
            rewrite-if1
            rewrite-if11
            rewrite-primitive
            rewrite-recognizer
            rewrite-solidify
            rewrite-solidify-plus
            rewrite-solidify-rec
            rewrite-stack-limit
            rewrite-with-lemma
            rewrite-with-lemmas
            rewrite-with-lemmas1
            rewrite-with-linear
            rune-<
            runep
            safe-1+
            safe-1-
            safe-<
            safe-<=
            safe-binary-+
            safe-binary--
            safe-caaaar
            safe-caaadr
            safe-caaar
            safe-caadar
            safe-caaddr
            safe-caadr
            safe-caar
            safe-cadaar
            safe-cadadr
            safe-cadar
            safe-caddar
            safe-cadddr
            safe-caddr
            safe-cadr
            safe-car
            safe-cdaaar
            safe-cdaadr
            safe-cdaar
            safe-cdadar
            safe-cdaddr
            safe-cdadr
            safe-cdar
            safe-cddaar
            safe-cddadr
            safe-cddar
            safe-cdddar
            safe-cddddr
            safe-cdddr
            safe-cddr
            safe-cdr
            safe-code-char
            safe-coerce
            safe-floor
            safe-intern-in-package-of-symbol
            safe-lognot
            safe-max
            safe-mod
            safe-nthcdr
            safe-rem
            safe-strip-cars
            safe-symbol-name
            saved-output-token-p
            scan-past-whitespace
            scan-to-cltl-command
            scan-to-landmark-number
            scons-tag-trees
            scons-tag-trees1
            search-type-alist
            search-type-alist-rec
            set-cl-ids-of-assumptions
            set-difference-eq
            set-timer
            set-w
            set-w!
            sgetprop
            simple-translate-and-eval
            simplify-clause-msg1
            simplify-clause1
            slot-member
            some-congruence-rule-disabledp
       some-controller-pocket-constant-and-non-controller-simplerp
            some-geneqv-disabledp
            some-subterm-worse-than-or-equal
            some-subterm-worse-than-or-equal-lst
            sort-approved
            sort-approved1
            sort-approved1-rating1
            sort-occurrences
            spaces
            splice-instrs
            splice-instrs1
            split-on-assumptions
            ssn
            standard-co
            standard-oi
            state-p1
            std-apart
            std-apart-top
            stobjp
            stobjs-in
            stobjs-out
            stop-redundant-event
            store-clause
            store-clause1
            string-append-lst
            string-from-list-of-chars
            string-listp
            strip-assumption-terms
            strip-branches
            strip-cadrs
            strip-cars
            strip-cdrs
            subcor-var
            subcor-var-lst
            subcor-var1
            sublis-expr
            sublis-expr-lst
            sublis-occ
            sublis-pat
            sublis-var
            sublis-var-lst
            subsetp-eq
            subsumption-replacement-loop
            suffix
            sweep-clauses
            sweep-clauses1
            symbol-<
            symbol-alistp
            symbol-class
            symbol-listp
            symbol-package-name
            t-and
            t-fix
            t-ite
            t-list
            t-not
            t-or
            table-alist
            table-fn
            table-fn1
            tag-tree-occur
            tagged-object
            tagged-objects
            tame-symbolp
            term-and-typ-to-lookup
            term-order
            termp
            thm-fn
            tilde-*-preprocess-phrase
            tilde-*-simp-phrase
            tilde-*-simp-phrase1
            tilde-@-abbreviate-object-phrase
            time-for-non-hits/call
            time-limit4-reached-p
            time/call
            to
            to-be-ignoredp
            to-if-error-p
            too-long
            total-time
            trans-alist
            trans-alist1
            trans-eval
            translate-bodies
            translate-bodies1
            translate-dcl-lst
            translate-deref
            translate-doc
            translate-hints
            translate-term-lst
            translate1
            translate11
            translate11-lst
            translate11-mv-let
            translated-acl2-unwind-protectp
            translated-acl2-unwind-protectp4
            tree-occur
            true-listp
            type-alist-clause-finish
            type-alist-clause-finish1
            type-alist-equality-loop
            type-alist-equality-loop1
            type-alist-fcd-lst
            type-set
            type-set-<
            type-set-<-1
            type-set-and-returned-formals
            type-set-and-returned-formals-with-rule
            type-set-car
            type-set-cdr
            type-set-cons
            type-set-equal
            type-set-finish
            type-set-lst
            type-set-not
            type-set-primitive
            type-set-quote
            type-set-recognizer
            type-set-relieve-hyps
            type-set-with-rule
            type-set-with-rule1
            type-set-with-rules
            unencumber-assumptions
            unify
            unify-sa-p
            union-eq
            union-equal
            untranslate
            untranslate-lst
            untranslate-preprocess-fn
            untranslate1
            untranslate1-lst
            update-world-index
            us
            user-stobj-alist
            user-stobj-alist-safe
            user-stobjsp
            v-to-nat
            var-fn-count
            var-fn-count-lst
            var-lessp
            var-to-tree
            var-to-tree-list
            vars-of-fal-aux
            verify-guards-fn1
            vx2
            w
            warning-off-p
            wash-memory
            watch-count
            maybe-watch-dump
            incf-watch-count
            set-watch-count
            watch-help
            time-of-last-watch-update
            watch-shell-command
            time-since-watch-start
            make-watchdog
            watch
            watch-kill
            watch-condition
            waterfall
            waterfall-msg
            waterfall-msg1
            waterfall-print-clause
            waterfall-step
            waterfall-step1
            waterfall0
            waterfall1
            waterfall1-lst
            widen
            watch-real-time
            watch-run-time
            world-evisceration-alist
            worse-than
            worth-hashing
            worth-hashing1
            x-and
            x-buf
            x-ff
            x-latch+
            x-latch-
            x-latch-+
            x-mux
            x-not
            x-or
            x-xor
            xor
            xxxjoin
            zip-variable-type-alist
            zp)
          do (setf (gethash sym ht) t))
    ht)
  
  "The user may freely add to the hash table
  *PROFILE-REJECT-HT*, which inhibits the collection of
  functions into lists of functions to be memoized and/or profiled.

  Here are some reasons for adding a function fn to
  *PROFILE-REJECT-HT*.

  1. A call of fn is normally so fast or fn is called so often that
  the extra instructions executed when a profiled or memoized version
  of fn is run will distort measurements excessively.  We tend not to
  profile any function that runs in under 6000 clock ticks or about 2
  microseconds.  The number of extra instructions seem to range
  between 20 and 100, depending upon what is being measured.  Counting
  function calls is relatively fast.  But if one measures elapsed
  time, one might as well measure everything else too.  Or so it seems
  in 2007 on terlingua.csres.utexas.edu.

  2. fn is a subroutine of another function being profiled, and we
  wish to reduce the distortion that profiling fn will cause.

  3. fn is 'transparent', like EVAL.  Is EVAL fast or slow?  The
  answer, of course, is that it mostly depends upon what one is
  EVALing.

  4. fn's name ends in '1', meaning 'auxiliary' to some folks.

  5. fn is boring.

  Our additions to *PROFILE-REJECT-HT* are utterly capricious.  The
  user should feel free to set *PROFILE-REJECT-HT* ad lib, at any
  time.")

(defn1 dubious-to-profile (fn)
  (cond ((not (symbolp fn)) "not a symbol.")
        ((not (fboundp fn)) "not fboundp.")
        ((eq (symbol-package fn) *main-lisp-package*)
         (ofn "~%;~10tin *main-lisp-package*."))
        #+Clozure
        ((ccl::%advised-p fn)
         (ofn "~%;10tadvised, and it will so continue."))
        ((member fn (eval '(trace)))
         (ofn "~%;~10ta member of (trace), and it will so ~
               continue."))
        ((member fn (eval '(old-trace)))
         (ofn "~%;~10ta member of (old-trace), and it will so ~
               continue."))
        ((eq fn 'return-last)
         "the function RETURN-LAST.")
        ((gethash fn *never-profile-ht*)
         (ofn "~%;~10tin *NEVER-PROFILE-HT*."))
        ((gethash fn *profile-reject-ht*)
         (ofn "in~%;~10t*PROFILE-REJECT-HT*.  Override with~
               ~%;~10t(REMHASH '~a *PROFILE-REJECT-HT*)."
              fn))
        ((macro-function fn) "a macro.")
        ((compiler-macro-function fn) "a compiler-macro-function.")
        ((special-form-or-op-p fn) "a special operator.")
        ((memoizedp-raw fn)
         (ofn "~%;~10tmemoized or profiled, ~
               and it will so continue."))
        #+Clozure
        ((multiple-value-bind (req opt restp keys)
             (ccl::function-args (symbol-function fn))
           (if (or restp
                   keys
                   (not (integerp req))
                   (not (eql opt 0)))
               (ofn "~%;~10thas some non-simple argument, e.g., &key ~
                     or &rest.")
             nil)))
        ((null (number-of-arguments fn))
         (input-output-number-warning fn))))

; memoize-flush 'forgets' all that was remembered for certain
; functions that use certain stobjs.  We must keep memoize-flush very
; fast in execution so as not to slow down stobj update or resize
; operations in general.  We 'forget' the pons table later.

(defmacro memoize-flush (st)
  (let ((s (st-lst st)))
    `(when (boundp ',s)
       (loop for sym in (symbol-value ',s) do
             (when (boundp (the symbol sym)) ; Is this test needed?
               (let ((old (symbol-value (the symbol sym))))
                 (unless (or (null old) (empty-ht-p old))
                   (setf (symbol-value (the symbol sym)) nil))))))))

(declaim (hash-table *memoize-info-ht*))

(defmacro pist (table &rest x)
  (cond ((atom x) nil)
        (t (list 'pons (car x)
                 (cons 'pist (cdr x)) table))))

(defmacro pist* (table &rest x)
  (cond ((atom x) x)
        ((atom (cdr x)) (car x))
        (t (list 'pons (car x)
                 (cons 'pist* (cons table (cdr x))) table))))

;  THE MEMO-INFO-HT-ENTRY DATA STRUCTURE

; *MEMOIZE-INFO-HT* maps each currently memoized function symbol, fn,
; to a DEFREC record of type MEMO-INFO-HT-ENTRY with 28 fields.

; fn             a symbol, the name of the function being memoized
; start-time     a symbol whose val is the start time of the current,
;                   outermost call of fn, or -1 if no call of fn
;                   is in progress.
; num            an integer, unique to fn
; tablename      a symbol whose value is the memoize table for fn
; ponstablename  a symbol whose value is the pons table for fn
; old-fn         the old value of (symbol-function fn), or nil.
; memoized-fn    the new value of (symbol-function fn)
; condition      T or NIL. :condition arg as passed to memoize-fn
; inline         T or NIL. :inline arg as passed to memoize-fn
; sts            the stobj memotable lists for fn
; trace          T or NIL. :trace arg as passed to memoize-fn
; before         form to evaluate first
; cl-defun       the function body actually used, in the inline=t
;                case, as supplied (or as computed, if not supplied)
; formals        as supplied (or as computed, if not supplied)
; specials       never to be used or explained -- secret args
; commutative    asserts this is a binary commutative function
; stobjs-in      as supplied (or as computed, if not supplied)
; stobjs-out     as supplied (or as computed, if not supplied)
; record-bytes   value as bound at the time MEMOIZE-FN is called
; record-calls            ''
; record-hits             ''
; record-hons-calls       ''
; record-mht-calls        ''
; record-pons-calls       ''
; record-time             ''
; watch-ifs      Boolean, whether to monitor each IF
; forget         Boolean, clears memo when outermost call exits.
; memo-table-init-size integer, default *mht-default-size*

; *memoize-info-ht* also maps num back to the corresponding symbol.

(defrec memoize-info-ht-entry
; vaguely ordered by most frequently referenced first
  (ext-anc-attachments
   start-time
   num
   tablename
   ponstablename
   condition
   inline
   memoized-fn
   old-fn
   fn
   sts
   trace
   before
   cl-defun
   formals
   commutative
   specials
   stobjs-in
   stobjs-out
   record-bytes
   record-calls
   record-hits
   record-hons-calls
   record-mht-calls
   record-pons-calls
   record-time
   watch-ifs
   forget
   memo-table-init-size)
  t)

(defparameter *memo-max-sizes*
  ;; Binds function names to memo-max-sizes-entry structures.
  ;;
  ;; Jared originally added this table because he wanted to know how big
  ;; memoization tables were getting (so that he could set up appropriate
  ;; initial sizes), but when tables are cleared they are thrown away, so for
  ;; tables that are frequently cleared it wasn't possible to see how large the
  ;; table had become.
  ;;
  ;; After seeing the information, we thought it might be a good idea to use it
  ;; to infer what a good table size might be when we recreate the memo table.
  ;; See the function predict-good-memoize-table-size for details.
  (make-hash-table))

; BOZO should we use this information to try to guess better sizes and
; rehash thresholds for memoize tables?

(defrec memo-max-sizes-entry
  ;; A single entry in the *memo-table-max-sizes* table.
  (num-clears   ; how many times has this table been cleared (nat)
   max-pt-size  ; maximum size of the pons table before any clear (nat)
   max-mt-size  ; maximum size of the memo table before any clear (nat)
   avg-pt-size  ; average size of pons table before any clear (float)
   avg-mt-size  ; average size of memo table before any clear (float)
   )
  t)

(defun make-initial-memoize-hash-table (fn init-size)

; FN is the name of a function.  INIT-SIZE is the initial size that the user
; says we should use.  We want to come create and return a new hash table for
; this function's memoization table.  One possible implementation of this
; function would just be:
;
;    (mht :size init-size)
;
; But we hope to do better.  Our idea is to look at how large the table has
; been in the past, and use that size to make a good prediction of how large
; the table will be this time.
;
; The idea here is to build a table that's just slightly bigger than the
; average size we've seen so far.  We arbitrarily say that "slightly bigger"
; means 1.2x the previous average.
;
; By itself this would be scary.  Big hash tables can use a lot of memory: a
; rule of thumb in CCL is that 1 MB of space buys you 44,000 entries.  I want
; to avoid creating a hundred-megabyte memo tables for a function just because
; it was used heavily for a short while and then cleared once before.  On the
; other hand, if a memo table truly does get large on a regular basis, then we
; do want to guess a big size for it.
;
; So in this code, I enforce an artificial maximum on our guess, but I allow
; this maximum to grow with the number of times we've cleared the table.
; Basically I allow the maximum guess to grow at a rate of 1 MB per clear.  If
; a table has been cleared 100 times, I think we have a pretty good sense of
; its average usage and we can be comfortable allocating up to 100 MB for it.
; If it's been cleared more than 1000 times, the cap is a gigabyte.  But of
; course, to actually reach such a large guess, you'd have to be repeatedly
; filling up the table to contain millions of entries and then clearing it.

  (let* ((max-sizes
          ;; The previously recorded sizes of this table, if any exist.
          (gethash fn *memo-max-sizes*))
         (size-to-use
          (if (not max-sizes)
              ;; We never cleared this memoize table before, so we don't have
              ;; anything to go on besides what the user says.  Do what they
              ;; say.
              init-size
            (let* ((nclears       (access memo-max-sizes-entry max-sizes :num-clears))
                   (avg-mt-size   (access memo-max-sizes-entry max-sizes :avg-mt-size))
                   (our-guess     (ceiling (* 1.20 avg-mt-size)))
                   (capped-guess  (min our-guess (* nclears 44000)))
                   (final-guess   (max 60 init-size capped-guess)))
              final-guess))))
    ;; BOZO also try to guess a better rehash-size?
    (mht :size size-to-use)))

(defun make-initial-memoize-pons-table (fn init-size)

; This is just like make-initial-memoize-hash-table, but for the pons table.

  (let* ((max-sizes (gethash fn *memo-max-sizes*))
         (size-to-use
          (if (not max-sizes)
              init-size
            (let* ((nclears       (access memo-max-sizes-entry max-sizes :num-clears))
                   (avg-pt-size   (access memo-max-sizes-entry max-sizes :avg-pt-size))
                   (our-guess     (ceiling (* 1.20 avg-pt-size)))
                   (capped-guess  (min our-guess (* nclears 44000)))
                   (final-guess   (max 60 init-size capped-guess)))
              final-guess))))
    ;; BOZO also try to guess a better rehash-size?
    (mht :size size-to-use)))

(defun update-memo-max-sizes (fn pt-size mt-size)
  ;; Called during clear-one-memo-and-pons-hash when the tables existed.
  ;; When called, pt-size and mt-size are nonzero.
  (let ((old (gethash fn *memo-max-sizes*)))
    (if (not old)
        (setf (gethash fn *memo-max-sizes*)
              (make memo-max-sizes-entry
                    :num-clears 1
                    :max-pt-size pt-size
                    :max-mt-size mt-size
                    :avg-pt-size (coerce pt-size 'float)
                    :avg-mt-size (coerce mt-size 'float)))
      (let* ((old.num-clears  (access memo-max-sizes-entry old :num-clears))
             (old.max-pt-size (access memo-max-sizes-entry old :max-pt-size))
             (old.max-mt-size (access memo-max-sizes-entry old :max-mt-size))
             (old.avg-pt-size (access memo-max-sizes-entry old :avg-pt-size))
             (old.avg-mt-size (access memo-max-sizes-entry old :avg-mt-size))
             (new.num-clears  (+ 1 old.num-clears)))
        (setf (gethash fn *memo-max-sizes*)
              (make memo-max-sizes-entry
                    :num-clears  new.num-clears
                    :max-pt-size (max pt-size old.max-pt-size)
                    :max-mt-size (max mt-size old.max-mt-size)
                    :avg-pt-size (/ (+ pt-size (* old.avg-pt-size old.num-clears))
                                    new.num-clears)
                    :avg-mt-size (/ (+ mt-size (* old.avg-mt-size old.num-clears))
                                    new.num-clears))))))
  nil)

(defun print-memo-max-sizes ()
  (when (equal (hash-table-count *memo-max-sizes*) 0)
    (return-from print-memo-max-sizes nil))
  (format t "Memo table statistics gathered at each from when they were cleared:~%~%")
  (let ((indent 8) ;; length of "Function"
        (indent-str nil))
    (maphash (lambda (fn entry)
               (declare (ignore entry))
               (setq indent (max indent (length (symbol-name fn)))))
             *memo-max-sizes*)
    (setq indent-str (format nil "~a" (+ 2 indent)))
    (format t (concatenate 'string "~" indent-str ":@a") "Function")
    (format t " ~10:@a | ~15:@a ~15:@a | ~15:@a ~15:@a~%"
            "Clears" "PT Max" "PT Avg" "MT Max" "MT Avg")
    (maphash
     (lambda (fn entry)
       (let* ((num-clears  (access memo-max-sizes-entry entry :num-clears))
              (max-pt-size (access memo-max-sizes-entry entry :max-pt-size))
              (max-mt-size (access memo-max-sizes-entry entry :max-mt-size))
              (avg-pt-size (access memo-max-sizes-entry entry :avg-pt-size))
              (avg-mt-size (access memo-max-sizes-entry entry :avg-mt-size)))
         (format t (concatenate 'string "~" indent-str ":@a ~10:D | ~15:D ~15:D | ~15:D ~15:D~%")
                 fn num-clears
                 max-pt-size (floor avg-pt-size)
                 max-mt-size (floor avg-mt-size))))
     *memo-max-sizes*)
    (format t "~%"))
  nil)

; MEMOIZE FUNCTIONS

#+Clozure
(defmacro heap-bytes-allocated ()
  '(the mfixnum (ccl::%heap-bytes-allocated)))

(defn sync-memoize-call-array ()

  ; To be called only by MEMOIZE-INIT, MEMOIZE-CALL-ARRAY-GROW, or
  ; SAVE-MEMOIZE-CALL-ARRAY.

  (let ((n1 (the fixnum
              (* *2max-memoize-fns* *2max-memoize-fns*)))
        (n2 (1+ *max-symbol-to-fixnum*)))
    (declare (type fixnum n1 n2))
    (unless (eql n1 (length *memoize-call-array*))
      (unless (eql 1 (length *memoize-call-array*))
        (setq *memoize-call-array*
              (make-array 1 :element-type 'mfixnum
                          :initial-element 0))
        (gc$))
      (setq *memoize-call-array*
            (make-array n1
                        :element-type 'mfixnum
                        :initial-element 0)))
    (unless (eql n2 (length *compute-array*))
      (setq *compute-array*
            (make-array n2 :initial-element nil)))
    (setq *caller* (* *ma-initial-max-symbol-to-fixnum*
                      *2max-memoize-fns*))))

(defun memoize-call-array-grow
  (&optional (2nmax (* 2 (ceiling (* 3/2 (/ *2max-memoize-fns* 2))))))
  (unwind-mch-lock
   (unless (integerp 2nmax)
     (ofe "(memoize-call-array-grow ~s).  Arg must be an integer."
          2nmax))
   (unless (evenp 2nmax)
     (ofe "(memoize-call-array-grow ~s).  Arg must be even." 2nmax))
   (unless (> 2nmax 100)
     (ofe "(memoize-call-array-grow ~s).  Arg must be > 100." 2nmax))
   (when (<= 2nmax *2max-memoize-fns*)
     (ofv "memoize-call-array-grow: *memoize-call-array* already ~
           big enough.")
     (return-from memoize-call-array-grow))
   (unless (<= (* 2nmax 2nmax) most-positive-fixnum)
     (ofe "memoize-call-array-grow:  most-positive-fixnum~%~
            exceeded.  Too many memoized functions."))
   (unless (< (* 2nmax 2nmax) array-total-size-limit)
     (ofe "memoize-call-array-grow: ARRAY-TOTAL-SIZE-LIMIT ~%~
            exceeded.  Too many memoized functions."))
   (unless (eql *caller* (* *ma-initial-max-symbol-to-fixnum*
                            *2max-memoize-fns*))
     (ofv "MEMOIZE-CALL-ARRAY-GROW was called while a ~
           memoized-function~% was executing, so call reports may ~
           be quite inaccurate."))

   (setq *memoize-call-array*
     (make-array 1 :element-type 'mfixnum :initial-element 0))
   (setq *2max-memoize-fns* 2nmax)
   (sync-memoize-call-array)
   (rememoize-all)))

(defn1 symbol-to-fixnum-create (s)
  (check-type s symbol)
  (let ((g (gethash s *memoize-info-ht*)))
    (if g (access memoize-info-ht-entry g :num)
      (let (new)
        (loop for i fixnum from
              (if (eql *caller*
                       (* *ma-initial-max-symbol-to-fixnum*
                          *2max-memoize-fns*))
                  (1+ *ma-initial-max-symbol-to-fixnum*)
                (1+ *max-symbol-to-fixnum*))
              below (the fixnum (floor *2max-memoize-fns* 2))
              do (unless (gethash i *memoize-info-ht*)
                   (setq new i)
                   (return)))
        (cond (new
               (setq *max-symbol-to-fixnum*
                     (max *max-symbol-to-fixnum* new))
               new)
              (t (memoize-call-array-grow)
                 (safe-incf *max-symbol-to-fixnum*
                            1 symbol-to-fixnum-create)
                 *max-symbol-to-fixnum*))))))

(defn1 symbol-to-fixnum (s)
  (check-type s symbol)
  (let ((g (gethash s *memoize-info-ht*)))
    (if g (access memoize-info-ht-entry g :num)
      (ofe "(symbol-to-fixnum ~s).  Illegal symbol."
           s))))

(defn1 fixnum-to-symbol (n)
  (check-type n fixnum)
  (or (gethash n *memoize-info-ht*)
      (ofe "(fixnum-to-symbol ~s). Illegal number."
           n)))

(defn1 coerce-index (x)
  (if (and (typep x 'fixnum)
           (>= x 0)
           (< x (length *memoize-call-array*)))
      x
    (symbol-to-fixnum x)))





;; ADDR-FOR.  This is fixed up in the new hons code and we have a proof of it,
;; but I'm not touching pons yet.

(defn1 integer-pair (x y)
  (let ((z (+ x y)))
    (+ (/ (* z (1+ z)) 2) y)))

(defconstant atom-case-fudge (+ 129 (expt 2 25)))
(defconstant most-positive-fudge (1- (expt 2 24)))
(defconstant most-negative-fudge (- (expt 2 24)))
(defconstant -most-negative-fudge (- most-negative-fudge))

(defn1 atom-case (s)
  (cond
   ((symbolp s)
    (cond ((eq s nil) 0)
          ((eq s t) 1)
          (t (let ((v (get (the symbol s) 'hons-hash-key)))
               (cond ((null v)
                      (let ((c (ccl::static-cons s nil)))
                        (setq v (+ atom-case-fudge
                                   (the fixnum (ccl::%staticp c))))
                        (setf (get (the symbol s) 'hons-hash-key) c)
                        (rplacd (the cons c) v)
                        v))
                     (t (cdr (the cons v))))))))
   ((and (typep s 'fixnum)
         (> (the fixnum s) most-negative-fudge)
         (<= (the fixnum s) most-positive-fudge))
    (the fixnum (+ -most-negative-fudge (the fixnum s))))))

(defmacro sqmpf ()
  (isqrt most-positive-fixnum))

(defmacro hmnf ()

; Half MOST-NEGATIVE-FIXNUM.

  (ceiling (/ most-negative-fixnum 2)))

(defmacro static-hons-shift ()
  (ceiling (/ (integer-length most-positive-fixnum) 2)))

(defn1 addr-for (x y)
  (let ((idx (let ((n (ccl::%staticp x)))
               (cond (n (+ atom-case-fudge (the fixnum n)))
                     (t (atom-case x)))))
        (large-case nil))
    (cond (idx (cond ((and (typep idx 'fixnum)
                           (< (the fixnum idx) (sqmpf)) nil))
                     (t (setq large-case t))))
          (t (return-from addr-for nil)))
    (let ((idy (let ((n (ccl::%staticp y)))
                 (cond (n (+ atom-case-fudge (the fixnum n)))
                       (t (atom-case y))))))
      (cond (idy (cond ((and (typep idy 'fixnum)
                             (< (the fixnum idy) (sqmpf))) nil)
                       (t (setq large-case t))))
            (t (return-from addr-for nil)))
    
; ADDR-FOR is 1-1, in a sense, for a two argument function, when not
; NIL.  That is, for all ACL2 objects x1, x2, y1, and y1, if (addr-for
; x1 y1) is not NIL and is equal to (addr-for x2 y2), then x1 is equal
; to x2 and y1 is equal to y2.

; Here is a sketch of a proof that if mpf = 2^60-1 and mnf = -2^60,
; then the ranges of large-case and the non-large case of ADDR-FOR do
; not intersect.  In the large case, one of idx or idy, must be >=
; 2^30, so (+ (/ (* (idx+idy+1) (idx+idy)) 2) idy) > 2^59.  Adding in
; -2^59 means that the large result will be positive. In the non-large
; case, the result of the logior will be <= 2^60-1, so the result of
; adding -2^60 will make the non-large result negative.

      (cond (large-case
             (let* ((z (+ idx idy))
                    (z1 (+ 1 z)))
               (if (oddp z)
                   (setq z1 (ash z1 -1))
                 (setq z (ash z -1)))
               (+ idy (+ (hmnf) (* z z1)))))
            (t (+ (the fixnum
                    (logior
                     (the fixnum
                       (ash (the fixnum idx) (static-hons-shift)))
                     (the fixnum idy)))
                  most-negative-fixnum))))))









; This code has the 'feature' that if the condition causes an error,
; so will the memoized function.

; PONS differs from HONS in that it does not honsify its arguments and
; in that it takes a hash table as a third argument.  We use PONS in
; memoization.

; We use PONS instead of HONS in memoization because we could not
; afford to honsify (using hons-shrink-alist!) certain alists in
; certain biology tests.  About the same time, we (gratuitously)
; decided to stop hons'ifying the output of memoized functions.

(defn1 pons (x y ht)
  (declare (hash-table ht))

; ***** pons *****

; If pons can create a hons, that will lead to a deadlock over locks!

; A crucial fact is:
; (implies (equal (pons x y ht) (pons x' y' ht))
;          (and (equal x x')
;               (equal y y'))

; Ignore the ht for the moment.  Suppose that
;    (equal (pons x (pons y z)) (pons x' (pons y' z'))).
; 
; It follows then that x=x', y=y', and z=z'.

  (let ((xval nil)
        (yval nil)
        (ans nil))

; We have taken string normalization out of pons because there might
; be a chance of confusing a 'normal' string with a stobj.

; If x1, ..., xn is pointwise EQL to y1, ..., yn, then are we sure
; that (pist* x1 ... xn) is EQ to (pist* y1 ... yn)?

; If CONS exists, then return it.  Does CDR exist in hash table?

    #+Clozure
    (let ((addr (addr-for x y)))
      (when addr (return-from pons addr)))

    (maybe-count-pons-calls)
    (setq yval (gethash y (the hash-table ht)))

; Does CAR exist in hash table?

    (cond (yval
           (cond ((not (consp yval))
                  (setq xval (gethash x (the hash-table yval)))
                  (cond (xval (setq ans xval))))
                 ((setq ans (assoc-no-error-at-end x yval))))))
    (cond

; If PONS found, then return previous CONS from hash table.
     (ans)

; Otherwise, maybe create new CONS and install in hash table.

     (t
      (setq yval (gethash y ht))
      (cond
       ((null yval)
        (setq ans (cons x y))
        (setf (gethash y ht) (list ans))
        ans)
       ((consp yval)
        (let ((ans (assoc-no-error-at-end x yval)))
            (cond
             (ans)
             (t (let ((ans (cons (cons x y) yval)))
                  (maybe-count-pons-misses)
                  (cond
                   ((too-long ans *start-car-ht-size*)
                    (let ((tab (mht)))
                      (declare (hash-table tab))
                      (loop for pair in ans do
                            (setf (gethash (car pair) tab) pair))
                      (setf (gethash y ht) tab)
                      (car ans)))
                   (t (setf (gethash y ht) ans)
                      (car ans))))))))
       (t (setq xval (gethash x (the hash-table yval)))
          (cond ((not xval)
                 (maybe-count-pons-misses)
                 (setf (gethash x (the hash-table yval))
                       (setq ans (cons x y))))
                (t (setq ans xval)))
          ans))))))

; We use DEFVAR for *UNSMASHED-IF* and *UNSMASHED-OR* so we don't set
; them; that could accidentally pick up the wrong value if this file
; were loaded twice.

(defvar *unsmashed-if* (compiler-macro-function 'if))

(defvar *unsmashed-or* (compiler-macro-function 'or))

(defg *smashed-if* nil)

(defg *smashed-or* nil)

(defn1 memoize-eval-compile (def watch-ifs)
  (unless (and (consp def)
               (eq 'defun (car def))
               (consp (cdr def))
               (symbolp (cadr def)))
    (ofe "MEMOIZE-EVAL-COMPILE:  Bad input:~%~s." def))
  (flet ((what-to-do () (compile (eval def))))
    (cond
     #+Clozure
     ((and watch-ifs *smashed-if* *unsmashed-if*)
      (cond ((and (eql ccl::*nx-speed* 3)
                  (eql ccl::*nx-safety* 0))
             (unwind-protect
               (progn
                 (setf (compiler-macro-function 'if) *smashed-if*)
                 (setf (compiler-macro-function 'or) *smashed-or*)
                 (what-to-do))
               (setf (compiler-macro-function 'if) *unsmashed-if*)
               (setf (compiler-macro-function 'or) *unsmashed-or*)))
            (t (ofd "~%; MEMOIZE-EVAL-COMPILE: ~a.  WATCH-IF does ~
                     not work unless SAFETY=0 and SPEED=3."
                    (cadr def))
               (what-to-do))))
     (t (what-to-do))))
  nil)

(defn1 memoizedp-raw (fn)
  (our-lock-unlock-memoize1
   (and (symbolp fn)
        (values (gethash fn *memoize-info-ht*)))))

(defg *hons-gentemp-counter* 0)
(declaim (type fixnum *hons-gentemp-counter*))
(defn1-one-output hons-gentemp (root)
  (check-type root string)
  (loop
   (safe-incf *hons-gentemp-counter* 1 hons-gentemp)
   (let ((name (ofn "HONS-G-~s,~s" root *hons-gentemp-counter*)))
     (multiple-value-bind (sym status)
         (intern name (find-package "ACL2_INVISIBLE"))
       (if (null status) (return sym))))))

(defn1 st-lst (st)

; ST-LST returns a symbol whose value is a list in which are saved the
; names of the memoize tables that will be set to nil whenever the
; stobj st is changed.

  (check-type st symbol)
  (multiple-value-bind (symbol status)
      (intern (ofn "HONS-S-~s,~s"
                   (package-name (symbol-package st))
                   (symbol-name st))
              (find-package "ACL2_INVISIBLE"))
    (or status (eval `(defg ,symbol nil)))
    symbol))

(defn1 dcls (l)
     (loop for dec in l nconc
           (let ((temp
                  (if (consp dec)
                      (loop for d in (cdr dec) nconc
                            (if (and (consp d) (eq (car d) 'ignore))
                                nil
                              (cons d nil))))))
             (if temp (cons (cons 'declare temp) nil)))))

(defn1 timer-error ()
  (ofe "timer-error."))

; PRINE  - princ eviscerated

(defg *assoc-eq-hack-ht* (mht :test 'eql))
(declaim (hash-table *assoc-eq-hack-ht*))

(defn assoc-eq-hack (x y)
  (cond ((atom y) nil)
        (t (let ((h (gethash y *assoc-eq-hack-ht*)))
             (cond (h (gethash x (the hash-table h)))
                   (t (setq h (mht :test 'eq))
                      (setf (gethash y *assoc-eq-hack-ht*)
                            h)
                      (loop for pair in y do
                            (setf (gethash (car pair)
                                           (the hash-table h))
                                  pair))
                      (gethash x (the hash-table h))))))))

(defun abbrev (x &optional
                (level *print-level*)
                (length *print-length*))
  (cond ((atom x) x)
        ((eql level 0) '?)
        ((eql length 0) '?)
        (t (let ((pair (assoc-eq-hack
                        x (table-alist 'evisc-table
                                       (w *the-live-state*)))))
             (cond (pair (cdr pair))
                   (t (let ((a (abbrev (car x)
                                       (and level (1- level))
                                       length))
                            (d (abbrev (cdr x)
                                       level
                                       (and length (1- length)))))
                        (cond ((and (eq a (car x))
                                    (eq d (cdr x)))
                               x)
                              ((and (eq a '?)
                                    (eq d '?))
                               '?)
                              (t (cons a d))))))))))
                                       
(defun prine (obj &optional stream)
  (let ((*print-pretty* nil))
    (princ (abbrev obj *print-level* *print-length*) stream)))


(defun prine-alist (obj &optional stream)

  ; Does not print the last atom.
  ; Prints "=" between pairs.

  (let ((*print-pretty* t))
    (let ((max 6))
      (cond
       ((loop for tail on obj always
              (and
               (consp (car tail))
               (atom (caar tail))
               (setq max (max max
                              (if (symbolp (caar tail))
                                  (length (symbol-name (caar tail)))
                                0)))))
        (loop for tail on obj do
              (cond ((eq obj tail) (write-char #\Space stream))
                    (t (oft "~&    ")))
              (princ (caar tail) stream)
              (loop for i fixnum below
                    (- max
                       (if (symbolp (caar tail))
                           (length (symbol-name (caar tail)))
                         0))
                    do (write-char #\Space stream))
              (princ " = ")
              (prine (cdar tail) stream)))
       (t (prine obj stream))))))

; MEMOIZE-FN

(defn1 mf-trace-exit (fn nrv ans)
  (oftr "~%< ~s " fn)
  (cond ((> nrv 1)
         (oftr "returned ~@r values:" nrv)
         (loop for i fixnum from 1 to nrv do
               (oft "~%~@r.~8t  " i)
               (prine (car ans) *trace-output*)))
        (t (prine ans *trace-output*)))
  (oftr ")~%"))

(defmacro defnmem (fn args body &key
                      (condition t)
                      (inline t)
                      (trace nil)
                      (specials nil))

  "DEFNMEM is a raw Lisp macro. (DEFNMEM fn args body) both DEFUNs and
   MEMOIZEs FN.  The CL-DEFUN, STOBJS-IN, FORMALS, and STOBJS-OUT
   options to MEMOIZE-FN are taken from ARGS, which may not use STATE
   or STOBJS.  FN is declared to return only one value."

  `(progn
     (when (intersection ',args lambda-list-keywords)
       (ofe "defnmem: In the defintion of ~s, the argument list ~s ~
             contains a member of lambda-list-keywords so do not ~
             use defnmem."
            ',fn ',args))
     (setf (gethash ',fn *number-of-arguments-and-values-ht*)
           (cons ,(length args) 1))
     (declaim (ftype (function ,(make-list-t (length args))
                               (values t))
                     ,fn))
     (defun ,fn ,args ,body)
     (memoize-fn ',fn
                 :condition ',condition
                 :inline ',inline
                 :trace ',trace
                 :specials ',specials
                 :cl-defun '(defun ,fn ,args ,body)
                 :stobjs-in (make-list (length ',args))
                 :formals ',args
                 :stobjs-out '(nil))
     ',fn))

(defn fle (x)

  "FLE is akin to the ANSI Common Lisp standard function
  FUNCTION-LAMBDA-EXPRESSION.  'FLE' is shorter.  (FLE 'foo) may
  return, among other things, the defining body of the function FOO.
  In Clozure Common Lisp, definition saving is controlled by the
  settings of the variables CCL::*SAVE-DEFINITIONS* and
  CCL::*FASL-SAVE-DEFINITIONS*.  Under Closure Common Lisp, we may
  also first print the name of the file in which FOO was defined."

  #+Clozure
  (let ((loc (ccl::find-definition-sources x)))
    (let ((*print-pretty* nil))
      (when loc (oft "~%; source: ~s" loc))))
  (cond ((functionp x)
         (function-lambda-expression x))
        ((symbolp x)
         (let ((fn (symbol-function x)))
           (cond ((functionp fn)
                  (function-lambda-expression fn))
                 #+Clozure
                 ((and (arrayp fn) (functionp (aref fn 1)))
                  (function-lambda-expression (aref fn 1)))
                 (t (ofe "Can't figure out ~a as a function." x)))))))

(defg *memoize-fn-signature-error*
  "
  Memoize-fn: could not determine a signature for ~a.~%~
  To assert the (number-of-inputs . number-of-outputs)~%~
  signature of ~:*~a, put a cons of two numbers in the hash-table ~%~
  *NUMBER-OF-ARGUMENTS-AND-VALUES-HT* under ~:*~a.  For example, ~%~
  do (setf (gethash '~:*~a *NUMBER-OF-ARGUMENTS-AND-VALUES-HT*)
         '(3 . 1))")

(defg *sort-to-from-by-calls* nil)

(defconstant *attached-fn-temp* (make-symbol "ATTACHED-FN-TEMP"))

(defvar *memoize-use-attachment-warning-p* t)

(defun memoize-use-attachment-warning (fn at-fn)
  (when *memoize-use-attachment-warning-p*
    (with-live-state
     (warning$ 'top-level "Attachment"
               "Although the function ~x0 is memoized, a result is not being ~
                stored because ~@1.  Warnings such as this one, about not ~
                storing results, will remain off for all functions for the ~
                remainder of the session unless the variable ~x2 is set to a ~
                non-nil value in raw Lisp."
               fn
               (mv-let (lookup-p at-fn)
                       (if (consp at-fn)
                           (assert$ (eq (car at-fn) :lookup)
                                    (mv t (cdr at-fn)))
                         (mv nil at-fn))
                       (cond (lookup-p
                              (msg "a stored result was used from a call of ~
                                    memoized function ~x0, which may have been ~
                                    computed using attachments"
                                   at-fn))
                             (t
                              (msg "an attachment to function ~x0 was used ~
                                    during evaluation of one of its calls"
                                   at-fn))))
               '*memoize-use-attachment-warning-p*))
    (setq *memoize-use-attachment-warning-p* nil)))

(defun memoize-fn (fn &key (condition t) (inline t) (trace nil)
                      (cl-defun :default)
                      (formals :default)
                      (stobjs-in :default)
                      (stobjs-out :default)
                      (commutative nil)
                      (specials nil)
                      (watch-ifs nil)
                      (forget nil)
                      (memo-table-init-size *mht-default-size*)
                      (aokp nil)
                      &aux (wrld (w *the-live-state*)))

  "The documentation for MEMOIZE-FN is very incomplete.  One may
  invoke (MEMOIZE-FN fn) on the name of a Common Lisp function FN from
  outside the ACL2 loop to get results of possible interest in terms
  of memoization activity and profiling information.  MEMOIZE-FN
  already has a dozen parameters.

  MEMOIZE-FN replaces the SYMBOL-FUNCTION for the symmbol FN with
  'enhanced' raw Common Lisp code that, supposedly, does not affect
  the value returned by FN but may make some notes and may even obtain
  some return values by remembering them from a previous call.

  If the CONDITION parameter is not NIL, then whenever FN is called,
  and there is not as yet any value remembered for a call of FN on the
  given arguments, then if the evaluation of the CONDITION parameter
  is not NIL, the values that are computed for FN on the given
  arguments will be saved under the given arguments.  If the CONDITION
  parameter is the name of an ACL2 function, the body of that function
  is used as the condition.

  If the INLINE parameter is T, then when MEMOIZE-FN creates a new
  body for FN, we place the old body of FN within the new body, i.e.,
  'in line'.  However, if the INLINE parameter is NIL, then we place
  code that calls the existing SYMBOL-FUNCTION for FN within the new
  body.  One might well argue that our parity for the INLINE parameter
  to MEMOIZE-fn is backwards, but we don't think so.

  The TRACE parameter to MEMOIZE-FN may be T, NIL, :INLINE, or
  :NOTINLINE.

  One may lie to MEMOIZE-FN to force the memoization of a function
  that has ACL2's state as an explicit parameter by using fraudulent
  FORMALS, STOBJS-IN, and STOBJS-OUT parameters to MEMOIZE-FN.

  If the COMMUTATIVE parameter is not NIL, then the two arguments may
  be swapped before further processing.  We hope/presume that ACL2
  will have been used first to prove that commutativity.

  If the CL-DEFN parameter is not NIL, we pretend that the current
  body of FN is that parameter, and similarly for FORMALS, STOBJS-IN,
  and STOBJS-OUT.

  If FN is a raw Common Lisp function and not an ACL2-approved
  function, it may make reference to a variable, say S, that has a
  SPECIAL binding, in which case one needs to consider what in the
  world the meaning is for memoizing such a function at all.  If S is
  a member of the SPECIALS parameter, then it is assumed that FN does
  not alter but only refers to S.  MEMOIZE-FN acts as though FN had S
  as an extra argument for purposes of memoization.

  The WATCH-IFS parameter to MEMOIZE-FN has meaning only when using
  Clozure Common Lisp (CCL).  Under CCL, if the WATCH-IFS parameter is
  not NIL, then every branch of every IF (including OR, AND, COND, and
  CASE) expression in the source code for FN is inflicted with an
  emendation that monitors how many times the true or false branch is
  taken.  This information is printed both by (MEMOIZE-SUMMARY) and in
  more detail by (IF-REPORT).

  If the FORGET parameter is not NIL, the pons and memo tables of FN
  are cleared at the end of every outermost call of FN."

; MIS-ORDERED-COMMUTATIVE-ARGS apparently, but only apparently,
; introduces nondeterminism into the values returned by ACL2 functions
; redefined with MEMOIZE-FN, something highly suspicious because it
; can so easily lead to a contradition.

; We believe that the use of the nondeterministic function
; MIS-ORDERED-COMMUTATIVE-ARGS in the memoization of an ACL2 function
; of two arguments that has been proven commutative is justified by
; the fact that the memoized function will return, modulo EQUAL, the
; same result regardless of what MIS-ORDERED-COMMUTATIVE-ARGS returns,
; and hence the nondeterminism cannot be detected by the ACL2 logic.

; WATCH-IFS forces INLINE.

  (when watch-ifs (setq inline t))

  (unwind-mch-lock
   (cond ((fboundp 'maybe-untrace!)
          (maybe-untrace! fn))
         ((fboundp 'old-untrace)
          (eval `(old-untrace ,fn))))
   (with-warnings-suppressed
    (unless *memoize-init-done*
      (ofe "Memoize-fn:  *MEMOIZE-INIT-DONE* is still nil."))
    (unless (symbolp fn)
      (ofe "Memoize-fn: ~s is not a symbol.") fn)
    (unless (or (fboundp fn) (not (eq cl-defun :default)))
      (ofe "Memoize-fn: ~s is not fboundp." fn))
    (when (or (macro-function fn)
              (special-operator-p fn)
              (compiler-macro-function fn))
      (ofe "Memoize-fn: ~s is a macro or a special operator or has ~
            a compiler macro." fn))
    (when (gethash fn *never-profile-ht*)
      (ofe "Memoize-fn: ~s is in *NEVER-PROFILE-HT*"
           fn))
    (when (memoizedp-raw fn)
      (ofd "~%; Memoize-fn: ** Warning: ~s is currently memoized. ~
          ~%; So first we unmemoize it and then memoize it again."
           fn)
      (unmemoize-fn fn))
    (when (member fn (eval '(trace)))
      (ofd "~%; Memoize-fn:  Untracing ~s before memoizing it." fn)
      (eval `(untrace ,fn)))

; TRACE, UNTRACE, OLD-TRACE, and OLD-UNTRACE are macros that get
; redefined sometimes.  So we use EVAL in calling them.

    #+Clozure
    (when (ccl::%advised-p fn)
      (ofe "~%; Memoize-fn: Please unadvise ~s before calling ~
            memoize-fn on it."
           fn))      
    (when (and (fboundp 'old-trace)
               (member fn (eval '(old-trace))))
      (ofd "~%; Memoize-fn:  Old-untracing ~s before memoizing it."
           fn)
      (eval `(old-untrace ,fn)))
    (when (eq fn 'return-last)
      (ofe "Memoize-fn: RETURN-LAST may not be memoized."
           fn))
    (when (getprop fn 'constrainedp nil 'current-acl2-world wrld)
      (ofe "Memoize-fn: ~s is constrained; you may instead wish ~%~
            to memoize a caller or to memoize its attachment (see ~%~
            :DOC defattach)."
           fn))
    #+Clozure
    (when (multiple-value-bind (req opt restp keys)
              (ccl::function-args (symbol-function fn))
            (or restp
                keys
                (not (integerp req))
                (not (eql opt 0))))
      (ofe "Memoize-fn: ~a has non-simple arguments." fn))
    (let*
      ((cl-defun (if (eq cl-defun :default)
                     (if inline
                         (cond
                          ((not (fboundp fn))
                           (ofe "MEMOIZE-FN: ** ~a is undefined."
                                fn))
                          ((cltl-def-from-name fn nil wrld))
                          ((function-lambda-expression
                            (symbol-function fn)))
                          (t
                           #+Clozure
                           (unless (and ccl::*save-source-locations*
                                        ccl::*fasl-save-definitions*)
                             (ofd "~&; Check the settings of ~
                                   CCL::*SAVE-SOURCE-LOCATIONS* ~
                                   and ~
                                   CCL::*FASL-SAVE-DEFINITIONS*."))
                           (ofe "MEMOIZE-FN: ** Cannot find a ~
                                      definition for ~a via ACL2 ~
                                      or ~
                                      FUNCTION-LAMBDA-EXPRESSION."
                                fn))) nil)
                   cl-defun))
       (formals
        (if (eq formals :default)
            (let ((fo (getprop fn 'formals t 'current-acl2-world wrld)))
              (if (eq fo t)
                  (if (consp cl-defun)
                      (cadr cl-defun)
                    (let ((n (number-of-arguments fn)))
                      (if n
                          (loop for i fixnum below n
                                collect (ofni "X~a" i))
                        (ofe *memoize-fn-signature-error* fn))))
                fo))
          formals))
       (stobjs-in (if (eq stobjs-in :default)
                      (let ((s (getprop fn 'stobjs-in t 'current-acl2-world
                                        wrld)))
                        (if (eq s t) (make-list (len formals)) s))
                    stobjs-in))
       (stobjs-out
        (if (eq stobjs-out :default)
            (let ((s (getprop fn 'stobjs-out t 'current-acl2-world wrld)))
              (if (eq s t)
                  (let ((n (number-of-return-values fn)))
                    (cond (n (make-list n))
                          ((and (null condition)
                                (null trace))
                           (list nil nil))
                          (t (ofe
                              "Memoize-fn: cannot determine the ~
                               number of return values of ~a.~%~
                               You may put a cons of ~
                               two numbers in the hash-table~%~
                               *NUMBER-OF-ARGUMENTS-AND-VALUES-HT* ~
                               under ~a. ~%For example, do (setf ~
                               (gethash '~a ~
                               *NUMBER-OF-ARGUMENTS-AND-VALUES-HT*) ~
                               '(~a . 1))"
                              fn fn fn (len stobjs-in)))))
                    s))
          stobjs-out)))
      (unless (and (symbol-listp formals)
                   (no-duplicatesp formals)
                   (loop for x in formals never (constantp x)))
        (ofe "Memoize-fn: FORMALS, ~a, must be a true list of ~
              distinct, nonconstant symbols."
             formals))
      (when (intersection lambda-list-keywords formals)
        (ofe "Memoize-fn: FORMALS, ~a, may not intersect ~
              LAMBDA-LIST-KEYWORDS."))
      (when (and condition (or (member 'state stobjs-in)
                               (member 'state stobjs-out)))
        (ofe "Memoize-fn:  ~s uses STATE." fn))
      (let*
        ((fnn (symbol-to-fixnum-create fn))
         (2mfnn (* *2max-memoize-fns* fnn))
         (*acl2-unwind-protect-stack*
          (or *acl2-unwind-protect-stack*
              (cons nil *acl2-unwind-protect-stack*)))
         (old-fn (if (fboundp fn) (symbol-function fn)))
         (body (if (or inline (null old-fn))
                   (car (last cl-defun))
                 `(funcall ,old-fn ,@formals)))
         (body-name (make-symbol "BODY-NAME"))
         (body-call (list body-name))
         (condition-body
          (cond ((booleanp condition) condition)
                ((symbolp condition)
                 (car (last (cltl-def-from-name condition nil wrld))))
                (t condition)))
         (dcls (dcls (cdddr (butlast cl-defun))))
         (start-time (let ((v (hons-gentemp
                               (suffix "START-TIME-" fn))))
                       (eval `(prog1 (defg ,v -1)
                                (declaim (type integer ,v))))))
         (tablename
          (eval `(defg
                   ,(hons-gentemp (suffix "MEMOIZE-HT-FOR-" fn))
                   nil)))
         (localtablename (make-symbol "TABLENAME"))
         (ponstablename
          (eval `(defg
                   ,(hons-gentemp (suffix "PONS-HT-FOR-" fn))
                   nil)))
         (localponstablename (make-symbol "PONSTABLENAME"))
         (sts (loop for x in (union stobjs-in stobjs-out)
                    when x collect (st-lst x)))
         (nra (+ (len formals) (len specials)))
         def
         success)
        (let*
          ((mf-trace-exit
            (and trace `((mf-trace-exit ',fn ,(length stobjs-out)
                                        ,*mf-ans*))))
           (mf-record-mht
            (and *record-mht-calls*
                 `((safe-incf (aref ,*mf-ma* ,2mfnn) 1 ,fn))))
           (mf-record-hit
            (and *record-hits* condition-body
                 `((safe-incf (aref ,*mf-ma*
                                    ,(+ 2mfnn *ma-hits-index*))
                              1 ,fn))))
           (lookup-marker (cons :lookup fn))
           (body3
            `(let (,*mf-ans* ,*mf-args* ,*mf-ans-p*)
               (declare (ignorable ,*mf-ans* ,*mf-args* ,*mf-ans-p*))
               (profiler-cond
                ((not ,condition-body)
                 ,@mf-record-hit ; sort of a hit
                 ,(if (not trace)
                      body-call
                    (if (cdr stobjs-out)
                        `(progn
                           (setq ,*mf-ans*
                                 (multiple-value-list ,body-call))
                           ,@mf-trace-exit
                           (values-list ,*mf-ans*))
                      `(progn (setq ,*mf-ans* ,body-call)
                              ,@mf-trace-exit
                              ,*mf-ans*))))
                ,@(and
                   condition-body
                   `((t
                      (profiler-when
                       (null ,tablename)
                       ,@mf-record-mht
                       (setq ,tablename
                             (make-initial-memoize-hash-table
                              ',fn ,memo-table-init-size))
                       ,@(if (> nra 1)
                             `((setq ,ponstablename
                                     (make-initial-memoize-pons-table
                                      ',fn ,memo-table-init-size)))))
                        ;; To avoid a remotely possible
                        ;; parallelism gethash error.
                        ,@(if (> nra 1)
                              `((setq ,localponstablename
                                      (profiler-or ,ponstablename
; BOZO should this be a make-initial-memoize-pons-table?
                                                   (mht)))))
                        #+parallel
                        ,@(if (> nra 1)
                              `((ccl::lock-hash-table ,localponstablename)))
                        (setq ,*mf-args* (pist* ,localponstablename
                                                ,@formals
                                                ,@specials))
                        #+parallel
                        ,@(if (> nra 1)
                              `((ccl::unlock-hash-table ,localponstablename)))
                        (setq ,localtablename
; BOZO should this be a make-initial-memoize-hash-table?
                              (profiler-or ,tablename (mht)))
                        (multiple-value-setq
                            (,*mf-ans* ,*mf-ans-p*)
                          ,(let ((gethash-form
                                  `(gethash ,*mf-args*
                                            (the hash-table ,localtablename))))
                             (cond (aokp `(profiler-cond
                                           (*aokp* ,gethash-form)
                                           (t (mv nil nil))))
                                   (t gethash-form))))
                        (profiler-cond
                         (,*mf-ans-p*
                          ,@(when aokp
                              `((update-attached-fn-called ',lookup-marker)))
                          ,@(if trace `((oftr "~% ~s remembered."
                                              ',fn)))
                          ,@mf-record-hit
                          ,@(cond
                             ((null (cdr stobjs-out))
                              `(,@mf-trace-exit ,*mf-ans*))
                             (t
                              (let ((len-1 (1- (length stobjs-out))))
                                `(,@(and
                                     trace
                                     `(progn
                                        (let* ((,*mf-ans*
                                                (append
                                                 (take ,len-1 ,*mf-ans*)
                                                 (list
                                                  (nthcdr ,len-1 ,*mf-ans*)))))
                                          ,@mf-trace-exit)))
                                  ,(cons
                                    'mv
                                    (nconc (loop for i fixnum below len-1
                                                 collect `(pop ,*mf-ans*))
                                           (list *mf-ans*))))))))
                         (t ,(let* ((vars
                                     (loop for i fixnum below
                                           (if (cdr stobjs-out)
                                               (length stobjs-out)
                                             1)
                                           collect (ofni "O~a" i)))
                                    (prog1-fn (if (cdr stobjs-out)
                                                  'multiple-value-prog1
                                                'prog1))
                                    (mf-trace-exit+
                                     (and mf-trace-exit
                                          `((let ((,*mf-ans*
                                                   ,(if stobjs-out
                                                        `(list* ,@vars)
                                                      (car vars))))
                                              ,@mf-trace-exit)))))
                               `(let (,*attached-fn-temp*)
                                  (mv?-let
                                   ,vars
                                   (let (*attached-fn-called*)
                                     (,prog1-fn
                                      ,body-call
                                      (setq ,*attached-fn-temp*
                                            *attached-fn-called*)))
                                   (progn
                                     (cond
                                      ,@(and (not aokp)
                                             `((,*attached-fn-temp*
                                                (memoize-use-attachment-warning
                                                 ',fn ,*attached-fn-temp*))))
                                      (t
                                       (setf
                                        (gethash ,*mf-args*
                                                 (the hash-table
                                                   ,localtablename))
                                        (list* ,@vars))))
                                     (update-attached-fn-called
                                      ,*attached-fn-temp*)
                                     ,@mf-trace-exit+
                                     (mv? ,@vars)))))))))))))
           (body2
            `(let ((,*mf-old-caller* *caller*)
                   #+Clozure
                   ,@(and *record-bytes*
                          `((,*mf-start-bytes*
                             (heap-bytes-allocated))))
                   ,@(and *record-hons-calls*
                          `((,*mf-start-hons* *hons-call-counter*)))
                   ,@(and *record-pons-calls*
                          `((,*mf-start-pons* *pons-call-counter*))))
               (declare
                (ignorable
                 #+Clozure
                 ,@(and *record-bytes* `(,*mf-start-bytes*))
                 ,@(and *record-hons-calls* `(,*mf-start-hons*))
                 ,@(and *record-pons-calls* `(,*mf-start-pons*)))
                (type fixnum
                      ,*mf-old-caller*
                      ,@(and *record-hons-calls* `(,*mf-start-hons*))
                      ,@(and *record-pons-calls* `(,*mf-start-pons*))
                      #+Clozure
                      ,@(and *record-bytes* `(,*mf-start-bytes*))))
               (unwind-protect
                   (progn
                     (setq ,start-time ,(if *record-time*
                                            '(internal-real-time)
                                          '0))
                     (setq *caller* ,2mfnn)
                     ,body3)
                 ,@(and *record-hons-calls*
                        `((safe-incf
                           (aref
                            ,*mf-ma*
                            ,(+ *ma-hons-index* 2mfnn))
                           (the mfixnum
                             (- *hons-call-counter*
                                ,*mf-start-hons*))
                           ,fn)))
                 ,@(and *record-pons-calls*
                        `((safe-incf
                           (aref ,*mf-ma* ,(+ *ma-pons-index* 2mfnn))
                           (the mfixnum
                             (- *pons-call-counter*
                                ,*mf-start-pons*))
                           ,fn)))
                 #+Clozure
                 ,@(and *record-bytes*
                        `((safe-incf
                           (aref ,*mf-ma* ,(+ *ma-bytes-index* 2mfnn))
                           (the mfixnum
                             (- (heap-bytes-allocated)
                                ,*mf-start-bytes*))
                           ,fn)))
                 ,@(and *record-time*
                        `((safe-incf
                           (aref ,*mf-ma*
                                 (the mfixnum (1+ ,*mf-count-loc*)))
                           (mod
                            (the integer (- (internal-real-time)
                                            ,start-time))
                            most-positive-mfixnum)
                           ,fn)))
                 ,@(and forget `((setq ,tablename nil)
                                 ,@(if (> nra 1)
                                       `((setq ,ponstablename nil)))))
                 (setq ,start-time -1)
                 (setq *caller* ,*mf-old-caller*)))))
          (setq def
            `(defun ,fn ,formals ,@dcls
               ,@(if trace
                     (if (member trace '(notinline inline))
                         `((declare (,trace ,fn)))
                       `((declare (notinline ,fn)))))
               (declare (ignorable ,@formals ,@specials))
               ,@(and commutative
                      `((cond ((mis-ordered-commutative-args
                                ,(car formals)
                                ,(cadr formals))
                               (rotatef ,(car formals)
                                        ,(cadr formals))))))
               ,@(and trace
                      `((oftr "~%(> ~s (" ',fn)
                        ,@(loop for v in (append formals specials)
                                append
                                `((oftr "~& ~s = " ',v)
                                  (prine ,v *trace-output*)))
                        (oftr "~& )")))
               (let* ((,*mf-count-loc*
                       ,(if (or *record-calls* *record-time*)
                            `(the fixnum (+ *caller* (* 2 ,fnn)))
                            0))
                      (,*mf-ma* *memoize-call-array*)
                      ,localtablename ,localponstablename)
                 (declare (type fixnum ,*mf-count-loc*)
                          (ignorable ,*mf-count-loc* ,*mf-ma*
                                     ,localponstablename
                                     ,localtablename)
                          (type (simple-array mfixnum (*))
                                ,*mf-ma*))
                 ,@(and *record-calls*
                        `((safe-incf (aref ,*mf-ma*
                                           ,*mf-count-loc*)
                                     1
                                     ,fn)))
                 (flet ((,body-name () ,body))
                   (profiler-if (eql -1 ,start-time)
                                ,body2
                                ,body3))))))
        (setf (gethash fn *number-of-arguments-and-values-ht*)
              (cons (length stobjs-in) (length stobjs-out)))
        (unwind-protect
          (progn
            (let ((ma *memoize-call-array*))
              (declare (type (simple-array mfixnum (*)) ma))
              (loop for i fixnum from 2mfnn
                    below (the fixnum (+ 2mfnn *2max-memoize-fns*))
                    unless (eql (aref ma i) 0)
                    do (setf (aref ma i) 0)))
            (memoize-eval-compile def watch-ifs)
            (setf (gethash fn *memoize-info-ht*)
                  (make memoize-info-ht-entry
                        :fn fn
                        :ext-anc-attachments
                        (and aokp (extended-ancestors fn wrld))
                        :tablename tablename
                        :ponstablename ponstablename
                        :old-fn old-fn
                        :memoized-fn (symbol-function fn)
                        :condition condition
                        :inline inline
                        :num fnn
                        :sts sts
                        :trace trace
                        :start-time start-time
                        :cl-defun cl-defun
                        :formals formals
                        :commutative commutative
                        :specials specials
                        :stobjs-in stobjs-in
                        :stobjs-out stobjs-out
                        :record-bytes      *record-bytes*
                        :record-calls      *record-calls*
                        :record-hits       *record-hits*
                        :record-hons-calls *record-hons-calls*
                        :record-mht-calls  *record-mht-calls*
                        :record-pons-calls *record-pons-calls*
                        :record-time       *record-time*
                        :watch-ifs         watch-ifs
                        :forget            forget
                        :memo-table-init-size memo-table-init-size))
            (setf (gethash fnn *memoize-info-ht*) fn)
            (and condition (loop for s in sts do
                                 (push tablename
                                       (symbol-value s))))
            (setq success t))
          (unless success
            (setf (symbol-function fn) old-fn)
            (remhash fn *memoize-info-ht*)
            (remhash fnn *memoize-info-ht*)
            (maphash (lambda (k v)
                       (when (eq fn (cadr v))
                         (remhash k *form-ht*)))
                     *form-ht*)
            (and condition
                 (loop for s in sts
                       when (eq tablename
                                (car (symbol-value
                                      (the symbol s))))
                       do (pop (symbol-value (the symbol s)))))
            (ofd "~&; Memoize-fn:  Failed to memoize ~s." fn)
            (setq fn nil)))))))
  fn)

(defn1 unmemoize-fn (fn)
  (unwind-mch-lock
   (maybe-untrace! fn)
   (let* ((ma *memoize-call-array*)
          (l (memoizedp-raw fn)))
     (declare (type (simple-array mfixnum (*)) ma))
     (unless l (ofe "Unmemoize-fn: ~s is not memoized." fn))
     (let* ((num (the fixnum (access memoize-info-ht-entry l
                                     :num)))
            (tablename (and l (access memoize-info-ht-entry l
                                      :tablename)))
            (n2 (* num *2max-memoize-fns*))
            (w (access memoize-info-ht-entry l :watch-ifs)))
       (declare (fixnum num n2))

       #+Clozure
       (when w
         (maphash (lambda (k v)
                    (when (eq fn (cadr v))
                      (remhash k *form-ht*)))
                  *form-ht*))

; Note: condition is a first-class ACL2 function, not to be messed
; with here.

       (let (#+Clozure (ccl:*warn-if-redefine-kernel* nil))
         (let ((old-fn (access memoize-info-ht-entry
                               l :old-fn)))
           (if old-fn
               (setf (symbol-function (the symbol fn)) old-fn)
             (fmakunbound fn))))
       (loop for i fixnum from n2
             below (the fixnum (+ n2 *2max-memoize-fns*))
             unless (eql (aref ma i) 0)
             do (setf (aref ma i) 0))
       (remhash fn *memoize-info-ht*)
       (remhash num *memoize-info-ht*)
       (setf (symbol-value (the symbol tablename)) nil)
       (setf (symbol-value
              (the symbol (access memoize-info-ht-entry
                                  l :ponstablename)))
             nil)
       (loop for s in (access memoize-info-ht-entry l :sts) do
             (when (boundp s)
               (setf (symbol-value (the symbol s))
                     (remove tablename (symbol-value
                                        (the symbol s)))))))))
  fn)

(defn1 maybe-unmemoize (fn)

; We rely on the normal undoing mechanism (for :ubt etc.) to take care of
; unmemoization.  However, as a courtesy to users who memoize using raw Lisp,
; we provide and call this utility for unmemoizing functions that are not known
; to ACL2 (via the memoize-table) as being memoized.

  (when (and (memoizedp-raw fn)
             (not (cdr (assoc-eq fn (table-alist 'memoize-table
                                                 (w *the-live-state*))))))
    (unmemoize-fn fn)))

(defn1 memoized-functions ()
  (our-lock-unlock-memoize1
  (let (l)
    (maphash (lambda (fn v) (declare (ignore v))
               (when (symbolp fn) (push fn l)))
             *memoize-info-ht*)
    l)))

(defn1 length-memoized-functions ()

  "(length-memoized-functions) returns the number of currently
  memoized/profiled functions."

  (values (floor (1- (hash-table-count (the hash-table
                                         *memoize-info-ht*)))
                 2)))

(defn1 unmemoize-all ()

  "(UNMEMOIZE-ALL) unmemoizes all currently memoized functions,
  including all profiled functions."

; A warning to would-be code improvers.  It would be a bad idea to
; redefine UNMEMOIZE-ALL to MAPHASH over *MEMOIZE-INFO-HT* because of
; the ANSI rules restricting which hash table entries may be modified
; during a MAPHASH.

  (loop for x in (memoized-functions) do (unmemoize-fn x)))

(defn1 memoize-info (k)

  "(MEMOIZE-INFO k) returns the settings of the various arguments to
  MEMOIZE-FN and the settings of the special variables that influence
  MEMOIZE-FN during the memoization of K."

  (let ((v (gethash k *memoize-info-ht*)))
    (and v
         (list (list (access memoize-info-ht-entry v :fn)
                     :condition
                     (access memoize-info-ht-entry v :condition)
                     :inline
                     (access memoize-info-ht-entry v :inline)
                     :trace
                     (access memoize-info-ht-entry v :trace)
                     :cl-defun
                     (access memoize-info-ht-entry v :cl-defun)
                     :formals
                     (access memoize-info-ht-entry v :formals)
                     :stobjs-in
                     (access memoize-info-ht-entry v :stobjs-in)
                     :specials
                     (access memoize-info-ht-entry v :specials)
                     :commutative
                     (access memoize-info-ht-entry v :commutative)
                     :stobjs-out
                     (access memoize-info-ht-entry v
                             :stobjs-out)
                     :watch-ifs
                     (access memoize-info-ht-entry v :watch-ifs)
                     :forget
                     (access memoize-info-ht-entry v :forget)
                     :memo-table-init-size
                     (access memoize-info-ht-entry v
                             :memo-table-init-size))

               (list
                (access memoize-info-ht-entry v :record-bytes)
                (access memoize-info-ht-entry v :record-calls)
                (access memoize-info-ht-entry v :record-hits)
                (access memoize-info-ht-entry v
                        :record-hons-calls)
                (access memoize-info-ht-entry v
                        :record-mht-calls)
                (access memoize-info-ht-entry v
                        :record-pons-calls)
                (access memoize-info-ht-entry v :record-time))))))

(defn1 rememoize-all ()
  (our-lock-unlock-memoize1
      (let (l)
        (maphash
         (lambda (k v)
           (declare (ignore v))
           (when (symbolp k) (push (memoize-info k) l)))
         *memoize-info-ht*)
        (loop for x in l do (unmemoize-fn (caar x)))
        (gc$)
        (clrhash *form-ht*)
        (setq *max-symbol-to-fixnum*
              *ma-initial-max-symbol-to-fixnum*)
        (loop for x in l do
              (progv '(*record-bytes*
                       *record-calls*
                       *record-hits*
                       *record-hons-calls*
                       *record-mht-calls*
                       *record-pons-calls*
                       *record-time*)
                  (cadr x)
                (apply 'memoize-fn (car x)))))))

(defn1 uses-state (fn)
  (let* ((w (w *the-live-state*))
         (stobjs-in (getprop fn 'stobjs-in t 'current-acl2-world w))
         (stobjs-out (getprop fn 'stobjs-out t
                              'current-acl2-world w)))
    (or (and (consp stobjs-in) (member 'state stobjs-in))
        (and (consp stobjs-out) (member 'state stobjs-out)))))

(defn memoize-here-come (n)
  (let ((m (ceiling
            (+ 100 (* 1.1 (- n (- (/ *2max-memoize-fns* 2)
                                  (floor
                                   (/ (hash-table-count
                                       *memoize-info-ht*)
                                      2)))))))))
    (when (posp m) (memoize-call-array-grow (* 2 m)))))

(defun profile (fn &rest r &key (condition nil) (inline nil)
                   &allow-other-keys)

  "PROFILE is a raw Lisp function.  PROFILE is much too wicked to ever
  be a proper part of ACL2, but can be useful in Common Lisp debugging
  and performance analysis, including examining the behavior of ACL2
  functions.  PROFILE returns FN.

  (PROFILE fn) redefines FN so that a count will be kept of the calls
  of FN.  The information recorded may be displayed, for example, by
  invoking (MEMOIZE-SUMMARY).

  PROFILE calls MEMOIZE-FN to do its work.  By default, PROFILE gives
  the two keyword parameters CONDITION and INLINE of MEMOIZE-FN the
  value NIL.  Other keyword parameters for MEMOIZE-FN are passed
  through.

  Please only call PROFILE from the very top-level of raw Common Lisp,
  not from inside the ACL2 loop or inside code that is
  memoized/profiled.  (To exit the ACL2 loop, type :q and later
  reenter the ACL2 loop with (lp).)"

  (apply #'memoize-fn fn
         :condition condition
         :inline inline
         r))

(defn1 profiled-functions ()

  ; The profiled functions are hereby arbitrarily defined as those
  ; produced by MEMOIZE-FN with null :CONDITION and :INLINE fields.

  (let (l)
    (maphash
     (lambda (k v)
       (when (and (symbolp k)
                  (null (access memoize-info-ht-entry
                                v :condition))
                  (null (access memoize-info-ht-entry
                                v :inline)))
         (push k l)))
     *memoize-info-ht*)
    l))
  
(defn1 unmemoize-profiled ()

  "UNMEMOIZE-PROFILED is a raw Lisp function.  (UNMEMOIZE-PROFILED)
  unmemoizes and unprofiles all functions currently memoized with
  :CONDITION=NIL and :INLINE=NIL."

  (loop for x in (profiled-functions) do
        (unmemoize-fn (car x))))

(defun profile-acl2 (&key (start 0)
                          trace
                          watch-ifs
                          forget
                          (lots-of-info t))

  "PROFILE-ACL2 is a raw Lisp function.  (PROFILE-ACL2 :start 'foo)
   profiles many functions that have been accepted by ACL2, starting
   with the acceptance of the function foo.  However, if a function is
   regarded as DUBIOUS-TO-PROFILE, then it is not profiled and an
   explanation is printed."

  (let ((*record-bytes* #+Clozure lots-of-info #-Clozure nil)
        (*record-calls* lots-of-info)
        (*record-hits* lots-of-info)
        (*record-hons-calls* lots-of-info)
        (*record-mht-calls* lots-of-info)
        (*record-pons-calls* lots-of-info)
        (*record-time* lots-of-info))
    (unless (integerp start)
      (unless (symbolp start)
        (ofe "~%; PROFILE-ACL2: ** ~a is not an event." start))
      (setq start (event-number start))
      (unless (integerp start)
        (ofe "~%; PROFILE-ACL2: ** ~a is not an event." start)))
    (let ((fns-ht (make-hash-table :test 'eq)))
      (declare (hash-table fns-ht))
      (loop for p in (set-difference-equal
                      (strip-cars (known-package-alist *the-live-state*))
                      '("ACL2-INPUT-CHANNEL" "ACL2-OUTPUT-CHANNEL"
                        "COMMON-LISP" "KEYWORD"))
            do
            (do-symbols (fn p)
              (cond ((gethash fn fns-ht) nil)
                    ((or (not (fboundp fn))
                         (macro-function fn)
                         (special-form-or-op-p fn))
                     (setf (gethash fn fns-ht) 'no))
                    ((or (not (integerp (event-number fn)))
                         (< (event-number fn) start))
                     (setf (gethash fn fns-ht) 'no))
                    ((dubious-to-profile fn)
                     (setf (gethash fn fns-ht) 'no)
                     (ofv "Not profiling '~a' because it's ~a"
                          (shorten fn 20)
                          (dubious-to-profile fn)))
                    (t (setf (gethash fn fns-ht) 'yes)))))
      (maphash (lambda (k v)
                 (if (eq v 'no) (remhash k fns-ht)))
               fns-ht)
      (ofv "Profiling ~:d functions." (hash-table-count fns-ht))
      (memoize-here-come (hash-table-count fns-ht))
      (maphash
       (lambda (k v)
         (declare (ignore v))
         (profile k
                  :trace trace
                  :watch-ifs watch-ifs
                  :forget forget))
       fns-ht)
      (clear-memoize-call-array)
      (oft "~%(clear-memoize-call-array) invoked.")
      (ofn "~a function~:p newly profiled."
           (hash-table-count fns-ht)))))

(defun profile-all (&key trace (lots-of-info t) forget watch-ifs)

  "PROFILE-ALL is a raw Lisp function.  (PROFILE-ALL) profiles each
  symbol that has a function-symbol and occurs in a package known
  to ACL2, unless it is
  
   1. memoized,
   2. traced,
   3. in the package COMMON-LISP,
   4. in *NEVER-PROFILE-HT*, or
   5. in *PROFILE-REJECT-HT*
   6. otherwise rejected by DUBIOUS-TO-PROFILE."

  (let ((*record-bytes* #+Clozure lots-of-info #-Clozure nil)
        (*record-calls* lots-of-info)
        (*record-hits* lots-of-info)
        (*record-hons-calls* lots-of-info)
        (*record-mht-calls* lots-of-info)
        (*record-pons-calls* lots-of-info)
        (*record-time* lots-of-info))
    (let ((fns-ht (make-hash-table :test 'eq)))
      (declare (hash-table fns-ht))
      (loop for p in (set-difference-equal
                      (strip-cars (known-package-alist *the-live-state*))
                      '("ACL2-INPUT-CHANNEL" "ACL2-OUTPUT-CHANNEL"
                        "COMMON-LISP" "KEYWORD"))
            do
            (do-symbols (fn p)
              (cond ((gethash fn fns-ht) nil)
                    ((or (not (fboundp fn))
                         (macro-function fn)
                         (special-form-or-op-p fn))
                     (setf (gethash fn fns-ht) 'no))
                    ((dubious-to-profile fn)
                     (setf (gethash fn fns-ht) 'no)
                     (ofv "Not profiling '~a' because it's ~a"
                          (shorten fn 20)
                          (dubious-to-profile fn)))
                    (t (setf (gethash fn fns-ht) 'yes)))))
      (maphash (lambda (k v)
                 (if (eq v 'no) (remhash k fns-ht)))
               fns-ht)
      (ofv "Profiling ~:d functions." (hash-table-count fns-ht))
      (memoize-here-come (hash-table-count fns-ht))
      (maphash
       (lambda (k v) (declare (ignore v))
         (profile k
                  :trace trace
                  :watch-ifs watch-ifs
                  :forget forget))
       fns-ht)
      (clear-memoize-call-array)
      (oft "~%(clear-memoize-call-array) invoked.")
      (ofn "~a function~:p newly profiled."
           (hash-table-count fns-ht)))))

(defn functions-defined-in-form (form)
  (cond ((consp form)
         (cond ((and (symbolp (car form))
                     (fboundp (car form))
                     (cdr form)
                     (symbolp (cadr form))
                     (fboundp (cadr form))
                     (eql 0 (search "def" (symbol-name (car form))
                                    :test #'char-equal)))
                (list (cadr form)))
               ((member (car form) '(progn progn!))
                (loop for z in (cdr form) nconc
                      (functions-defined-in-form z)))))))

(defn functions-defined-in-file (file)
  (let ((x nil)
        (avrc (cons nil nil)))
    (our-syntax ; protects against changes to *package*, etc.
     (let ((*readtable* (copy-readtable nil)))
       (set-dispatch-macro-character
        #\# #\, #'(lambda (stream char n)
                    (declare (ignore stream char n))
                    (values)))
       (set-dispatch-macro-character
        #\#
        #\.
        #'(lambda (stream char n)
            (declare (ignore stream char n))
            (values)))
       (with-open-file (stream file)
         (ignore-errors
           (loop until (eq avrc (setq x (read stream nil avrc)))
                 nconc
                 (functions-defined-in-form x))))))))

(defun profile-file (file &rest r)
   
  "PROFILE-FILE is a raw Lisp function.  (PROFILE-FILE file) calls
  PROFILE on 'all the functions defined in' FILE, a relatively vague
  concept.  However, if packages are changed in FILE as it is read, in
  a sneaky way, or if macros are defined and then used at the top of
  FILE, who knows which functions will be profiled?  Functions that do
  not pass the test DUBIOUS-TO-PROFILE are not profiled.  A list of
  the names of the functions profiled is returned."

  (loop for fn in (functions-defined-in-file file)
        unless (dubious-to-profile fn)
        collect (apply #'profile fn r)))

;  MEMOIZE-LET

; It might be a good enhancement to HT-LET to permit the carrying
; forward, with HOPY-CONS-CONSUME, of other honses.

(defn1 not-memoized-error (f)
  (ofe "NOT-MEMOIZED-ERROR:  ~s is not memoized." f))

(defmacro memoize-let-raw (fn form)
  (let ((fn-name (gensym "FN-NAME"))
        (tablevalue (gensym "TABLEVALUE"))
        (ponstablevalue (gensym "PONSTABLEVALUE"))
        (h (gensym "H"))
        (ht1 (gensym "HT1")))
    `(let* ((,fn-name ,fn)
            (,h (memoizedp-raw ,fn-name)))
       (unless ,h (not-memoized-error ,fn-name))
       (let* ((,tablevalue
               (symbol-value
                (access memoize-info-ht-entry ,h :tablename)))
              (,ponstablevalue
               (symbol-value
                (access memoize-info-ht-entry ,h :ponstablename)))
; BOZO should probably use make-initial-memoize-hash-table
              (,ht1 (mht)))
         (unwind-protect
             (progn (setf (symbol-value
                           (access memoize-info-ht-entry ,h
                                   :tablename))
                          ,ht1)
                    (setf (symbol-value
                           (access memoize-info-ht-entry ,h
                                   :ponstablename))
                           (mht))
                    ,form)
           ;; During the evaluation of form, a change to a stobj may
           ;; result in tablename getting a new value, in which case
           ;; we may not restore its old value.  And a change in the
           ;; memoization status of fn would make a restoration
           ;; pointless.
           (let ((test (and (eq (symbol-value
                                 (access memoize-info-ht-entry
                                         ,h :tablename))
                                ,ht1)
                            (eq ,h (memoizedp-raw ,fn-name)))))
             (setf (symbol-value (access memoize-info-ht-entry
                                         ,h :tablename))
                   (and test ,tablevalue))
             (setf (symbol-value (access memoize-info-ht-entry
                                         ,h :ponstablename))
                   (and test ,ponstablevalue))))))))


; MEMOIZE-ON AND MEMOIZE-OFF

(defmacro memoize-on-raw (fn x)
  `(let* ((,*mo-f* ,fn) (,*mo-h* (memoizedp-raw ,*mo-f*)))
     (unless ,*mo-h* (not-memoized-error ,*mo-f*))
     (let ((,*mo-o* (symbol-function (the symbol ,*mo-f*))))
       (unwind-protect
           (progn (setf (symbol-function (the symbol ,*mo-f*))
                        (access memoize-info-ht-entry ,*mo-h*
                                :memoized-fn))
                  ,x)
         (setf (symbol-function (the symbol ,*mo-f*)) ,*mo-o*)))))

(defmacro memoize-off-raw (fn x)
  `(let* ((,*mo-f* ,fn) (,*mo-h* (memoizedp-raw ,*mo-f*)))
       (unless ,*mo-h* (not-memoized-error ,*mo-f*))
       (let ((,*mo-o* (symbol-function (the symbol ,*mo-f*))))
         (unwind-protect
             (progn (setf (symbol-function (the symbol ,*mo-f*))
                          (access memoize-info-ht-entry ,*mo-h*
                                  :old-fn))
                    ,x)
           (setf (symbol-function (the symbol ,*mo-f*)) ,*mo-o*)))))

(defn1 memoize-condition (fn)
  (let ((x (gethash fn *memoize-info-ht*)))
    (if x
        (access memoize-info-ht-entry x :condition)
      nil)))

(defn global-suppress-condition-nil-memoization ()
  (maphash
   (lambda (k l)
     (when (symbolp k)
       (when (null (memoize-condition l))
         (setf (symbol-function k)
               (access memoize-info-ht-entry l :old-fn)))))
   *memoize-info-ht*))

(defn global-restore-memoize ()
  (maphash (lambda (k l)
             (when (symbolp k)
               (setf (symbol-function k)
                     (access memoize-info-ht-entry l :memoized-fn))))
           *memoize-info-ht*))


; STATISTICS GATHERING AND PRINTING ROUTINES

(defg *memoize-summary-order-list*
  '(total-time number-of-calls)

  "*MEMOIZE-SUMMARY-ORDER-LIST* is a raw Lisp variable.  It is a list
  of functions that MEMOIZE-SUMMARY uses to sort all functions that
  are currently memoized in preparation for displaying information
  about them.  The order used is lexicographical, with the first order
  having the most weight.  Each order function takes one argument, a
  symbol, and returns a rational.

  The default is '(total-time number-of-calls).

  Options for the functions include:

     bytes-allocated
     bytes-allocated/call
     event-number
     execution-order
     hits/calls
     hons-calls
     pons-calls
     number-of-calls
     number-of-hits
     number-of-memoized-entries
     number-of-mht-calls
     symbol-name-order
     time-for-non-hits/call
     time/call
     total-time.
  ")

(defg *memoize-summary-limit* 20

  "*MEMOIZE-SUMMARY-LIMIT* is a raw Lisp variable whose value is the
  maximum number of functions upon which MEMOIZE-SUMMARY reports.  A
  NIL value means report on all.")

(defg *shorten-ht* (mht :test 'eql))

(defn shorten (x n)
  (cond ((and (stringp x) (<= (length x) n))
         x)
        (t
         (let ((x
                ;; Jared -- ugh, this was using maybe-str-hash directly.  It
                ;; looks like X is supposed to be a string or symbol.  Here's
                ;; a dumb approximation of the previous behavior:
                (if (stringp x)
                    (hons-copy x)
                  x)))
           (cond ((gethash x *shorten-ht*))
                 (t (let ((*print-pretty* nil)
                          (*print-length* 10)
                          (*print-level* 5)
                          (*print-lines* 2))
                      (let ((str
                             (with-output-to-string
                               (s)
                               (cond ((stringp x) (princ x s))
                                     (t (prin1 x s))))))
                        (setf (gethash x *shorten-ht*)
                              (cond ((<= (length str) n) str)
                                    ((setf (gethash x *shorten-ht*)
                                           (concatenate
                                            'string
                                            (subseq str 0 (max 0 n))
                                            "...")))))))))))))

(defg *memoize-summary-order-reversed* nil

  "*MEMOIZE-SUMMARY-ORDER-REVERSED* is a raw Lisp variable.  When it
  is not NIL, then MEMOIZE-SUMMARY reports on functions in order from
  least to greatest.")

(defg *print-alist-width* 45)

(defn1 print-alist (alist separation)
  (check-type separation (integer 0))
  (setq alist
        (loop for x in alist collect
              (progn
                (check-type x
                            (cons (or string symbol)
                                  (cons (or string (integer 0))
                                        null)))
                (list (shorten (car x) *print-alist-width*)
                      (if (integerp (cadr x))
                          (ofnum (cadr x))
                        (cadr x))))))
  (let* ((max1 (loop for x in alist maximize (length (car x))))
         (max2 (loop for x in alist maximize (length (cadr x))))
         (width (max (or *print-right-margin* 70)
                     (+ separation max1 max2))))
    (loop for x in alist do
          (fresh-line)
          (princ (car x))
          (loop for i
                below (- width (+ (length (car x))
                                  (length (cadr x))))
                do (write-char #\Space))
          (princ (cadr x))))
  nil)


(defn1 pons-summary ()
  (our-syntax-nice
   (let ((sssub 0) (nponses 0) (nsubs 0) (nponstab 0))
     (declare (type mfixnum sssub nponses nsubs))
   (oft "(defun pons-summary~%")
   (maphash
    (lambda (k v)
      (cond ((symbolp k)
             (let ((tab (symbol-value (access memoize-info-ht-entry v
                                              :ponstablename))))
               (when tab
                 (very-unsafe-incf nponstab 1 pons-summary)
                 (maphash
                  (lambda (k v) (declare (ignore k))
                    (cond
                     ((not (listp v))
                      (very-unsafe-incf
                       sssub
                       (hash-table-size (the hash-table v))
                       pons-summary)
                      (very-unsafe-incf
                       nponses (hash-table-count (the hash-table v))
                       pons-summary)
                      (very-unsafe-incf nsubs 1 pons-summary))
                     (t (very-unsafe-incf nponses (length v)
                                          pons-summary))))
                  tab))))))
    *memoize-info-ht*)
   (print-alist
    `((" Pons hits/calls"
       ,(let* ((c *pons-call-counter*)
               (d *pons-misses-counter*))
          (ofn "~,1e / ~,1e = ~,2f" d c (/ (- c d) (+ .0000001 c)))))
      (" Number of pons tables" ,(ofnum nponstab))
      (" Number of pons sub tables" ,(ofnum nsubs))
      (" Sum of pons sub table sizes" ,(ofnum sssub))
      (" Number of ponses" ,(ofnum nponses)))
    5)
   (oft ")")
   nil)))

(defun memoized-values (&optional (fn (memoized-functions)))

  "(MEMOIZED-VALUES fn) prints all the currently memoized values for
   FN."

  (cond ((listp fn) (mapc #'memoized-values fn))
        ((not (memoizedp-raw fn))
         (oft "~%; Memoized-values:  ~s is not memoized." fn))
        (t (let ((tb (symbol-value
                      (access memoize-info-ht-entry
                              (gethash fn *memoize-info-ht*)
                              :tablename))))
             (cond ((and tb (not (eql 0 (hash-table-count
                                         (the hash-table tb)))))
                    (oft "~%; Memoized values for ~s." fn)
                    (maphash (lambda (key v)
                               (format t "~%~s~%=>~%~s" key v))
                             (the hash-table tb)))))))
  nil)

(defvar *acl2--*)

(defn print-call-stack ()

  "(PRINT-CALL-STACK) prints the stack of memoized function calls
  currently running and the time they have been running."

  (let (l
        (time (internal-real-time))
        (*print-case* :downcase))
    (maphash (lambda (k v)
               (cond ((symbolp k)
                      (let ((x (symbol-value
                                (the symbol
                                  (access memoize-info-ht-entry
                                          v :start-time)))))
                        (declare (type mfixnum x))
                        (when (> x 0)
                          (push (cons k x) l))))))
             *memoize-info-ht*)
    (setq l (sort l #'< :key #'cdr))
    (setq l (loop for pair in l collect
                  (list (car pair)
                        (ofnum (/ (- time (cdr pair))
                                  *float-ticks/second*)))))
    (our-syntax-brief (when - (oft "~%? ~a" -)))
    (our-syntax-brief
     (when (boundp '*acl2--*) (oft "~%> ~a~%" *acl2--*)))
    (when l
      (terpri)
      (print-alist
       (cons '("Stack of monitored function calls."
               "Time since outermost call.")
             l)
       5))))

(defn1 hons-calls (x)

  "For a memoized function fn, (HONS-CALLS fn) is the number of times
  fn has called hons."

  (setq x (coerce-index x))
  (aref *memoize-call-array*
        (the mfixnum
          (+ *ma-hons-index*
                       (the mfixnum
                         (* *2max-memoize-fns*
                            (the mfixnum x)))))))

(defn1 pons-calls (x)

  "For a memoized function X, (PONS-CALLS x) is the number of times
   X has called pons."

  (setq x (coerce-index x))
  (aref *memoize-call-array*
        (the mfixnum (+ *ma-pons-index*
                       (the mfixnum
                         (* *2max-memoize-fns*
                            (the mfixnum x)))))))

#+Clozure
(defn1 bytes-allocated (x)

  "For a memoized function X, (BYTES-ALLOCATED x) is the number of
  heap bytes X has caused to be allocated on the heap."

  (setq x (coerce-index x))
  (aref *memoize-call-array*
        (the mfixnum (+ *ma-bytes-index*
                       (the mfixnum
                         (* *2max-memoize-fns*
                            (the mfixnum x)))))))

(defn1 number-of-hits (x)

  "For a memoized function X, (NUMBER-OF-HITS x) is the number of
  times that a call of X returned a remembered answer."

  (setq x (coerce-index x))
  (aref *memoize-call-array*
        (the mfixnum (+ *ma-hits-index*
                       (the mfixnum
                         (* *2max-memoize-fns*
                            (the mfixnum x)))))))

(defn1 number-of-memoized-entries (x)

  "For a memoized function X, (NUMBER-OF-MEMOIZED-ENTRIES x) is the
  number of entries currently stored for X."
  
  (let ((h (gethash x *memoize-info-ht*)))
    (unless h (ofe "~a is not memoized." x))
    (let* ((sym (access memoize-info-ht-entry
                        h
                        :tablename))
           (val (symbol-value sym)))
      (if (hash-table-p val)
          (hash-table-count (the hash-table val))
        0))))

(defn1 number-of-mht-calls (x)

  "For a memoized function X, (NUMBER-OF-MHT-CALLS x) is the number
  of times that the memoize hash-table for X was created."

  (setq x (coerce-index x))
  (aref *memoize-call-array*
        (the mfixnum (+ *ma-mht-index*
                       (the mfixnum
                         (* *2max-memoize-fns*
                            (the mfixnum x)))))))

(defn1 time-for-non-hits/call (x)
  (setq x (coerce-index x))
  (let ((n (- (number-of-calls x) (number-of-hits x))))
    (if (zerop n) 0 (/ (total-time x) n))))

(defn1 time/call (x)
  (setq x (coerce-index x))
  (let ((n (number-of-calls x)))
    (if (zerop n) 0 (/ (total-time x) n))))

(defn1 hits/calls (x)
  (setq x (coerce-index x))
  (let ((n (number-of-calls x)))
    (if (zerop n) 0 (/ (number-of-hits x) (float n)))))

#+Clozure
(defn1 bytes-allocated/call (x)
  (setq x (coerce-index x))
  (let ((n (number-of-calls x)))
    (if (eql n 0)
        0
      (/ (bytes-allocated x) n))))

(defn char-list-fraction (l)
  (if (atom l) 0
    (+ (char-code (car l))
       (/ (char-list-fraction (cdr l))
          256))))

(defn symbol-name-order (s)

  "SYMBOL-NAME-ORDER maps symbols to rationals preserving
  lexicographic order."

  (unless (symbolp s) (setq s (fixnum-to-symbol s)))
  (- (char-list-fraction (coerce (symbol-name s) 'list))))

(defn1 execution-order (s)
  (unless (symbolp s) (setq s (fixnum-to-symbol s)))
  (the mfixnum (symbol-value
               (the symbol
                 (access memoize-info-ht-entry
                         (gethash s *memoize-info-ht*)
                         :start-time)))))

#+Clozure
(defg *current-compiler-function* 'unknown)

#+Clozure
(defg *trace-if-compiler-macro* nil)

#+Clozure
(defg *watch-if-branches-ht* (make-hash-table :test 'eq))

#+Clozure
(defg *watch-if-branches-taken-ht* (make-hash-table :test 'eq))

(declaim (hash-table *watch-if-branches-ht*
                     *watch-if-branches-taken-ht*))

(defn compute-calls-and-times ()
  (let ((ma *memoize-call-array*)
        (2m *2max-memoize-fns*)
        (ca *compute-array*)
        (n (the fixnum (1+ *max-symbol-to-fixnum*))))
    (declare (type (simple-array mfixnum (*)) ma)
             (type (simple-array t (*)) ca)
             (type fixnum 2m n))
    (cond ((eql (length ca) n)
           (loop for i fixnum below n
                 do (setf (aref ca i) nil)))
          (t (setq *compute-array*
                   (make-array n :initial-element nil))
             (setq ca *compute-array*)))
    (loop for i fixnum below (the fixnum (* 2 n))
          do (setf (aref ma i) 0))
    (loop for i fixnum
          from *ma-initial-max-symbol-to-fixnum*
          to *max-symbol-to-fixnum* do
          (let ((2im (the fixnum (* i 2m))))
            (declare (type fixnum 2im))
            (loop for j fixnum
                  from *ma-initial-max-symbol-to-fixnum*
                  to *max-symbol-to-fixnum* do
                  (let* ((2j (the fixnum (* 2 j)))
                         (index (the fixnum (+ 2j 2im))))
                    (declare (type fixnum 2j index))
                    (let ((calls (the mfixnum (aref ma index))))
                      (declare (type mfixnum calls))
                      (when (> calls 0)
                        (let ((time (aref ma (the mfixnum
                                               (1+ index)))))
                          (declare (type mfixnum time))
                          (setf (aref ma 2j)
                                (the mfixnum (+ (aref ma 2j) calls)))
                          (setf (aref ma (the mfixnum (1+ 2j)))
                                (the mfixnum (+ (aref
                                                ma
                                                (the mfixnum (1+ 2j)))
                                               time)))
                          (push i (aref ca j))))))))))
  #+Clozure
  (clrhash *watch-if-branches-ht*)
  #+Clozure
  (clrhash *watch-if-branches-taken-ht*)
  #+Clozure
  (maphash
   (lambda (k v) (declare (ignore k))
     (setf (gethash (cadr v) *watch-if-branches-ht*)
           (+ 2 (or (gethash (cadr v)
                             *watch-if-branches-ht*)
                    0)))
     (setf (gethash (cadr v) *watch-if-branches-taken-ht*)
           (+ (signum (aref *if-true-array* (the fixnum (car v))))
              (signum (aref *if-false-array* (the fixnum (car v))))
              (or (gethash (cadr v)
                           *watch-if-branches-taken-ht*)
                  0))))
   *form-ht*))

(defn1 number-of-calls (x)
  (setq x (coerce-index x))

; One must call COMPUTE-CALLS-AND-TIMES before invoking
; NUMBER-OF-CALLS to get sensible results.

  (aref *memoize-call-array*
        (the mfixnum (* 2 (the mfixnum x)))))

(defn1 print-not-called ()

  "(PRINT-NOT-CALLED) prints, one to a line, in alphabetic order, the
  currently memoized functions that have never been called.  Possibly
  useful when looking for test coverage."

  (our-lock-unlock-memoize1
   (progn
     (compute-calls-and-times)
     (let ((ans nil))
       (maphash (lambda (k v)
                  (declare (ignore v))
                  (when (and (symbolp k)
                             (eql 0 (number-of-calls k)))
                    (push k ans)))
                *memoize-info-ht*)
       (loop for x in (sort ans 'alphorder)
             do (print x))))))

(defn1 total-time (x)

  (setq x (coerce-index x))

; One must call COMPUTE-CALLS-AND-TIMES before invoking
; TOTAL-TIME to get sensible results.

  (/ (aref *memoize-call-array*
           (the fixnum (1+ (the fixnum (* 2 x)))))
     *float-ticks/second*))

(defn lex-> (l1 l2)
  (cond ((or (atom l1)
             (atom l2))
         nil)
        ((> (car l1) (car l2)) t)
        ((< (car l1) (car l2)) nil)
        (t (lex-> (cdr l1) (cdr l2)))))

(defn1 memoize-summary-sort ()
  (let (pairs)
    (maphash
     (lambda (fn v)
       (when (symbolp fn)
       (let ((num (access memoize-info-ht-entry v :num)))
         (declare (type fixnum num))
         (when (< 0 (number-of-calls num))
           (push (cons fn (loop for order
                                in *memoize-summary-order-list*
                                collect (funcall order fn)))
                 pairs)))))
     *memoize-info-ht*)
    (sort pairs
          (if *memoize-summary-order-reversed*
              (lambda (x y) (lex-> y x))
            #'lex->)
          :key #'cdr)))

(defn1 memoize-summary ()

  "(MEMOIZE-SUMMARY) reports data stored during the execution of the
  functions in (MEMOIZED-FUNCTIONS).

  Typically each call of a memoized function, fn, is counted.
  The elapsed time until an outermost function call of fn ends, the
  number of heap bytes allocated in that period (CCL only), and other
  'charges' are 'billed' to fn.  That is, quantities such as elapsed
  time and heap bytes allocated are not charged to subsidiary
  recursive calls of fn while an outermost call of fn is running.
  Recursive calls of fn, and memoized 'hits', are counted, unless fn
  was memoized with NIL as the value of the :INLINE parameter of
  MEMOIZE.

  The settings of the following determine, at the time a function is
  given to MEMOIZE, the information that is collected for calls of
  the function:

         Variable              type

         *RECORD-BYTES*       boolean    (available in CCL only)
         *RECORD-CALLS*       boolean 
         *RECORD-HITS*        boolean 
         *RECORD-HONS-CALLS*  boolean 
         *RECORD-MHT-CALLS*   boolean 
         *RECORD-PONS-CALLS*  boolean 
         *RECORD-TIME*        boolean 

  In Clozure Common Lisp, the :WATCH-IFS keyword parameter of
  MEMOIZE-FN determines whether IFs in the body of the function being
  memoized are monitored.

  The settings of the following determine, at the time that
  MEMOIZE-SUMMARY is called, what information is printed:

         *REPORT-BYTES*       boolean   (available in CCL only)
         *REPORT-CALLS*       boolean 
         *REPORT-CALLS-FROM*  boolean 
         *REPORT-CALLS-TO*    boolean 
         *REPORT-HITS*        boolean 
         *REPORT-HONS-CALLS*  boolean 
         *REPORT-MHT-CALLS*   boolean 
         *REPORT-PONS-CALLS*  boolean 
         *REPORT-TIME*        boolean 
         *REPORT-IFS*         boolean

         *REPORT-ON-MEMO-TABLES*   boolean 
         *REPORT-ON-PONS-TABLES*   boolean 
         *MEMOIZE-SUMMARY-LIMIT*            (or integerp null)
         *MEMOIZE-SUMMARY-ORDER-LIST*       (symbol symbol ... symbol)
         *MEMOIZE-SUMMARY-ORDER-REVERSED*   boolean

  Functions are sorted lexicographically according to the ordering
  induced by the function names in *MEMOIZE-SUMMARY-ORDER-LIST*, each
  member of which must be a unary function that returns a rational.

  The times reported by MEMOIZE-SUMMARY are always elapsed times, that
  is, wall-clock times in seconds, unless 'run-time' is explicitly
  mentioned in the output that WATCH prints.

  (CLEAR-MEMOIZE-TABLES) forgets the remembered values of all memoized
  function calls.  It does not alter a function's status as being a
  memoized function, nor does not it the monitoring data accumulated.

  (UNMEMOIZE-ALL) undoes the memoization status of all memoized
  functions.

  (CLEAR-MEMOIZE-CALL-ARRAY) zeroes out the monitoring information for
  all functions.  It does not alter any function's status as a
  memoized function nor does it change the values remembered for any
  memoized function.

  Here is an example of hacking with *MEMOIZE-SUMMARY-ORDER-LIST* that
  instructs MEMOIZE-SUMMARY to print information about, say,
  1ST-MOD-ERR first:

    (PUSH (LAMBDA (FN)
            (IF (EQ FN '1ST-MOD-ERR) 1 0))
          *MEMOIZE-SUMMARY-ORDER-LIST*)."

  (compute-calls-and-times)
  (memoize-summary-after-compute-calls-and-times)
  nil)

(defg *short-symbol-name-width* 30)

(defn short-symbol-name (sym)
  (let ((str (symbol-name sym)))
    (cond ((> (length str) *short-symbol-name-width*)
           (intern (ofn "~a..."
                        (subseq str 0
                                *short-symbol-name-width*))
                   (symbol-package sym)))
          (t sym))))

(defn1 outside-p (x)
  (or (<= x *ma-initial-max-symbol-to-fixnum*)
      (null (gethash x *memoize-info-ht*))))

(defn1 memoize-summary-after-compute-calls-and-times ()
  
;  If COMPUTE-CALLS-AND-TIMES is not called shortly before this
;  function, MEMOIZE-SUMMARY-AFTER-COMPUTE-CALLS-AND-TIMES, is called,
;  the information reported may be quite untimely.

 (let* ((fn-pairs (memoize-summary-sort))
        (ma *memoize-call-array*)
        (len-orig-fn-pairs (len fn-pairs))
        (len-fn-pairs 0)
        (global-total-time 0)
        (global-bytes-allocated 0)
        (global-hons-calls 0)
        (global-pons-calls 0))
   (declare (type (simple-array mfixnum (*)) ma)
            (type fixnum len-orig-fn-pairs len-fn-pairs))
   (when (and *memoize-summary-limit*
              (> len-orig-fn-pairs *memoize-summary-limit*))
     (setq fn-pairs
           (loop for i fixnum from 1 to *memoize-summary-limit* as
                 x in fn-pairs collect x)))
   (setq len-fn-pairs (len fn-pairs))
   (when (> len-fn-pairs 0)
     (oft "~%Sorted by *memoize-summary-order-list* = ~a."
          *memoize-summary-order-list*)
     (when (< len-fn-pairs len-orig-fn-pairs)
       (oft "~%Reporting on ~:d of ~:d functions because ~
             *memoize-summary-limit* = ~a."
            len-fn-pairs
            len-orig-fn-pairs
            *memoize-summary-limit*)))
   (setq global-total-time
     (loop for pair in fn-pairs sum (total-time (car pair))))
   (setq global-bytes-allocated
     (+ 1 (loop for pair in fn-pairs sum
                (bytes-allocated (car pair)))))
   (setq global-hons-calls
     (+ 1 (loop for pair in fn-pairs sum (hons-calls (car pair)))))
   (setq global-pons-calls
     (+ 1 (loop for pair in fn-pairs sum (pons-calls (car pair)))))
   (when (null fn-pairs)
     (oft "~%(memoize-summary) has nothing to report.~%"))
   (loop for pair in fn-pairs do
    (let* ((fn (car pair))
           (l (gethash fn *memoize-info-ht*))
           (tablename
            (symbol-value
             (access memoize-info-ht-entry l :tablename)))
           (ponstablename
            (symbol-value
             (access memoize-info-ht-entry l :ponstablename)))
           (start-time
            (the mfixnum
              (symbol-value
               (the symbol
                 (access memoize-info-ht-entry l :start-time)))))
           (num (the fixnum (access memoize-info-ht-entry l :num)))
           (nhits (the mfixnum (number-of-hits num)))
           (nmht (the mfixnum (number-of-mht-calls num)))
           (ncalls
            (the mfixnum (max 1 (the mfixnum (number-of-calls num)))))
           (hons-calls (the mfixnum (hons-calls num)))
           (pons-calls (the mfixnum (pons-calls num)))
           (no-hits (or (not *report-hits*)
                        (null (memoize-condition fn))))
           #+Clozure
           (bytes-allocated (bytes-allocated num))
           (tt (total-time num))
           (t/c (time/call num))
           (tnh (time-for-non-hits/call num))
           (in-progress-str
            (if (eql start-time -1) " " ", running, ")))
      (declare (type integer start-time)
               (type fixnum num)
               (type mfixnum nhits nmht ncalls
                     hons-calls pons-calls
                     #+Clozure bytes-allocated))
      (print-alist
       `((,(ofn "(defun ~s~a~a"
                (short-symbol-name fn)
                (if no-hits
                    (ofn " call~a" (if (eql nhits 1) "" "s"))
                  " hits/calls")
                in-progress-str)
          ,(if (or *report-calls* *report-hits*)
               (if no-hits
                   (ofn "~a" (ofnum ncalls))
                 (ofn "~8,2e/~8,2e = ~4,1f%"
                      nhits
                      ncalls
                      (* 100 (/ nhits (float ncalls)))))
          ""))
         ,@(if (and *report-mht-calls* (>= nmht 2))
               `((" Number of calls to mht" ,(ofnum nmht))))
         ,@(if *report-time*
               `((" Time of all outermost calls"
                  ,(ofn "~a; ~4,1f%"
                        (ofnum tt)
                        (* 100 (/ tt global-total-time))))
                 (" Time per call" ,(ofnum t/c))))

         ,@(if (let ((v (gethash fn *memoize-info-ht*)))
                 (and (null (access memoize-info-ht-entry v
                                    :condition))
                      (null (access memoize-info-ht-entry v
                                    :inline))
                      (< t/c 1e-6)))
               `((,(ofn " Doubtful timing info for ~a." fn)
                  "Heisenberg effect.")))
         #+Clozure
         ,@(if (and (> bytes-allocated 0) *report-bytes*)
               `((" Heap bytes allocated"
                  ,(ofn "~a; ~4,1f%"
                        (ofnum bytes-allocated)
                        (* 100 (/ bytes-allocated
                                  global-bytes-allocated))))
                 (" Heap bytes allocated per call"
                  ,(ofnum (/ bytes-allocated ncalls)))))
         ,@(if (and (> hons-calls 0) (> global-hons-calls 0)
                    *report-hons-calls*)
               `((" Hons calls"
                  ,(ofn "~a; ~4,1f%"
                        (ofnum hons-calls)
                        (* 100 (/ hons-calls global-hons-calls))))))
         #+Clozure
         ,@(if (and *report-ifs* (gethash fn *watch-if-branches-ht*))
               `((" IF branch coverage"
                  ,(ofn "~a taken out of ~a"
                        (ofnum (gethash
                                fn *watch-if-branches-taken-ht*))
                        (ofnum (gethash
                                fn *watch-if-branches-ht*))))))
         ,@(if (and (> pons-calls 0)
                    (> global-pons-calls 0)
                    *report-pons-calls*)
               `((" Pons calls"
                  ,(ofn "~a; ~4,1f%"
                        (ofnum pons-calls)
                        (* 100 (/ pons-calls global-pons-calls))))))
         ,@(if (and *report-hits* *report-time* (not (eql 0 nhits)))
               `((" Time per missed call" ,(ofnum tnh))))
         ,@(if *report-calls-to*
               (let ((l nil)
                     (outside-fn-time 0)
                     (outside-fn-count 0))
                 (declare (type mfixnum outside-fn-count))
                 (loop for callern in
                  (loop for i below (length *compute-array*)
                        when (member num (aref *compute-array* i))
                        collect i) do
                  (let* ((call-loc
                          (the fixnum
                            (+ (* 2 callern)
                               (the fixnum
                                 (* num *2max-memoize-fns*)))))
                         (calls (aref ma call-loc)))
                    (declare (fixnum call-loc)
                             (type mfixnum calls))
                    (let* ((time-loc (the fixnum (1+ call-loc)))
                           (time (aref ma time-loc))
                           (ltt (/ time *float-ticks/second*)))
                      (cond ((or (outside-p callern)
                                 (< (* 100 ltt) tt))
                             (incf outside-fn-time ltt)
                             (incf outside-fn-count calls))
                            (t (push
                                `((,(ofn " To ~a"
                                         (fixnum-to-symbol callern))
                                   ,(ofn
                                     "~8,2e calls took~8,2e;~5,1f%"
                                     calls ltt
                                     (if (< .001 ltt tt)
                                         (* 100 (/ ltt tt))
                                       '?)))
                                  . ,(if *sort-to-from-by-calls*
                                         calls
                                       time))
                                l))))))
                 (when (> outside-fn-time 0)
                   (push
                    `((,(ofn " To other functions")
                       ,(ofn "~8,2e calls took~8,2e;~5,1f%"
                             outside-fn-count
                             outside-fn-time
                             (if (< .001 outside-fn-time tt)
                                 (* 100 (/ outside-fn-time tt))
                               '?)))
                      . ,(if *sort-to-from-by-calls*
                             outside-fn-count
                           outside-fn-time))
                    l))
                 (setq l (sort l #'> :key #'cdr))
                 (strip-cars l)))
         ,@(if *report-calls-from*
               (let ((l nil)
                     (2num (the fixnum (* 2 num)))
                     (outside-caller-time 0)
                     (outside-caller-count 0))
                 (declare (fixnum 2num))
                 (loop
                  for callern in (aref *compute-array* num) do
                  (let* ((call-loc
                          (the fixnum
                            (+ 2num
                               (the fixnum
                                 (* callern *2max-memoize-fns*)))))
                         (calls (aref ma call-loc)))
                    (declare (fixnum call-loc)
                             (type mfixnum calls))
                    (let* ((time-loc (the fixnum (1+ call-loc)))
                           (time (aref ma time-loc))
                           (ltt (/ time *float-ticks/second*)))
                      (cond
                       ((or (outside-p callern) (< (* 100 ltt) tt))
                        (incf outside-caller-time ltt)
                        (incf outside-caller-count calls))
                       (t (push
                           `((,(ofn " From ~a"
                                    (fixnum-to-symbol callern))
                              ,(ofn "~8,2e calls took~8,2e;~5,1f%"
                                    calls
                                    ltt
                                    (if (< .001 ltt tt)
                                        (* 100 (/ ltt tt))
                                      '?)))
                             . ,(if *sort-to-from-by-calls*
                                    calls
                                  time))
                           l))))))
                 (when (> outside-caller-time 0)
                   (push
                    `((,(ofn " From other functions")
                       ,(ofn "~8,2e calls took~8,2e;~5,1f%"
                             outside-caller-count
                             outside-caller-time
                             (if (< .001 outside-caller-time tt)
                                 (* 100 (/ outside-caller-time tt))
                               '?)))
                      . ,(if *sort-to-from-by-calls*
                             outside-caller-count
                           outside-caller-time))
                    l))
                 (setq l (sort l #'> :key #'cdr))
                 (strip-cars l)))
             .
         ,(if (and (not *report-on-memo-tables*)
                   (not *report-on-pons-tables*))
              nil
            (let ((spsub 0) (nponses 0) (npsubs 0))
              (declare (type mfixnum spsub nponses npsubs))
              (and
               (and ponstablename *report-on-pons-tables*)
               (maphash
                (lambda (key value)
                  (declare (ignore key))
                  (cond
                   ((not (listp value))
                    (very-unsafe-incf spsub (hash-table-size
                                             (the hash-table value))
                                      memoize-summary)
                    (very-unsafe-incf nponses
                                      (hash-table-count
                                       (the hash-table value))
                                      memoize-summary)
                    (very-unsafe-incf npsubs 1 memoize-summary))
                   (t (very-unsafe-incf nponses
                                        (length value)
                                        memoize-summary))))
                ponstablename))
              `(,@(and
                   (and tablename *report-on-memo-tables*)
                   `((,(ofn " Memoize table count/size")
                      ,(ofn "~8,2e/~8,2e = ~4,1f%"
                            (hash-table-count
                             (the hash-table tablename))
                            (hash-table-size
                             (the hash-table tablename))
                            (* 100
                               (/ (hash-table-count
                                   (the hash-table tablename))
                                  (hash-table-size
                                   (the hash-table tablename))))))))
                  ,@(and
                     (and ponstablename *report-on-pons-tables*)
                     `((" (Pons table count/size"
                        ,(ofn "~:d/~:d = ~4,1f%)"
                              (hash-table-count
                               (the hash-table ponstablename))
                              (hash-table-size
                               (the hash-table ponstablename))
                              (* 100
                                 (/ (hash-table-count
                                     (the hash-table ponstablename))
                                    (hash-table-size
                                     (the hash-table
                                       ponstablename))))))
                       (" (Number of pons sub tables"
                        ,(ofn "~a)" (ofnum npsubs)))
                       (" (Sum of pons sub table sizes"
                        ,(ofn "~a)" (ofnum spsub)))
                       (" (Number of ponses"
                        ,(ofn "~a)" (ofnum nponses)))))))))
       5))
         (oft ")"))))


(defn1 empty-ht-p (x)
  (and (hash-table-p x)
       (eql 0 (hash-table-count (the hash-table x)))))

(defn clear-one-memo-and-pons-hash (l)

;  It is debatable whether one should use the CLRHASH approach or
;  the set-to-NIL approach in CLEAR-ONE-MEMO-AND-PONS-HASH.  The
;  CLRHASH approach, in addition to reducing the number of
;  MAKE-HASH-TABLE calls necessary, has the effect of immediately
;  clearing a hash-table even if some other function is holding on
;  to it, so more garbage may get garbage collected sooner than
;  otherwise.  The set-to-NIL approach has the advantage of costing
;  very few instructions and very little paging.

  (let* ((fn (access memoize-info-ht-entry l :fn))
         (mt (symbol-value (access memoize-info-ht-entry l :tablename)))
         (pt (symbol-value (access memoize-info-ht-entry l :ponstablename)))
         (mt-count (and mt (hash-table-count mt)))
         (pt-count (and pt (hash-table-count pt))))
    (when mt
      (setf (symbol-value (access memoize-info-ht-entry l :tablename)) nil))
    (when pt
      (setf (symbol-value (access memoize-info-ht-entry l :ponstablename)) nil))
    (when (or mt-count pt-count)
      (update-memo-max-sizes fn (or pt-count 1) (or mt-count 1)))
    nil))

(defn1 clear-memoize-table (k)

; See also hons.lisp.

  (when (symbolp k)
    (let ((l (gethash k *memoize-info-ht*)))
      (when l (clear-one-memo-and-pons-hash l)))))

(defn1 clear-memoize-tables ()

; See hons.lisp.

  (ofvv "Running (clear-memoize-tables).")
  (let (success)
    (unwind-protect
        (progn
          (maphash (lambda (k l)
                     (when (symbolp k)
                       (clear-one-memo-and-pons-hash l)))
                   *memoize-info-ht*)
          (setq success t))
      (or success (ofe "clear-memoize-tables failed.")))))

(defn clear-memoize-call-array ()

  "(CLEAR-MEMOIZE-CALL-ARRAY) zeros out all records of function calls
  as far as reporting by MEMOIZE-SUMMARY, etc. is concerned."

  (ofvv "Running (clear-memoize-call-array).")
  (let ((m *memoize-call-array*))
    (declare (type (simple-array mfixnum (*)) m))
    (loop for i fixnum below (length m)
          do (setf (aref m i) 0))))

(defn clear-memoize-statistics ()
  (clear-memoize-call-array)
  nil)
  
; HONS READ

; Hash consing when reading is implemented via a change to the
; readtable for the characters open parenthesis, close parenthesis,
; and period, the consing dot.

; *** NOTE:  The following collection of functions is just that: a
;            collection.  Unless you understand everything about the
;            various read table macros, then don't touch this code!

; See matching comment below.

; Note: our implementation of the #=/## reader, which we built because
; some Lisps would not let us get past #500 or so, does not comply
; with ANSI at least in this regard: it does not allow the entry of
; looping structures as in '(#0= (3 #0#)), which is no problem for
; ACL2 users.

; WARNING: Any call of READ using *hons-readtable* as *readtable*
; needs to worry about the possible top-level return of
; *CLOSE-PAREN-OBJ* and *DOT-OBJ*, which are simply part of the
; fiction whereby we read while honsing.  Those two objects should
; absolutely not be returned as the value of an ACL2 function.  See,
; for example, the definition of HONS-READ.

(defg *close-paren-obj* '(#\)))

(defg *dot-obj*         '(#\.))

(defg *hons-readtable* (copy-readtable *acl2-readtable*))

(defg *hacked-acl2-readtable* (copy-readtable *acl2-readtable*))

(defparameter *compact-print-file-ht* nil)

(defparameter *hons-read-ht* nil) ; bound sometimes

(defmacro hons-read-ar-len () (expt 2 21))

(defparameter *hons-read-ar*
  (make-array (hons-read-ar-len) :initial-element 0))

(defparameter *hons-read-ar-max* -1)

(defparameter *compact-print-file-n* 0)

(declaim (type fixnum *compact-print-file-n*))

(defg *space-owed* nil)

(defg *hons-readtable-init-done* nil)

(defn1 hread-nonsense (x)
  (or (eq x *close-paren-obj*) (eq x *dot-obj*)))

(defn1 check-hread-nonsense (x stream)
  (cond ((hread-nonsense x)
         (hread-error "~&;  Illegal object: ~s." stream (car x)))))

(defun hread-error (string stream &rest r)
  (our-syntax-nice
   (let* ((*standard-input* *debug-io*))
     (apply #'format *error-output* string r)
     (cond ((and (streamp stream) (file-position stream))
            (format *error-output*
                    "~&; near file-position ~s in stream ~s."
                    (file-position stream) stream)))
     (ofe "hread."))))

(defn1 illegal-error1 (x stream)
  (hread-error "~&; ** Error:  Illegal:  ~s." stream x))

(defn1 illegal-error2 (stream char)
  (illegal-error1 char stream))

(defn1 close-paren-read-macro (stream char)
  (declare (ignore char))
  (if *read-suppress* (illegal-error1 #\\ stream))
  *close-paren-obj*)

(defn1 dot-read-macro (stream char)
  (declare (ignore char))
  (if *read-suppress* (illegal-error1 #\. stream))
  (let ((ch (peek-char nil stream t nil t)))
    (cond ((or (member ch '(#\( #\) #\' #\` #\, #\" #\;
                            #\Tab #\Space #\Newline))
               (eql 13 (char-code ch))
               (multiple-value-bind (fn nonterminating)
                   (get-macro-character ch)
                 (and fn (not nonterminating))))
           *dot-obj*)
          (t (let ((*readtable* *acl2-readtable*))
               (unread-char #\. stream)
               (hons-copy (read stream t nil t)))))))

(defn1 hons-read-list (stream)

  ; ***** hons

  ; HONS-READ-LIST must return a HONSP whenever it turns a CONSP, even
  ; when the object comes from some readmacro such as that for quote
  ; or backquote that might return a CONS.  Hence the calls to
  ; HONS-COPY.

  (let ((o (read stream t nil t)))
    (cond
     ((eq o *close-paren-obj*) nil)
     ((eq o *dot-obj*)
      (let ((lo (read stream t nil t))
            (lp (read stream t nil t)))
        (check-hread-nonsense lo stream)
        (cond
         ((eq lp *close-paren-obj*)
          (hons-copy lo))
         (t (illegal-error1 #\. stream)))))
     (t (hons o (hons-read-list stream))))))

(defn1 hons-read-list-top (stream)

  ; ***** hons

  (let ((o (read stream t nil t)))
    (cond
     ((eq o *close-paren-obj*) nil)
     (t (check-hread-nonsense o stream)
        (hons o (hons-read-list stream))))))

(defn1 hons-read-reader (stream char)

  ; ***** hons

  (declare (ignore char))
  (cond (*read-suppress*
         (unread-char #\( stream)
         (let ((*readtable* *acl2-readtable*))
           (read stream t nil t)
           nil))
        (t (hons-read-list-top stream))))

(defg *use-hons-in-read-object* t)

(defun clear-hons-read-ar (index)
  (loop for i from 0 to index do
        (setf (aref (the (simple-array t (*)) *hons-read-ar*)
                    (the fixnum i))
              0)))

(defvar *inside-hons-read*
; WARNING: Do not use defg, since this variable can be let-bound.
  nil)

(defun hons-read (&optional stream (eep t) eofv rp)

  "HONS-READ takes the same args as READ.  If
  *USE-HONS-IN-READ-OBJECT* is non-NIL, then HONS is used in the
  reading instead of CONS.

  We currently disallow any call of hons-read with rp=nil inside
  a call of hons-read."

  (when (and (not rp) *inside-hons-read*)
    (error "Recursive hons-read!"))
  (let ((*inside-hons-read* t)
        (our-eofv (cons nil nil)))
    (cond (*use-hons-in-read-object*
            (our-lock-unlock-hons1
             
; Although a readmacro such as quote or backquote might return a CONS
; that is not HONSP, HONS-READ-LIST will turn those into HONSES.

              (cond (rp      ; DO NOT BIND *HONS-READ-HT/AR-MAX*.
                     (let* ((*readtable* *hons-readtable*)
                            (x (read stream eep our-eofv rp)))
                       (cond ((and (null eep) (eq x our-eofv))
                              eofv)
                             (t (check-hread-nonsense x stream)
                                (hons-copy x)))))
                    (t       ; DO BIND *HONS-READ-HT/AR-MAX*,
                             ; OTHERWISE SAME.
                     (let* ((*hons-read-ht* nil)
                            (*hons-read-ar-max* -1)
                            (*readtable* *hons-readtable*)
                            (x (read stream eep our-eofv rp)))
                       (clear-hons-read-ar *hons-read-ar-max*)
                       (cond ((and (null eep) (eq x our-eofv))
                              eofv)
                             (t (check-hread-nonsense x stream)
                                (hons-copy x))))))))
          (t (cond (rp ; DO NOT BIND *HONS-READ-HT/AR-MAX*.
                    (let* ((*readtable* *hacked-acl2-readtable*)
                           (x (read stream eep our-eofv rp)))
                      (cond ((and (null eep) (eq x our-eofv))
                             eofv)
                            (t x))))
                   (t ; DO BIND *HONS-READ-HT/AR-MAX*, OTHERWISE SAME.
                    (let* ((*hons-read-ht* nil)
                           (*hons-read-ar-max* -1)
                           (*readtable* *hacked-acl2-readtable*)
                           (x (read stream eep our-eofv rp)))
                      (clear-hons-read-ar *hons-read-ar-max*)
                      (cond ((and (null eep) (eq x our-eofv))
                             eofv)
                            (t x)))))))))

(defn1 hons-read-file (file-name)
  (with-open-file (stream file-name)
    (let ((eof (cons nil nil)) temp ans)
      (loop (setq temp (hons-read stream nil eof nil))
            (cond ((eq eof temp)
                   (setq ans (nreverse ans))
                   (when *use-hons-in-read-object*
                     (setq ans (hons-copy ans)))
                   (return ans))
                  (t (push temp ans)))))))


;  COMPACT PRINT AND READ

(defmacro space-if-necessary (stream)

; do not call

  `(when *space-owed*
     (write-char #\Space ,stream)
     (setq *space-owed* nil)))

(defn1 compact-print-file-scan (x)

; do not call

  (unless (or (and (symbolp x)
                   (let ((p (symbol-package x)))
                     (or (eq p *main-lisp-package*)
                         (eq p *package*)))
                   (<= (length (symbol-name x)) 4))

              ; On the one hand, in ANSI Lisp, you can't READ the same
              ; string twice.  On the other hand, in HONSing, we
              ; cannonicalize strings.  Should we or shouldn't we
              ; identify common strings here?  Sometimes we do, and
              ; sometimes we don't.

              (and (stringp x) (<= (length x) 2))
              (and (integerp x) (< -100 x 1000))
              (characterp x))
    (let ((g (gethash x *compact-print-file-ht*)))
      (unless (or (atom x) g)
        (compact-print-file-scan (car x))
        (compact-print-file-scan (cdr x)))
      (unless (eq g 'give-it-a-name)
        (setf (gethash x *compact-print-file-ht*)
              (if g 'give-it-a-name 'found-at-least-once))))))

(defn1 compact-print-file-help (x hash stream)

; do not call directly.

  (cond ((typep hash 'fixnum)
         (space-if-necessary stream)
         (write-char #\# stream)
         (princ hash stream)
         (write-char #\# stream))
        (t (cond ((eq hash 'give-it-a-name)
                  (let ((n *compact-print-file-n*))
                    (declare (type fixnum n))
                    (when (eql n most-positive-fixnum)
                      (ofe "*compact-print-file-n* overflow."))
                    (setq n (the fixnum (+ 1 n)))
                    (setq *compact-print-file-n* n)
                    (setf (gethash x *compact-print-file-ht*) n)
                    (space-if-necessary stream)
                    (write-char #\# stream)
                    (princ n stream)
                    (write-char #\= stream))))
           (cond
            ((null x)
             (write-char #\( stream)
             (write-char #\) stream)
             (setq *space-owed* nil))
            ((atom x)
             (space-if-necessary stream)

             ; This PRIN1 could commence with a vertical bar that
             ; might be immediately preceded by a sharp sign, which
             ; could confuse comment reading.

             (prin1 x stream)
             (setq *space-owed* t))
            (t (write-char #\( stream)
               (setq *space-owed* nil)
               (loop (compact-print-file-help
                      (car x)
                      (gethash (car x) *compact-print-file-ht*)
                      stream)
                     (cond
                      ((null (cdr x))
                       (write-char #\) stream)
                       (setq *space-owed* nil)
                       (return))
                      ((or (progn
                             (setq hash
                                   (gethash (cdr x)
                                            *compact-print-file-ht*))
                             (or (eq hash 'give-it-a-name)
                                 (typep hash 'fixnum)))
                           (atom (cdr x)))
                       (space-if-necessary stream)
                       (write-char #\. stream)
                       (setq *space-owed* t)
                       (compact-print-file-help (cdr x) hash stream)
                       (write-char #\) stream)
                       (setq *space-owed* nil)
                       (return))
                      (t (pop x)))))))))

(defun compact-print-stream (data stream)
  (cond ((null *print-circle-stream*)
         (error "Attempt to call compact-print-stream without ~
                 initializing ~% *print-circle-stream*.  Consider ~
                 opening output ~% channel with macro ~
                 with-output-object-channel-sharing."))
        ((not (eq stream *print-circle-stream*))
         (error "Attempt to call compact-print-stream on other ~
                 than the current stream.")))
  (our-lock-unlock-hons1
   (let ((*compact-print-file-ht* (mht)))
     (setq *space-owed* nil)
     (let ((p *package*))
       (loop for two in

             ;; We'll cause an error if the settings of these are
             ;; different than they will be under OUR-SYNTAX.

             '((*print-array*                t)
               (*print-base*                 10)
               (*print-case*                 :upcase)
               (*print-circle*               t)
               (*print-escape*               t)
               (*print-pretty*               nil)
               (*print-radix*                nil)
               (*read-base*                  10)
               (*read-suppress*              nil)
               (*readtable*                  *acl2-readtable*))
             when (not (equal (symbol-value (car two))
                              (if (symbolp (cadr two))
                                  (symbol-value (cadr two))
                                (cadr two))))
             do
             (ofe "PRINT-COMPACT-STREAM: Problem with the setting ~
                   of ~a" two))

       ; Currently, there is no way from within ACL2 to alter
       ; READTABLE-CASE.  Thank goodness.  So the following error will
       ; never happen.  But if ACL2 were someday 'enhanced' to permit
       ; control over READTABLE-CASE, there just might be a problem
       ; about the setting of *PRINT-READABLY* to T by OUR-SYNTAX
       ; below if the current setting of *PRINT-READABLY* were NIL.

       ;; *PACKAGE* -- we let the user use any ACL2 package.

       (unless (eq (readtable-case *acl2-readtable*) :upcase)
         (ofe "PRINT-COMPACT-STREAM: Problem with the setting of ~
               (readtable-case *acl2-readtable*)."))
       
       ;; We do not cause an error if the following *PRINT-...*
       ;; variable settings are different from what OUR-SYNTAX will
       ;; effect, and for many good reasons, as follows.

       ;; *PRINT-READABLY* -- a very tedious explanation.  When
       ;; *PRINT-READABLY* is T, then some extra errors may be caught
       ;; when attempting to print unprintable objects, and there are
       ;; effects upon the printing of arrays.  OUR-SYNTAX binds
       ;; *PRINT-READABLY* to T, and that will be O.K. because (a) we
       ;; don't print packages or arrays in ACL2, (b) we want an error
       ;; signaled by PRINT-OBJECT$ whenever it might be appropriate,
       ;; and (c) as far as we can imagine, when printing any ordinary
       ;; ACL2 object no errors should arise, excepting of the
       ;; catastrophic sort, e.g., disk space exhaused, power outage,
       ;; stack overflow.  But errors may well happen in printing some
       ;; legitimate Lisp, as opposed to ACL2, objects, when printing
       ;; with *PRINT-READABLY* bound to T, e.g., some bizarre
       ;; 'floating point numbers' such as 'infinity', packages, and
       ;; readtables.  Cf. the ANSI function PRINT-UNREADABLE-OBJECT.

       ;; *PRINT-LENGTH*          -- only for pretty
       ;; *PRINT-LEVEL*           -- only for pretty
       ;; *PRINT-LINES*           -- only for pretty
       ;; *PRINT-PPRINT-DISPATCH* -- only for pretty
       ;; *PRINT-MISER-WIDTH*     -- only for pretty
       ;; *PRINT-RIGHT-MARGIN*    -- only for pretty

       ;; *READ-DEFAULT-FLOAT-FORMAT* -- no floats in ACL2

       ;; *PRINT-GENSYM* -- no gensyms in ACL2

       ;; *READ-EVAL* -- OUR-SYNTAX uses T for *READ-EVAL*.  But we
       ;; don't print #. in compact-printing unless the # is properly
       ;; quoted with vertical bars or back-slashes.
       
       ;; Though OUR-SYNTAX binds *PRINT-CIRCLE* to NIL,
       ;; COMPACT-PRINT-STREAM is designed to do the job that
       ;; *PRINT-CIRCLE* should do, except for circular objects, which
       ;; are not found in ACL2.

       (our-syntax
        (setq *package* p)  ; Bound by OUR-SYNTAX to *ACL2-READTABLE*.
        (compact-print-file-scan data)
        (compact-print-file-help
         data
         (gethash data *compact-print-file-ht*)
         stream)
        nil)))))

(defun compact-print-file
  (data file-name &key (if-exists :supersede))

; May be called directly.

  "(COMPACT-PRINT-FILE x str) PRIN1s x to a new file named str so that
   Common Lisp can READ the result and get back something EQUAL,
   assuming the package and readtable are the same on print and read.
   COMPACT-PRINT-FILE prints as though *PRINT-CIRCLE* were T to
   minimize printing by a kind of compression, using traditional Lisp
   #..# syntax.  However, circular object are not handled.  See the
   bindings of some *PRINT-...* variables via OUR-SYNTAX in
   COMPACT-PRINT-STREAM, which favor accuracy and not prettiness.  The
   ACL2 package, ACL2 readtable, and decimal *PRINT-BASE* are used."

  (setq *compact-print-file-n* 0)
  (with-open-file (stream file-name
                          :direction :output
                          :if-exists if-exists)
    (let ((*print-circle-stream* stream)

; These *print... and *read... settings are deliberately inflicted
; upon the user of COMPACT-PRINT-FILE.  The user is still free to
; choose *PACKAGE*.  Read the comment in compact-print-stream for
; information about our rather fascist approach to these settings.

          (*print-base* 10)
          (*print-case* :UPCASE)
          (*print-circle* t)
          (*print-escape* t)
          (*print-pretty* nil)
          (*read-base* 10)
          (*read-eval* t)  ; to support #.constant printing
          (*read-suppress* nil)
          (*readtable* *acl2-readtable*)
          
          ; Not relevant once one knows that *PRINT-PRETTY* is NIL:

          (*print-length* nil)
          (*print-level* nil)
          (*print-lines* nil)
          (*print-radix* nil)
          (*print-right-margin* nil)

          ; Not relevant when printing only ACL2 objects:

          (*print-readably* t)
          (*read-default-float-format*  'single-float)
          (*print-gensym* t)
          (*print-array* t)

          ; This one is crucial to know about since strings are ACL2
          ; objects:

          #+CCL
          (ccl::*print-string-length* nil)

          #+CCL
          (ccl::*print-abbreviate-quote* nil)

          ; These are irrelevant as long as we are printing
          ; an ACL2 object.

          #+CCL
          (ccl::*print-structure* t)
          #+CCL
          (ccl::*print-simple-vector* nil)
          #+CCL
          (ccl::*print-simple-bit-vector* nil)

          ; Do many other Lisps have their own private set of secret
          ; print control variables?

          )
      (compact-print-stream data stream))
    (namestring (our-truename stream))))
  
(defun ns-=-reader (stream subchar arg)
  
; We don't use DEFN1 because this function might return 0 values.

; Do not call ns-=-reader directly.

; NS-=-READER intentionally does not read circular Lisp objects
; correctly, such as those normally created by reading #2=(1 #2#).
; Such a circular object could not be an ACL2 object anyway.  An
; attempt to read such an object will result in a clean error, e.g., a
; report that the expression #2# makes no sense because a #2= ?
; expression has not been fully read.

; *HONS-READ-HT* must always have a value, either NIL or a hash table;
; cf. READ-OBJECT and COMPACT-READ-FILE.

; *HONS-READ-AR* must always have a value, either NIL or a simple
; vector.  cf. READ-OBJECT and COMPACT-READ-FILE.

  (declare (ignore subchar))
  (cond ((null arg)
         (hread-error "~&; ns-=-reader: ** Error: #= is illegal."
                      stream arg))
        (*read-suppress* (values))
        ((< arg (hons-read-ar-len))
         (let ((x (read stream t nil t)))
           (cond ((eql x 0) ; 0 might be confused for the default
                  (unless *hons-read-ht*
                    (setq *hons-read-ht* (make-hash-table)))
                  (multiple-value-bind (val present-p)
                      (gethash arg *hons-read-ht*)
                    (when present-p
                      (hread-error
                       "~&; ns-=-reader: ** Error: #~s= is already ~
                        defined to be ~s."
                       stream arg val))
                    (setf (gethash arg *hons-read-ht*) 0)))
                 (t (setf *hons-read-ar-max*
                          (max (the fixnum *hons-read-ar-max*)
                               (the fixnum arg)))
                    (setf (aref (the (simple-array t (*))
                                  *hons-read-ar*)
                                (the fixnum arg))
                          x)))))
        (*hons-read-ht*
         (multiple-value-bind (val present-p)
             (gethash arg *hons-read-ht*)
           (when present-p
             (hread-error
              "~&; ns-=-reader: ** Error: #~s= is already ~
               defined to be ~s."
              stream arg val))
           (setf (gethash arg *hons-read-ht*)
                 (read stream t nil t))))
        (t (setq *hons-read-ht* (make-hash-table))
           (setf (gethash arg *hons-read-ht*)
                 (read stream t nil t)))))

(defn1 ns-ns-reader (stream subchar arg)

; Do not call NS-NS-READER directly.

; *HONS-READ-HT* must always have as its value NIL or a hash table.
; *HONS-READ-AR* must always have as its value NIL or a simple,
; one-dimensional array.  cf. READ-OBJECT and COMPACT-READ-FILE.

  (declare (ignore subchar))
  (cond (*read-suppress* nil)  ; ?
        ((null arg)
         (hread-error
          "~&; ns-ns-reader: ** Error: meaningless ##."
          stream arg))
        ((and *hons-read-ar* (< arg (hons-read-ar-len)))
         (let ((ans (aref (the (simple-array t (*)) *hons-read-ar*)
                          (the fixnum arg))))
           (cond ((eql ans 0) ; could be the default
                  (unless *hons-read-ht*
                    (setq *hons-read-ht* (make-hash-table)))
                  (multiple-value-bind (val present-p)
                      (gethash arg *hons-read-ht*)
                    (cond (present-p val)
                          (t (hread-error
                              "~&; ns-ns-reader: ** Error: ~
                               meaningless #~s#."
                              stream arg)))))
                 (t ans))))
        (*hons-read-ht*
         (multiple-value-bind (val present-p)
             (gethash arg *hons-read-ht*)
           (cond (present-p val)
                 (t (hread-error
                     "~&; ns-ns-reader: ** Error: meaningless ~
                      #~s#."
                     stream arg)))))
        (t (hread-error
            "~&; ns-ns-reader:  ** Error:  meaningless #~s#."
            stream arg))))

(defn1 compact-read-file (fn)

; May be called directly.

   "(COMPACT-READ-FILE fn) READs the first Lisp/ACL2 form of the file
   named FN.  The file should have exactly one Lisp object in it.

   HONS is used instead of CONS while reading when
   *USE-HONS-IN-READ-OBJECT* is not NIL.

   The *ACL2-READTABLE* is used during reading.  The reading respects
   Common Lisp's #2= and #2# readmacro support, however not for
   circular cons structures."

   (with-open-file (stream fn)
     (let* ((eof (cons nil nil))
            (p (hons-read stream nil eof nil)))
          (when (eq p eof)
            (ofe "compact-read-file: ~s appears empty." fn))
          (unless (eq (read stream nil eof) eof)
            (ofe "compact-read-file: ~s has too many ~
                 forms." fn))
          p)))


;  HONS READTABLE INIT

(defn1 hons-readtable-init ()

  (when *hons-readtable-init-done*
    (ofe "hons-readtable-init: already done."))

  (setq *hons-readtable* (copy-readtable *acl2-readtable*))
  (set-macro-character
   #\( #'hons-read-reader       nil *hons-readtable*)
  (set-macro-character
   #\) #'close-paren-read-macro nil *hons-readtable*)
  (set-macro-character
   #\. #'dot-read-macro         t   *hons-readtable*)
  (set-dispatch-macro-character
   #\# #\# #'ns-ns-reader           *hons-readtable*)
  (set-dispatch-macro-character
   #\# #\= #'ns-=-reader            *hons-readtable*)

  (setq *hacked-acl2-readtable* (copy-readtable *acl2-readtable*))
  (set-dispatch-macro-character
   #\# #\# #'ns-ns-reader           *hacked-acl2-readtable*)
  (set-dispatch-macro-character
   #\# #\= #'ns-=-reader            *hacked-acl2-readtable*)

  (setq *hons-readtable-init-done* t))


; MEMOIZE INIT

(defn1 memoize-init ()

; May not be repeated.

  (when *memoize-init-done* (ofe "memoize-init:  already done."))

  (unwind-mch-lock
   (unless (eql *caller* (the fixnum
                          (* *ma-initial-max-symbol-to-fixnum*
                             *2max-memoize-fns*)))
     (ofe "memoize-init:  A memoized function is running."))
   (let (success)
     (unwind-protect
       (progn
         #+Clozure (setup-smashed-if)
         (setq *pons-call-counter* 0)
         (setq *pons-misses-counter* 0)
         (setq *memoize-info-ht* (mht))
         (setf (gethash *ma-initial-max-symbol-to-fixnum*
                        *memoize-info-ht*)
               "outside-caller")
         (setq *max-symbol-to-fixnum*
           *ma-initial-max-symbol-to-fixnum*)
         (setq *2max-memoize-fns*
           (* 2 *initial-max-memoize-fns*))
         (sync-memoize-call-array)
         (clrhash *form-ht*)
         (setq success t))
       (if success (setq *memoize-init-done* t)
         (ofd "~%; memoize init: Error **"))))))


(defg *max-mem-usage* (expt 2 32)

  "*MAX-MEM-USAGE* an upper bound, in bytes of memory used, that when
  exceeded results in certain garbage collection actions.")

(defg *gc-min-threshold* (expt 2 30))

#+Clozure
(defn1 set-and-reset-gc-thresholds ()
  (let ((n (max (- *max-mem-usage* (ccl::%usedbytes))
                *gc-min-threshold*)))
    (cond ((not (eql n (ccl::lisp-heap-gc-threshold)))
           (ccl::set-lisp-heap-gc-threshold n)
           (ofvv "~&; set-and-reset-gc-thresholds: Reserving ~:d additional bytes.~%"
                 n))))
  (ccl::use-lisp-heap-gc-threshold)
; (ofvv "~&; set-and-reset-gc-thresholds: Calling ~
;        ~%(use-lisp-heap-gc-threshold).")
  (cond ((not (eql *gc-min-threshold*
                   (ccl::lisp-heap-gc-threshold)))
         (ccl::set-lisp-heap-gc-threshold *gc-min-threshold*)
         (ofvv "~&; set-and-reset-gc-thresholds: Will reserve ~:d bytes after
next GC.~%"
               *gc-min-threshold*))))

(defvar *sol-gc-installed* nil)

#+Clozure
(defn1 start-sol-gc ()
  
; The following settings are highly heuristic.  We arrange that gc
; occurs at 1/8 of the physical memory size in bytes, in order to
; leave room for the gc point to grow (as per
; set-and-reset-gc-thresholds).  If we can determine the physical
; memory; great; otherwise we assume that it it contains at least 4GB,
; a reasonable assumption we think for anyone using the HONS version
; of ACL2.

  (let* ((phys (physical-memory))
         (memsize (cond ((> phys 0) (* phys 1024)) ; to bytes
                        (t (expt 2 32)))))
    (setq *max-mem-usage* (min (floor memsize 8)
                               (expt 2 32)))
    (setq *gc-min-threshold* (floor *max-mem-usage* 4)))

; OLD COMMENT:
; Trigger GC after we've used all but (1/8, but not more than 1 GB) of
; the physical memory.

  (unless *sol-gc-installed*
    (ccl::add-gc-hook
     #'(lambda ()
         (ccl::process-interrupt
          (slot-value ccl:*application* 'ccl::initial-listener-process)
          #'set-and-reset-gc-thresholds))
     :post-gc)
    (setq *sol-gc-installed* t))

  (set-and-reset-gc-thresholds))

#+Clozure
(defn1 set-gc-threshold (bound)
  (when (< (ccl::lisp-heap-gc-threshold) bound)
    (ofv "*hons-init-hook*:  Setting (ccl::lisp-heap-gc-threshold) ~
          to ~:d bytes."
         bound)
    (ccl::set-lisp-heap-gc-threshold bound)
    (ccl::use-lisp-heap-gc-threshold))
  nil)
     
#+Clozure
(defun maybe-set-gc-threshold (&optional (fraction 1/32))
  (let (n)
    (setq n (physical-memory))
    (cond ((and (integerp n) (> n (* 2 (expt 10 9))))
           (setq n (floor (* n fraction)))
           (set-gc-threshold n)))))

#+Clozure
(defun number-procs-running ()
  (with-standard-io-syntax
   (with-open-stream (s (csh :stream "vmstat"))
     (read-line s)
     (read-line s)
     (read s))))

#+Clozure
(defn1 load-average ()
  (let ((str (csh "uptime")))
    (let ((loc (search "load average: " str)))
      (values (read-from-string str nil nil :start (+ 14 loc))))))

#+Clozure
(defun rwx-size (&optional verbose)

  "(RWX-SIZE) returns two numbers: (a) the number of bytes that are in
  use by the current CCL process, according to Gary Byers, as detailed
  below, and (b) the number of bytes that are not in use by the
  current Lisp process, but that have been merely imagined in secret
  correspondence between CCL and Gnu-Linux.  Do not worry about (b).

  If the optional argument, VERBOSE, is T, then information about
  memory chunks that both contribute to (a) and that exceed
  1 million bytes are printed to *debug-io*."

;; From an email sent by Gary Byers:

;; If you want a meaningful and accurate answer to the question of how
;; much memory the process is using, I don't know of a more accurate
;; or meaningful answer than what you'd get if you looked at each line
;; in the pseudofile

;; /proc/<pid>/maps

;; on Linux (where <pid> is the process ID of the process) and totaled
;; the sizes of each region that was readable, writable, or
;; executable.  The regions are described by lines that look something
;; like:

;; 300040eef000-300042f60000 rwxp 300040eef000 00:00 0 
;; 300042f60000-307c00000000 ---p 300042f60000 00:00 0

;; The first of these lines describes a region that's readable (r),
;; writable (w), and executable (x); the second line descibes a much
;; larger region that has none of these attributes.  The first region
;; costs something: we have to have some physical memory in order to
;; read/write/execute the contents of those pages (and if we're low on
;; physical memory the OS might move those contents to swap space, and
;; if this happens a lot we'll see delays like those that you
;; describe.)  It's sometimes said that the first region is
;; "committed" memory (the OS has to commit some real resources in
;; order for you to be able to read and write to it) and the second
;; region isn't committed.

; The following code by Boyer is not to be blamed on Byers.

  (let ((fn (format nil "/proc/~a/maps" (ccl::getpid)))
        (count '?)
        potential
        int1 int2 pos1 pos2 next)
    (with-standard-io-syntax
     (when (ignore-errors (probe-file fn))
       (setq count 0)
       (setq potential 0)
       (with-open-file (s fn)
         (loop while (setq next (read-line s nil nil)) do
               (multiple-value-setq (int1 pos1)
                 (parse-integer next :radix 16 :junk-allowed t))
               (multiple-value-setq (int2 pos2)
                 (parse-integer next :start (1+ pos1)
                                :radix 16 :junk-allowed t))
               (let ((add (- int2 int1)))
                 (cond ((loop for i from (+ pos2 1) to (+ pos2 3)
                              thereis
                              (member (char next i) '(#\r #\w #\x)))
                        (incf count add)
                        (when verbose
                          (format *debug-io*
                                  "~&~a~%adds ~:d"
                                  next (- int2 int1))))
                       (t (incf potential add))))))))
    (when verbose (format *debug-io* "~%(rwx-size)=~:d" count))
    (values count potential)))

(defg *gnu-linux-proc-stat-fields*
  '((:pid "Process ID.")
    (:comm "Filename of executable.")
    (:state "Run,Sleep,D=Wait,Zombie,Traced or stopped,W=paging.")
    (:ppid "PID of parent.")
    (:pgrp "Process group ID.")
    (:session "Session ID.")
    (:tty_nr "TTY.")
    (:tpgid "Process group ID of tty owner.")
    (:flags "Kernel flags word.")
    (:minflt "Minor faults no loading from disk.")
    (:cminflt "Minor faults of waited-for children.")
    (:majflt "Major faults loading from disk.")
    (:cmajflt "Major faults of waited-for children.")
    (:utime "User time.")
    (:stime "Kernel time.")
    (:cutime "User time of waited-for children.")
    (:cstime "Kernel time of waited-for children.")
    (:priority "Nice+15.")
    (:nice "Nice. 19 (nicest) to -19 (not  nice to others).")
    (:zero "Always 0.")
    (:itrealvalue "Time before SIGALRM.")
    (:starttime "Time started after system boot.")
    (:vsize "Virtual memory size.")
    (:rss "RSS - pages in real memory.")
    (:rlim "RSS limit.")
    (:startcode "Address above which program text can run.")
    (:endcode "Address below which program text can run.")
    (:startstack "Address of start of the stack.")
    (:kstkesp "ESP (:stack pointer).")
    (:kstkeip "EIP (:instruction pointer).")
    (:signal "Bitmap of pending signals.")
    (:blocked "Bitmap of blocked signals.")
    (:sigignore "Bitmap of ignored signals.")
    (:sigcatch "Bitmap of caught signals.")
    (:wchan "Channel in which waiting.")
    (:nswap "(not maintained).")
    (:cnswap "(not maintained).")
    (:exit_signal "To be sent to parent when we die.")
    (:processor "CPU number last executed on.")
    (:rt_priority "Real-time scheduling.")
    (:policy "Scheduling.")))

(defn pid-owner (&optional also-cmdline)
  (let ((str (csh "ps -A -o user,pid"))
        (ans nil)
        (line nil))
    (with-standard-io-syntax
     (with-input-from-string
      (s str)
      (read-line s nil nil)
      (loop while (setq line (read-line s nil nil))
            collect
            (let ((items
                   (with-input-from-string
                    (s line)
                    (loop for i below 2 collect
                          (ignore-errors (read s nil nil))))))
              (let ((owner (car items))
                    (pid (cadr items)))
                (when (and (integerp pid)
                           (not (equal owner 'root)))
                  (let* ((cfile
                          (ignore-errors
                            (probe-file
                             (format nil "/proc/~a/cmdline" pid)))))
                    (when cfile
                      (let ((cmdline
                             (and also-cmdline
                                  cfile
                                  (with-open-file
                                    (s cfile)
                                    (read-line s nil nil)))))
                        (push (list pid owner cmdline) ans))))))))))
     (sort ans '< :key 'car)))

(defn print-ancestry (&optional (p (ccl::getpid)))
  (with-open-stream
   (s (csh :stream "ps ww -A -o pid,ppid,cmd"))
   (let (first l ans trip)
     (loop (setq first (read s nil nil))
           (when (null first) (return nil))
           (push (list first (read s nil nil) (read-line s nil nil))
                 l))
     (loop (setq trip (assoc p l))
           (when (null trip) (return nil))
           (push (caddr trip) ans)
           (setq p (cadr trip)))
     (setq ans (nreverse ans))
     (loop for i from 0 while ans do
           (terpri)
           (loop repeat i do (write-char #\Space))
           (princ (pop ans))))))

(defn print-fds (&optional (p (ccl::getpid)))
  (loop for x in (directory (ofn "/proc/~a/fd/*" p))
        do
        (let ((n (namestring x)))
          (unless (or (eql #\/ (char n (1- (length n))))
                      (looking-at "/dev/pts/" n)
                      (looking-at "/scratch/" n)
                      (looking-at "/proc/" n))
            (fresh-line)
            (princ n)))))
                  
(defn print-proc-stat (pid)
  (with-standard-io-syntax
  (ignore-errors
    (with-open-file
      (s (format nil "/proc/~a/stat" pid))
      (loop for key in *gnu-linux-proc-stat-fields* do
            (let ((x (read s)))
              (unless (member (car key)
                              '(nswap zero cnswap rlim kstkesp kstkeip
                                      startstack wchan policy
                                      rt_policy))
                (format *standard-output*
                        "~%~a~12t~15:d~30t~a"
                        (car key)
                        x
                        (cadr key)))))))))

(defn proc-stat (pid)
  (with-standard-io-syntax
   (ignore-errors
     (with-open-file
       (s (format nil "/proc/~a/stat" pid))
       (loop for key in *gnu-linux-proc-stat-fields*
             nconc (list (car key) (read s)))))))

#+Clozure
(defn rss (&optional verbose)
  (with-standard-io-syntax
   (let ((ans nil))
     (loop for triple in (pid-owner) do
           (let ((items (proc-stat (car triple))))
             (let ((rss (getf items :rss)))
               (when (and (integerp rss) (> rss 1000))
                 (push (list (car triple)
                             (cadr triple)
                             rss
                             (getf items :comm))
                       ans)))))
     (setq ans (sort ans '> :key 'third))
     (when verbose
       (oft "~%pid       user               rss comm")
       (loop for x in ans do
             (apply 'format
                    *standard-output*
                    "~%~a~10t~a~20t~12:d~30t~a"
                    x))
       (oft "~%from man proc: rss = Resident Set Size.  Number of ~
          pages in real memory.")
       (oft "~%host-page-size:  ~:d" CCL:*HOST-PAGE-SIZE*))
     ans)))

(defg *hons-init-hook*
  '(progn

     #+Clozure
     (unless (> (parse-integer ccl::*openmcl-svn-revision*
                               :junk-allowed t)
                13296)
       (fresh-line)
       (princ "Better use a version of CCL past revision 13280."))

     (set-gag-mode t)

     (f-put-global 'hons-enabled t *the-live-state*)

     "If the ACL2 global PRINT-CIRCLE is not t,
      then .cert files may be huge."

     (f-put-global 'print-circle t *the-live-state*)
     (f-put-global 'print-circle-files t *the-live-state*)

     "Tell the user how to shut off asides."

     (hons-init-hook-set '*ofv-note-printed* nil)

     (when (boundp '*help*)
       (ofv "Type *HELP* outside the ACL2 loop for some ~
             documentation tips."))

     (hons-init-hook-set '*print-pretty* t)

     (when (not (memoizedp-raw 'bad-lisp-objectp))
       (with-lower-overhead
        (memoize-fn 'bad-lisp-objectp :forget t)))

     (when (not (memoizedp-raw 'worse-than-builtin))
  
; Warning: If this is changed or removed, visit the comment in 
; worse-than-builtin.
  
       (with-lower-overhead
        (memoize-fn 'worse-than-builtin
                    :condition ; Sol Swords suggestion
                    '(and (nvariablep term1)
                          (not (fquotep term1))
                          (nvariablep term2)
                          (not (fquotep term2))))))

     (when (not (memoizedp-raw 'fchecksum-obj))

     "If this memoization is removed, modify the comment in
      fchecksum-obj about memoization of that function."

       (with-lower-overhead
        (memoize-fn 'fchecksum-obj :forget t)))

     (when (not (memoizedp-raw 'expansion-alist-pkg-names-memoize))

     "If this memoization is removed, modify the comment in
      expansion-alist-pkg-names about memoization of that function."

       (with-lower-overhead
        (memoize-fn 'expansion-alist-pkg-names-memoize :forget t)))

     ;; [Jared]: merged in from e4/memoize-raw.lsp
     (when (not (memoizedp-raw 'physical-memory))
       (with-lower-overhead
        (memoize-fn 'physical-memory :inline nil)))

     ;; [Jared]: merged in from e4/memoize-raw.lsp
     (when (not (memoizedp-raw 'swap-total))
       (with-lower-overhead
        (memoize-fn 'swap-total :inline nil)))


     #+Clozure
     (progn

       (hons-init-hook-set 'ccl::*long-site-name*
                           (ignore-errors (ccl::getenv "HOSTNAME")))

       (hons-init-hook-set 'ccl::*short-site-name*
         (subseq ccl::*long-site-name*
                 0 (search "." ccl::*long-site-name*)))

       (hons-init-hook-set '*print-right-margin*
        (ignore-errors (read-from-string (ccl::getenv "COLUMNS"))))

       "Permit FUNCTION-LAMBDA-EXPRESSION to return the form
        used in the DEFUN of a function symbol."

       (hons-init-hook-set 'ccl::*save-definitions* t)

       (hons-init-hook-set 'ccl::*save-source-locations* t)

       (hons-init-hook-set 'ccl::*fasl-save-definitions* t)

       (hons-init-hook-set 'ccl::*record-source-file* t)

       "Allow control-d to exit from CCL."

       (hons-init-hook-set 'ccl::*quit-on-eof* t)

;   This might be a good idea, but we do not understand about
;   ccl::advise being called twice, e.g., via *hons-init-hook*.
; 
;    "Before an image is saved or we otherwise quit, we kill any WATCH
;     process and delete any /tmp file created by the csh/sh facility."
;   
;     (ccl::advise ccl::quit
;                 (progn (watch-kill) (csh-stop) (sh-stop))
;                 :when :before)

       "It is usually best for the user to know what the garbage
        collector is doing when using HONS and MEMOIZE."

       (unless (equal '(t t)
                      (multiple-value-list (ccl::gc-verbose-p)))
         (ofvv "*hons-init-hook*:  Setting CCL's gc to verbose.")
         (ccl::gc-verbose t t))
     
       "CCL's ephemeral gc doesn't seem to work well with honsing and
        memoizing, so we always shut it off."
     
       (when (ccl::egc-active-p)
         (ofvv "*hons-init-hook*:  Turning off CCL's ephemeral gc.")
         (ccl::egc nil))
     
       "Sol Swords's scheme to control GC in CCL.  See long comment in
        memoize-raw.lisp."

       #+Clozure (start-sol-gc)


;; [Jared]: removing the (user-INIT) thing because it's just asking
;; for inconsistencies.  Instead, replacing it with the what Sol and
;; Warren and I have been using:

       ;; "Run (user-INIT) if it exists."

       ;; #+Clozure
       ;; (let ((init-fn
       ;;        (intern
       ;;         (string-upcase
       ;;          (format nil "~a-init" (ccl::getenv "USER")))
       ;;         :acl2)))
       ;;   (cond ((fboundp init-fn)
       ;;          (ofvv "Running (~a)." init-fn)
       ;;          (funcall init-fn))
       ;;         (t (ofvv "~% ~a not fboundp, hence not funcalled."
       ;;                  init-fn))))

       #+Clozure
       (progn (ccl::egc nil)
              (set-and-reset-gc-thresholds))

       ))
  
  "*HONS-INIT-HOOK* is EVALed by HONS-INIT.  *HONS-INIT-HOOK* may be
  EVALed several times because HONS-INIT may be called several times.
  *HONS-INIT-HOOK* is supposed to set some options that a user might
  want to set in a ccl-init.lisp or an acl2-init.lsp file but might
  not know to set.")

(defn hons-init-hook-set (var val)
  (unless (symbolp var)
    (ofe "HONS-INIT-HOOK-SET works for symbols, not ~a." var))
  (when (not (equal val (symbol-value var)))
    (ofv "*hons-init-hook*:  Setting ~a to ~a." var val)
    (setf (symbol-value var) val)))     

;          Sol Sword's scheme to control GC in CCL
; 
; The goal is to get CCL to perform a GC whenever we're using almost
; all the physical memory, but not otherwise.
; 
; The usual way of controlling GC on CCL is via LISP-HEAP-GC-THRESHOLD.
; This value is approximately amount of memory that will be allocated
; immediately after GC.  This means that the next GC will occur after
; LISP-HEAP-GC-THRESHOLD more bytes are used (by consing or array
; allocation or whatever.)  But this means the total memory used by the
; time the next GC comes around is the threshold plus the amount that
; remained in use at the end of the previous GC.  This is a problem
; because of the following scenario:
; 
;  - We set the LISP-HEAP-GC-THRESHOLD to 3GB since we'd like to be able
;    to use most of the 4GB physical memory available.
; 
;  - A GC runs or we say USE-LISP-HEAP-GC-THRESHOLD to ensure that 3GB
;    is available to us.
; 
;  - We run a computation until we've exhausted this 3GB, at which point
;    a GC occurs.  
; 
;  - The GC reclaims 1.2 GB out of the 3GB used, so there is 1.8 GB
;    still in use.
; 
;  - After GC, 3GB more is automatically allocated -- but this means we
;    won't GC again until we have 4.8 GB in use, meaning we've gone to
;    swap.
; 
; What we really want is, instead of allocating a constant additional
; amount after each GC, to allocate up to a fixed total amount including
; what's already in use.  To emulate that behavior, we use the hack
; below.  This operates as follows (assuming the same 4GB total physical
; memory as in the above example:)
; 
; 1. We set the LISP-HEAP-GC-THRESHOLD to (3.5G - used bytes) and call
; USE-LISP-HEAP-GC-THRESHOLD so that our next GC will occur when we've
; used a total of 3.5G.
; 
; 2. We set the threshold back to 1GB without calling
; USE-LISP-HEAP-GC-THRESHOLD.
; 
; 3. Run a computation until we use up the 3.5G and the GC is called.
; Say the GC reclaims 1.2GB so there's 2.3GB in use.  1GB more (the
; current LISP-HEAP-GC-THRESHOLD) is allocated so the ceiling is 3.3GB.)
; 
; 4. A post-GC hook runs which again sets the threshold to (3.5G -
; used bytes), calls USE-LISP-HEAP-GC-THRESHOLD to raise the ceiling to
; 3.5G, then sets the threshold back to 1GB, and the process repeats.
; 
; A subtlety about this scheme is that post-GC hooks runs in a separate
; thread from the main execution.  A possible bug is that in step 4,
; between checking the amount of memory in use and calling
; USE-LISP-HEAP-GC-THRESHOLD, more memory might be used up by the main
; execution, which would set the ceiling higher than we intended.  To
; prevent this, we interrupt the main thread to run step 4.

(defn1 hons-init ()

; We assume ACL2-DEFAULT-RESTART will be called at least once.  We
; suspect it will be called whenever an ACL2H CCL saved image is
; started up.  We know that ACL2-DEFAULT-RESTART calls HONS-INIT.  We
; are unsure how many times ACL2-DEFAULT-RESTART might be called, and
; so we code HONS-INIT so that it may be called multiple times.

  (in-package "ACL2")
  (unless *hons-readtable-init-done* (hons-readtable-init))
  (unless *memoize-init-done* (memoize-init))
  (float-ticks/second-init)
  (eval *hons-init-hook*))

(defn all-module-names ()
  (loop for x in (table-alist 'defm-table (w *the-live-state*))
        collect
        (cadar x)))
               
(defn all-modules ()
  (loop for n in (all-module-names) collect
        (symbol-value n)))

(defg *current-module-names-ht* (make-hash-table :test 'eq))

(defn1 current-module-name-p (x)
  (cond ((eq (w *the-live-state*)
             (gethash *current-module-names-ht*
                      *current-module-names-ht*))
         (gethash x *current-module-names-ht*))
        (t (clrhash *current-module-names-ht*)
           (loop for x in (table-alist 'defm-table
                                       (w *the-live-state*))
                 do (setf (gethash (cadar x)
                                   *current-module-names-ht*)
                          t))
           (setf (gethash *current-module-names-ht*
                          *current-module-names-ht*)
                 (w *the-live-state*))
           (gethash x *current-module-names-ht*))))

;;; SHORTER, OLDER NAMES

; Note: memsum is defined in memoize.lisp.

(defun memstat (&rest r)
  (apply #'memoized-values r))

(defmacro memo-on (&rest r)
  `(memoize-on ,@r))

(defmacro memo-off (&rest r)
  `(memoize-off ,@r))

(defun clear-memo-tables (&rest r)
  (setq *pons-call-counter* 0)
  (setq *pons-misses-counter* 0)
  (apply #'clear-memoize-tables r))

(defg *compiled-module-ht* (mht :test 'eq)

  "The hash table *COMPILED-MODULE-HT* maps a module name n to a cons
  of (1) the module named n with (2) the compiled version of module n,
  which is a compiled function, for primitive modules, and an array,
  for nonprimitive modules.  The car is EQ to the module that was the
  symbol value of n when the compilation was done.")


;;;                                WATCH

(defg *watch-forms*
  '("\"A string or a quoted form in *WATCH-FORMS* is ignored.\""
    (print-call-stack)
    #+Clozure '(bytes-used)
    (memoize-summary)
    (time-since-watch-start)
    (time-of-last-watch-update)
    '(mapc 'print-some-documentation *watch-items*)
    '(hons-calls/sec-run-time)
    '(hons-hits/calls)
    '(hons-acons-summary)
    '(pons-calls/sec-run-time)
    '(pons-hits/calls)
    '(pons-summary)
    '(hons-summary)
    '(print-fds)
    '(print-ancestry)
    #+Clozure '(watch-shell-command "pwd")
    '(functions-that-may-be-too-fast-to-sensibly-profile)
    '(physical-memory-on-this-machine)
    #+Clozure '(number-of-cpus-on-this-machine)
    #+Clozure (gc-count)
    )

  "The forms in *WATCH-FORMS* are evaluated periodically and the
  output is written to *WATCH-FILE*.  Change *WATCH-FORMS*
  to produce whatever watch output you want.")

(defg *watch-items*
  '((length-memoized-functions)
    *memoize-summary-limit*
    *memoize-summary-order-list*
    *memoize-summary-order-reversed*
    *max-mem-usage*

    *watch-forms*
    *watch-file*
    *watch-items*

    *count-pons-calls*

    *memoize-summary-order-list*
    *memoize-summary-order-reversed*
    *memoize-summary-limit*

    *record-bytes*
    *record-calls*
    *record-hits*
    *record-hons-calls*
    *record-mht-calls*
    *record-pons-calls*
    *record-time*

    *report-bytes*
    *report-calls*
    *report-calls-from*
    *report-calls-to*
    *report-hits*
    *report-hons-calls*
    *report-mht-calls*
    *report-pons-calls*
    *report-time*
    *report-on-memo-tables*
    *report-on-pons-tables*

    #+Clozure (ccl::lisp-heap-gc-threshold)
    #+Clozure (ccl::%freebytes)

    )
  "*WATCH-ITEMS* is a list of forms that are printed with their values
  and documentation if (MAPC 'PRINT-SOME-DOCUMENTATION *WATCH-ITEMS*)
  is a member of *WATCH-FORMS* and (WATCH-DO) is invoked.")

(defg *watch-last-real-time* 0)

(defg *watch-last-run-time* 0)

(defg *watch-start-real-time* 0)

(defg *watch-start-run-time* 0)

(defg *watch-start-gc-count*  0)

(defg *watch-start-gc-time* 0)

(defg *watch-start-heap-bytes-allocated* 0)

(declaim (mfixnum *watch-last-real-time* *watch-last-run-time*
                  *watch-start-real-time* *watch-start-run-time*
                  *watch-start-gc-count* *watch-start-gc-time*))

(defg *watch-file-form*

  '(format nil "watch-output-temp-~D.lsp" (getpid$))

  "The value of *WATCH-FILE-FORM* should be a form that is to
  be evaluated whenever (WATCH) is invoked in order to get
  the string that is to name *WATCH-FILE*.")


#+Clozure
(defv *watch-dog-process* nil

  "*WATCH-DOG-PROCESS*, when non-NIL is a CCL process that
  periodically asks the main CCL thread/process,
  *WATCH-STARTUP-PROCESS*, to invoke MAYBE-WATCH-DUMP.

  It is always ok to kill the *WATCH-DOG-PROCESS*.  (WATCH-KILL) does
  that.")

#+Clozure
(defv *watch-startup-process* nil

  "*WATCH-STARTUP-PROCESS*, when non-NIL is the CCL process that
  created the *WATCH-DOG-PROCESS*, and the only process that should
  ever run MAYBE-WATCH-DUMP.")

#+Clozure
(defparameter *with-space-timer-raw-limit* nil)
  
#+Clozure
(defparameter *with-run-timer-raw-limit* nil
  
  "*WITH-RUN-TIMER-RAW-LIMIT* is bound only by WITH-RUN-TIMER-RAW, and
  is bound to a nonnegative integer representing the value of
  (INTERNAL-RUN-TIME) after which, if the watch process interrupts the
  main Lisp process to run MAYBE-WATCH-DUMP, the execution of
  MAYBE-WATCH-DUMP will raise an error with a condition of type
  WITH-TIMER-RAW-CONDITION-TYPE.")

#+Clozure
(defparameter *with-real-timer-raw-limit* nil
  
  "*WITH-REAL-TIMER-RAW-LIMIT* is bound only by WITH-REAL-TIMER-RAW,
  and is bound to a nonnegative integer representing the value of
  (INTERNAL-REAL-TIME) after which, if the watch process interrupts
  the main Lisp process to run MAYBE-WATCH-DUMP, the execution of
  MAYBE-WATCH-DUMP will raise an error with a condition of type
  WITH-TIMER-RAW-CONDITION-TYPE.")

#+Clozure
(defg *watch-lock-ht* (make-hash-table)
  "*WATCH-LOCK-HT* is used to provide a locking mechanism to
  prevent watch-dump from being run twice at the same time.")
  
#+Clozure
(declaim (hash-table *watch-lock-ht*))

#+Clozure
(defg *watch-real-seconds-between-dumps* 5

  "WATCH-DUMP will not run more than once every
  *WATCH-REAL-SECONDS-BETWEEN-DUMPS* seconds.")

#+Clozure
(declaim (fixnum *watch-real-seconds-between-dumps*))

#+Clozure
(defn watch-condition ()
  (unless (eq *watch-dog-process* ccl::*current-process*)
    (ofto "~%WATCH-CONDITION should only be called by ~
          *watch-dog-process*:~%~a~%never by~%~a."
          *watch-dog-process*
          ccl::*current-process*))
  (and *watch-file*
       (eql 0 ccl::*break-level*)
       (let ((run nil) (real nil))
         (or (and *with-space-timer-raw-limit*
                  (> (ccl::%usedbytes) *with-space-timer-raw-limit*))
             (and *with-real-timer-raw-limit*
                  (> (setq real (get-internal-real-time))
                     *with-real-timer-raw-limit*))
             (and *with-run-timer-raw-limit*
                  (> (setq run (get-internal-run-time))
                     *with-run-timer-raw-limit*))
             (and (> (or run (get-internal-run-time))
                     *watch-last-run-time*)
                  (> (or real (get-internal-real-time))
                     (+ *watch-last-real-time*
                        (* *watch-real-seconds-between-dumps*
                           internal-time-units-per-second))))))
       (eql 0 (hash-table-count *watch-lock-ht*))))

#+Clozure
(defmacro with-watch-lock (&rest r)

; WITH-WATCH-LOCK may well do nothing, knowing that a later call of
; MAYBE-WATCH-DUMP will probably evenutally be made by the
; WATCH-DOG-PROCESS, and that will be good enough.  WITH-WATCH-LOCK
; does not support a queue of pending requests for the lock.

  `(progn
     (cond ((not (eq *watch-startup-process* ccl::*current-process*))
            (ofd "~%; WITH-WATCH-LOCK: ** Only the ~
                   *WATCH-STARTUP-PROCESS* may obtain the watch ~
                   lock."))
           ((not (eql 0 ccl::*break-level*))
            (ofd "~%; WITH-WATCH-LOCK: ** (eql 0 ~
                  ccl::*break-level*)."))
           ((not *watch-file*)
            (ofd "~%; *WATCH-FILE* is NIL.  Invoke (watch)."))
           ((eql 0 (hash-table-count *watch-lock-ht*))
            
; At this point, nothing has the watch lock.  We race for the watch
; lock but unknown others may also get into the race, this very
; process executing this very code.

            (let ((id (cons nil nil)))  ; a unique object
              (unwind-protect 
                  (progn
                    (setf (gethash id *watch-lock-ht*) t)
                    (cond ((eql (hash-table-count *watch-lock-ht*) 1)
                           
; The watch lock has been obtained by only one of 'us', and any
; competitors will do nothing.
                           
                           ,@r)
                          (t (ofd "~%; WITH-WATCH-LOCK: ** the watch ~
                                   lock is currently taken."))))
                (remhash id *watch-lock-ht*))
              
; The watch lock is released as of now, if it was obtained.
              
              ))
           (t (ofd "~%; WITH-WATCH-LOCK: ** the watch lock is ~
                    currently taken.")))
     *watch-file*))

#+Clozure
(define-condition with-timer-raw-condition-type (error) ())

; The following 'condition' type and one 'instance' thereof are
; created to support one use in the HANDLER-CASE form in
; WITH-RUN-TIMER-RAW or WITH-RUN-TIMER-RAW, permitting time out errors
; to be distinguished from all other sorts of errors.

#+Clozure
(defg *with-space-timer-raw-condition-instance*
  (make-condition 'with-timer-raw-condition-type))

#+Clozure
(defg *with-real-timer-raw-condition-instance*
  (make-condition 'with-timer-raw-condition-type))

#+Clozure
(defg *with-run-timer-raw-condition-instance*
  (make-condition 'with-timer-raw-condition-type))

#+Clozure
(defv *space-timer-raw-bytes* 1)

#+Clozure
(defv *space-timer-raw-value* '("space out"))

#+Clozure
(defv *real-timer-raw-seconds* 1)

#+Clozure
(defv *real-timer-raw-value* '("time out"))

#+Clozure
(defv *run-timer-raw-seconds* 1)

#+Clozure
(defv *run-timer-raw-value* '("time out"))

#+Clozure
(defmacro with-space-timer-raw (form
                                &key
                          (bytes *space-timer-raw-bytes*)
                          (space-out-value *space-timer-raw-value*))
  `(let* ((old *with-space-timer-raw-limit*)
          (new (+ (ccl::%usedbytes) ,bytes))
          (new2 (if *with-space-timer-raw-limit*
                    (min *with-space-timer-raw-limit* new)
                  new)))
     (handler-case
      (progn (setq *with-space-timer-raw-limit* new2)
             (unwind-protect ,form
               (setq *with-space-timer-raw-limit* old)))
      (with-timer-raw-condition-type
       (c)
       (cond ((eq c *with-space-timer-raw-condition-instance*)
              ; (ofd "~&; space-out when evaluating:~%~s." ',form)
              (setq *with-space-timer-raw-limit* old)
              ',space-out-value)
             (t (error c)))))))

#+Clozure
(defmacro with-real-timer-raw (form
                          &key
                          (seconds *real-timer-raw-seconds*)
                          (time-out-value *real-timer-raw-value*))
  
  "(WITH-REAL-TIMER-RAW form &key seconds time-out-value) begins an
  evaluation of FORM, but the evaluation may and should be aborted
  when more than SECONDS seconds of real-time (wall time) elapses.
  Whether an abort actually occurs depends upon the vagaries of time,
  including whether the watch-dog-process, if there is one, is
  successful in interrupting the main Lisp process.  If and when the
  evaluation of FORM completes, WITH-REAL-TIMER-RAW returns the
  value(s) of that evaluation.  But otherwise, TIME-OUT-VALUE is
  returned.  SECONDS defaults to the value of
  *REAL-TIMER-RAW-SECONDS*.  TIME-OUT-VALUE defaults to a list of
  length one whose only member is a string; such an object satisfies
  TO-IF-ERROR-P.

  If WITH-REAL-TIMER-RAW is called while WITH-REAL-TIMER-RAW is
  running, the new time limit is bounded by any and all real-timer
  limits already in place."

 `(let* ((old *with-real-timer-raw-limit*)
         (new (floor
               (+ (get-internal-real-time)
                  (* ,seconds internal-time-units-per-second))))
         (new2 (if *with-real-timer-raw-limit*
                   (min *with-real-timer-raw-limit* new)
                 new)))
    (handler-case
     (progn (setq *with-real-timer-raw-limit* new2)
            (unwind-protect ,form
              (setq *with-real-timer-raw-limit* old)))
     (with-timer-raw-condition-type
      (c)
      (cond ((eq c *with-real-timer-raw-condition-instance*)
             (ofd "~&; real-time-out when evaluating:~%~s." ',form)
             (setq *with-real-timer-raw-limit* old)
             ',time-out-value)
            (t (error c)))))))

#+Clozure
(defmacro with-run-timer-raw (form
                          &key
                          (seconds *run-timer-raw-seconds*)
                          (time-out-value *run-timer-raw-value*))
  
  "(WITH-RUN-TIMER-RAW form &key seconds time-out-value) begins an
  evaluation of FORM, but the evaluation may and should be aborted
  when more than SECONDS seconds of run-time (not wall time) elapses.
  Whether an abort actually occurs depends upon the vagaries of time,
  including whether the watch-dog-process, if there is one, is
  successful in interrupting the main Lisp process.  If and when the
  evaluation of FORM completes, WITH-RUN-TIMER-RAW returns the
  value(s) of that evaluation.  But otherwise, TIME-OUT-VALUE is
  returned.  SECONDS defaults to the value of *RUN-TIMER-RAW-SECONDS*,
  which is initially 5.  TIME-OUT-VALUE defaults to a list of length
  one whose only member is a string; such an object satisfies
  TO-IF-ERROR-P.

  If WITH-RUN-TIMER-RAW is called while WITH-RUN-TIMER-RAW is running,
  the new time limit is bounded by any and all run-time limits already
  in place."

 `(let* ((old *with-run-timer-raw-limit*)
         (new (floor
               (+ (get-internal-run-time)
                  (* ,seconds internal-time-units-per-second))))
         (new2 (if *with-run-timer-raw-limit*
                   (min *with-run-timer-raw-limit* new)
                 new)))
    (handler-case
     (progn (setq *with-run-timer-raw-limit* new2)
            (unwind-protect ,form
              (setq *with-run-timer-raw-limit* old)))
     (with-timer-raw-condition-type
      (c)
      (cond ((eq c *with-run-timer-raw-condition-instance*)
             (ofd "~&; run-time-out when evaluating:~%~s." ',form)
             (setq *with-run-timer-raw-limit* old)
             ',time-out-value)
            (t (error c)))))))

(defn1 watch-dump ()

  "(WATCH-DUMP) writes to the watch file the characters sent to
  *STANDARD-OUTPUT* by the evaluation of the members of *WATCH-FORMS*.

  The value of *WATCH-FILE* is returned by WATCH-DUMP.

  If *WATCH-FILE* is NIL, (WATCH) is invoked."

  (unless *watch-file* (watch))
  (setf (fill-pointer *watch-string*) 0)
  (our-syntax-nice
   (with-output-to-string
     (*standard-output* *watch-string*)
     (setq *print-miser-width* 100)
     (loop for form in *watch-forms* do
           (handler-case
            (eval form)
            (with-timer-raw-condition-type
             (c) ; pass it on up
             (incf-watch-count)
             (error c))
            (error ()
                   (oft "~&~s~50t? error in eval ?~%"
                        form)))
           (fresh-line)))
   (with-open-file (stream *watch-file* :direction :output
                           :if-exists :supersede)
     (write-string *watch-string* stream))
   (setq *watch-last-real-time* (get-internal-real-time))
   (setq *watch-last-run-time* (get-internal-run-time)))
  *watch-file*)

#+Clozure
(defn1 maybe-watch-dump ()

  "The function MAYBE-WATCH-DUMP is only executed as an interruption
  request to the main Lisp thread from the watch dog process.  To
  repeat, MAYBE-WATCH-DUMP is executed only by the main Lisp thread.
  There is no overwhelming reason why this should be so, but the issue
  of 'shared' hash tables, 'static' variables, ERROR handling, and
  DEFPARAMETER bindings should be carefully considered if this design
  choice is reconsidered.

  (MAYBE-WATCH-DUMP) performs three unrelated tasks.

  1.  If *WITH-RUN-TIMER-RAW-LIMIT* is a nonnegative integer that is
  less than (GET-INTERNAL-RUN-TIME), then an error of type
  TIMER-RAW-CONDITION is raised, which normally will be caught by the
  error handler established by a pending call of WITH-RUN-TIMER-RAW.

  2.  If *WITH-REAL-TIMER-RAW-LIMIT* is a nonnegative integer that is
  less than (GET-INTERNAL-REAL-TIME), then an error of type
  TIMER-RAW-CONDITION is raised, which normally will be caught by
  the error handler established by a pending call of
  WITH-REAL-TIMER-RAW.

  3.  If the watch lock can be obtained, (WATCH-DUMP) is run."

  (cond ((not (eql 0 ccl::*break-level*))
         (incf-watch-count))
        ((and *watch-file*
              (eq *watch-startup-process* ccl::*current-process*))
         (when (and *with-space-timer-raw-limit*
                    (> (ccl::%usedbytes)
                       *with-space-timer-raw-limit*))
           (setq *with-space-timer-raw-limit* nil)
           (incf-watch-count)
           (error *with-space-timer-raw-condition-instance*))
         (when (and *with-run-timer-raw-limit*
                    (> (get-internal-run-time)
                       *with-run-timer-raw-limit*))
           (setq *with-run-timer-raw-limit* nil)
           (incf-watch-count)
           (error *with-run-timer-raw-condition-instance*))
         (when (and *with-real-timer-raw-limit*
                    (> (get-internal-real-time)
                       *with-real-timer-raw-limit*))
           (setq *with-real-timer-raw-limit* nil)
           (incf-watch-count)
           (error *with-real-timer-raw-condition-instance*))
         (handler-case
  
; No thread or stack frame can be expected to handle an error under
; MAYBE-WATCH-DUMP in WATCH-DUMP, because MAYBE-WATCH-DUMP is run as
; the result of an interrupt from the watch dog process.  In this
; unexpected case, we ignore the error, after printing a note to
; *DEBUG-IO*.
  
; MAYBE-WATCH-DUMP calls (INCF-WATCH-COUNT), even if MAYBE-WATCH-DUMP
; exits via ERROR or exits after catching and ignoring an error.
; Otherwise, the interrupting watch dog process might wait a very long
; time before resuming normal operation."

          (with-watch-lock (watch-dump))
          (with-timer-raw-condition-type
           (c) ; pass it on up
           (incf-watch-count)
           (error c))
          (error
           (x)
           (ofd "~%; MAYBE-WATCH-DUMP: An error is being ignored:~% ~
                 ~a." x)
           (incf-watch-count)))
         (incf-watch-count)
         *watch-file*)
        (t (incf-watch-count)
           (ofd "~%; MAYBE-WATCH-DUMP may only be called by the ~
                 *WATCH-STARTUP-PROCESS*"))))

(defn1 watch-kill ()

  "(WATCH-KILL) kills the CCL *WATCH-DOG-PROCESS*, if any, and sets
  the *WATCH-FILE* to NIL.  It is alway OK to invoke (WATCH-KILL)."

  (setq *watch-file* nil)
  #+Clozure
  (when *watch-dog-process*
    (ignore-errors (ccl::process-kill *watch-dog-process*))
    (setq *watch-dog-process* nil))
  #+Clozure
  (setq
    *watch-dog-process*            nil
    *with-real-timer-raw-limit*    nil
    *with-space-timer-raw-limit*   nil
    *with-run-timer-raw-limit*     nil
    *watch-startup-process*        nil))

(defg *watch-count-ht* (make-hash-table))

(defn1 watch-count ()
  (values (gethash 'count *watch-count-ht*)))

(defn1 incf-watch-count ()
  (incf (gethash 'count *watch-count-ht*)))
  
(defn1 set-watch-count (x)
  (setf (gethash 'count *watch-count-ht*) x))

(defv *watch-sleep-seconds* 1
  
  "The watch dog process sleeps at least *WATCH-SLEEP-SECONDS*
  before interrupting the main process.")

(defn1 swap-total ()
  (meminfo "SwapTotal:"))

(defun watch (&optional force-dog)

  "WATCH is a raw Lisp function that initiates the printing of
  profiling information.  (WATCH) sets *WATCH-FILE* to the string that
  results from the evaluation of *WATCH-FILE-FORM*, a string that is
  to be the name of a file we call the 'watch file'.

  In Clozure Common Lisp, (WATCH) also initiates the periodic
  evaluation of (WATCH-DUMP), which evaluates the members of the list
  *WATCH-FORMS*, but diverts characters for *STANDARD-OUTPUT* to the
  watch file.  The value of *WATCH-FILE* is returned by both (WATCH)
  and (WATCH-DUMP).  (WATCH-KILL) ends the periodic printing to the
  watch file.

  You are most welcome to, even encouraged to, change the members of
  *WATCH-FORMS* to have your desired output written to the watch file.

  Often (MEMOIZE-SUMMARY) is a member of *WATCH-FORMS*.  It prints
  information about calls of memoized and/or profiled functions.

  Often (PRINT-CALL-STACK) is a member of *WATCH-FORMS*.  It shows the
  names of memoized and/or profiled functions that are currently in
  execution and how long they have been executing.

  Other favorite members of *WATCH-FORMS* include (PRINT-FDS),
  (BYTES-USED), and (GC-COUNT).

  We suggest the following approach for getting profiling information
  about calls to Common Lisp functions:

    0. Invoke (WATCH).
  
    1. Profile some functions that have been defined.

       For example, call (PROFILE 'foo1), ...

       Or, for example, call PROFILE-FILE on the name of a file that
       contains the definitions of some functions that have been
       defined.

       Or, as a perhaps extreme example, invoke
       (PROFILE-ACL2), which will profile many of the functions that
       have been introduced to ACL2, but may take a minute or two.

       Or, as a very extreme example, invoke
       (PROFILE-ALL), which will profile many functions, but may take
       a minute or two.

    2. Run a Lisp computation of interest to you that causes some of
       the functions you have profiled to be executed.
 
    3. Invoke (WATCH-DUMP).

    4. Examine, perhaps in Emacs, the watch file, whose name was
       returned by (WATCH-DUMP).  The watch file contains information
       about the behavior of the functions you had profiled or
       memoized during the computation of interest.

  From within ACL2, you may MEMOIZE any of your ACL2 Common Lisp
  compliant ACL2 functions.  One might MEMOIZE a function that is
  called repeatedly on the exact same arguments.  Deciding which
  functions to memoize is tricky.  The information from (WATCH-DUMP)
  helps.  Sometimes, we are even led to radically recode some of our
  functions so that they will behave better when memoized.

  In Emacs, the command 'M-X AUTO-REVERT-MODE' toggles auto-revert
  mode, i.e., causes a buffer to exit auto-revert mode if it is in
  auto-revert mode, or to enter auto-revert mode if it is not.  In
  other words, to stop a buffer from being auto-reverted, simply
  toggle auto-revert mode; toggle it again later if you want more
  updating.  'M-X AUTO-REVERT-MODE' may be thought of as a way of
  telling Emacs, 'keep the watch buffer still'.

  In Clozure Common Lisp, if the FORCE-DOG argument to WATCH (default
  NIL) is non-NIL or if (LIVE-TERMINAL-P) is non-NIL a 'watch dog'
  thread is created to periodically call (WATCH-DUMP).  The thread is
  the value of *WATCH-DOG-PROCESS*.

  Invoke (WATCH-HELP) outside of ACL2 for further details."

  #+Clozure
  (ccl::cpu-count)
  (watch-kill)
  #+Clozure
  (pushnew 'watch-kill ccl::*save-exit-functions*)
  (setq *watch-lock-ht* (make-hash-table))
  (setq *watch-file* nil)
  (setq *watch-start-real-time* (get-internal-real-time))
  (setq *watch-start-run-time* (get-internal-run-time))
  (setq *watch-last-real-time* 0)
  (setq *watch-last-run-time* 0)
  (set-watch-count 0)
  (clear-memoize-call-array)
  (unless (and (ignore-errors
                 (setq *watch-file* (eval *watch-file-form*)))
               (stringp *watch-file*))
    (ofe "; WATCH: evaluation of *WATCH-FILE-FORM* failed to ~
          produce a string."))
  #+Clozure
  (progn
    (setq *watch-start-gc-count* (ccl::full-gccount))
    (setq *watch-start-gc-time* (ccl::gctime))
    (setq *watch-start-heap-bytes-allocated* (heap-bytes-allocated))
    (setq *watch-startup-process* ccl::*current-process*)
    (when (or force-dog (live-terminal-p))
      (setq *watch-dog-process*
        (ccl::process-run-function "watch-dog-process"
         (lambda ()
           (let (x)
             (loop (sleep *watch-sleep-seconds*)
                   (setq x (watch-count))
                   (when (watch-condition)
                     (ccl:process-interrupt *watch-startup-process*
                                            #'maybe-watch-dump)
                     (loop for i from 1 while (>= x (watch-count))
                           do (sleep *watch-sleep-seconds*))))))))
      (ofv "An invocation of (WATCH) has now started a new ~%; ~
            Aside:  Clozure Common Lisp thread, the ~
            *WATCH-DOG-PROCESS*, which~%; Aside:  calls ~
            (MAYBE-WATCH-DUMP) periodically, which writes to the ~
            file ~%; Aside:  whose name is the value of ~
            *WATCH-FILE*, viz.,~%; Aside:  ~a.~%(WATCH-KILL) kills ~
            the thread.~%"
         *watch-file*)))
  (watch-dump))

(defn1 first-string (l)
  (loop for x in l when (stringp x) do (return x)))

(defg *undocumented-symbols* nil)

(defn1 print-some-documentation (x)
  (let ((state *the-live-state*)
        (types-of-documentation
         '(compiler-macro function
                          method-combination
                          setf structure type variable
                          t)))

; 0. Print it, evaluate it, and print the value, if possible.

    (oft "~&~%~a" x)
    (let* ((avrc (cons nil nil))
           (value avrc))
      (cond ((symbolp x)
             (cond ((boundp x)
                    (setq value (symbol-value x)))
                   ((fboundp x) nil)
                   (t (setq value "unbound"))))
            (t (setq value "error-in-evaluation")
               (ignore-errors
                 (setq value
                   (multiple-value-list (eval x))))))
      (cond ((not (eq value avrc))
             (when (and (consp value) (null (cdr value)))
               (setq value (car value)))
             (let ((str (format nil "~a" value)))
               (cond ((numberp value) (oft " => ~:d." value))
                     ((> (length str) 40)
                      (oft " =>~%~a." str))
                     (t (oft " => ~a." str)))))
            (t (oft "."))))
    (cond
     ((not (symbolp x)) nil)
     ((get-doc-string x state)

; 1. For a symbol with regular ACL2 documentation, use :doc!.

      (oft "~%:doc! ")
      (let ((*acl2-unwind-protect-stack*
             (cons nil *acl2-unwind-protect-stack*)))
        (doc!-fn x state)))
     (t (let* ((tem nil)
               (found nil)
               (w (w state))
               (def (first-string (cltl-def-from-name x nil w))))
          (cond
           (def

; 2. Else, for an ACL2 function symbol with a DOC string, print it.

            (oft "~%(first-string (cltl-def-from-name '~a nil (w ~
                   *the-live-state*))) =>~%~a"
                 x def))
           (t
             
; 3. Else, for a symbol with some Common Lisp DOCUMENTATION, print
; that.

            (loop for type in types-of-documentation
                  when (setq tem (documentation x type)) do
                  (oft "~%(documentation '~a '~a) => ~% ~a"
                       type x tem)
                  (setq found t))
            (loop for type-pair in '((function saved-function)
                                     (variable saved-variable))
                  when (and (null (documentation x (car type-pair)))
                            (setq tem (documentation
                                       x
                                       (cadr type-pair))))
                  do
                  (oft "~%(documentation '~a '~a) => ~% ~a"
                       (cadr type-pair) x tem)
                  (setq found t))
            (cond ((null found)

; 4. Else, call DESCRIBE.

                   (pushnew x *undocumented-symbols*)

                   (oft "~%(describe '~a) =>~%" x)
                   (describe x))))))))))

(defmacro print-documentation (&rest r)

  "(PRINT-DOCUMENTATION x) prints out some things about the symbols in
  r, such as values and documentation."

  `(progn
     (oft "~%For further information about these ~a items, see ~
           below.~%"
          (length ',r))
     (loop for x in ',r as i from 1 do
           (oft "~% ~3d.~4t~a" i x))
     (terpri)
     (terpri)
     (mapc 'print-some-documentation ',r)
     (values)))

(defn1 watch-help ()

  "(WATCH-HELP) prints some documentation for WATCH, MEMOIZE, PROFILE,
  etc."

  (print-documentation
   watch
   watch-dump
   #+Clozure maybe-watch-dump
   watch-kill

   memoize-summary
   memoized-values
   *memoize-summary-order-list*
   *memoize-summary-limit*
   *memoize-summary-order-reversed*
   hons-acons-summary
   if-report

   #+Clozure bytes-allocated
   hons-calls
   hons-statistics
   hons-summary
   number-of-memoized-entries
   number-of-mht-calls
   print-call-stack
   symbol-name-order

   clear-memoize-call-array
   clear-memoize-tables
   clear-memoize-table

   profile
   profile-acl2
   profile-all
   profile-file

   memoize
   memoize-fn

   pons-summary
   print-call-stack

   unmemoize
   unmemoize-all
   unmemoize-profiled

   print-documentation
   compact-print-file
   compact-read-file
                  
   *watch-items*
   *watch-forms*
   *watch-file-form*
   *watch-string*
   *watch-file*
   *watch-startup-process*
   *watch-last-real-time*
   *watch-last-run-time*
   *watch-real-seconds-between-dumps*
   *watch-lock-ht*
   
   #+Clozure
   *watch-dog-process*
   #+Clozure
   watch-kill

   bytes-allocated
   bytes-allocated/call
   event-number
   execution-order
   hits/calls
   hons-calls
   pons-calls
   number-of-calls
   number-of-hits
   number-of-memoized-entries
   number-of-mht-calls
   symbol-name-order
   time-for-non-hits/call
   time/call
   total-time
  
   resize-memo
   resize-pons

   ))


;  USER MALEABLE WATCH FUNCTIONS AND VARIABLES

#+Clozure
(defun bytes-used ()
  (multiple-value-bind (dynamic static library frozen-size)
      (ccl::%usedbytes)
    (declare (ignorable library))
    (let* ((sum (+ dynamic static library frozen-size))
           (stack-size (ccl::%stack-space))
           (id (ccl::getpid))
           (rwx-size (rwx-size)))
      (declare (ignorable sum))
      (oft   

; (stat (proc-stat id))

;  ~%reserved:   ~15:d~ (ccl::%reservedbytes)

;  ~%library:   ~15:d  library

; ~%memfree:   ~15:d~29tfrom /proc/meminfo~
;  (* 1024 (meminfo "MemFree:")
; ~%swapfree:  ~15:d~29tfrom /proc/meminfo"
; (* 1024 (meminfo "SwapFree:")
; ~%rss:       ~15:d~29tfrom /proc/~a/stat - ram used~
;             (rss-size (* (getf stat :rss) ccl:*host-page-size*))
; ~%jobs:      ~15:d~29tfrom vmstat~" (number-procs-running)
; ~%load avg:  ~15f~29tone minute, from uptime" (load-average)

 "~%(bytes-used)~
  ~%dynamic:   ~15:d~29tlisp-heap-gc-threshold:    ~14:d~
  ~%stack:     ~15:d~29tmax-mem-usage:             ~14:d~
  ~%free:      ~15:d~29tgc-min-threshold:          ~14:d~
  ~%rwx:       ~15:d~29tfrom /proc/~a/maps - virtual used"

 dynamic               (ccl::lisp-heap-gc-threshold)
 stack-size            *max-mem-usage*
 (ccl::%freebytes)     *gc-min-threshold*
 rwx-size              id))))


(defmacro defw (fn &rest r)
  `(defn ,fn ()
     (let ((fn (string-capitalize (symbol-name ',fn))))
       ,@r)))

(defmacro oft-wrm (str &rest r)
  `(oft ,str (or *print-right-margin* 70) ,@r))

(defn1 date-string ()
  (multiple-value-bind (sec mi h d mo y)
      (decode-universal-time (get-universal-time))
    (let (m)
      (cond ((> h 12)
             (setq m " p.m.")
             (setq h (- h 12)))
            (t (setq m " a.m.")))
      (ofn "~2,d:~2,'0d:~2,'0d~a ~4d/~d/~d"
           h mi sec m y mo d))))

(defw time-of-last-watch-update
  (oft-wrm "~v<~a~;~a~>" fn (date-string)))

(defun watch-real-time ()
  (/ (- (get-internal-real-time) *watch-start-real-time*)
     *float-internal-time-units-per-second*))

(defun watch-run-time ()
  (/ (- (get-internal-run-time) *watch-start-run-time*)
     *float-internal-time-units-per-second*))

(defw hons-calls/sec-run-time
  (let* ((c *hons-call-counter*)
         (ans
          (cond ((eql c 0) "No hons calls yet.")
                (t (ofn "~,1e" (round (/ c (+ .000001
                                              (watch-run-time)))))))))
    (oft-wrm "~v<~a~;~a~>" fn ans)))

(defw pons-calls/sec-run-time
  (let* ((c *pons-call-counter*)
         (ans
          (cond ((eql c 0) "No pons calls yet.")
                (t (ofn "~,1e" (round (/ c (+ .000001
                                              (watch-run-time)))))))))
    (oft-wrm "~v<~a~;~a~>" fn ans)))

(defw pons-hits/calls
  (let* ((c *pons-call-counter*)
         (h (- c *pons-misses-counter*))
         (ans
          (cond ((eql c 0) "No pons calls yet.")
                (t (ofn "~,1e / ~,1e = ~,2f" h c (/ h c))))))
    (oft-wrm "~v<~a~;~a~>" fn ans)))

(defw hons-hits/calls
  (let* ((c *hons-call-counter*)
         (h (- c *hons-misses-counter*))
         (ans
          (cond ((eql c 0) "No hons calls yet.")
                (t (ofn "~,1e / ~,1e = ~,2f" h c (/ h c))))))
    (oft-wrm "~v<~a~;~a~>" fn ans)
    #+Clozure
    (oft-wrm "~%~v<Heap bytes allocated since watch start~;~,1e~>"
             (- (heap-bytes-allocated)
                *watch-start-heap-bytes-allocated*))))

#+Clozure
(defw gc-count ()
  (if *watch-file*
      (let ((h 0)
            (mi 0)
            (sec (floor (- (ccl::gctime) *watch-start-gc-time*)
                        internal-time-units-per-second)))
        (multiple-value-setq (mi sec) (floor sec 60))
        (multiple-value-setq (h mi) (floor mi 60))
        (oft-wrm "~v,20<~a~;~a.~;~a~;~2d:~2,'0d:~2,'0d.~>"
             fn
             (- (ccl::full-gccount) *watch-start-gc-count*)
             "Time in gc since watch start"
             h mi sec))))

(defun functions-that-may-be-too-fast-to-sensibly-profile ()
  (let ((ans (loop for fn in (profiled-functions)
                   when (< (total-time fn)
                           (* 1e-6 (number-of-calls fn)))
                   collect fn)))
    (when ans (oft "Too fast to sensibly profile?~%~a" ans))))

#+Clozure
(defw number-of-cpus-on-this-machine
  (let* ((ans (ofn "~:d" (ccl::cpu-count))))
    (oft-wrm "~v<~a~;~a~>" fn ans)))

(defw physical-memory-on-this-machine
  (let* ((ans (ofn "~:d" (physical-memory))))
    (oft-wrm "~v<~a~;~a bytes.~>" fn ans)))

#+Clozure
(defun watch-shell-command (&rest args)
  (let* ((as (args-spaced args))
         (output (csh as)))
    (oft-wrm "~v<~a~;~a~>" as output)))

(defw time-since-watch-start ()
  (if *watch-file*
      (multiple-value-bind (mi1 sec1)
          (floor (round (watch-real-time)) 60)
        (multiple-value-bind (h1 mi1) (floor mi1 60)
          (multiple-value-bind (mi2 sec2)
              (floor (round (watch-run-time)) 60)
            (multiple-value-bind (h2 mi2) (floor mi2 60)
              (oft-wrm "~v<Watch update ~a. ~
                ~;~a~;~2d:~2,'0d:~2,'0d.~;~a~;~2d:~2,'0d:~2,'0d.~>"
                       (watch-count) fn h1 mi1 sec1 "Run-time"
                   h2 mi2 sec2)))))))

(defw timer-function-name
  (let ((ans #+RDTSC "RDTSC"
             #-RDTSC "GET-INTERNAL-REAL-TIME."))
    (oft-wrm "~v<~a~;~a~>" fn ans)))

#+Clozure
(defun make-watchdog (duration)

;   Thanks to Gary Byers for this!

   (let* ((done (ccl:make-semaphore))
          (current ccl:*current-process*))
      (ccl::process-run-function "watchdog"
        (lambda ()
          (or (ccl:timed-wait-on-semaphore done duration)
              (ccl:process-interrupt
               current #'error "Time exceeded"))))
      done))

#+Clozure
(defun call-with-timeout (function duration)

  "(CALL-WITH-TIMEOUT function duration) calls FUNCTION on no
  arguments and returns its values unless more than DURATION seconds
  elapses before completion, in which case the FUNCTION computation is
  interrupted and calls ERROR.

  Thanks to Gary Byers for this beaut."

   (let* ((semaphore (make-watchdog duration)))
      (unwind-protect
          (funcall function)
        (ccl:signal-semaphore semaphore)))) 


;  COMPILER MACRO for IF

#+Clozure
(ccl::advise ccl::compile-named-function
             (when (and (consp ccl::arglist)
                        (consp (cdr ccl::arglist))
                        (consp (cddr ccl::arglist))
                        (symbolp (caddr ccl::arglist)))
               (clrhash *ignore-form-ht*)
               (setq *current-compiler-function*
                 (caddr ccl::arglist)))
             )

#+Clozure
(defun if-report (&optional fn stream)

  "(IF-REPORT) prints information about the execution of every branch
  of every IF, COND, AND, OR, CASE, WHEN, and UNLESS form of every
  memoized/profiled function that was memoized with :WATCH-IFS
  non-NIL.  (IF-REPORT fn) prints the same information, but only about
  the given function name, FN."

  (compute-calls-and-times)
  (let ((*print-level* 4)
        (*print-length* 4)
        (*print-pretty* t)
        last-fn n (ifs-found 0) (if-true 0) (if-false 0)
        (not-called 0)
        (called 0))
    (when (>= *if-counter* 0)
      (format stream "~2%Report on IF branches taken.")
      (let ((form-ar (make-array (the fixnum (1+ *if-counter*))
                                 :initial-element 0)))
        (declare (type (simple-array t (*)) form-ar))
        (maphash (lambda (k v) (declare (ignore k))
                   (when (or (null fn)
                             (eq (cadr v) fn))
                     (setf (aref form-ar (car v))
                           (cons (cddr v) (cadr v)))))
                 *form-ht*)
        (let ((top *if-counter*)
              ref)
          (declare (type fixnum top))
          (loop
           for i from 0 to top
           unless (eql 0 (setq ref (aref form-ar i)))
           do
           (let ((call (car ref))
                 (fn (cdr ref)))
             ;; ref has the form
             ;; (orig-call . function)
             (cond ((not (eq fn last-fn))
                    (setq n (number-of-calls fn))
                    (if (eq n 0)
                        (incf not-called)
                      (incf called))
                    (format stream "~2%~a was called ~a time~:P."
                         fn n)
                    (setq last-fn fn)))
             (cond
              ((> n 0)
               (incf ifs-found)
               (cond
                ((eql 0 (aref *if-true-array* i))
                 (cond
                  ((eql 0 (aref *if-false-array* i))
                   (format stream
                           "~%Neither branch of ~%~a~%was taken."
                           call))
                  (t (incf if-true)
                     (format
                      stream
                      "~%The true branch of ~%~a~%was not taken."
                      call))))
                ((eql 0 (aref *if-false-array* i))
                 (incf if-false)
                 (format stream
                         "~%The false branch of ~%~a~%was not taken."
                         call))
                (t (incf if-true) (incf if-false))))))))
        (format stream
                "~3%~:d ~10tnumber of functions called.~
              ~%~:d ~10tnumber of functions not called.~
              ~%~,2f% ~10tpercentage of functions called.~
              ~%~:d ~10tnumber of branches taken.~
              ~%~:d ~10tnumber of branches not taken.~
              ~%~,2f% ~10tpercentage of branches taken.
              ~%"
                called
                not-called
                (if (eql (+ called not-called) 0)
                    100
                  (* 100
                     (/ called
                        (float (+ called not-called)))))
                (+ if-true if-false)
                (- (* 2 ifs-found) (+ if-true if-false))
                (if (eql ifs-found 0)
                    100
                  (* 100
                     (float
                      (/ (+ if-true if-false)
                         (* 2 ifs-found))))))
        (format stream "~2%End of report on IF branches taken.~%")))))

#+Clozure
(defun dump-if-report (&optional (out "if-report.text"))
  (with-open-file (stream
                   out
                   :direction :output
                   :if-exists :supersede)
    (if-report stream))
  "if-report.text")

; The compiler macro for IF in the Clozure Common Lisp sources circa 2008:

; (define-compiler-macro if (&whole call test true &optional false
;                                   &environment env)
;   (multiple-value-bind (test test-win) (nx-transform test env)
;     (multiple-value-bind (true true-win) (nx-transform true env)
;       (multiple-value-bind (false false-win) (nx-transform false env)
;         (if (or (quoted-form-p test) (self-evaluating-p test))
;           (if (eval test)
;             true
;             false)
;           (if (or test-win true-win false-win)
;             `(if ,test ,true ,false)
;             call))))))

#+Clozure
(defun setup-smashed-if ()

; SETUP-SMASHED-IF creates COMPILER-MACRO for IF and OR via calls of
; DEFINE-COMPILER-MACRO, stores the compiler macros, and restores the
; previous values.

  (let ((ccl::*nx-safety* 0)
        (ccl::*nx-speed* 3))

; Warning: In Clozure, (DEFINE-COMPILER-MACRO IF ...) 'seems' to do
; nothing, not even cause an error, if SAFETY=3.

; According to the ANSI standard, one is not supposed to mess with a
; compiler macro for any symbol in the Common Lisp package.  So the
; following hacking of the compiler macros for IF and OR is very
; dubious.  But it seemed easier than writing a code walker for all of
; Common Lisp, with its 50 or so special forms.  Our purpose this is
; to help get statistical performance information, and that is all
; that justifies this dangerous behavior.

 (when (and *unsmashed-if* (null *smashed-if*))
      (unwind-protect
        (progn

(define-compiler-macro if
  (&whole call test true &optional false &environment env)
  (declare (ignorable env))
  (when *trace-if-compiler-macro*
    (prinl call test true false))
  (let
    ((ans
      (cond
       ((gethash call *form-ht*)

; According to the ANSI standard, there is no guarantee that a Common
; Lisp compiler macro ever gets called!  We hope and believe that
; Clozure's compiler arranges that every IF forms gets processed by
; the compiler macro for IF so that we can 'IF-fix' it, when
; approriate.  A form in *FORM-HT* is an IF form that has been
; 'IF-fixed': both its true and false branch first increment a special
; counter for the the number of times that each branch is taken.  We
; do not want to 'IF-fix' again a form that has already been
; 'IF-fixed'; if it has, the new compiler macro for IF returns it as
; the answer.  Any caller of this compiler macro for IF will know, by
; the ANSI rules for compiler macros, not to hope for any further
; improvement on the form.  If an ordinary macro (not a compiler
; macro) returned its input, macro expansion would enter an immediate
; infinite loop.  It is lucky for us that Clozure translates COND and
; CASE into IF via macros.

        call)
       (t

; Although it may seem very hard to tell, we do closely follow the
; code for the compiler-macro for IF from the Clozure compiler.  See
; that code below.

        (multiple-value-bind (test test-win)
            (ccl::nx-transform test env)
        (multiple-value-bind (true true-win)
            (ccl::nx-transform true env)
        (multiple-value-bind (false false-win)
            (ccl::nx-transform false env)
          (cond
           ((or (ccl::quoted-form-p test)
                (ccl::self-evaluating-p test))
            (when *trace-if-compiler-macro*
              (prinl "IF test already settled"))
            (if (eval test) true false))
           ((gethash call *ignore-form-ht*)

; Forms in *IGNORE-FORM-HT* are not to be 'fixed' because they are
; part of the profiling machinery.  See the definition of PROFILER-IF
; and those macros that use PROFILER-IF, such as PROFILER-AND,
; PROFILER-OR, PROFILER-WHEN, and PROFILER-UNLESS.

            (when *trace-if-compiler-macro*
              (prinl "ignore case" test true false))
            (cond ((or test-win true-win false-win)
                   (let ((new `(if ,test ,true ,false)))

; We make ignorability contagious.

                     (setf (gethash new *ignore-form-ht*) t)
                     new))
                  (t call)))
           (t         
            (incf *if-counter*)
            (when *trace-if-compiler-macro*
              (prinl "*IF-COUNTER* incremented"
                     call test true false))

; Our code here would be much simpler if in place of *IF-TRUE-ARRAY*
; and *IF-FALSE-ARRAY* we used two adjustable arrays and the function
; VECTOR-PUSH-EXTEND.  However, an adjustable array is not a
; SIMPLE-ARRAY, and so we possibly could lose efficiency, which we
; need when incrementing IF-branch counters.

            (when (>= *if-counter* (length *if-true-array*))
              (let ((ar (make-array
                         (+ (length *if-true-array*) 1000)
                         :element-type 'mfixnum
                         :initial-element -1)))
                (declare (type (simple-array mfixnum (*)) ar))
                (loop for i fixnum
                      below (length *if-true-array*)
                      do (setf (aref ar i)
                               (aref *if-true-array* i)))
                (setq *if-true-array* ar)))
            (when (>= *if-counter* (length *if-false-array*))
              (let ((ar (make-array (+ (length *if-false-array*)
                                       1000)
                                    :element-type 'mfixnum
                                    :initial-element -1)))
                (declare (type (simple-array mfixnum (*)) ar))
                (loop for i fixnum
                      below (length *if-false-array*)
                      do (setf (aref ar i)
                               (aref *if-false-array* i)))
                (setq *if-false-array* ar)))
            (setf (aref *if-true-array* *if-counter*) 0)
            (setf (aref *if-false-array* *if-counter*) 0)
            (let ((new-call `(if ,test
                                 (progn
                                   (very-very-unsafe-aref-incf
                                    *if-true-array*
                                    ,*if-counter*)
                                   ,true)
                               (progn
                                 (very-very-unsafe-aref-incf
                                  *if-false-array*
                                  ,*if-counter*)
                                 ,false))))

; The immediately preceding backquoted form is what we call the
; 'IF-fixing' of an expression.

              (when *trace-if-compiler-macro*
                (prinl new-call call))
              (setf (gethash new-call *form-ht*)
                    (list* *if-counter*
                           *current-compiler-function*
                           call))
              new-call))))))))))
    (when *trace-if-compiler-macro* (prinl ans))
    ans))
(setq *smashed-if* (compiler-macro-function 'if)))
(setf (compiler-macro-function 'if) *unsmashed-if*))

(unwind-protect
  (progn

; Apparently some times in CCL compilation, OR is not expanded to IF,
; so we force it here.

(define-compiler-macro or (&whole call &rest r &environment env)
  (declare (ignore r) (ignorable env))
  (cond ((null (cdr call)) nil)
        ((null (cddr call)) (cadr call))
        ((null (cdddr call))
         (cond ((atom (cadr call))
                `(if ,(cadr call)
                     ,(cadr call)
                   ,(caddr call)))
               (t (let ((v (gensym)))
                    `(let ((,v ,(cadr call)))
                       (if ,v ,v ,(caddr call)))))))
        (t (cond ((atom (cadr call))
                  `(if ,(cadr call) ,(cadr call) (or ,@(cddr call))))
                 (t (let ((v (gensym)))
                      `(let ((,v ,(cadr call)))
                         (if ,v ,v (or ,@(cddr call))))))))))

(setq *smashed-or* (compiler-macro-function 'or)))
(setf (compiler-macro-function 'or) *unsmashed-or*))

)))




(defun copy-hash-table
  (ht &key
      (new-test (hash-table-test ht))
      (new-size (hash-table-size ht))
      (new-rehash-size (hash-table-rehash-size ht))
      (new-rehash-threshold (hash-table-rehash-threshold ht))
      (new-weak (ccl::hash-table-weak-p ht))
      (new-shared (ccl::nhash.owner ht)))
  
  "(COPY-HASH-TABLE ht) takes a hash-table and returns a copy of it
  that may have some different attributes, depending upon the keyword
  values supplied for :NEW-SIZE and other keywords.  All the key/value
  pairs are copied.  Thus,
     (COPY-HASH-TABLE ht :NEW-SIZE 1000000)
  returns a copy of ht of size about 1000000."

;;    Some remarks by Gary Byers about how this function might
;;    be improved.

;;    There's probably a way to do this that preserves the
;;    EQness of the table.  A hash-table contains some
;;    general information and a "hash-table-vector", which
;;    contains a few words of other information and all of
;;    the key/value pairs; the HASH-TABLE itself is relatively
;;    small, but the underlying vector can get very large.
;;    (HASH-TABLE-SIZE is really a function of the size of
;;    the underlying hash-table-vector.)

;;    The hash-table-vector isn't really user-accessible;
;;    it's just an artifact of the implementation.  We could
;;    (if we remembered how ...) implement a RESIZE-HASH-TABLE
;;    function that created a new vector, hashed all of the
;;    key/value pairs from the old vector into the new one,
;;    and made the new vector the hash table's vector.  There
;;    are a few variants of that resizing function in the hash
;;    table code, but they're complicated and not user accesible:
;;    doing this in the real world is complicated by concurrency
;;    issues (if two threads call RESIZE-HASH-TABLE at about the
;;    same time, which one "wins" ?  Can you ensure that one of
;;    them wins and the hash table's in a consistent state afterwards,
;;    rather than partly believing that it's of the size specified
;;    by thread A and partly of that specified by thread B ? Etc.)

;;    The :LOCK-FREE argument to MAKE-HASH-TABLE is only important
;;    if :SHARED is true.  A hash-table can be:

;;    a) thread-private, if :SHARED is false
;;    b) shared, using locks if :SHARED is true and :LOCK-FREE is 
;;       false
;;    c) shared, without using locks if :SHARED is true and :LOCK-FREE
;;        is true.

;;    (c) is the default; it allows many threads to access the table
;;    concurrently without locking.  READ operations (GETHASH) are
;;    very cheap; write operations are more complicated and expensive
;;    (more expensive than in the locking case.)  In (a), everything's
;;    fairly cheap (no concurrency overhead), but that's only viable
;;    some of the time.

;;    If your COPY-HASH-TABLE function is sure that the source is
;;    of type (a) (... :shared nil ...), it doesn't have to worry
;;    about the :LOCK-FREE argument; you can make the new table's
;;    lock-freed-ness default to the old table's by adding a
;;    keyword arg:

;;    (new-lock-free (ccl::hash-lock-free-p ht))

;;    and passing NEW-LOCK-FREE's value as the value of :LOCK-FREE
;;    when creating the new table.


      (let ((new (make-hash-table
                  :test             new-test
                  :size             new-size
                  :rehash-size      new-rehash-size
                  :rehash-threshold new-rehash-threshold
                  #+Clozure
                  :weak
                  #+Clozure
                  new-weak
                  #+Clozure
                  :shared
                  #+Clozure
                  new-shared)))
        (maphash (lambda (k v) (setf (gethash k new) v)) ht)
        new))

;;   CSH

; 
; Here is a quite simple version of OPEN-GZIPPED-FILE that is fine to
; use in CCL for a few files, but perhaps not for thousands of files
; because FORK can take a serious amount of time for a big CCL job such
; as ACL2 since a copy is made by FORK of the entire job.
; 
; (defun open-gzipped-file (name)
;    (ccl::external-process-output-stream
;      (ccl::run-program "gunzip" (list "-c"  name)
;                        :output :stream :wait nil)))
; 
; To eliminate FORK as a source of such inefficiency, we provide the
; function CSH, which establishes a lasting subsidiary cshell process
; executing a 'read-and-execute one CSH line' loop.  It may be a good
; idea to call CSH very early, even before you need it, simply to get
; that process running when you can, i.e., when your image is small
; enough.

(defv *csh-process* nil

  "When not NIL, *CSH-PROCESS* has as its value the Lisp process
  object for an underlying csh process.")

(defv *csh-temporary-file-name* nil

  "When not NIL, *CSH-TEMPORARY-FILE-NAME* has as its value a stream
  via which an underlying csh process sends synchronizing info back to
  Lisp.")

#+Clozure
(defn1 csh-stop ()

  "(csh-stop) kills the subsidiary csh process if there is one."

  (ignore-errors
    (when (ccl::external-process-p *csh-process*)
      (ccl::signal-external-process *csh-process* 9)))
  (setq *csh-process* nil)
  (ignore-errors
    (when (and *csh-temporary-file-name*
               (probe-file *csh-temporary-file-name*))
      (delete-file *csh-temporary-file-name*)))
  (setq *csh-temporary-file-name* nil))

#+Clozure
(defv *csh-start-string*
  "set tm=`mktemp /tmp/acl2-csh-temp.XXXXXX`; echo $tm")
  
#+Clozure
(defn1 csh-start ()

  "(CSH-START) creates a subsidiary csh process.  CSH-START
  is called automatically by CSH."  

  (csh-stop)
  (setq *csh-process*
    (ccl::run-program "/bin/csh" (list "-f")
                      :input :stream
                      :output :stream
                      :wait nil))
  (let ((is (ccl::external-process-input-stream *csh-process*)))
    (our-syntax
     (write-line *csh-start-string* is)
     (finish-output is)
     (setq *csh-temporary-file-name*
       (read-line
        (ccl::external-process-output-stream *csh-process*)
        nil
        :eof)) ; wait
     (cond ((ignore-errors
              (probe-file *csh-temporary-file-name*))
            *csh-temporary-file-name*)
           (t (ofe "csh-start: failed."))))))
         
(defn1 args-spaced (args)
  (cond ((atom args) "")
        ((and (atom (cdr args))
              (stringp (car args)))
         (car args))
        (t (with-output-to-string (s)
             (loop for tail on args do
                   (our-syntax
                    (princ (car tail) s)
                    (when (cdr tail) (write-char #\Space s))))))))

#+Clozure
(defun csh (&rest args)

  "CSH is a raw Lisp function.  Called with no arguments, (CSH)
  returns a status report on a process, which is created if necessary,
  and which, once created, is the value of the Lisp variable
  *CSH-PROCESS*.

  On each call to CSH, one csh shell command is executed.  Unless for
  some unusual reason the process is killed, the same process executes
  all the commands.  That is, to repeat, a new process is not created
  for each command, but the same csh process is used repeatedly.  This
  may significantly reduce the copying overhead of a call to FORK to
  create a new process under a big Lisp job, as the ACL2 function
  SYSTEM-CALL does on each call.

  (CSH :STREAM arg1 ... argn) executes a single csh command, namely,
  the string obtained by placing spaces between the strings, symbols,
  or numbers arg1 ... argn.  A stream of the command's standard output
  is returned as the value of CSH.  For example,

     (CSH :STREAM '|gunzip -c foo.gz|)

  returns an open input stream that contains the ungzipped contents of
  the file 'foo.gz'.

  If arg1 is not :STREAM, (CSH arg1 ... argn) executes one csh command
  exactly as in the :STREAM case, namely, the string obtained by
  placing spaces between the strings, symbols, or numbers arg1
  ... argn.  But the standard output of the command is printed into a
  string, which is returned as the value of CSH.  If the last
  character of that output is a newline, it is not included in the
  string returned.

  The standard output from the command is diverted through a unique
  /tmp file, whose name is the value of the variable
  *CSH-TEMPORARY-FILE-NAME*.

  If the command sends any output to error output, a Lisp ERROR is
  caused and the error output of the command is printed to Lisp's
  *STANDARD-OUTPUT*.

  Each single csh command fed to CSH should be only one line long, and
  should not involve any of the fancier csh characters such *, ~, !,
  =, |, <, >, &, \, {, }, single quote, semicolon, period, question
  mark, parentheses, square brackets, double quote, and backquote.
  Stick to alphanumeric characters, space, and hyphen if possible.
  Create a separate, small .csh file to do anything fancy involving
  csh and those punctuation characters.  See abc-iprove.csh for one
  example, which involves creating a temp file."

  ;; CSH is at least as dangerous as SYSCALL, so would need a
  ;; trust-tag if made into an ACL2 command.

  ;; Implementation note: For CSH to work, the csh shell command
  ;; 'echo' with no arguments must 'flush' its output, in addition to
  ;; printing a newline, or in Lisp terminology, 'echo' must
  ;; 'finish-output'.  We believe 'echo' does that, but we have not
  ;; tracked down where it officially says so.  If 'echo' does not
  ;; flush its output, then the READ-CHAR below may wait forever.
  ;; Probably, adding a 'sync' command would guarantee the flushing.
   
  (with-standard-io-syntax
   (pushnew 'csh-stop ccl::*save-exit-functions*)
   (unless (ccl::external-process-p *csh-process*) (csh-start))
   (prog*
    ((p *csh-process*)
     (command (if (eq (car args) :stream) (cdr args) args))
     (is (ccl::external-process-input-stream p))
     (os (ccl::external-process-output-stream p))
     (x nil))

    (unless args
      (return
       (list :status (ccl::external-process-status p)
             :process p
             :input-stream (ccl::external-process-input-stream p)
             :output-stream (ccl::external-process-output-stream p)
             :temp-file-name *csh-temporary-file-name*)))
   
    ;; It seems so peculiar to 'print' to an 'input' here, but input
    ;; and output are opposite on the other end.

    (write-string (args-spaced command) is)
    (write-line " > $tm < /dev/null ; echo" is)
    (finish-output is)
    (setq x (read-char os nil :eof))
   
    ;; If necessary, READ-CHAR will wait.
   
    (unless (and (eql x #\Newline) (null (listen os)))
      (loop while (characterp x) do
            (write-char x *error-output*)
            (force-output *error-output*)
            (setq x (read-char-no-hang os nil :eof)))
      (csh-stop)
      (ofe "CSH: ~a." args))
    (return
     (cond
      ((eq :stream (car args)) (open *csh-temporary-file-name*))
      (t (with-open-file (o *csh-temporary-file-name*)
           (with-output-to-string
             (s)
             (loop while
                   (and (not (eq :eof (setq x (read-char
                                               o nil :eof))))
                        (or (not (eql x #\Newline))
                            (not (eq :eof (peek-char
                                           nil o nil :eof)))))
                   do (write-char x s))))))))))

(defv *sh-process* nil

  "When not NIL, *SH-PROCESS* has as its value the Lisp process
  object for an underlying sh process.")

(defv *sh-temporary-file-name* nil

  "When not NIL, *SH-TEMPORARY-FILE-NAME* has as it value a stream
  via which an underlying sh process sends synchronizing info back to
  Lisp.")

#+Clozure
(defn1 sh-stop ()

  "(sh-stop) kills the subsidiary sh process if there is one."

  (ignore-errors
    (when (ccl::external-process-p *sh-process*)
      (ccl::signal-external-process *sh-process* 9)))
  (setq *sh-process* nil)
  (ignore-errors
    (when (and *sh-temporary-file-name*
               (probe-file *sh-temporary-file-name*))
      (delete-file *sh-temporary-file-name*)))
  (setq *sh-temporary-file-name* nil))

#+Clozure
(defv *sh-start-string*
  "tm=`mktemp /tmp/acl2-sh-temp.XXXXXX`; echo $tm")
  
#+Clozure
(defn1 sh-start ()

  "(SH-START) creates a subsidiary sh process.  SH-START
  is called automatically by SH."  

  (sh-stop)
  (setq *sh-process*
    (ccl::run-program "/bin/sh" nil
                      :input :stream
                      :output :stream
                      :wait nil))
  (let ((is (ccl::external-process-input-stream *sh-process*)))
    (our-syntax
     (write-line *sh-start-string* is)
     (finish-output is)
     (setq *sh-temporary-file-name*
       (read-line
        (ccl::external-process-output-stream *sh-process*)
        nil
        :eof)) ; wait
     (cond ((probe-file *sh-temporary-file-name*)
            *sh-temporary-file-name*)
           (t (ofe "sh-start: failed."))))))

#+Clozure
(defun sh (&rest args)

  "SH is a raw Lisp function.  (SH) returns a status report on a lower
  'sh' shell process, which is created if necessary, and which, once
  created, is the value of the Lisp variable *SH-PROCESS*.

  On each call to SH, one sh shell command is executed.  The same sh
  process executes all the commands.  That is, a new process is not
  created for each command, but the same sh process is used
  repeatedly.  This may significantly reduce the copying overhead
  incurred by a call to FORK to create a new process under a big Lisp
  job, as the ACL2 function SYSTEM-CALL might on each call.

  (SH :STREAM arg1 ... argn) executes a single sh command, namely,
  the string obtained by placing spaces between the strings, symbols,
  or numbers arg1 ... argn.  A stream of the command's standard output
  is returned as the value of SH.  For example,

     (SH :STREAM '|gunzip -c foo.gz|)

  returns an open input stream that contains the ungzipped contents of
  the file 'foo.gz'.

  If arg1 is not :STREAM, (SH arg1 ... argn) executes one sh command
  exactly as in the :STREAM case, namely, the string obtained by
  placing spaces between the strings, symbols, or numbers arg1
  ... argn.  But the standard output of the command is printed into a
  string, which is returned as the value of SH.  If the last character
  of that output is a newline, it is not included in the string
  returned.

  The standard output from the command is diverted through a unique
  /tmp file, whose name is the value of the variable
  *SH-TEMPORARY-FILE-NAME*.

  If the command sends any output to error output, a Lisp ERROR is
  caused and the error output of the command is printed to Lisp's
  *STANDARD-OUTPUT*.

  SH is almost identical to CSH.

  For the best of hacking luck, each single SH command fed to SH
  should be only one line long, and should not involve any of the
  fancier SH characters such *, ~, !, =, |, <, >, &, \, {, }, single
  quote, semicolon, period, question mark, parentheses, square
  brackets, double quote, and backquote.  Stick to alphanumeric
  characters, space, and hyphen if possible.  Create a separate, small
  .sh file to do anything fancy involving sh and such punctuation
  characters.  See abc-iprove.csh for one example, which involves
  creating a temp file."

  (with-standard-io-syntax
   (pushnew 'sh-stop ccl::*save-exit-functions*)
   (unless (ccl::external-process-p *sh-process*) (sh-start))
   (prog*
    ((p *sh-process*)
     (command (if (eq (car args) :stream) (cdr args) args))
     (is (ccl::external-process-input-stream p))
     (os (ccl::external-process-output-stream p))
     (x nil))

    (unless args
      (return
       (list :status (ccl::external-process-status p)
             :process p
             :input-stream (ccl::external-process-input-stream p)
             :output-stream (ccl::external-process-output-stream p)
             :temp-file-name *sh-temporary-file-name*)))
   
    ;; It seems so peculiar to 'print' to an 'input' here, but input
    ;; and output are opposite on the other end.

    (write-string (args-spaced command) is)
    (write-line " > $tm < /dev/null ; echo" is)
    (finish-output is)
    (setq x (read-char os nil :eof))
   
    ;; If necessary, READ-CHAR will wait.
   
    (unless (and (eql x #\Newline) (null (listen os)))
      (loop while (characterp x) do
            (write-char x *error-output*)
            (force-output *error-output*)
            (setq x (read-char-no-hang os nil :eof)))
      (sh-stop)
      (ofe "SH: ~a." args))
    (return
     (cond
      ((eq :stream (car args))
       (open *sh-temporary-file-name*))
      (t (with-open-file
           (o *sh-temporary-file-name*)
           (with-output-to-string
             (s)
             (loop while
                   (and (not (eq :eof (setq x (read-char
                                               o nil :eof))))
                        (or (not (eql x #\Newline))
                            (not (eq :eof (peek-char
                                           nil o nil :eof)))))
                   do (write-char x s))))))))))

                            
; A SOMETIMES FASTER VERSION OF THE COMMON LISP CASE FUNCTION

#+Clozure
(let ((ccl::*warn-if-redefine-kernel* nil))

#+Clozure
(defmacro case (key &body forms)

  ; A modification of the CCL DEFMACRO for CASE.

  "CASE Keyform {({(Key*) | Key} Form*)}* Evaluates the Forms in the
  first clause with a Key EQL to the value of Keyform. If a singleton
  key is T then the clause is a default clause."

  (multiple-value-bind (less-than-or-equal n greater-than)
    (splitable-case forms)
    (cond
     (less-than-or-equal
      (let ((key-var (gensym)))
        `(let ((,key-var ,key))
           (cond ((not (typep ,key-var 'fixnum)) nil)
                 ((< (the fixnum ,key-var) ,n)
                  (fixnum-case ,key-var ,@less-than-or-equal))
                 (t (fixnum-case ,key-var ,@greater-than))))))
     (t (let ((key-var (gensym)))
          `(let ((,key-var ,key))
             (declare (ignorable ,key-var))
             (cond ,@(ccl::case-aux forms key-var nil nil)))))))))

#+Clozure
(defmacro fixnum-case (key &body forms)
  ; For use only when key is a symbol known to hold a fixum.
  (multiple-value-bind (less-than-or-equal n greater-than)
    (splitable-case forms)
    (cond (less-than-or-equal
           `(cond ((< (the fixnum ,key) ,n)
                   (fixnum-case ,key ,@less-than-or-equal))
                  (t (fixnum-case ,key ,@greater-than))))
          (t (let ((key-var (gensym)))
               `(let ((,key-var (the fixnum ,key)))
                  (declare (ignorable ,key-var) (fixnum ,key-var))
                  (cond ,@(ccl::case-aux forms key-var nil nil))))))))

#+Clozure
(defun splitable-case (forms)
  (let ((l (length forms)))
    (cond
     ((and (> l 8)
           (loop for x in forms
                 always (and (consp x) (typep (car x) 'fixnum))))
      (let* ((c (sort (copy-list forms) #'< :key #'car))
             (h (floor l 2))
             (s (car (nth h c))))
        (loop for tail on c
              when (and (cdr tail) (eql (car tail) (cadr tail)))
              do (error "CASE: duplicate-keys: ~a." (car tail)))
        (values
         (loop for x in forms when (< (car x) s) collect x)
         s
         (loop for x in forms when (>= (car x) s) collect x)))))))

(defmacro with-lower-overhead (&rest r)
  `(let ((*record-bytes* nil)
         (*record-calls* nil)
         (*record-hits* nil)
         (*record-hons-calls* nil)
         (*record-mht-calls* nil)
         (*record-pons-calls* nil)
         (*record-time* nil)
         (*hons-report-discipline-failure* nil))
     (globlet ((*count-pons-calls* nil))
              ,@ r)))

(defn lower-overhead ()
  ;; Doesn't help much.
  (setq *record-bytes* nil)
  (setq *record-calls* nil)
  (setq *record-hits* nil)
  (setq *record-hons-calls* nil)
  (setq *record-mht-calls* nil)
  (setq *record-pons-calls* nil)
  (setq *record-time* nil)
  (setq *hons-report-discipline-failure* nil)
  (setq *count-pons-calls* nil))

(let ((state *the-live-state*))
  (f-put-global 'doc-prefix " " state))

(defun our-gctime ()
  (ccl::timeval->microseconds ccl::*total-gc-microseconds*))

(defun update-memo-entry-for-attachments (fns entry wrld)

; We return (mv changed-p new-entry), where if changed-p is not t or nil then
; it is a function symbol whose attachment has changed, which requires clearing
; of the corresponding memo table.

  (let* ((ext-anc-attachments
          (access memoize-info-ht-entry entry :ext-anc-attachments))
         (valid-p
          (if (eq fns :clear)
              :clear
            (or (null ext-anc-attachments)
                (ext-anc-attachments-valid-p fns ext-anc-attachments wrld t)))))
    (cond ((eq valid-p t) (mv nil entry))
          (t
           (mv (if (eq valid-p nil) t valid-p)
               (change memoize-info-ht-entry entry
                       :ext-anc-attachments
                       (extended-ancestors (access memoize-info-ht-entry entry
                                                   :fn)
                                           wrld)))))))

(defun update-memo-entries-for-attachments (fns wrld state)
  (let ((ctx 'top-level)
        (fns (if (eq fns :clear)
                 fns
               (strict-merge-sort-symbol-<
                (loop for fn in fns
                      collect (canonical-sibling fn wrld))))))
    (when (eq fns :clear)
      (observation ctx
                   "Memoization tables for functions memoized with :AOKP T ~
                    are being cleared."))
    (when fns ; optimization
      (maphash (lambda (k entry)
                 (when (symbolp k)
                   (mv-let (changedp new-entry)
                           (update-memo-entry-for-attachments fns entry wrld)
                           (when changedp
                             (when (not (or (eq changedp t)
                                            (eq fns :clear)))
                               (observation ctx
                                            "Memoization table for function ~x0 ~
                                           is being cleared because ~
                                           attachment to function ~x1 has ~
                                           changed."
                                            k changedp)
                               (clear-one-memo-and-pons-hash entry))
                             (setf (gethash k *memoize-info-ht*)
                                   new-entry)))))
               *memoize-info-ht*))))
