; ACL2 Version 6.1 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2013, Regents of the University of Texas

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
; Austin, TX 78701 U.S.A.

; memoize-raw.lisp -- Raw lisp definitions for memoization functions, only to
; be included in the experimental HONS version of ACL2.

; The original version of this file was contributed by Bob Boyer and
; Warren A. Hunt, Jr.  The design of this system of Hash CONS,
; function memoization, and fast association lists (applicative hash
; tables) was initially implemented by Boyer and Hunt.

(in-package "ACL2")

; [Jared] notes about cleanup...
;
;   - Added lots of comments that shouldn't change anything


(eval-when
 (:execute :compile-toplevel :load-toplevel)

 #-hons
 ;; [Jared]: Is there a real reason that memoization needs hons?
 (error "memoize-raw.lisp should only be included when #+hons is set.")

 ;; [Jared]: Below are the old comments about :parallel.  This feature hasn't
 ;; been enabled for a long time as far as I can tell.  We probably need to
 ;; revisit everything related to #+parallel.  We probably also want to use the
 ;; #+acl2-par feature instead of #+parallel, for eventual compatibility with
 ;; ACL2(p).  It appears that #+parallel is only used in this file.

 ;; (pushnew :parallel *features*) causes a lot of locking that is of no value
 ;; in a sequentially executing system.  We have attempted to make honsing,
 ;; memoizing, and Emod-compilation 'thread safe', whatever in hell that means,
 ;; but we have no idea what we are really doing and are simply coding based
 ;; upon what we feel is intuitive common sense.  Very subtle stuff.



 ;; One may comment out the following PUSHNEW and rebuild to get profiling
 ;; times not based upon the curious and wondrous RDTSC instruction of some x86
 ;; processors.  On a machine with several cores, the RDTSC values returned by
 ;; different cores may be slightly different, which could lead one into such
 ;; nonsense as instructions apparently executing in negative time, when timing
 ;; starts on one core and finishes on another.  To some extent we ignore such
 ;; RDTSC nonsense, but we still can report mysterious results since we have no
 ;; clue about which core we are running on in CCL.

  #+Clozure
  (when (fboundp 'ccl::rdtsc) (pushnew :RDTSC *features*))

  )




; MFIXNUM
;
; We use the type mfixnum for counting things that are best counted in the
; trillions or more.  Mfixnums happen to coincide with regular fixnums on
; 64-bit CCL and SBCL.

(defconstant most-positive-mfixnum (1- (expt 2 60)))

(deftype mfixnum ()
  `(integer ,(- -1 most-positive-mfixnum)
            ,most-positive-mfixnum))








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



(defmacro defn1 (f a &rest r)
  (when (intersection a lambda-list-keywords)
    (error "DEFN1: ** In the defintion of ~s, the argument list ~s ~
            contains a member of lambda-list-keywords so do not ~
            use defn1."
           f a))
  `(progn
     (setf (gethash ',f *number-of-arguments-and-values-ht*)
           (cons ,(length a) 1))
     (declaim (ftype (function ,(make-list (len a) :initial-element t)
                               (values t))
                     ,f))
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
     (declaim (ftype (function ,(make-list (len a) :initial-element t)
                               (values t)) ,f))
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
     (declaim (ftype (function ,(make-list (len a) :initial-element t)
                               (values t t)) ,f))
     (defun ,f ,a (declare (xargs :guard t)) ,@r)))





; TIMING UTILITIES

; *float-ticks/second* is set correctly by HONS-INIT.

(defg *float-ticks/second* 1.0)

(defg *float-internal-units-per-second*
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
         `(if (>= 0 (the mfixnum ,inc))
                   nil
                   (safe-incf-aux ,x ,inc ,where)))
        (t (let ((incv (make-symbol "INCV")))
             `(let ((,incv (the mfixnum ,inc)))
                (declare (type mfixnum ,incv))
                (if (>= 0 ,incv)
                         nil
                         (safe-incf-aux ,x ,incv ,where)))))))

(defn1 safe-incf-aux-error (x inc where)
  (error "~%; SAFE-INCF-AUX: ** Error: ~a."
         (list :x x :inc inc :where where)))

(defmacro safe-incf-aux (x inc where)
  (cond
   ((not (or (symbolp inc)
             (and (< inc most-positive-mfixnum)
                           (> inc 0))))
    (safe-incf-aux-error x inc where))
   ((and (true-listp x)
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
           (cond ((<= ,v (the mfixnum
                                    (- most-positive-mfixnum
                                       (the mfixnum ,inc))))
                       (setf (the mfixnum ,x)
                             (the mfixnum (+ ,v (the mfixnum ,inc))))
                       nil)
                      (t (safe-incf-aux-error ',x ',inc
                                              ',where))))))))



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

(defn1 memoize-fn-suffix (str sym)
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

(save-def
(defn1 physical-memory () (meminfo "MemTotal:"))
)

(save-def
(defn1 swap-total ()
  (meminfo "SwapTotal:"))
)


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



; HONS VARIABLES, MACROS, AND DATA STRUCTURES

; Gary Byers recalls Lisp folklore that alists are faster than hash
; tables up to length 18.

(defconstant *start-car-ht-size*            18)

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




(declaim (type mfixnum *pons-call-counter* *pons-misses-counter*))

; Definition. ***** means 'Do not call this function unless you are
; sure that a superior caller in this thread has the lock on
; *HONS-STR-HT*.

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

(defn1 mis-ordered-commutative-args (x y)
  #-Clozure
  ;; [Jared]: Lisps besides Clozure don't have static conses so we can't
  ;; reorder arguments based on their indices.  It's possible we could do
  ;; something like sort based on address, maybe, but I haven't thought about
  ;; it.
  (declare (ignore x y))
  #-Clozure
  nil
  #+Clozure
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







;;;;;;;;;; MEMOIZE ;;;;;;;;;; MEMOIZE ;;;;;;;;;; MEMOIZE ;;;;;;;;;;
;;;;;;;;;; MEMOIZE ;;;;;;;;;; MEMOIZE ;;;;;;;;;; MEMOIZE ;;;;;;;;;;

;  MEMOIZE VARIABLES, MACROS, AND DATA STRUCTURES

(defv *never-profile-ht*
  (let ((h (make-hash-table :test 'eq)))
    (loop for x in
          '(bytes-used
            memoize-summary
            memoize-summary-after-compute-calls-and-times
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
            profile-fn
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
            reverse-strip-cars
            reverse-strip-cdrs
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
            terpri
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

(defg *caller* (* *ma-initial-max-symbol-to-fixnum* *2max-memoize-fns*)
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
            reverse-strip-cars
            reverse-strip-cdrs
            short-symbol-name
            hons-calls
            memoize-condition
            1-way-unify-top
            absorb-frame
            access-command-tuple-number
            access-event-tuple-depth
            access-event-tuple-form
            access-event-tuple-number
            accumulate-ttree-and-step-limit-into-state
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
            cons-term1
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
;;            csh
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
            tau-auto-modep
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
            print-hint-events-summary
            print-prompt
            print-rational-as-decimal
            print-redefinition-warning
            print-rules-and-hint-events-summary
            print-runes-summary
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
            quote-listp
            quotep
            qzget-sign-abs
            raw-mode-p
            read-acl2-oracle
            read-acl2-oracle@par
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
            step-limit
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
            memoize-fn-suffix
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
            time-limit5-reached-p
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
            untrans-table
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
        #-Clozure
        ((multiple-value-bind
          (sym foundp)
          (find-symbol (symbol-name fn) *main-lisp-package*)
          (declare (ignore sym))
          foundp)
; Avoid "cannot be printed readably" error in SBCL and perhaps other Lisps (but
; since we haven't had this problem in CCL, we exclude the test for CCL).
         (ofn "~%;~10tsymbol-name is found in *main-lisp-package*."))
        #+Clozure
        ((ccl::%advised-p fn)
         (ofn "~%;10tadvised, and it will so continue."))
        ((member fn (eval '(trace)))
         (ofn "~%;~10ta member of (trace), and it will so ~
               continue."))
        ((and (fboundp 'old-trace)
              (member fn (eval '(old-trace))))
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
        ((getprop fn 'constrainedp nil 'current-acl2-world
                  (w *the-live-state*))
         "constrained.")
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

; Essay on Memoization Involving Stobjs

; We allow memoization of functions that take user-defined stobjs (not state)
; as arguments but do not return stobjs.  The key is the use of memoize-flush
; to "forget" all that was remembered for certain functions that use certain
; stobjs.  We must keep memoize-flush very fast in execution so as not to slow
; down stobj update or resize operations in general.  Indeed, memoize-flush may
; (according to tests run) incur essentially no cost (after Version_4.3) as
; long as no functions with stobj arguments are actually memoized.

; The following example shows why we disallow memoization of functions that
; return stobjs.  First, redefine memoize-table-chk by eliminating the branch
; that causes an error in the presence of stobj names in stobjs-out.  Then
; start up ACL2 and submit the forms below.  The problem is that we do not
; inhibit storing a result in the case that the stobj has changed from the time
; the function was called to the time the result is to be stored.

; (defstobj st fld)
; (defun foo (st)
;   (declare (xargs :stobjs st))
;   (let ((st (update-fld (cons (fld st) (fld st)) st)))
;     (mv (fld st) st)))
; (foo st) ; updates (fld st), returns (mv (nil) st)
; (memoize 'foo)
; (foo st) ; updates (fld st), returns (mv ((nil) nil) st)
; (foo st) ; no longer updates (fld st)
; (foo st) ; no longer updates (fld st)
; (fld st) ; still ((nil . nil). (nil . nil))

(defun memoize-flush1 (lst)

; Experiments showed that when lst is nil, it is faster to call this function
; then to inline its code into the body of memoize-flush.

; We "forget" all memoized values by clearing all necessary memoize tables; see
; the comment about memoize-flush in memoize-fn.  We leave the pons table alone
; in order to keep this flushing operation as fast as possible.  Note that the
; pons table merely stores keys to be looked up in the memo table, so there is
; no soundness issue, and in fact those pons table entries might remain useful;
; the cost is the space taken up by the pons tables.

  (loop for sym in lst do
        (when (boundp (the symbol sym)) ; Is this test needed?
          (let ((old (symbol-value (the symbol sym))))
            (unless (or (null old) (empty-ht-p old))
              (setf (symbol-value (the symbol sym)) nil))))))

(defmacro memoize-flush (st)

; See memoize-flush1 for a relevant discussion.

  (let ((s (st-lst st)))
    `(when ,s ; optimization
       (memoize-flush1 ,s))))

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
  (declare (ignorable init-size))

; This is similar to make-initial-memoize-table, but for the pons table.

  (let* ((max-sizes (gethash fn *memo-max-sizes*))
         (size-to-use
          (if (not max-sizes)
              ;; We've never cleared this pons table before, so we don't have
              ;; anything to go on besides what the user says.  Now, this is
              ;; subtle.  Originally I just returned init-size here, i.e., "do
              ;; what the user says."  But while this makes sense for the memo
              ;; table, it doesn't necessarily make much sense for the pons
              ;; table.  In particular, we can sometimes avoid ponsing by using
              ;; our static-cons-index-hashing scheme.
              ;;
              ;; In some sense it would probably be good to give the user
              ;; explicit control over the pons table size.  But for now, the
              ;; main use of our memoize table size controls is to set things
              ;; up for big BDD/AIG/SEXPR operations where we've got honsed
              ;; data.  So, I'm going to just use 60 here, and say that the
              ;; memo-table-init-size only affects the memoize table and not
              ;; the pons table.
              60
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

#+Clozure
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

#+Clozure
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


(defn1 memoize-eval-compile (def)
  (unless (and (consp def)
               (eq 'defun (car def))
               (consp (cdr def))
               (symbolp (cadr def)))
    (ofe "MEMOIZE-EVAL-COMPILE:  Bad input:~%~s." def))
  (compile (eval def))
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
  (intern (ofn "HONS-S-~s,~s"
               (package-name (symbol-package st))
               (symbol-name st))
          (find-package "ACL2_INVISIBLE")))

(defn1 dcls (l)
     (loop for dec in l nconc
           (let ((temp
                  (if (consp dec)
                      (loop for d in (cdr dec) nconc
                            (if (and (consp d) (eq (car d) 'ignore))
                                nil
                              (cons d nil))))))
             (if temp (cons (cons 'declare temp) nil)))))


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

(defg *memoize-fn-signature-error*
  "
  Memoize-fn: could not determine a signature for ~a.~%~
  To assert the (number-of-inputs . number-of-outputs)~%~
  signature of ~:*~a, put a cons of two numbers in the hash-table ~%~
  *NUMBER-OF-ARGUMENTS-AND-VALUES-HT* under ~:*~a.  For example, ~%~
  do (setf (gethash '~:*~a *NUMBER-OF-ARGUMENTS-AND-VALUES-HT*)
         '(3 . 1))")

(defg *sort-to-from-by-calls* nil)

(defvar *memoize-use-attachment-warning-p* t)

(defun memoize-use-attachment-warning (fn at-fn)
  (when *memoize-use-attachment-warning-p*
    (let ((state *the-live-state*))
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
                                     memoized function ~x0, which may have ~
                                     been computed using attachments"
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

  If the FORGET parameter is not NIL, the pons and memo tables of FN
  are discarded at the end of every outermost call of FN."

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

  #-hons
  (return-from memoize-fn
               (progn (when (not (zerop *ld-level*))
                        (warning$ 'memoize nil
                                  "No change for function ~x0: Memoization ~
                                   requests are ignored in this ACL2 ~
                                   executable because it is not hons-enabled."
                                  fn))
                      fn))

  (when (equal condition *nil*)
    (setq condition nil))

  (unwind-mch-lock
   (maybe-untrace! fn) ; See the comment about Memoization in trace$-def.
   (with-warnings-suppressed

; Big old bunch of error checking...


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

    ;; Doesn't this get checked below?  See the lambda-list intersection thing
    #+Clozure
    (when (multiple-value-bind (req opt restp keys)
              (ccl::function-args (symbol-function fn))
            (or restp
                keys
                (not (integerp req))
                (not (eql opt 0))))
      (ofe "Memoize-fn: ~a has non-simple arguments." fn))


    (let*
      ((cl-defun
        ;; Magic code to try to look up the Common Lisp definition for this function.
        (cond ((eq cl-defun :default)
               (if inline
                   (cond

                    ((not (fboundp fn))
                     (ofe "MEMOIZE-FN: ** ~a is undefined."
                          fn))

                    ((let ((def (cltl-def-from-name fn wrld)))
                       (cond (def (assert (eq (car def) 'defun))
                                  (cdr def)))))

                    ((multiple-value-bind
                      (def flg)
                      (our-function-lambda-expression fn)
                      (cond (flg (cdr def))
                            (def (assert (eq (car def)
                                             'lambda))
                                 def))))

                    (t
                     #+Clozure
                     (unless (and ccl::*save-source-locations*
                                  ccl::*fasl-save-definitions*)
                       (ofd "~&; Check the settings of ~
                             CCL::*SAVE-SOURCE-LOCATIONS* and ~
                             CCL::*FASL-SAVE-DEFINITIONS*."))
                     (ofe "MEMOIZE-FN: ** Cannot find a definition for ~a via ~
                           ACL2 or OUR-FUNCTION-LAMBDA-EXPRESSION."
                          fn))) nil))
              ((eq (car cl-defun) 'defun)
               (cdr cl-defun))
              (t cl-defun)))

       (formals
        ;; Magic code to try to figure out what the formals of the function are.
        ;; For ACL2 functions this works via looking up the 'formals property
        ;; For raw Lips functions we may be able to extract the formals from the
        ;; cl-defun above, or we may generate a list (X1 ... XN) in some cases?
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

       (stobjs-in
        ;; Either the ACL2 stobjs-in property or (T T T T ...) for the number
        ;; of formals that we inferred the function has.
        (if (eq stobjs-in :default)
            (let ((s (getprop fn 'stobjs-in t 'current-acl2-world
                              wrld)))
              (if (eq s t) (make-list (len formals)) s))
          stobjs-in))

       (stobjs-out
        ;; Either the ACL2 stobjs-out property or (T T T T ...) for the number
        ;; of return values that we inferred the function has.
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

      ;; Not sure why this check is necessary or useful
      (unless (and (symbol-listp formals)
                   (no-duplicatesp formals)
                   (loop for x in formals never (constantp x)))
        (ofe "Memoize-fn: FORMALS, ~a, must be a true list of ~
              distinct, nonconstant symbols."
             formals))

      (when (intersection lambda-list-keywords formals)
        (ofe "Memoize-fn: FORMALS, ~a, may not intersect ~
              LAMBDA-LIST-KEYWORDS."))

      ;; Don't memoize functions involving state.  Fair enough.
      ;; Can you memoize functions with other stobjs??
      (when (and condition (or (member 'state stobjs-in)
                               (member 'state stobjs-out)))
        (ofe "Memoize-fn:  ~s uses STATE." fn))


      (let*
        ((fnn (symbol-to-fixnum-create fn))  ; performance counting; see memoize-call-array
         (2mfnn (* *2max-memoize-fns* fnn))  ; performance counting; see memoize-call-array

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
                 ;; Bizarre thing where the condition can be just the name of an ACL2 function,
                 ;; see the documentation above
                 (car (last (cltl-def-from-name condition wrld))))
                (t condition)))

         (dcls (dcls (cddr (butlast cl-defun))))
         (start-time (let ((v (hons-gentemp
                               (memoize-fn-suffix "START-TIME-" fn))))
                       (eval `(prog1 (defg ,v -1)
                                (declaim (type integer ,v))))))
         (tablename
          ;; Submits the defg form and returns the crazy name that gets generated.
          (eval `(defg
                   ,(hons-gentemp (memoize-fn-suffix "MEMOIZE-HT-FOR-" fn))
                   nil)))
         (ponstablename
          ;; Submits the defg form and returns the crazy name that gets generated.
          (eval `(defg
                   ,(hons-gentemp (memoize-fn-suffix "PONS-HT-FOR-" fn))
                   nil)))

         (localtablename (make-symbol "TABLENAME"))
         (localponstablename (make-symbol "PONSTABLENAME"))
         (sts

; Here we support memoize-flush, which keeps memoize tables coherent in the
; presence of user-defined stobjs.  For each (user-level) stobj input name, st,
; we collect up the variable (st-lst st), whose value is the list of names of
; memoize tables that need to be cleared whenever that stobj changes.  Below,
; we will push the present function's table name onto each of these lists.

; Ultimately, stobj updates are made by stobj primitives.  After the stobj
; primitive for stobj st makes an update, the memo table for a function f
; taking st as its nth argument (say) is no longer valid for saved calls of f
; for which the nth argument is st.  Because of congruent stobjs and abstract
; stobjs, that nth argument need not be st, and we believe that in principle,
; we could restrict flushing of memo table entries of f to those whose nth
; argument is eq to the stobj being updated (whether st, congruent to st, or an
; abstract stobj whose concrete stobj is congruent to st).  But for now we take
; the coarser approach, which has the advantage that we simply throw away the
; memo-table for f when flushing, leaving it to be garbage collected; see
; memoize-flush1.

          (and condition ; else no memo table usage, so skip flushing
               (remove-duplicates-eq
                (loop for st in (union stobjs-in stobjs-out)
                      when st
                      collect
                      (assert$
                       (not (and condition
                                 (eq st 'state))) ; see memoize-table-chk
                       (st-lst (congruent-stobj-rep

; In the case that st is an abstract stobj, we replace it with the
; corresponding concrete stobj before getting a canonical (congruent)
; representative; see the rather long comment just above that mentions
; "abstract" stobjs.

                                (or (concrete-stobj st wrld)
                                    st)
                                wrld)))))))

         ;; Number of arguments.  Specials only matter for common lisp functions, see the notes above in memoize-fn.
         ;; Basically if the function reads from specials we want to count them as args.
         (nra (+ (len formals) (len specials)))

         def
         success)
        (let*
          ((mf-trace-exit
            ;; Ignore this, just some kind of tracing...
            (and trace `((mf-trace-exit ',fn ,(length stobjs-out)
                                        ,*mf-ans*))))
           (mf-record-mht
            ;; performance counting, see memoize-call-array
            (and *record-mht-calls*
                 `((safe-incf (aref ,*mf-ma* ,2mfnn) 1 ,fn))))
           (mf-record-hit
            ;; performance counting, see memoize-call-array
            (and *record-hits* condition-body
                 `((safe-incf (aref ,*mf-ma*
                                    ,(+ 2mfnn *ma-hits-index*))
                              1 ,fn))))
           (lookup-marker (cons :lookup fn))



           (body3
            ;; Main part of the new function definition...

            `(let (,*mf-ans* ,*mf-args* ,*mf-ans-p*)
               (declare (ignorable ,*mf-ans* ,*mf-args* ,*mf-ans-p*))

               (cond
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

                      ;; reinitialize tables if they don't exist...
                      (when
                       (null ,tablename)
                       ,@mf-record-mht
                       (setq ,tablename (make-initial-memoize-hash-table ',fn ,memo-table-init-size))

                       ,@(if (> nra 1) ; number of arguments
                             `((setq ,ponstablename
                                     (make-initial-memoize-pons-table ',fn ,memo-table-init-size)))))


                      ;; To avoid a remotely possible parallelism gethash error.  (jared: what?!?)
                      ,@(if (> nra 1)
                            `((setq ,localponstablename
                                    (or ,ponstablename
                                                 ;; BOZO should this be a make-initial-memoize-pons-table?
                                                 (mht)))))


                      ;; Generate the pons key... if there's just one arg, pist* just returns the arg and
                      ;; doesn't do any ponsing.

                      #+parallel ,@(if (> nra 1) `((ccl::lock-hash-table ,localponstablename)))
                      (setq ,*mf-args* (pist* ,localponstablename ,@formals ,@specials))
                      #+parallel ,@(if (> nra 1) `((ccl::unlock-hash-table ,localponstablename)))


                      ;; dunno what this is for... maybe we're binding a localtablename variable to avoid
                      ;; doing special lookups or some such?

                      (setq ,localtablename
                            ;; BOZO should this be a make-initial-memoize-hash-table?
                            (or ,tablename (mht)))


                      ;; this is the lookup of the memoized result.

                      (multiple-value-setq
                       (,*mf-ans* ,*mf-ans-p*)
                       ,(let ((gethash-form
                               `(gethash ,*mf-args*
                                         (the hash-table ,localtablename))))
                          (cond (aokp `(cond
                                        (*aokp* ,gethash-form)
                                        (t (mv nil nil))))
                                (t gethash-form))))



                      (cond
                       (,*mf-ans-p*

                        ;; Memoized lookup succeeds.  Do profiling things, return answer...

                        ,@(when aokp `((update-attached-fn-called ',lookup-marker)))
                        ,@(if trace `((oftr "~% ~s remembered." ',fn)))
                        ,@mf-record-hit
                        ,@(cond ((null (cdr stobjs-out))
                                 `(,@mf-trace-exit ,*mf-ans*))
                                (t
                                 ;; No idea what this is doing...
                                 (let ((len-1 (1- (length stobjs-out))))
                                   `(,@(and trace
                                            `(progn
                                               (let* ((,*mf-ans* (append (take ,len-1 ,*mf-ans*)
                                                                         (list (nthcdr ,len-1 ,*mf-ans*)))))
                                                 ,@mf-trace-exit)))
                                     ,(cons
                                       'mv
                                       (nconc (loop for i fixnum below len-1 collect `(pop ,*mf-ans*))
                                              (list *mf-ans*))))))))


                       (t

                        ;; Memoized lookup failed.  Need to run the function and get its results...

                        ,(let* ((vars
                                 ;; Make variables (O0 O1 ... 0N) for the outputs?  Don't really understand what stobjs-out is
                                 ;; for here...
                                 (loop for i fixnum below (if (cdr stobjs-out) (length stobjs-out) 1) collect (ofni "O~a" i)))

                                (prog1-fn (if (cdr stobjs-out) 'multiple-value-prog1 'prog1))
                                (mf-trace-exit+
                                 (and mf-trace-exit
                                      `((let ((,*mf-ans* ,(if stobjs-out `(list* ,@vars) (car vars))))
                                          ,@mf-trace-exit)))))

                             `(let (,*attached-fn-temp*)
                                (mv?-let
                                 ,vars
                                 (let (*attached-fn-called*)
                                   ;; This is where the actual function is being run.  The 01...0N vars are being bound to
                                   ;; the results...
                                   (,prog1-fn
                                    ,body-call
                                    (setq ,*attached-fn-temp* *attached-fn-called*)))
                                 (progn
                                   (cond
                                    ,@(and (not aokp)
                                           `((,*attached-fn-temp*
                                              (memoize-use-attachment-warning ',fn ,*attached-fn-temp*))))
                                    (t
                                     ;; Actually install the results
                                     (setf (gethash ,*mf-args* (the hash-table ,localtablename))
                                           (list* ,@vars))))
                                   (update-attached-fn-called ,*attached-fn-temp*)
                                   ,@mf-trace-exit+
                                   (mv? ,@vars)))))))))))))


           (body2
            ;; Bunch of extra profiling stuff wrapped around body3.

            `(let ((,*mf-old-caller* *caller*)
                   #+Clozure
                   ,@(and *record-bytes*
                          `((,*mf-start-bytes*
                             (heap-bytes-allocated))))
                   ;; [Jared]: removing this, hons tracking hasn't worked since hl-hons
                   ;; ,@(and *record-hons-calls*
                   ;;        `((,*mf-start-hons* *hons-call-counter*)))
                   ,@(and *record-pons-calls*
                          `((,*mf-start-pons* *pons-call-counter*))))
               (declare
                (ignorable
                 #+Clozure
                 ,@(and *record-bytes* `(,*mf-start-bytes*))
                 ;; ,@(and *record-hons-calls* `(,*mf-start-hons*))
                 ,@(and *record-pons-calls* `(,*mf-start-pons*)))
                (type fixnum
                      ,*mf-old-caller*
                      ;; ,@(and *record-hons-calls* `(,*mf-start-hons*))
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
                 ;; [Jared]: removing this, hons tracking hasn't worked since hl-hons
                 ;; ,@(and *record-hons-calls*
                 ;;        `((safe-incf (aref ,*mf-ma* ,(+ *ma-hons-index* 2mfnn))
                 ;;          (the mfixnum (- *hons-call-counter* ,*mf-start-hons*)) ,fn)))
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
                 ,@(and forget

; Below, we "clear" the tables by setting them to nil, rather than by calling
; clrhash.  The latter approach would probably avoid reallocation of space, but
; we suspect that a gain in space efficiency may be offset by a loss in time
; efficiency.  The present approach has been working, so we prefer not to
; change it.  Below is just a little space analysis.

; When we evaluated (defconstant *a* (make-list 1000)) in raw Lisp (CCL) and
; then ran (time$ (bad-lisp-objectp *a*)), we saw about 71K bytes allocated,
; which dropped to just 1,136 bytes after evaluating (unmemoize-fn
; 'bad-lisp-objectp).  Then we evaluated (memoize-fn 'bad-lisp-objectp) -- this
; time without a :forget argument -- and found about 71K bytes allocated on the
; first timing of (bad-lisp-objectp *a*), but only 1,136 bytes allocated on
; subsequent evaluations, presumably because we weren't starting from scratch.
; We suspect that the byte allocation on subsequent runs may have been well
; under 71K even after memoizing with :forget t, if the tables had been cleared
; with clrhash rather than being blown away as is done just below.

                        `((setq ,tablename nil)
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
                   (if (eql -1 ,start-time)
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
            (memoize-eval-compile def)
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
  #-hons
  (return-from unmemoize-fn
               (progn (when (not (zerop *ld-level*))
                        (warning$ 'unmemoize nil
                                  "No change for function ~x0: Unmemoization ~
                                   requests are ignored in this ACL2 ~
                                   executable because it is not hons-enabled."
                                  fn))
                      fn))
  (unwind-mch-lock
   (maybe-untrace! fn) ; See the comment about Memoization in trace$-def.
   (let* ((ma *memoize-call-array*)
          (l (memoizedp-raw fn)))
     (declare (type (simple-array mfixnum (*)) ma))
     (unless l (ofe "Unmemoize-fn: ~s is not memoized." fn))
     (let* ((num (the fixnum (access memoize-info-ht-entry l
                                     :num)))
            (tablename (and l (access memoize-info-ht-entry l
                                      :tablename)))
            (n2 (* num *2max-memoize-fns*))
            )
       (declare (fixnum num n2))

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

; WARNING: ACL2 users should probably avoid this function, using
; (clear-memo-table) in the ACL2 loop instead.

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

(defun profile-fn (fn &rest r &key (condition nil) (inline nil)
                      &allow-other-keys)
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


; VERY-UNSAFE-INCF

(defmacro very-unsafe-incf (x inc &rest r)

; returns NIL !

  (declare (ignore r))

  (unless (symbolp x)
    ;; Compile-time sanity check
    (error "very-unsafe-incf should only be used on symbols, not ~a" x))

  `(locally (declare (type mfixnum ,x))
            (setq ,x (the mfixnum (+ ,x (the mfixnum ,inc))))
            nil))

(defmacro very-very-unsafe-aref-incf (ar loc)
 `(setf (aref (the (simple-array mfixnum (*)) ,ar) ,loc)
        (the mfixnum (1+ (aref (the (simple-array mfixnum (*)) ,ar)
                              ,loc)))))


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
;; [Jared]: what?
;;    (our-syntax-brief
;;     (when (boundp '*acl2--*) (oft "~%> ~a~%" *acl2--*)))
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
  )

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

         *REPORT-ON-MEMO-TABLES*   boolean
         *REPORT-ON-PONS-TABLES*   boolean
         *MEMOIZE-SUMMARY-LIMIT*            (or integerp null)
         *MEMOIZE-SUMMARY-ORDER-LIST*       (symbol symbol ... symbol)
         *MEMOIZE-SUMMARY-ORDER-REVERSED*   boolean

  Functions are sorted lexicographically according to the ordering
  induced by the function names in *MEMOIZE-SUMMARY-ORDER-LIST*, each
  member of which must be a unary function that returns a rational.

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
        #+Clozure
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
   #+Clozure
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
           (tt (max .000001 (total-time num)))
           (t/c (time/call num))
           (tnh (time-for-non-hits/call num))
           (in-progress-str
            (if (eql start-time -1) " " ", running, "))
           (selftime tt))
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
                      (decf selftime ltt)
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
                                     (if (> (* 10000 ltt) tt)
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
                             (if (> (* 10000 outside-fn-time) tt)
                                 (* 100 (/ outside-fn-time tt))
                               '?)))
                      . ,(if *sort-to-from-by-calls*
                             outside-fn-count
                           outside-fn-time))
                    l))
                 (when (and (> selftime 0)
                            (not (= selftime tt)))
                   (push `((,(ofn " To self/unprofiled functions")
                            ,(ofn "~8,2e;~5,1f%"
                                  selftime
                                  (if (> (* 10000 selftime) tt)
                                      (* 100 (/ selftime tt))
                                    '?)))
                           . ,(if *sort-to-from-by-calls*
                                  0 ;; ?
                                (* selftime *float-ticks/second*)))
                         l))
                 (setq l (sort l #'> :key #'cdr))
                 ; (cw "l: ~x0~%" l)
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
      (when l (clear-one-memo-and-pons-hash l))))
  k)

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
      (or success (ofe "clear-memoize-tables failed."))))
  nil)

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

; Note: The hons reader was formerly defined here, but it's now in community
; book books/serialize/compact-print-raw.lsp (loaded when the community book
; serialize/compact-print is included).

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
         (setq success t))
       (if success (setq *memoize-init-done* t)
         (ofd "~%; memoize init: Error **"))))))



;; [Jared and Sol]: It is gross to leave these in here, but we're going to do
;; it, because right now they're used within WATCH.  If we eventually decide
;; that WATCH is deprecated or anything like that, we can move these to
;; centaur/misc/memory-mgmt, where they are actually used now.

(defg *max-mem-usage* (expt 2 32)

  "*MAX-MEM-USAGE* an upper bound, in bytes of memory used, that when
  exceeded results in certain garbage collection actions.

  Note: not used by ACL2(h) itself; see the centaur/misc/memory-mgmt
  books.")

(defg *gc-min-threshold* (expt 2 30)
  "Note: not used by ACL2(h) itself; see the centaur/misc/memory-mgmt
  books.")




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
(defmacro globlet (bindings &rest rest)
  ;; [Jared]: this is only used in with-lower-overhead AFAICT.

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

#-Clozure
(defmacro globlet (&rest r)

; See #+Clozure definition for an explanation of why we need this macro.  In
; Lispworks, we get this warning if we use the #+Clozure definition:

; ;;;*** Warning in ACL2::HONS-INIT-HOOK-MEMOIZATIONS: #:*COUNT-PONS-CALLS* bound lexically.

; So we use a much simpler definition here.

  `(let ,@r))

(defmacro with-lower-overhead (&rest r)
  `(let ((*record-bytes* nil)
         (*record-calls*

; It is a mystery why we need to set *record-calls* to t in LispWorks.  But we
; do.  Otherwise, for example, evaluation hangs for
;   (bad-lisp-objectp (make-list 100000))
; when bad-lisp-objectp is in the initial memoized state produced by calling
; hons-init (see hons-init-hook-memoizations, which has a call in
; *hons-init-hook*).

          #-lispworks nil #+lispworks t)
         (*record-hits* nil)
         (*record-hons-calls* nil)
         (*record-mht-calls* nil)
         (*record-pons-calls* nil)
         (*record-time* nil))
     (globlet ((*count-pons-calls* nil))
              ,@ r)))

(defun hons-init-hook-memoizations ()

; Keep in sync with hons-init-hook-unmemoizations.

; We pull out the memoization calls so we can unmemoize and re-memoize these
; functions when the user enables and disables waterfall parallelism,
; respectively.

  (when (not (memoizedp-raw 'bad-lisp-objectp))
    (with-lower-overhead
     (memoize-fn 'bad-lisp-objectp :forget t)))

  (when (not (memoizedp-raw 'worse-than-builtin))
    ;; Warning: If this is changed or removed, visit the comment in
    ;; worse-than-builtin.
    (with-lower-overhead
     (memoize-fn 'worse-than-builtin
                 :condition ; Sol Swords suggestion
                 '(and (nvariablep term1)
                       (not (fquotep term1))
                       (nvariablep term2)
                       (not (fquotep term2))))))

  (when (not (memoizedp-raw 'fchecksum-obj))
    ;; Warning: If this memoization is removed, modify the comment in
    ;; fchecksum-obj about memoization of that function.
    (with-lower-overhead
     (memoize-fn 'fchecksum-obj :forget t)))

  (when (not (memoizedp-raw 'expansion-alist-pkg-names-memoize))
    ;; Warning: If this memoization is removed, modify the comment in
    ;; expansion-alist-pkg-names about memoization of that function.
    (with-lower-overhead
     (memoize-fn 'expansion-alist-pkg-names-memoize :forget t)))

  (when (not (memoizedp-raw 'physical-memory))
    ;; [Jared]: merged in from e4/memoize-raw.lsp
    (with-lower-overhead
     (memoize-fn 'physical-memory :inline nil)))

  (when (not (memoizedp-raw 'swap-total))
    ;; [Jared]: merged in from e4/memoize-raw.lsp
    (with-lower-overhead
     (memoize-fn 'swap-total :inline nil))))

(defun hons-init-hook-unmemoizations ()

; Keep in sync with hons-init-hook-memoizations.

  (when (memoizedp-raw 'bad-lisp-objectp)
    (unmemoize-fn 'bad-lisp-objectp))
  (when (memoizedp-raw 'worse-than-builtin)
    (unmemoize-fn 'worse-than-builtin))
  (when (memoizedp-raw 'fchecksum-obj)
    (unmemoize-fn 'fchecksum-obj))
  (when (memoizedp-raw 'expansion-alist-pkg-names-memoize)
    (unmemoize-fn 'expansion-alist-pkg-names-memoize))
  (when (memoizedp-raw 'physical-memory)
    (unmemoize-fn 'physical-memory))
  (when (memoizedp-raw 'swap-total)
    (unmemoize-fn 'swap-total)))

(defg *hons-init-hook*
  '(progn

     #+Clozure
     (unless (> (parse-integer ccl::*openmcl-svn-revision*
                               :junk-allowed t)
                13296)
       (fresh-line)
       (princ "Better use a version of CCL past revision 13280."))

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

     (hons-init-hook-memoizations)

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

       ;; With *print-array* turned on, we end up sometimes seeing the SBITS
       ;; array in backtraces, etc, which can effectively kill your session.
       (setq *print-array* nil)

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


(defn1 hons-init ()

; We assume ACL2-DEFAULT-RESTART will be called at least once.  We
; suspect it will be called whenever an ACL2H CCL saved image is
; started up.  We know that ACL2-DEFAULT-RESTART calls HONS-INIT.  We
; are unsure how many times ACL2-DEFAULT-RESTART might be called, and
; so we code HONS-INIT so that it may be called multiple times.

  (in-package "ACL2")
  (unless *memoize-init-done* (memoize-init))
  (float-ticks/second-init)
  (eval *hons-init-hook*))


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





(defn lower-overhead ()
  ;; Doesn't help much.
  (setq *record-bytes* nil)
  (setq *record-calls*

; See the comment about LispWorks in with-lower-overhead; we make the analogous
; adjustment for LispWorks here, in case it's necessary.

        #-lispworks nil #+lispworks t)
  (setq *record-hits* nil)
  (setq *record-hons-calls* nil)
  (setq *record-mht-calls* nil)
  (setq *record-pons-calls* nil)
  (setq *record-time* nil)
  (setq *count-pons-calls* nil))

#+Clozure
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






;; (defun copy-hash-table
;;   (ht &key
;;       (new-test (hash-table-test ht))
;;       (new-size (hash-table-size ht))
;;       (new-rehash-size (hash-table-rehash-size ht))
;;       (new-rehash-threshold (hash-table-rehash-threshold ht))
;;       #+Clozure
;;       (new-weak (ccl::hash-table-weak-p ht))
;;       #+Clozure
;;       (new-shared (ccl::nhash.owner ht)))

;;   "(COPY-HASH-TABLE ht) takes a hash-table and returns a copy of it
;;   that may have some different attributes, depending upon the keyword
;;   values supplied for :NEW-SIZE and other keywords.  All the key/value
;;   pairs are copied.  Thus,
;;      (COPY-HASH-TABLE ht :NEW-SIZE 1000000)
;;   returns a copy of ht of size about 1000000."

;; ;;    Some remarks by Gary Byers about how this function might
;; ;;    be improved.

;; ;;    There's probably a way to do this that preserves the
;; ;;    EQness of the table.  A hash-table contains some
;; ;;    general information and a "hash-table-vector", which
;; ;;    contains a few words of other information and all of
;; ;;    the key/value pairs; the HASH-TABLE itself is relatively
;; ;;    small, but the underlying vector can get very large.
;; ;;    (HASH-TABLE-SIZE is really a function of the size of
;; ;;    the underlying hash-table-vector.)

;; ;;    The hash-table-vector isn't really user-accessible;
;; ;;    it's just an artifact of the implementation.  We could
;; ;;    (if we remembered how ...) implement a RESIZE-HASH-TABLE
;; ;;    function that created a new vector, hashed all of the
;; ;;    key/value pairs from the old vector into the new one,
;; ;;    and made the new vector the hash table's vector.  There
;; ;;    are a few variants of that resizing function in the hash
;; ;;    table code, but they're complicated and not user accesible:
;; ;;    doing this in the real world is complicated by concurrency
;; ;;    issues (if two threads call RESIZE-HASH-TABLE at about the
;; ;;    same time, which one "wins" ?  Can you ensure that one of
;; ;;    them wins and the hash table's in a consistent state afterwards,
;; ;;    rather than partly believing that it's of the size specified
;; ;;    by thread A and partly of that specified by thread B ? Etc.)

;; ;;    The :LOCK-FREE argument to MAKE-HASH-TABLE is only important
;; ;;    if :SHARED is true.  A hash-table can be:

;; ;;    a) thread-private, if :SHARED is false
;; ;;    b) shared, using locks if :SHARED is true and :LOCK-FREE is
;; ;;       false
;; ;;    c) shared, without using locks if :SHARED is true and :LOCK-FREE
;; ;;        is true.

;; ;;    (c) is the default; it allows many threads to access the table
;; ;;    concurrently without locking.  READ operations (GETHASH) are
;; ;;    very cheap; write operations are more complicated and expensive
;; ;;    (more expensive than in the locking case.)  In (a), everything's
;; ;;    fairly cheap (no concurrency overhead), but that's only viable
;; ;;    some of the time.

;; ;;    If your COPY-HASH-TABLE function is sure that the source is
;; ;;    of type (a) (... :shared nil ...), it doesn't have to worry
;; ;;    about the :LOCK-FREE argument; you can make the new table's
;; ;;    lock-freed-ness default to the old table's by adding a
;; ;;    keyword arg:

;; ;;    (new-lock-free (ccl::hash-lock-free-p ht))

;; ;;    and passing NEW-LOCK-FREE's value as the value of :LOCK-FREE
;; ;;    when creating the new table.


;;       (let ((new (make-hash-table
;;                   :test             new-test
;;                   :size             new-size
;;                   :rehash-size      new-rehash-size
;;                   :rehash-threshold new-rehash-threshold
;;                   #+Clozure
;;                   :weak
;;                   #+Clozure
;;                   new-weak
;;                   #+Clozure
;;                   :shared
;;                   #+Clozure
;;                   new-shared)))
;;         (maphash (lambda (k v) (setf (gethash k new) v)) ht)
;;         new))

