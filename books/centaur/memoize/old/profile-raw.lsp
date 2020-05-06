; profile-raw.lsp
; Copyright (C) 2013, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; This file was originally part of the HONS version of ACL2.  The original
; version of ACL2(h) was contributed by Bob Boyer and Warren A. Hunt, Jr.  The
; design of this system of Hash CONS, function memoization, and fast
; association lists (applicative hash tables) was initially implemented by
; Boyer and Hunt.

(in-package "ACL2")

(defv *profile-reject-ht*
  ;; [Jared]: This prevents profiling of functions when automatically deciding
  ;; what to profile using (profile-all) or (profile-file), etc.
  ;;
  ;; Note that the following are in addition to what already doesn't get
  ;; profiled via things like never-memoize.
  (let ((ht (hl-mht :test 'eq)))
    (loop for sym in
          '(
            ;; These seem too primitive to profile:
            acl2-numberp
            aref1
            aref2
            binary-+
            booleanp
            complex-rationalp
            digit-to-char
            eqlablep
            intern-in-package-of-symbol
            kwote
            len
            natp
            posp
            print-base-p
            quotep
            symbol-<
            symbol-package-name
            xor
            zp)
          do (setf (gethash sym ht) t))
    ht)
  "The initial list of functions in the *profile-reject-ht* is meant to be
   quite minimal.  Our goal is only to avoid profiling functions that we think
   are so fast, or are called so often, that the extra instructions executed
   when profiling or memoizing them will excessively distort our measurements.

   However, *profile-reject-ht* is also meant as a convenient way for users to
   avoid profiling other functions.  This may be useful for many reasons, for
   instance:

     1. You may encounter other functions that, like the entries above, are
        very fast or called very often and cannot be profiled without unduly
        damaging accuracy.

     2. You may want to avoid profiling, e.g., recursive ``-aux'' functions of
        higher level wrappers that you are already profiling, for similar
        reasons.

     3. You may want to avoid profiling functions that are ``transparent,''
        like eval.  Is eval fast or slow?  The answer, of course, is that it
        mostly depends upon what one is evaling.

     4. You may want to avoid profiling certain functions that are unrelated to
        whatever you happen to be investigating at the current moment, or
        functions that you have already spent time optimizing, etc.

   In short: you should feel free to modify this list at runtime to suit your
   purposes.")

(declaim (hash-table *profile-reject-ht*))

; From ACL2 6.5 memoize-raw.lisp:
(defmacro ofn (&rest r) ; For forming strings.
  `(our-syntax (format nil ,@r)))

(defun-one-output dubious-to-profile (fn)
  (cond ((not (symbolp fn)) " is not a symbol.")
        ((not (fboundp fn)) " is not fboundp.")
        ((eq (symbol-package fn) *main-lisp-package*)
         (ofn " is in *main-lisp-package*."))
        #-Clozure
        ((multiple-value-bind
          (sym foundp)
          (find-symbol (symbol-name fn) *main-lisp-package*)
          (declare (ignore sym))
          foundp)
; Avoid "cannot be printed readably" error in SBCL and perhaps other Lisps (but
; since we haven't had this problem in CCL, we exclude the test for CCL).
         (ofn "s symbol-name is found in *main-lisp-package*."))
        #+Clozure
        ((ccl::%advised-p fn)
         (ofn " is advised, and it will so continue."))
        ((member fn (eval '(trace)))
         (ofn " is a member of (trace), and it will so continue."))
        ((and (fboundp 'old-trace)
              (member fn (eval '(old-trace))))
         (ofn " is a member of (old-trace), and it will so continue."))
        ((gethash fn *never-memoize-ht*)
         (ofn " is in *NEVER-MEMOIZE-HT*."))
        ((gethash fn *profile-reject-ht*)
         (ofn " is in *PROFILE-REJECT-HT*.  Override with~
               ~%;~10t(REMHASH '~a *PROFILE-REJECT-HT*)."
              fn))
        ((macro-function fn) " is a macro.")
        ((compiler-macro-function fn) " is a compiler-macro-function.")
        ((special-form-or-op-p fn) " is a special operator.")
        ((getprop fn 'constrainedp nil 'current-acl2-world
                  (w *the-live-state*))
         " is constrained.")
        ((memoizedp-raw fn)
         (ofn " is memoized or profiled, and it will so continue."))
        ((eq (memoize-fn-formals fn (w *the-live-state*) t)
             t)
         (ofn " its formals cannot be computed."))
        #+Clozure
        ((multiple-value-bind (req opt restp keys)
             (ccl::function-args (symbol-function fn))
           (if (or restp
                   keys
                   (not (integerp req))
                   (not (eql opt 0)))
               (ofn " it has some non-simple argument, e.g., &key or &rest.")
             nil)))
;       ((null (mf-len-inputs fn)) (input-output-number-warning fn))
        ))

(declaim (ftype (function (t) (values t)) profile-acl2-event-number))

(defun profile-acl2-event-number (fn)
  (cond ((symbolp fn)
         (fgetprop fn 'absolute-event-number t (w *the-live-state*)))
        (t (error "PROFILE-ACL2-EVENT-NUMBER: ** ~a is not a symbol." fn))))

(defn memoize-here-come (n)
  (let ((m (ceiling
            ;; Jared upped this from 100 to 500 to try to avoid errors with
            ;; "MEMOIZE-CALL-ARRAY-GROW was called while a memoized function
            ;;  was executing" when profiling things like the certify-book
            ;; of doc/top.lisp
            (+ 500 (* 1.1 (- n (- (/ *2max-memoize-fns* 2)
                                  (floor
                                   (/ (hash-table-count
                                       *memoize-info-ht*)
                                      2)))))))))
    (when (posp m) (memoize-call-array-grow (* 2 m)))))

; As of 10/14/2014, ofv was defined here in a way that conflicts with its
; definition in output-raw.lsp.  We opt to avoid ofv entirely and define a much
; simplified version here.
(defvar *ofv2-verbose* nil)
(defmacro ofv2 (&rest r)
  `(when *ofv2-verbose*
     (format t ,@r)
     (force-output t)))

#+sbcl
(defun sbcl-check-tls-size ()

; On 4/24/2020, using SBCL 2.0.3 and ACL2 8.3, we found that it is currently
; impossible to run profile-acl2 or profile-all on our linux platform.  The
; error message says "Thread local storage exhausted.", and the error seems to
; be due to an inherent limitation in SBCL on the number of special variables,
; together with the factthat memoization (or profiling) a function creates
; special variables (perhaps four of them).  A solution may be to change
; memoize-raw.lisp to use a single array special variable where we now generate
; a special variable for each function.  That can be investigated if anyone
; really needs profile-acl2 or profile-all to run in SBCL.

  (cerror "Continue at your own risk.  But you may find that Lisp quits~%~
           with the error message, \"Thread local storage exhausted.\"  We~%~
           know of no way to work around that problem."
          "Profiling a large number of functions will likely fail in SBCL.~%~
           You can try it by first executing ~s~%~
           and then selecting \"Continue at your own risk\" from the~%~
           debugger.  But you may find that Lisp quits with the error,~%~
           \"Thread local storage exhausted.\"  We know of no way to work~%~
           around that problem."
          '(set-debugger-enable t))

; Below are a comment and code that are out of date, as the constant
; sb-vm::tls-size no longer exists in SBCL.

;  ; As of SBCL 1.4.14 (and probably many versions preceding that one),
;  ; sb-vm:tls-size is 4096, which is insufficient for profile-acl2 or
;  ; profile-all.  We could simply check the following inequality shortly
;  ; before profiling, replacing 5322 by the number of functions to profile.
;  ; But further attempts to profile would need sb-vm::tls-size to be
;  ; corresponding larger, so we simply check that the default has been
;  ; overridden, presumably by editing an SBCL source file as suggested below.
;
;    (when (= sb-vm:tls-size 4096)
;      (error "~s will fail with default builds of SBCL.  A~%~
;              solution is to build SBCL with a larger value of ~s.~%~
;              You can do this by first editing~%~
;              src/compiler/generic/parms.lisp,~%replacing~%~
;              \"(defconstant tls-size 4096)\"~%by~%~
;              \"(defconstant tls-size 16384)\"~%~
;              and then building SBCL from source, preferably with:~%~a"
;             'profile-acl2
;             'sb-vm::tls-size
;             "sh make.sh --without-immobile-space --without-immobile-code --without-compact-instance-header"))
  )

(defun profile-acl2-fn (start lots-of-info forget)
  #+sbcl (sbcl-check-tls-size)
  (let ((*record-bytes* #+Clozure lots-of-info #-Clozure nil)
        (*record-calls* lots-of-info)
        (*record-hits* lots-of-info)
;       (*record-hons-calls* lots-of-info)
        (*record-mht-calls* lots-of-info)
        (*record-pons-calls* lots-of-info)
        (*record-time* lots-of-info))
    (unless (integerp start)
      (unless (symbolp start)
        (error "~%; PROFILE-ACL2: ** ~a is not an event." start))
      (setq start (profile-acl2-event-number start))
      (unless (integerp start)
        (error "~%; PROFILE-ACL2: ** ~a is not an event." start)))
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
                         (compiler-macro-function fn)
                         (macro-function fn)
                         (special-form-or-op-p fn))
                     (setf (gethash fn fns-ht) 'no))
                    ((or (not (integerp (profile-acl2-event-number fn)))
                         (< (profile-acl2-event-number fn) start))
                     (setf (gethash fn fns-ht) 'no))
                    ((dubious-to-profile fn)
                     (setf (gethash fn fns-ht) 'no)
                     (ofv2 "Not profiling '~a' because it~a~%"
                           (mf-shorten fn 20)
                           (dubious-to-profile fn)))
                    (t (setf (gethash fn fns-ht) 'yes)))))
      (maphash (lambda (k v)
                 (if (eq v 'no) (remhash k fns-ht)))
               fns-ht)
      (format t
              "Profiling ~:d functions.~%"
              (hash-table-count fns-ht))
      (memoize-here-come (hash-table-count fns-ht))
      (maphash
       (lambda (k v)
         (declare (ignore v))
         (profile-fn k
                     :forget forget))
       fns-ht)
      (clear-memoize-statistics)
      (format t "~%(clear-memoize-statistics) invoked.~%")
      (format t "~a function~:p newly profiled.~%"
              (hash-table-count fns-ht))))
  nil)

(defun profile-all-fn (lots-of-info forget pkg)
  #+sbcl (sbcl-check-tls-size)
  (let ((*record-bytes* #+Clozure lots-of-info #-Clozure nil)
        (*record-calls* lots-of-info)
        (*record-hits* lots-of-info)
        (*record-hons-calls* lots-of-info)
        (*record-mht-calls* lots-of-info)
        (*record-pons-calls* lots-of-info)
        (*record-time* lots-of-info))
    (let ((fns-ht (make-hash-table :test 'eq)))
      (declare (hash-table fns-ht))
      (loop for p in
            (if pkg
                (if (stringp pkg) (list pkg) pkg)
              (set-difference-equal
               (strip-cars (known-package-alist *the-live-state*))
               '("ACL2-INPUT-CHANNEL" "ACL2-OUTPUT-CHANNEL"
                 "COMMON-LISP" "KEYWORD")))
            do
            (do-symbols (fn p)
              (cond ((gethash fn fns-ht) nil)
                    ((or (not (fboundp fn))
                         (macro-function fn)
                         (special-form-or-op-p fn))
                     (setf (gethash fn fns-ht) 'no))
                    ((dubious-to-profile fn)
                     (setf (gethash fn fns-ht) 'no)
                     (ofv2 "Not profiling '~a' because it~a~%"
                           (mf-shorten fn 20)
                           (dubious-to-profile fn)))
                    (t (setf (gethash fn fns-ht) 'yes)))))
      (maphash (lambda (k v)
                 (if (eq v 'no) (remhash k fns-ht)))
               fns-ht)
      (format t
              "Profiling ~:d functions."
              (hash-table-count fns-ht))
      (memoize-here-come (hash-table-count fns-ht))
      (maphash
       (lambda (k v) (declare (ignore v))
         (profile-fn k
                     :forget forget))
       fns-ht)
      (clear-memoize-statistics)
      (format t "~%(clear-memoize-statistics) invoked.~%")
      (ofn "~a function~:p newly profiled.~%"
           (hash-table-count fns-ht))))
  nil)

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
  PROFILE-FN on 'all the functions defined in' FILE, a relatively vague
  concept.  However, if packages are changed in FILE as it is read, in
  a sneaky way, or if macros are defined and then used at the top of
  FILE, who knows which functions will be profiled?  Functions that do
  not pass the test DUBIOUS-TO-PROFILE are not profiled.  A list of
  the names of the functions profiled is returned."

  (loop for fn in (functions-defined-in-file file)
        unless (dubious-to-profile fn)
        collect (apply #'profile-fn fn r)))

