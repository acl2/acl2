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

(defun profile-acl2 (&key (start 0)
                          trace
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
         (profile-fn k
                     :trace trace
                     :forget forget))
       fns-ht)
      (clear-memoize-call-array)
      (oft "~%(clear-memoize-call-array) invoked.")
      (ofn "~a function~:p newly profiled."
           (hash-table-count fns-ht)))))

(defun profile-all (&key trace (lots-of-info t) forget
                         pkg)

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
         (profile-fn k
                     :trace trace
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
  PROFILE-FN on 'all the functions defined in' FILE, a relatively vague
  concept.  However, if packages are changed in FILE as it is read, in
  a sneaky way, or if macros are defined and then used at the top of
  FILE, who knows which functions will be profiled?  Functions that do
  not pass the test DUBIOUS-TO-PROFILE are not profiled.  A list of
  the names of the functions profiled is returned."

  (loop for fn in (functions-defined-in-file file)
        unless (dubious-to-profile fn)
        collect (apply #'profile-fn fn r)))