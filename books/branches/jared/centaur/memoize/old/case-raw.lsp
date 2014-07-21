; case-raw.lsp
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



