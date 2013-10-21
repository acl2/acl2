; Memoize Library
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>
;
; This library is a descendant of the memoization scheme developed by Bob Boyer
; and Warren A. Hunt, Jr. which was incorporated into the HONS version of ACL2,
; sometimes called ACL2(h).

(in-package "MEMOIZE")


; A trivial but critical part of memoizing functions is knowing how many
; arguments they take and how many return values they produce.
;
; Interface:
;
;    (numargs fn)
;      - Tries to detect how many arguments fn takes
;      - Returns NIL on failure
;
;    (numvals fn)
;      - Tries to detect how many return values fn has
;      - Returns NIL on failure
;
;    (declare-numargs fn nargs nvals)
;      - Explicitly asserts that FN has NARGS arguments and NVALS return values
;      - This takes precedence over the introspection code in numargs and numvals.
;      - You'd better be right, for soundness.

(defparameter *numargs-table*
  ;; Format: function name -> (nargs . nvals)
  ;;  - nargs and nvals are naturals, or NIL for unknown
  (let ((ht (make-hash-table)))
    ;; Special functions that we want to make sure we pretend
    ;; we don't know about
    (setf (gethash 'if ht)          '(nil . nil))
    (setf (gethash 'return-last ht) '(nil . nil))
    ht))

(declaim (hash-table *numargs-table*))

(defun declare-numargs (fn nargs nvals)
  (setf (gethash fn *numargs-table*)
        (cons nargs nvals)))

(defun numargs (fn)
  (let* ((state acl2::*the-live-state*)
         (w     (w state))
         (pair  (gethash fn *numargs-table*)))
    (cond ((not (symbolp fn))
           nil)
          ((consp pair)
           ;; Table takes precedence
           (car pair))
          ;; Magic code that works for proper ACL2 functions.
          ((let ((formals (getprop fn 'formals t 'current-acl2-world w)))
             (and (not (eq t formals))
                  (length formals))))
          ((or (not (fboundp fn))
               (macro-function fn)
               (special-operator-p fn))
           nil)
          #+Clozure
          ;; Magic code that works for raw Lisp functions on CCL.
          ((multiple-value-bind (req opt restp keys)
                                (ccl::function-args (symbol-function fn))
                                (and (null restp)
                                     (null keys)
                                     (integerp req)
                                     (eql opt 0)
                                     req)))

          (t nil))))

(defun numvals (fn)
  (let* ((state acl2::*the-live-state*)
         (w     (w state))
         (pair  (gethash fn *numargs-table*)))
    (cond ((not (symbolp fn))
           nil)
          ((consp pair)
           ;; Table takes precedence
           (cdr pair))
          ((let ((formals (getprop fn 'formals t 'current-acl2-world w)))
             ;; Figures out the number of return values for ACL2 functions.
             (and (not (eq t formals))
                  (len (stobjs-out fn w)))))
          (t nil))))

