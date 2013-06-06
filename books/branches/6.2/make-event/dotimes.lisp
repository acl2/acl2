#|

   Dotimes, Version 0.2
   Copyright (C) 2006 by David Rager <ragerdl@cs.utexas.edu>

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public Lic-
   ense along with this program; if not, write to the Free Soft-
   ware Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
   02111-1307, USA.



 dotimes.lisp

   This file provides a dotimes$ macro for use at the top-level.  I also needed
   a version of dotimes that returned error triples so that I could run events
   multiple times for performance benchmarking.  Dotimes$-with-error-triple
   meets these requirements.  The use of dotimes$-with-error-triple requires an
   active ttag.

   Anyone should feel to cleanup or enhance these macros.

Jared Davis, Matt Kaufmann, and Sandip Ray contributed to this book.
|#

(in-package "ACL2")

(defmacro dotimes$ (var-limit-form form &key (name 'dotimes-default-name-foo))
  (declare (xargs :guard (and (true-listp var-limit-form)
                              (equal (length var-limit-form) 2))))
  
  (let ((var (car var-limit-form))
        (limit (cadr var-limit-form)))
    
    `(make-event
      (with-output 
       :off summary
       (progn
         (with-output
          :off :all
          (defun ,name (,var)
            (declare (xargs :measure (acl2-count ,var)))
            (if (zp ,var)
                (cw "Done with dotimes~%")
              (prog2$ ,form
                      (,name (1- ,var))))))
         (value-triple (,name ,limit))
         (value-triple '(value-triple :invisible)

; The following keyword :on-skip-proofs t was added by Matt K. after v4-3.
; Without it, value-triple returns (mv nil :skipped state) when skipping
; proofs, as is done during the Expand/Port step of provisional certification
; (see :DOC provisional-certification).

                       :on-skip-proofs t))))))

(defmacro dotimes$-with-error-triple
  (var-limit-form form &key (name 'dotimes-default-name-foo))
  (declare (xargs :guard (and (true-listp var-limit-form)
                              (equal (length var-limit-form) 2))))
  
  (let ((var (car var-limit-form))
        (limit (cadr var-limit-form)))
    
    `(make-event
      (with-output 
       :off summary
       (progn!
         (with-output
          :off :all
          (progn
            (set-state-ok t)
            (defun ,name (,var state)
              (declare (xargs :measure (acl2-count ,var)
                              :mode :program))
              (if (zp ,var)
                  (mv nil (cw "Done with dotimes~%") state)
                (mv-let (erp val state)
                  ,form
; I don't have a need to recognize errors right now.  Someone else can feel
; free to implement such a feature if they like.
                  (declare (ignore erp val))
                  (,name (1- ,var) state))))
            (set-state-ok nil)))
         (,name ,limit state)
         (value-triple '(value-triple :invisible)
; See comment about addition of :on-skip-proofs t in the definition of
; dotimes$.
                       :on-skip-proofs t))))))

; A test:
(local
 (encapsulate
  ()

  (defun fib (x)
    (declare (xargs :guard (natp x)))
    (cond ((mbe :logic (or (zp x) (<= x 0))
                :exec (<= x 0))
           0)
          ((= x 1)
           1)

          (t
           (let ((a (fib (- x 1)))
                 (b (fib (- x 2))))
           
             (+ a b)))))
  
  (dotimes$ (i 4) (time$ (fib 25)) :name dotimes-foo)))

#|
; The following examples work, but I have disabled them so that people can
; include this book without needing an active ttag.  Note that the use of
; dotimes$-with-error-triple does require an active ttag.

(defttag t)

(local
 (encapsulate
  ()
  (dotimes$-with-error-triple
   (i 4)
   (time$ (thm (equal 3 3))))))

(dotimes$-with-error-triple 
 (i 100) 
 (thm (equal (append x (append y z))
             (append (append x y) z))) 
 :name dotimes-thmm)

|#
