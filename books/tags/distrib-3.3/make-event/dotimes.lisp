#|

   Dotimes, Version 0.1
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

   This file provides a dotimes$ macro for use at the top-level. 
   It also provides a brief example.

Jared Davis, Matt Kaufmann, and Sandip Ray contributed to this book.
|# ; |

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
         (value-triple '(value-triple :invisible)))))))

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
  
  (dotimes$ (i 4) (time$ (fib 25)))))
