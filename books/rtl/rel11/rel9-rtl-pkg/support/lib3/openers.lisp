; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic 
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc. 
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT ANY
; WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
; PARTICULAR PURPOSE.  See the GNU General Public License for more details.
;
; You should have received a copy of the GNU General Public License along with
; this program; see the file "gpl.txt" in this directory.  If not, write to the
; Free Software Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA
; 02110-1335, USA.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

(set-enforce-redundancy t)

(local (include-book "../../support/support/openers"))

(program)

; In this file, an event-control (evctl) data structure is either (posedge
; clk), (negedge clk), or (even n).

(defun negate-event-control (evctl)
  (if (equal evctl '(even n))
      (list 'not evctl)
    (let* ((edge0 (car evctl))
           (clk (cadr evctl))
           (edge (case edge0
                   (posedge 'pedge)
                   (negedge 'nedge)
                   (otherwise
                    (er hard 'gen-model-preamble-common
                        "Unable to handle edge specifier ~x0."
                        edge0)))))
      `(not (,edge (,clk (1- n)) (,clk n))))))

(defun negate-event-control-list (x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
      nil
    (cons (negate-event-control (car x))
          (negate-event-control-list (cdr x)))))

(defmacro def$open (name type &rest evctl-lst)
  (if (eq type :skipped)
      `(value-triple '(def$open ,name :skipped))
    (let ((evctl-lst (if (eq type :input)
                         (assert$ (null evctl-lst)
                                  '((even n)))
                       evctl-lst)))
      `(defthm ,(intern-in-package-of-symbol
                 (concatenate 'string (symbol-name name) "$OPEN")
                 name)
         (implies (and (integerp n)
                       (< 0 n)
                       ,@(negate-event-control-list evctl-lst))
                  (equal (,name n)
                         (,name (1- n))))
         :hints (("Goal"
                  :expand ((,name n)
                           ,@(and (eq type :wire) `((,name (1- n)))))))))))
