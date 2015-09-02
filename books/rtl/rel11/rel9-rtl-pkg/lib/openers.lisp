; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

(set-enforce-redundancy t)

(local (include-book "../support/support/openers"))

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
