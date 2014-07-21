; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "ACL2")
(include-book "defun" :ttags :all)

;; We introduce some macros which can be used to redefine functions in certain
;; ways that improve their traceability.
;;
;; IMPORTANT NOTE:  These macros only work on functions which
;;   (1) have their guards verified, and
;;   (2) were introduced with MILAWA::defun
;;
;; (redef-notinline foo)
;;   Redefines foo (with its own definition), but adds (declare (notinline foo))
;;   so that the compiler cannot optimize away recursive calls.  In some lisps,
;;   particularly OpenMCL, this will allow you to see all the calls with trace.
;;
;; (redef-original foo)
;;   Redefines foo with its own definition, and without adding the notinline
;;   declaration.  In other words, this "restores foo to its original version"
;;   which may give you better performance if the compiler chooses to optimize
;;   away recursive calls of foo.
;;
;;
;; Here is an example:
;;
;; ACL2 !> (in-package "ACL2")
;; ACL2 !> (MILAWA::defun fact (x acc)
;;           (declare (xargs :guard (and (natp x)
;;                                       (natp acc))))
;;           (if (zp x)
;;               acc
;;             (fact (- x 1) (* x acc))))
;; ACL2 !> (trace$ fact)
;; ACL2 !> (fact 5 1)
;;
;; 1> (ACL2_*1*_ACL2::FACT 5 1)
;;   2> (FACT 5 1)
;;   <2 (FACT 120)
;; <1 (ACL2_*1*_ACL2::FACT 120)
;; 120
;;
;; ACL2 !> (redef-notinline fact)
;; ACL2 !> (fact 5 1)
;;
;; 1> (ACL2_*1*_ACL2::FACT 5 1)
;;   2> (FACT 5 1)
;;     3> (FACT 4 5)
;;       4> (FACT 3 20)
;;         5> (FACT 2 60)
;;           6> (FACT 1 120)
;;             7> (FACT 0 120)
;;             <7 (FACT 120)
;;           <6 (FACT 120)
;;         <5 (FACT 120)
;;       <4 (FACT 120)
;;     <3 (FACT 120)
;;   <2 (FACT 120)
;; <1 (ACL2_*1*_ACL2::FACT 120)
;; 120
;;
;; ACL2 !> (redef-original fact)
;; ACL2 !> (fact 5 1)
;;
;; 1> (ACL2_*1*_ACL2::FACT 5 1)
;;   2> (FACT 5 1)
;;   <2 (FACT 120)
;; <1 (ACL2_*1*_ACL2::FACT 120)
;; 120

(defun redef-notinline-fn (f notinlinep)
   (declare (ignore f notinlinep)
            (xargs :guard t))
   nil)

(defttag redef-notinline)

(progn!
 (set-raw-mode t)
 (defun redef-notinline-fn (f notinlinep)
   (let* ((state *the-live-state*)
          (world   (w state))
          (def     (assoc f (get-acl2-defun-entries world))))
     (if (not def)
         (cw "redef-notinline-fn: attempting to redefine ~x0, which wasn't introduced with MILAWA::defun.~%" f)
       (let* ((formals (second def))
              (new-def (if notinlinep
                           `(defun ,f ,formals
                              ,@(cons `(declare (notinline ,f)) (cddr def)))
                         `(defun ,f ,formals
                            ,@(cddr def)))))
         (eval new-def)
         nil)))))

(defmacro redef-original (f)
  `(redef-notinline-fn ',f nil))

(defmacro redef-notinline (f)
  `(redef-notinline-fn ',f t))



