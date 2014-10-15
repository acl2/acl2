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

(in-package "MILAWA")

(ACL2::defttag hons-proofs)

(ACL2::progn!
 (ACL2::set-raw-mode t)

 (ACL2::defun logic.function (name args)
              (ACL2::hons name args))

 (ACL2::defun logic.lambda (xs b ts)
              (ACL2::hons (ACL2::hist 'lambda xs b) ts))

 (ACL2::defun logic.pequal (a b)
              (ACL2::hist 'pequal* a b))

 (ACL2::defun logic.por (a b)
              (ACL2::hist 'por* a b))

 (ACL2::defun logic.pnot (a)
              (ACL2::hist 'pnot* a))

 (ACL2::defun logic.appeal (method conclusion subproofs extras)
              (if extras
                  (ACL2::hist method conclusion subproofs extras)
                (if subproofs
                    (ACL2::hist method conclusion subproofs)
                  (ACL2::hist method conclusion))))

 (ACL2::defun logic.appeal-identity (x)
              (if (consp x)
                  x
                (ACL2::hons nil nil)))

 (ACL2::defun hons-lookup (key map)
              (ACL2::hons-get key map))

 (ACL2::defun hons-update (key val map)
              (ACL2::hons-acons key val map))

 (ACL2::defun rw.eqtrace (method iffp lhs rhs subtraces)
              (ACL2::hons (ACL2::hons lhs rhs)
                          (ACL2::hons iffp
                                      (ACL2::hons method subtraces))))

 (ACL2::defun rw.trace (method hypbox lhs rhs iffp subtraces extras)
              (ACL2::hons (ACL2::hons method rhs)
                          (ACL2::hons (ACL2::hons lhs iffp)
                                      (ACL2::hons hypbox
                                                  (ACL2::hons extras subtraces)))))

 (ACL2::defun rw.ftrace (rhs fgoals)
              (ACL2::hons rhs fgoals)))








