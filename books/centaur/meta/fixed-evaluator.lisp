;; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
;; SPDX-License-Identifier: BSD-3-Clause
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:

;; o Redistributions of source code must retain the above copyright
;;   notice, this list of conditions and the following disclaimer.

;; o Redistributions in binary form must reproduce the above copyright
;;   notice, this list of conditions and the following disclaimer in the
;;   documentation and/or other materials provided with the distribution.

;; o Neither the name of the copyright holder nor the names of
;;   its contributors may be used to endorse or promote products derived
;;   from this software without specific prior written permission.

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;; Author: Sol Swords <sol.swords@arm.com>

(in-package "CMR")


(defun defeval-form-to-fixed (x)
  (case-match x
    (('encapsulate &
       inhibit
       base-theory
       ('local ('defun-nx apply-fn . apply-def))
       ('local ('mutual-recursion . eval-def))
       ('local ('in-theory . disables))
       ('local ('defthm . thm1))
       ('local ('defthm . thm2))
       ('local ('defthm . thm3))
       ('local ('defthm . thm4))
       . rest)
     `(encapsulate nil
        ,inhibit
        ,base-theory
        ;; most important: make the apply and eval defs nonlocal.
        (defun-nx ,apply-fn . ,apply-def)
        (mutual-recursion . ,eval-def)
        ;; we also want to leave the evaluator and apply definitions disabled,
        ;; and export the helper theorems about evfn-lst.
        (in-theory . ,disables)
        (defthm . ,thm1)
        (defthm . ,thm2)
        (defthm . ,thm3)
        (defthm . ,thm4)
        . ,rest))
    (& (er hard? 'defevaluator-fixed "Unexpected form of defevaluator expansion!"))))


(defun defevaluator-fixed-form (evfn evfn-lst namedp fn-args-lst)
  (declare (xargs :mode :program))
  (let* ((form1 (acl2::defevaluator-form evfn evfn-lst namedp fn-args-lst))
         (form2 (subst (intern-in-package-of-symbol
                        (concatenate 'string (symbol-name evfn) "-APPLY")
                        evfn)
                       'acl2::apply-for-defevaluator
                       form1)))
    (defeval-form-to-fixed form2)))


(defmacro defevaluator-fixed (evfn evfn-lst fn-args-lst &key namedp)
  (defevaluator-fixed-form evfn evfn-lst namedp fn-args-lst))


;; test
(local (defevaluator-fixed foo-ev foo-ev-lst
         ((cons a b)
          (equal x y)
          (if a b c)
          (implies x y)
          (binary-+ a b)
          (unary-- x))
         :namedp t))
