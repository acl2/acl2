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

(defun %defderiv-fn (name world hintsmap omit-okp)
  (declare (xargs :mode :program))
  (let* ((info-entry     (lookup name (dd.get-info-for-%defderiv world)))
         (local-axioms   (second info-entry))
         (local-thms     (third info-entry))
         (soundness-hint (fourth info-entry))
         (name-okp       (ACL2::mksym name '-okp)))
    `(encapsulate
      ()
      (encapsulate
       ()
       ,@(if (or local-axioms local-thms)
             `((local (%enable default
                               ,@(strip-firsts local-axioms)
                               ,@(strip-firsts local-thms))))
           nil)

       (%autoadmit ,name)
       (%noexec ,name)

       (local (%enable default ,name))

       (%autoprove ,(ACL2::mksym name '-under-iff)
                   ;; BOZO globally disable forcing here after implementing
                   ;; a flag in the control structure for it
                   )
       (%autoprove ,(ACL2::mksym 'forcing-logic.appealp-of- name)
                   ,@(cdr (lookup (ACL2::mksym 'forcing-logic.appealp-of- name) hintsmap)))

       (%autoprove ,(ACL2::mksym 'forcing-logic.conclusion-of- name)
                   ,@(cdr (lookup (ACL2::mksym 'forcing-logic.conclusion-of- name) hintsmap)))

       (%autoprove ,(ACL2::mksym 'forcing-logic.proofp-of- name)
                   ,@(cdr (lookup (ACL2::mksym 'forcing-logic.proofp-of- name) hintsmap))))

      ,@(if omit-okp
            nil
          `((%autoadmit ,name-okp)
            (%autoprove ,(ACL2::mksym 'booleanp-of- name-okp)
                        ,@(or (cdr (lookup (ACL2::mksym 'booleanp-of- name-okp) hintsmap))
                              `((%enable default ,name-okp))))
            (%autoprove ,(ACL2::mksym name-okp '-of-logic.appeal-identity)
                        ,@(or (cdr (lookup (ACL2::mksym name-okp '-of-logic.appeal-identity) hintsmap))
                              `((%enable default ,name-okp))))
            (local (%enable default backtracking-logic.formula-atblp-rules))
            (local (%disable default
                             forcing-logic.formula-atblp-rules
                             forcing-lookup-of-logic.function-name-free
                             forcing-logic.term-list-atblp-of-logic.function-args))
            (%autoprove ,(ACL2::mksym 'lemma-1-for-soundness-of- name-okp)
                        (%enable default ,name-okp)
                        ,@(or (cdr (lookup (ACL2::mksym 'lemma-1-for-soundness-of- name-okp) hintsmap))
                              nil))
            (%autoprove ,(ACL2::mksym 'lemma-2-for-soundness-of- name-okp)
                        (%enable default ,name-okp)
                        ,@(or (cdr (lookup (ACL2::mksym 'lemma-2-for-soundness-of- name-okp) hintsmap))
                              nil))
            (%autoprove ,(ACL2::mksym 'forcing-soundness-of- name-okp)
                        ,@(or (cdr (lookup (ACL2::mksym 'forcing-soundness-of- name-okp) hintsmap))
                              `((%enable default
                                         ,(ACL2::mksym 'lemma-1-for-soundness-of- name-okp)
                                         ,(ACL2::mksym 'lemma-2-for-soundness-of- name-okp))
                                (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                                                 (x (,name ,@soundness-hint))))
                                (%auto :strategy (cleanup split crewrite))
                                (%enable default ,name-okp)
                                (%auto :strategy (cleanup split crewrite)))
                              )))))))

(defmacro %defderiv (name &key hintsmap omit-okp)
  `(ACL2::make-event (%defderiv-fn ',name (ACL2::w ACL2::state) ',hintsmap ',omit-okp)))

(defmacro %deftheorem (name)
  ;; We don't need to bother with proving the theorems.  But, we do want to
  ;; have the theorem functions available.
  `(encapsulate
    ()
    (%autoadmit ,name)
    (%noexec ,name)))
