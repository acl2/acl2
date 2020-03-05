; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FGL")

;; This includes just the thm/defthm-producing macros, so that books can
;; include the rest of FGL locally and just include this book nonlocally in
;; order to have their def-fgl-thms exported.

(include-book "std/alists/alist-defuns" :dir :system)

(defun fgl-thm-fn (args)
  (declare (xargs :mode :program))
  (let* ((concl (if (keywordp (car args))
                    (cadr (assoc-keyword :concl args))
                  (car args)))
         (args (if (keywordp (car args))
                   args
                 (cdr args)))
         (body (let ((look (assoc-keyword :hyp args)))
                 (if look
                     `(implies ,(cadr look) ,concl)
                   concl)))
         (rule-classes (let ((look (assoc-keyword :rule-classes args)))
                         (and look
                              `(:rule-classes ,(cadr look)))))
         (hints (cadr (assoc-keyword :hints args))))
    `(thm
      ,body
      :hints (,@hints
              '(:clause-processor expand-an-implies-cp)
              '(:clause-processor (fgl-interp-cp clause (default-fgl-config . ,args) interp-st state)))
      ,@rule-classes)))

(defmacro fgl-thm (&rest args)
  (fgl-thm-fn args))

(defun def-fgl-thm-fn (name args)
  (declare (xargs :mode :program))
  `(defthm ,name
     . ,(cdr (fgl-thm-fn args))))

(defmacro def-fgl-thm (name &rest args)
  (def-fgl-thm-fn name args))


(defun fgl-param-thm-cases (param-bindings param-hyp)
  (if (atom param-bindings)
      nil
    (cons (list (msg "Case: ~x0" (caar param-bindings))
                `(let ,(pairlis$ (alist-keys (caar param-bindings))
                                 (pairlis$ (kwote-lst (alist-keys (alist-vals (caar param-bindings))))
                                           nil))
                   ,param-hyp))
          (fgl-param-thm-cases (cdr param-bindings) param-hyp))))


(defun fgl-param-thm-fn (args)
  (declare (xargs :mode :program))
  (let* ((concl (if (keywordp (car args))
                    (cadr (assoc-keyword :concl args))
                  (car args)))
         (args (if (keywordp (car args))
                   args
                 (cdr args)))
         (body (let ((look (assoc-keyword :hyp args)))
                 (if look
                     `(implies ,(cadr look) ,concl)
                   concl)))
         (rule-classes (let ((look (assoc-keyword :rule-classes args)))
                         (and look
                              `(:rule-classes ,(cadr look)))))
         (hints (cadr (assoc-keyword :hints args))))
    `(thm
      ,body
      :hints (,@hints
              (fgl-casesplit :cases
                             (fgl-param-thm-cases
                              ,(cadr (assoc-keyword :param-bindings args))
                              ',(cadr (assoc-keyword :param-hyp args)))
                             :split-params ,(cadr (assoc-keyword :split-params args))
                             :solve-params ,(cadr (assoc-keyword :solve-params args))
                             :split-concl-p ,(cadr (assoc-keyword :split-concl-p args))
                             :repeat-concl-p ,(cadr (assoc-keyword :repeat-concl-p args)))
              '(:clause-processor (fgl-interp-cp clause (default-fgl-config . ,args) interp-st state)))
      ,@rule-classes)))

(defmacro fgl-param-thm (&rest args)
  (fgl-param-thm-fn args))

(defun def-fgl-param-thm-fn (name args)
  (declare (xargs :mode :program))
  `(defthm ,name
     . ,(cdr (fgl-param-thm-fn args))))

(defmacro def-fgl-param-thm (name &rest args)
  (def-fgl-param-thm-fn name args))
                         
            
