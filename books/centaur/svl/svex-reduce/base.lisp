
; Copyright (C) 2023 Intel Corporation
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
;
; Original author: Mertcan Temel <mert.temel@intel.com>

(in-package "SVL")

(include-book "centaur/sv/svex/eval" :dir :system)
(include-book "centaur/sv/svex/eval-dollar" :dir :system)
(include-book "tools/templates" :dir :system)

(defun hons-list-macro (acl2::lst)
  (declare (xargs :guard t))
  (if (consp acl2::lst)
      (cons 'hons
            (cons (car acl2::lst)
                  (cons (hons-list-macro (cdr acl2::lst))
                        nil)))
    nil))

(DEFMACRO hons-LIST (&REST ARGS)
  (hons-list-macro ARGS))

(defmacro svex-eval-lemma-tmpl (form)
  `(progn
     ,form
     ,(acl2::template-subst
       form
       :atom-alist '((svex-eval . svex-eval$)
                     (svex-apply . svex-apply$)
                     (svexlist-eval . svexlist-eval$)
                     (svex-alist-eval . svex-alist-eval$))
       :str-alist '(("SVEX-EVAL" . "SVEX-EVAL$")
                    ("SVEX-APPLY" . "SVEX-APPLY$")
                    ("SVEXLIST-EVAL" . "SVEXLIST-EVAL$")
                    ("SVEX-ALIST-EVAL" . "SVEX-ALIST-EVAL$"))
       :pkg-sym 'pkg
       )
     ))
