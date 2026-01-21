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
; Original author: Mayank Manjrekar <mayank.manjrekar2@arm.com>

(in-package "COMPRESS")

(include-book "tools/match-tree" :dir :system)

(defun treematch-when-fn (x pat when nomatch-body match-body)
  (let* ((allvars (remove-duplicates-eq (match-tree-binders pat)))
         (vars! (remove-duplicates-eq (match-tree-!vars pat nil)))
         (vars? (set-difference-eq allvars vars!)))
    `(b* (((mv _treematch-ok ?_treematch-alist)
           (match-tree ',pat ,x ,(match-tree-initial-alist-term vars!)))
          ((assocs . ,(prefix-?-vars vars?)) _treematch-alist)
          ((when (not (and _treematch-ok
                           ,when)))
           (check-vars-not-free
            (_treematch-ok _treematch-alist)
            ,nomatch-body)))
      (check-vars-not-free
       (_treematch-ok _treematch-alist)
       ,match-body))))

(acl2::def-b*-binder unless-match-when
  :decls ((declare (xargs :guard (or (and (equal (len args) 4)
                                          (keywordp (caddr args))
                                          (eq (caddr args) :when))
                                     (equal (len args) 2)))))
  :body
  (if (= (len args) 2)
      (acl2::treematch-fn (car args) (cadr args)
                    `(progn$ . ,acl2::forms)
                    acl2::rest-expr)
    (treematch-when-fn (car args) (cadr args) (cadddr args)
                     `(progn$ . ,acl2::forms)
                     acl2::rest-expr)))

(acl2::def-b*-binder when-match-when
  :decls ((declare (xargs :guard (or (and (equal (len args) 4)
                                          (keywordp (caddr args))
                                          (eq (caddr args) :when))
                                     (equal (len args) 2)))))
  :body
  (if (= (len args) 2)
      (acl2::treematch-fn (car args) (cadr args)
                    acl2::rest-expr
                    `(progn$ . ,acl2::forms))
    (treematch-when-fn (car args) (cadr args) (cadddr args)
                     acl2::rest-expr
                     `(progn$ . ,acl2::forms))))

(defun treematch*-when-fn (x pats)
  (cond ((atom pats) nil)
        ((eq (caar pats) '&) `(progn$ . ,(cdar pats)))
        ((and (equal (len (car pats)) 4)
              (keywordp (cadar pats))
              (eq (cadar pats) :when))
         (treematch-when-fn x (caar pats) (caddar pats)
                            (treematch*-when-fn x (cdr pats))
                            `(progn$ . ,(cdddar pats))))
        (t (acl2::treematch-fn x (caar pats)
                         (treematch*-when-fn x (cdr pats))
                         `(progn$ . ,(cdar pats))))))

(defmacro treematch-when (x &rest pats)
  (if (atom x)
      (treematch*-when-fn x pats)
    (let ((var (acl2::pack x)))
      `(b* ((,var ,x))
        ,(treematch*-when-fn var pats)))))
