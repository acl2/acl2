; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2019 Centaur Technology
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
; Original author: Mertcan Temel <mert@utexas.edu>

(in-package "SVL")

(defconst *package-name* "SVL")

(include-book "tools")

(include-book "std/strings/decimal" :dir :system)

;(include-book "std/strings/substrp" :dir :system)

(Include-Book "std/strings/cat-base" :dir :system)

(encapsulate
  nil
  (define strlist-to-str
    ((lst (string-listp lst)))
    (if (atom lst)
        ""
      (string-append (car lst)
                     (strlist-to-str (cdr lst)))))

  (define
    sym-app-fnc (args)
    (if (atom args)
        (if (equal args nil)
            ""
          (b* ((e args))
            (if (string-listp e)
                (strlist-to-str e)
              (if (symbolp e)
                  (symbol-name e)
                (if (stringp e)
                    e
                  (str::intstr (ifix e)))))))
      (string-append
       (string-append
        (b* ((e (car args)))
          (if (string-listp e)
              (strlist-to-str e)
            (if (symbolp e)
                (symbol-name (car args))
              (if (stringp e)
                  e
                (str::intstr (ifix e))))))
        (if (and (consp (cdr args))
                 (not (stringp (car args)))
                 (not (string-listp (car args))))
            "_"
          ""))
       (sym-app-fnc (cdr args)))))

  (define sa-body (args)
    (intern$ (sym-app-fnc args) *package-name*))

  (defmacro sa (&rest args)
    `(intern$
      (sym-app-fnc (list ,@args))
      ,*package-name*)))

(defmacro rw-error-for-svl-run-cycle-module
    (module-name &key (svl-design 'svl-design) (index 'nil))
  `(defthm ,(sa 'svl-run-cycle-error-for module-name index)
     (equal (svl-run-cycle ,module-name
                           delayed-env
                           inputs
                           ,svl-design)
            (progn$
             (hard-error 'rw-error-for-svl-run-cycle
                         "Svl-run-cycle call for ~p0 has slipped through all of
    its rewrite rules with these inputs: ~p1 ~%"
                         `((#\0 . ,,module-name)
                           (#\1 . ,inputs)))
             (hide (svl-run-cycle ,module-name
                                  delayed-env
                                  inputs
                                  ,svl-design))))
     :hints (("Goal"
              :expand (hide (svl-run-cycle ,module-name
                                           delayed-env
                                           inputs
                                           ,svl-design))
              :in-theory (theory 'acl2::minimal-theory)))))
