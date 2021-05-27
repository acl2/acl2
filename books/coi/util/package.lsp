; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
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

#!ACL2 (in-package "ACL2")

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(defpkg "COI-DEBUG" nil)

(defpkg "DEF" nil)

(defpkg "DEFUN"
  (append '(acl2::val acl2::met)
          *acl2-exports*
          *common-lisp-symbols-from-main-lisp-package*))

(defpkg "GENSYM" nil)

(defpkg "RULE-SETS"
  (remove 'assert
  (remove 'version
	  (append *acl2-exports*
		  *common-lisp-symbols-from-main-lisp-package*))))

(defpkg "TABLE" *acl2-exports*)

(defconst *mv-nth-exports*
  '(met val v0 v1 v2 v3 v4))

(defconst *util-exports*
  (append *mv-nth-exports* nil))

(defpkg "TALIST"
  (append '(acl2::*t* acl2::*nil* acl2::val acl2::met acl2::and-list
            acl2::ts-union acl2::ts-subsetp acl2::ts-intersectp)
          *acl2-exports*
          *common-lisp-symbols-from-main-lisp-package*))

(ld "centaur/fty/package.lsp" :dir :system)
