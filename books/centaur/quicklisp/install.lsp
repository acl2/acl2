; ACL2 Quicklisp Interface
; Copyright (C) 2008-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

; This just does the initial quicklisp install.  It should get run when the
; Makefile tries to build setup.lisp

(make-event
 (let ((cbd (cbd)))
   `(defconst *cbd* ',cbd)))

;; Horrible junk to try to get ASDF not to put its stuff here, in the
;; quicklisp/asdf-home directory, rather than in the user's home directory in
;; places like ~/.cache and ~/.config.
(setenv$ "XDG_CONFIG_HOME" (concatenate 'string *cbd* "asdf-home/config"))
(setenv$ "XDG_DATA_HOME"   (concatenate 'string *cbd* "asdf-home/data"))
(setenv$ "XDG_CACHE_HOME"  (concatenate 'string *cbd* "asdf-home/cache"))

:q
(in-package "CL-USER")
(load "quicklisp.lsp")

(quicklisp-quickstart:install :path (concatenate 'string acl2::*cbd* "inst"))


#|| 
;; Seeing available versions, instructions up at
;;   http://blog.quicklisp.org/2011/08/going-back-in-dist-time.html

(ql-dist:available-versions (ql-dist:dist "quicklisp"))

||#

(setq ql-util::*do-not-prompt* t)
(ql-dist:install-dist
 "http://beta.quicklisp.org/dist/quicklisp/2014-06-16/distinfo.txt"
;; "http://beta.quicklisp.org/dist/quicklisp/2014-01-13/distinfo.txt"
 :replace t)

(quit)
