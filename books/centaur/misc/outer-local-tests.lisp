; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>


(in-package "ACL2")




(local
 (progn

   (include-book "outer-local")

   (defmacro fn-exists? (flg fn)
     `(make-event
       (let ((fn ',fn) (flg ,flg))
         (if (iff (eq :none (getprop fn 'formals
                                     :none 'current-acl2-world (w state)))
                  flg)
             (er hard? 'fn-exists
                 (if flg "~x0 should exist but doesn't"
                   "~x0 shouldn't exist but does")
                 fn)
           `(value-triple ',fn)))))


   (encapsulate nil
     (with-outer-locals
       (with-outer-locals
         (outer-local (defun xa () nil))
         (outer-local :level 2
                      (defun xb () nil)
                      (outer-local
                       (defun xc () nil))))
       (outer-local (defun xd () nil))
       (fn-exists? t xa)
       (fn-exists? t xb)
       (fn-exists? t xc)
       (fn-exists? t xd))
     (fn-exists? nil xa)
     (fn-exists? t xb)
     (fn-exists? nil xc)
     (fn-exists? t xd))

   (fn-exists? nil xa)
   (fn-exists? nil xb)
   (fn-exists? nil xc)
   (fn-exists? nil xd)))
