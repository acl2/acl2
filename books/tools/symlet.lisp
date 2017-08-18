; let-syms/symlet -- hack to replace symbols with expressions
; Copyright (C) 2017 Centaur Technology
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





(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)



(defmacro let-syms (bindings term)
  (sublis (pairlis$ (strip-cars bindings)
                    (strip-cars (strip-cdrs bindings)))
          term))

(acl2::def-b*-binder symlet
  :body
  (cond ((and (eql (len acl2::args) 1)
              (eql (len acl2::forms) 1))
         `(let-syms
           ((,(car acl2::args) ,(car acl2::forms)))
           ,acl2::rest-expr))

        ((and (acl2::doublet-listp acl2::args) (not acl2::forms))
         `(let-syms ,acl2::args ,acl2::rest-expr))

        (t
         (er hard? 'symlet "Symlet takes either exactly 1 argument and 1 ~
                            form, or a doublet-list as arguments and no form"))))
