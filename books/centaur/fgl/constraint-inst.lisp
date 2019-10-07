; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(include-book "bfr")

(local (std::add-default-post-define-hook :fix))

(defprod constraint-instance
  ((thmname symbolp)
   (subst fgl-object-bindings-p))
  :layout :tree)

(fty::deflist constraint-instancelist :elt-type constraint-instance :true-listp t)


(define constraint-instance-bfrlist ((x constraint-instance-p))
  (fgl-object-bindings-bfrlist (constraint-instance->subst x)))

(define constraint-instancelist-bfrlist ((x constraint-instancelist-p))
  (if (atom x)
      nil
    (append (constraint-instance-bfrlist (car x))
            (constraint-instancelist-bfrlist (cdr x))))
  ///
  (defthm constraint-instancelist-bfrlist-of-append
    (equal (constraint-instancelist-bfrlist (append a b))
           (append (constraint-instancelist-bfrlist a)
                   (constraint-instancelist-bfrlist b)))
    :hints(("Goal" :in-theory (enable constraint-instancelist-bfrlist)))))
