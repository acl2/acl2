; Centaur BED Library
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>

(include-book "std/portcullis" :dir :system)

(defpkg "BED"
  (set-difference-eq
   (union-eq std::*std-exports*
             set::*sets-exports*
             acl2::*acl2-exports*
             acl2::*common-lisp-symbols-from-main-lisp-package*
             '(set::enable
               set::disable
               set::e/d
               str::cat
               str::natstr
               str::implode
               str::explode
               enable*
               disable*
               e/d*

               b*

               bitp
               bfix
               lnfix
               lifix
               lbfix
               nat-equiv
               int-equiv
               bit-equiv
               bool->bit

               b-not
               b-eqv
               b-xor
               b-ior
               b-nor
               b-and
               b-nand
               b-orc2
               b-orc1
               b-andc1
               b-andc2

               logcar
               logcdr
               loghead
               logtail
               arith-equiv-forwarding

               aig-eval
               aig-env-lookup
               aig-not
               aig-iff
               aig-xor
               aig-and
               aig-or
               aig-ite
               aig-vars
               aig-vars-1pass
               aig-atom-p
               aig-var-p
               ))
   '(acl2::union
     acl2::delete
     acl2::enable
     acl2::disable
     acl2::e/d
     )))
