; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(in-package "GL")

(include-book "glcp-geval")
(include-book "rewrite-tables")

(acl2::def-unify glcp-generic-geval-ev glcp-generic-geval-ev-alist)
(acl2::def-meta-extract glcp-generic-geval-ev glcp-generic-geval-ev-lst)

(define good-rewrite-rulesp (rules)
  (if (atom rules)
      t
    (and (glcp-generic-geval-ev-theoremp (acl2::rewrite-rule-term (car rules)))
         (good-rewrite-rulesp (cdr rules)))))


(acl2::def-functional-instance good-rewrite-rulesp-of-fn-branch-merge-rules
  mextract-good-rewrite-rulesp-of-fn-branch-merge-rules
  ((acl2::mextract-ev glcp-generic-geval-ev)
   (acl2::mextract-ev-lst glcp-generic-geval-ev-lst)
   (acl2::mextract-ev-falsify glcp-generic-geval-ev-falsify)
   (acl2::mextract-global-badguy glcp-generic-geval-ev-meta-extract-global-badguy)
   (mextract-good-rewrite-rulesp good-rewrite-rulesp))
  :hints((and stable-under-simplificationp
              '(:in-theory (enable glcp-generic-geval-ev-of-fncall-args
                                   glcp-generic-geval-ev-of-nonsymbol-atom
                                   good-rewrite-rulesp)))))

(acl2::def-functional-instance good-rewrite-rulesp-of-fn-rewrite-rules
  mextract-good-rewrite-rulesp-of-fn-rewrite-rules
  ((acl2::mextract-ev glcp-generic-geval-ev)
   (acl2::mextract-ev-lst glcp-generic-geval-ev-lst)
   (acl2::mextract-ev-falsify glcp-generic-geval-ev-falsify)
   (acl2::mextract-global-badguy glcp-generic-geval-ev-meta-extract-global-badguy)
   (mextract-good-rewrite-rulesp good-rewrite-rulesp))
  :hints((and stable-under-simplificationp
              '(:in-theory (enable glcp-generic-geval-ev-of-fncall-args
                                   glcp-generic-geval-ev-of-nonsymbol-atom
                                   good-rewrite-rulesp)))))
