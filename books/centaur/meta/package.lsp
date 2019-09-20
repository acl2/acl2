; Centaur Meta-reasoning Library
; Copyright (C) 2019 Centaur Technology
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
(include-book "centaur/fty/portcullis" :dir :system)

(defpkg "CMR"
  (append (set-difference-eq std::*std-exports*
                             '(std::defalist std::deflist std::defenum))
          *standard-acl2-imports*
          '(b* list-fix list-equiv
             defxdoc defsection
             lnfix
             alist-keys alist-vals
             def-ruleset def-ruleset! add-to-ruleset add-to-ruleset!
             a b c d e f g h i j k l m n o p q r s v x y z
             pseudo-var pseudo-var-p pseudo-var-fix pseudo-var-equiv
             pseudo-fn pseudo-fn-p pseudo-fn-fix pseudo-fn-equiv
             pseudo-lambda pseudo-lambda-p pseudo-lambda-fix pseudo-lambda-equiv
             pseudo-fnsym pseudo-fnsym-p pseudo-fnsym-fix pseudo-fnsym-equiv
             pseudo-term pseudo-term-kind pseudo-term-case
             pseudo-term-fix pseudo-term-equiv pseudo-term-count
             pseudo-term-list pseudo-term-list-fix pseudo-term-list-equiv pseudo-term-list-count
             pseudo-term-null
             pseudo-term-quote pseudo-term-quote->val
             pseudo-term-var pseudo-term-var->name
             pseudo-term-fncall pseudo-term-fncall->fn
             pseudo-term-lambda pseudo-term-lambda->formals pseudo-term-lambda->body pseudo-term-lambda->fn
             pseudo-term-call pseudo-term-call->fn pseudo-term-call->args
             pseudo-term-const
             
             base-ev base-ev-list defthm-base-ev-flag
             pair-vars
             eval-alists-agree eval-alists-agree-bad-guy eval-alists-agree-by-bad-guy
             eval-alist-equiv eval-alist-equiv-bad-guy eval-alist-equiv-by-bad-guy

             def-b*-binder args forms rest-expr

             remove-non-symbols remove-corresp-non-symbols

             set-equiv repeat

             hq

             std::defret-mutual
             fty::deffixtype
             fty::deffixequiv
             fty::deffixequiv-mutual
             fty::deffixcong
             fty::defalist
             fty::defmap
             fty::deflist
             fty::defprod
             fty::deftypes
             fty::deftagsum
             fty::defflexsum
             fty::defenum

             disjoin conjoin conjoin-clauses clauses-result)))
