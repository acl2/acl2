; VL Verilog Toolkit
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

(in-package "VL")
(include-book "blocks")
(include-book "centaur/fty/visitor" :dir :system)
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (std::add-default-post-define-hook :fix))


(defxdoc allexprs
  :parents (mlib)
  :short "Functions for gathering all the expressions used throughout some
module item."

  :long "<p>These functions gather up what we regard as the \"top level\"
expressions used throughout various module items.  That is, consider an
assignment statement such as @('foo = a + b'); the associated list of allexprs
would include two expressions: one for @('foo'), and one for @('a + b').</p>

<p>Note that despite the name \"allexprs\", we actually do not gather
expressions within @('(* foo = bar *)')-style attributes.</p>")

(set-bogus-mutual-recursion-ok t)

(fty::defvisitor-template allexprs-nrev ((x :object)
                                         (nrev))
  :returns (nrev1 (:acc nrev :fix (nrev-fix nrev))
                  ;; (equal nrev1
                  ;;        (append nrev (<type>-allexprs x)))
                  ;; :hints ((and stable-under-simplificationp
                  ;;              '(:expand ((<type>-allexprs x)))))
                  )
  :type-fns ((vl-expr (lambda (x nrev) (nrev-push (vl-expr-fix x) nrev))))
  :field-fns ((atts :skip))
  :fnname-template <type>-allexprs-nrev)

; Added by Matt K. 2/20/2016, pending possible mod by Sol to defvisitor.
(set-bogus-measure-ok t)

(fty::defvisitors vl-allexprs-nrev
  :template allexprs-nrev
  :types (vl-design vl-genblob))


(fty::defvisitor-template allexprs ((x :object))
  :returns (exprs (:join (append exprs1 exprs)
                   :initial nil
                   :tmp-var exprs1)
                  vl-exprlist-p)
  :type-fns ((vl-expr (lambda (x) (list (vl-expr-fix x)))))
  :field-fns ((atts :skip))
  :fnname-template <type>-allexprs
  :reversep t)

(fty::defvisitors vl-ctxelement-allexprs
  :template allexprs
  :types (vl-ctxelement))

(fty::defvisitors vl-allexprs
  :template allexprs
  :types (vl-design vl-genblob))


(fty::defvisitor-template allexprs-nrev ((x :object)
                                         (nrev))
  :returns (nrev1 (:acc nrev :fix (nrev-fix nrev))
                  (equal nrev1
                         (append nrev (<type>-allexprs x)))
                  :hints ((and stable-under-simplificationp
                               '(:expand ((<type>-allexprs x))))))
  :type-fns ((vl-expr (lambda (x nrev) (nrev-push (vl-expr-fix x) nrev))))
  :field-fns ((atts :skip))
  :fnname-template <type>-allexprs-nrev)

(local (in-theory (enable acl2::rcons)))

(with-output :off (event)
  (fty::defvisitors vl-allexprs-nrev
    :template allexprs-nrev
    :types (vl-design vl-genblob)))
