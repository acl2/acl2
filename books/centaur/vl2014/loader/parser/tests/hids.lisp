; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "base")
(include-book "../expressions")
(include-book "../../../mlib/hid-tools")

(defparser-top vl-parse-expression :resulttype vl-expr-p)

; Note: see expressions.lisp for general tests of expression parsing, including
; many tests of HID parsing.
;
; In this file our focus is a little bit different.  In short, the
; representation of hierarchical identifier expressions, index operations, and
; scope operations is quite tricky.  To deal with this complexity, the
; hid-tools file introduces some abstract functions for working with HIDs.
;
; In this file, we try to ensure that our abstract functions in hid-tools are
; going to properly recognize the things that our parser produces.  In other
; words, this isn't necessarily so much a test of our parser, as it is a test
; of our understanding of the kinds of HIDs we're going to get out of the
; parser.

(define ezparse ((str stringp)
                 &key
                 ((config vl-loadconfig-p) '*vl-default-loadconfig*))
  :returns (expr vl-expr-p)
  (b* ((echars (vl-echarlist-from-str str))
       ((mv successp tokens warnings)
        (vl-lex echars
                :config config
                :warnings nil))
       ((unless successp)
        (raise "FAILURE: didn't even lex the input successfully.")
        *vl-default-expr*)
       ((mv tokens ?cmap) (vl-kill-whitespace-and-comments tokens))
       (pstate            (make-vl-parsestate :warnings warnings))
       ((mv errmsg val tokens ?pstate)
        (vl-parse-expression-top :tokens tokens
                                 :pstate pstate
                                 :config config))
       ((when errmsg)
        (raise "Parsing error: ~x0." errmsg)
        *vl-default-expr*)
       ((when (consp tokens))
        (raise "Extra input after the expression: ~s0"
               (vl-tokenlist->string-with-spaces tokens))
        *vl-default-expr*))
    val))

(assert! (vl-hidexpr-p (ezparse "foo.bar")))
(assert! (vl-hidexpr-p (ezparse "foo[1].bar")))
(assert! (vl-hidexpr-p (ezparse "foo[1][2].bar")))
(assert! (not (vl-hidexpr-p (ezparse "foo.bar[1]"))))
(assert! (not (vl-hidexpr-p (ezparse "foo.bar[1][2]"))))

(assert! (b* ((expr (ezparse "foo.bar[1]"))
              ((when (vl-atom-p expr))
               nil)
              ((vl-nonatom expr)))
           (and (vl-op-equiv expr.op :vl-index)
                (vl-hidexpr-p (first expr.args)))))

(assert! (b* ((expr (ezparse "foo.bar[1][2]"))
              ((when (vl-atom-p expr))
               nil)
              ((vl-nonatom expr))
              ((unless (vl-op-equiv expr.op :vl-index))
               nil)
              ((list from two) expr.args))
           (and (vl-expr-resolved-p two)
                (eql (vl-resolved->val two) 2)
                (not (vl-atom-p from))
                (vl-op-equiv (vl-nonatom->op from) :vl-index)
                (b* (((list foobar one) (vl-nonatom->args from)))
                  (and (vl-expr-resolved-p one)
                       (eql (vl-resolved->val one) 1)
                       (vl-hidexpr-p foobar)
                       (equal (vl-flatten-hidexpr foobar) "foo.bar"))))))

#||

next: packaged hids

(assert! (not (vl-hidexpr-p (ezparse "pkg::foo.bar"))))

(ezparse "pkg::foo.bar")
(ezparse "pkg::foo.bar[1]")
(ezparse "pkg::foo.bar[1][2]")
||#
