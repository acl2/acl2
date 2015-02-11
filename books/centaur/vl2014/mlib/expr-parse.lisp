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
(include-book "print-warnings")
(include-book "../loader/lexer/lexer")
(include-book "../loader/parser/expressions")
(include-book "../loader/parser/error")
(local (include-book "../util/arithmetic"))

(defsection vl-parse-expr-from-str
  :parents (mlib)
  :short "Try to parse a Verilog expression from an ACL2 string."

  :long "<p>It is occasionally convenient to parse Verilog expressions from
strings, for instance in @(see acl2::symbolic-test-vectors) we want to let the
user write Verilog-style hierarchical identifiers to describe the wires they
are interested in.</p>

<p>@(call vl-parse-expr-from-str) returns a @(see vl-expr-p) or @('nil') to
signal failure.</p>

<p>We expect that @('str') contains <b>exactly one</b> Verilog expression.  We
will fail if this isn't the case, or if any part of the lexing/parsing process
fails or produces warnings.  In these cases we will print warning messages to
standard output, but there's no programmatic way to extract the warnings.</p>

<p>We have arbitrarily decided not to preprocess the string.  This means you
can't use @('`ifdef') stuff or @('`defines').  However, comments and whitespace
are tolerated and ignored.</p>

<p>We don't transform the expression at all.  This means, for instance, that if
you parse an expression like \"foo[3-1:0]\" then it'll still have the subtract
there.  Furthermore, we don't know what module the expression belongs in, so it
won't be sized, may refer to invalid wires, etc.</p>"

  (defund vl-parse-expr-from-str (str)
    (declare (xargs :guard (stringp str)))
    (b* ((echars (vl-echarlist-from-str str))

         ((mv successp tokens warnings) (vl-lex echars
                                                :config *vl-default-loadconfig*
                                                :warnings nil))
         ((unless successp)
          (cw "; vl-parse-expr-from-str: Lexing failed for ~s0.~%" str))
         ((when warnings)
          (vl-cw-ps-seq
           (vl-println "Warnings from VL-PARSE-EXPR-FROM-STR:")
           (vl-print-warnings warnings))
          (cw "; vl-parse-expr-from-str: Lexer warnings for ~s0.~%" str))

         ((mv tokens ?cmap) (vl-kill-whitespace-and-comments tokens))
         (pstate (make-vl-parsestate :warnings nil))
         ((acl2::local-stobjs tokstream) (mv val tokstream))
         (tokstream (vl-tokstream-update-tokens tokens))
         (tokstream (vl-tokstream-update-pstate pstate))
         ((mv err val tokstream)
          (vl-parse-expression :config *vl-default-loadconfig*))
         ((when err)
          (vl-report-parse-error err tokens)
          (cw "; vl-parse-expr-from-str: Parsing failed for ~s0.~%" str)
          (mv nil tokstream))
         ((vl-parsestate pstate) (vl-tokstream->pstate))
         ((when pstate.warnings)
          (vl-cw-ps-seq
           (vl-println "Warnings from VL-PARSE-EXPR-FROM-STR:")
           (vl-print-warnings pstate.warnings))
          (cw "; vl-parse-expr-from-str: Parser warnings for ~s0." str)
          (mv nil tokstream))
         ((when (vl-tokstream->tokens))
          (cw "; vl-parse-expr-from-str: Content remains after parsing an ~
                 expression from the string.~% ~
                 - Original string: ~s0~% ~
                 - First expr: ~s1~% ~
                 - Remaining after parse: ~s2~%"
              str
              (vl-pps-expr val)
              (vl-tokenlist->string-with-spaces (vl-tokstream->tokens)))
          (mv nil tokstream)))
      (mv val tokstream)))

  (local (in-theory (enable vl-parse-expr-from-str)))

  (defthm vl-expr-p-of-vl-parse-expr-from-string
    (equal (vl-expr-p (vl-parse-expr-from-str str))
           (if (vl-parse-expr-from-str str)
               t
             nil)))

  (local (include-book "expr-tools"))

  (local (assert!
          (b* ((expr (vl-parse-expr-from-str "foo[3]"))
               ((unless (and expr
                             (vl-expr-p expr)
                             (not (vl-atom-p expr))
                             (equal (vl-nonatom->op expr) :vl-index)))
                (er hard? '|foo[3]| "Expected index into foo"))
               ((list from idx) (vl-nonatom->args expr)))
            (and (vl-idexpr-p from)
                 (equal (vl-idexpr->name from) "foo")
                 (vl-expr-resolved-p idx)
                 (equal (vl-resolved->val idx) 3)))))

  (local (assert!
          (b* ((expr (vl-parse-expr-from-str "foo[3:0] /* comments are okay */
// so are these

// and whitespace"))
               ((unless (and expr
                             (vl-expr-p expr)
                             (not (vl-atom-p expr))
                             (equal (vl-nonatom->op expr) :vl-select-colon)))
                (er hard? '|foo[3:0]| "Expected partselect"))
               ((list from msb lsb) (vl-nonatom->args expr)))
            (and (vl-idexpr-p from)
                 (equal (vl-idexpr->name from) "foo")
                 (vl-expr-resolved-p msb)
                 (equal (vl-resolved->val msb) 3)
                 (vl-expr-resolved-p lsb)
                 (equal (vl-resolved->val lsb) 0)))))

  (local (assert!
          (b* ((expr (vl-parse-expr-from-str "foo[3:0], bar")))
            ;; Shouldn't work, more than one expr
            (not expr))))

  (local (assert!
          (b* ((expr (vl-parse-expr-from-str "foo[")))
            ;; Shouldn't work, invalid syntax
            (not expr))))

  (local (assert!
          (b* ((expr (vl-parse-expr-from-str "foo;")))
            ;; Shouldn't work, extra junk after the expression (the semicolon)
            (not expr)))))

