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
(include-book "../expr")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))

(defxdoc lvalues
  :parents (mlib)
  :short "Tools for gathering up lvalues and checking the well-formedness of
expressions in lvalue positions.")

(local (xdoc::set-default-parents lvalues))

(defines vl-expr-net-lvalue-p
  :parents (lvalues vl-parse-net-lvalue-2012)
  :short "Recognizer an expression that is OK for a SystemVerilog-2012
          @('net_lvalue')."

  :long "<p>Here's the grammar for @('net_lvalue'):</p>

         @({
              net_lvalue ::= ps_or_hierarchical_net_identifier constant_select
                           | '{' net_lvalue { ',' net_lvalue } '}'
                           | [ assignment_pattern_expression_type ] assignment_pattern_net_lvalue
         })

         <p>The first production essentially corresponds to our notion of an
         index expression and the second to concatenation.  The third
         production is quite similar to @('assignment_pattern_expression'),
         which can be a valid expression @('primary'),</p>

         @({
              assignment_pattern_expression ::= [ assignment_pattern_expression_type ] assignment_pattern
         })

         <p>Except that here we have an @('assignment_pattern_net_lvalue')
         instead of an @('assignment_pattern').  So let's compare:</p>

         @({
              assignment_pattern_net_lvalue ::= QUOTE '{' net_lvalue { ',' net_lvalue } '}'

              assignment_pattern ::= QUOTE '{' expression { ',' expression } '}'
                                   | QUOTE '{' structure_pattern_key ...
                                   | QUOTE '{' array_pattern_key ...
                                   | QUOTE '{' constant_expression '{' ...
         })

         <p>So essentially the grammar is just trying to (1) rule out the
         fancier structure/array/replication assignment patterns while still
         allowing basic positional assignment patterns, and (2) ensure that all
         of the expressions within the assignment pattern here happen to be
         good @('net_lvalue')s.  We'll recognize these expressions with @(see
         vl-expr-net-lvalue-p).</p>"

  (define vl-expr-net-lvalue-p ((x vl-expr-p))
    :returns bool
    :measure (vl-expr-count x)
    (vl-expr-case x
      :vl-index t
      :vl-concat (vl-exprlist-net-lvalues-p x.parts)
      :vl-pattern (and (not x.pat)
                       (vl-assignpat-net-lvalue-p x.pat))
      :otherwise nil))

  (define vl-assignpat-net-lvalue-p ((x vl-assignpat-p))
    :returns bool
    :measure (vl-assignpat-count x)
    (vl-assignpat-case x
      :positional (vl-exprlist-net-lvalues-p x.vals)
      :otherwise nil))

  (define vl-exprlist-net-lvalues-p ((x vl-exprlist-p))
    :returns bool
    :measure (vl-exprlist-count x)
    (or (atom x)
        (and (vl-expr-net-lvalue-p (car x))
             (vl-exprlist-net-lvalues-p (cdr x))))))


(define vl-expr-variable-lvalue-p ((x vl-expr-p))
  :parents (lvalues vl-parse-variable-lvalue-2012)
  :returns bool
  :short "Recognize an expression that is OK for a SystemVerilog-2012
          @('variable_lvalue')."

  :long "<p>Here's the original grammar for @('variable_lvalue').</p>

         @({
              variable_lvalue ::= [ implicit_class_handle '.' | package_scope ] hierarchical_variable_identifier select
                                | '{' variable_lvalue { ',' variable_lvalue } '}'
                                | [ assignment_pattern_expression_type ] assignment_pattern_variable_lvalue
                                | streaming_concatenation
         })

         <p>Footnote 46 applies.  <i>In a @('variable_lvalue') that is assigned
         within a @('sequence_match_item'), any @('select') shall also be a
         @('constant_select').</i> But that's not local to @('variable_lvalue')
         (and for that matter isn't really a syntactic requirement anyway), so
         we don't check that here.</p>

         <p>Footnote 47 also applies.  <i>The streaming_concatenation
         expression here shall not be nested within another
         @('variable_lvalue'), shall not be the target of an increment or
         decrement operator, nor the target of any assignment operator except
         the simple @('=') or nonblocking assignment @('<=') operator.</i> It's
         easy for us to rule out nested streaming concatenations here, but the
         remaining requirements aren't local to @('variable_lvalue') so we
         don't check them here.</p>

         <p>The first production essentially corresponds to our notion of an
         index expression, the second to concatenation.  The third production
         is quite similar to @('assignment_pattern_expression'), which can be a
         valid expression @('primary'),</p>

         @({
              assignment_pattern_expression ::= [ assignment_pattern_expression_type ] assignment_pattern
         })

         <p>Except that here we have an @('assignment_pattern_variable_lvalue')
         instead of an @('assignment_pattern').  So let's compare:</p>

         @({
              assignment_pattern_variable_lvalue ::= QUOTE '{' variable_lvalue { ',' variable_lvalue } '}'

              assignment_pattern ::= QUOTE '{' expression { ',' expression } '}'
                                   | QUOTE '{' structure_pattern_key ...
                                   | QUOTE '{' array_pattern_key ...
                                   | QUOTE '{' constant_expression '{' ...
         })

         <p>So essentially the grammar is just trying to (1) rule out the
         fancier structure/array/replication assignment patterns while still
         allowing basic positional assignment patterns, and (2) ensure that all
         of the expressions within the assignment pattern here happen to be
         good @('variable_lvalue')s.  We'll recognize these expressions with
         @(see vl-expr-variable-lvalue-p).</p>

         <p>Finally, the last production just corresponds to our usual notion
         of streaming concatenation, modulo the nesting restriction, so that's
         about it.</p>

         <p>Comparing all of the above to the story for @('net_lvalue'), I
         think these are exactly the same as @('net_lvalue') except that we
         allow streaming concatenations.</p>"

  ;; All of that for just this.  Sheish.
  (let ((x (vl-expr-fix x)))
    (or (vl-expr-net-lvalue-p x)
        (vl-expr-case x :vl-stream))))



