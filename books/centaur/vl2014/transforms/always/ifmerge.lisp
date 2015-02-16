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
(include-book "conditions")
(include-book "../../mlib/stmt-tools")
(local (include-book "../../util/arithmetic"))

(defxdoc ifmerge
  :parents (always-top)
  :short "Merge nested @('if') statements and blocks."

  :long "<p>Our goal here is to flatten out a statement by removing any nested
@('if') structures, for instance, we might rewrite:</p>

@({
 a1 <= z1;             -->    a1 <= z1;
 if (c1)                      if (c1) a2 <= z2;
 begin                        if (c1 && c2) a3 <= z3;
   a2 <= z2;                  if (c1 && c3) a4 <= z4;
   if (c2) a3 <= z3;          if (c1 && c3) a5 <= z5;
   if (c3)
   begin
      a4 <= z4;
      a5 <= z5;
   end
 end
})

<p>We expect expressions to be sized, and that @(see unelse) has been run to
remove @('else') expressions.</p>")

(local (xdoc::set-default-parents ifmerge))

(local (in-theory (disable (tau-system))))

(defines vl-stmt-ifmerge
  :short "Main if-merging rewrite."

  (define vl-stmt-ifmerge
    ((x          "Statement to rewrite."
                 vl-stmt-p)
     (outer-cond "Initially @('nil'), but becomes the merged outer-condition as
                  we descend through ifs."
                 (or (not outer-cond)
                     (and (vl-expr-p outer-cond)
                          (posp (vl-expr->finalwidth outer-cond))
                          (equal (vl-expr->finaltype outer-cond)
                                 :vl-unsigned))))
     (warnings vl-warninglist-p)
     (elem     vl-modelement-p
               "Context for error messages."))
    :returns (mv (warnings vl-warninglist-p)
                 (flat-stmts vl-stmtlist-p))
    :verify-guards nil
    :measure (vl-stmt-count x)
    :hints(("Goal" :in-theory (disable (force))))
    :flag :stmt
    (b* (((fun (stop outer-cond x warnings))
          ;; We can stop at any time, by wrapping up the statement we've
          ;; gotten to in the outer-cond we've accumulated so far.
          (mv (ok)
              (if outer-cond
                  (list (make-vl-ifstmt :condition outer-cond
                                        :truebranch x
                                        :falsebranch (make-vl-nullstmt)))
                (list (vl-stmt-fix x)))))

         ((when (vl-nullstmt-p x))
          ;; Special case: don't call STOP.  A null statement does nothing,
          ;; whether it has a condition or not, so just let it fizzle away.
          ;; This is like  rewriting "if (condition) [null] --> null".
          (mv (ok) nil))

         ((when (vl-atomicstmt-p x))
          (stop outer-cond x warnings))

         ((when (vl-ifstmt-p x))
          (b* (((vl-ifstmt x) x)
               (width (vl-expr->finalwidth x.condition))
               (type  (vl-expr->finaltype x.condition))
               ((unless (and type (posp width)))
                (stop outer-cond x
                      (warn :type :vl-ifmerge-fail
                            :msg "~a0: can't merge if statement.  Expected ~
                                   the condition, ~a1, to have positive width ~
                                   and decided type, but found width ~x2 and ~
                                   type ~x3."
                            :args (list elem x.condition width type)
                            :fn 'vl-stmt-ifmerge)))
               ((unless (vl-expr-welltyped-p x.condition))
                (stop outer-cond x
                      (warn :type :vl-ifmerge-fail
                            :msg "~a0: can't merge if statement.  Expected ~
                                   the condition, ~a1, to be well-typed, but ~
                                   it is not.  Raw expression: ~x1."
                            :args (list elem x.condition)
                            :fn 'vl-stmt-ifmerge)))
               ((unless (vl-nullstmt-p x.falsebranch))
                (stop outer-cond x
                      (warn :type :vl-ifmerge-fail
                            :msg "~a0: can't merge if statement.  Expected ~
                                   all 'else' statements to be gone by now."
                            :args (list elem x)
                            :fn 'vl-stmt-ifmerge)))
               (merged-cond (vl-condition-merge outer-cond x.condition)))
            (vl-stmt-ifmerge x.truebranch merged-cond warnings elem)))

         ((when (vl-blockstmt-p x))
          (b* (((vl-blockstmt x) x)
               ((when (or x.name x.vardecls x.paramdecls (not x.sequentialp)))
                ;; Too hard to think about, just stop here.
                (stop outer-cond x warnings)))
            ;; Else, simple begin/else block: dive into it
            (vl-stmtlist-ifmerge x.stmts outer-cond warnings elem)))

         ((when (vl-timingstmt-p x))
          (b* (((when outer-cond)
                ;; We've gotten to something like:
                ;;  if (foo) begin
                ;;    @(posedge clk) ...
                ;;  end
                ;; so we have to stop, because it's not okay to move the
                ;; @(posedge clk) above the if test.
                (stop outer-cond x warnings))
               ;; Else, we found something like @(posedge clk) but we don't
               ;; have any ifs above us anyway, so we can freely keep going
               ;; here.
               ((vl-timingstmt x) x)
               ((mv warnings stmt-list)
                (vl-stmt-ifmerge x.body nil warnings elem))
               (new-body
                (if (equal (len stmt-list) 1)
                    (car stmt-list)
                  (make-vl-blockstmt :sequentialp t
                                     :stmts stmt-list))))
            (mv (ok)
                (list (change-vl-timingstmt x :body new-body))))))

      (stop outer-cond x warnings)))

  (define vl-stmtlist-ifmerge
    ((x          "List of statements from a simple begin/end block."
                 vl-stmtlist-p)
     (outer-cond (or (not outer-cond)
                     (and (vl-expr-p outer-cond)
                          (posp (vl-expr->finalwidth outer-cond))
                          (equal (vl-expr->finaltype outer-cond)
                                 :vl-unsigned))))
     (warnings   vl-warninglist-p)
     (elem       vl-modelement-p))
    :returns (mv (warnings vl-warninglist-p)
                 (flat-stmts vl-stmtlist-p))
    :verify-guards nil
    :measure (vl-stmtlist-count x)
    :flag :list
    (b* (((when (atom x))
          (mv (ok) nil))
         ((mv warnings stmts1)
          (vl-stmt-ifmerge (car x) outer-cond warnings elem))
         ((mv warnings stmts2)
          (vl-stmtlist-ifmerge (cdr x) outer-cond warnings elem)))
      (mv warnings
          (append-without-guard stmts1 stmts2))))

  ///
  (verify-guards vl-stmt-ifmerge))

(define vl-always-ifmerge ((x        vl-always-p)
                           (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x    vl-always-p))
  (b* (((vl-always x) x)
       ((mv warnings stmt-list)
        (vl-stmt-ifmerge x.stmt nil warnings x))
       (new-stmt
        (if (equal (len stmt-list) 1)
            (car stmt-list)
          (make-vl-blockstmt :sequentialp t
                             :stmts stmt-list))))
    (mv warnings (change-vl-always x :stmt new-stmt))))

(define vl-alwayslist-ifmerge ((x        vl-alwayslist-p)
                               (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x    vl-alwayslist-p))
  (b* (((when (atom x))
        (mv (ok) x))
       ((mv warnings car) (vl-always-ifmerge (car x) warnings))
       ((mv warnings cdr) (vl-alwayslist-ifmerge (cdr x) warnings)))
    (mv warnings (cons car cdr))))

(define vl-module-ifmerge ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        (vl-module-fix x))
       ((unless x.alwayses)
        ;; Optimization: not going to do anything, don't bother re-consing the
        ;; module.
        (vl-module-fix x))
       ((mv warnings alwayses)
        (vl-alwayslist-ifmerge x.alwayses x.warnings)))
    (change-vl-module x
                      :warnings warnings
                      :alwayses alwayses)))

(defprojection vl-modulelist-ifmerge (x)
  (vl-module-ifmerge x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-ifmerge
  :short "Top-level @(see ifmerge) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-ifmerge x.mods))))

