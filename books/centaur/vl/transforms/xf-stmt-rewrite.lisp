; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "xf-resolve-ranges")
(include-book "../mlib/stmt-tools")
(local (include-book "../util/arithmetic"))


(defxdoc stmtrewrite
  :parents (transforms)
  :short "Rewrite statements into simpler forms."

  :long "<p>In this transformation, our goal is to simplify Verilog statements
by applying rewrite rules.  The goal is to make later statement processing
simpler by making statements more canonical and regular.</p>

<p>BOZO sorry about the lack of documentation, in a hurry.</p>

<h4>Order Notes</h4>

<p>Do this AFTER unparameterization, so that width parameters and stuff have
been propagated.</p>

<p>But do it BEFORE sizing and width computations.  We may insert unsized
constants, e.g., in forever-loop conversion.</p>")


;; implemented rewrites:
;;   wait statements --> while loops        - done
;;   forever statements --> while loops     - done
;;   unroll some repeat statements          - done
;;   eliminate null stmts from blocks       - done
;;   eliminate empty and singleton blocks   - done
;;   flatten compatible sub-blocks          - done
;;   eliminate "always null;"               - done
;;   eliminate "initial null;               - done
;;   @(...) null --> null; (top level only) - done
;;   merge nested ifs (without elses)       - done
;;   $display(...) --> null                 - done
;;   pure-null case stmts --> null          - done
;;
;; eventually implement:
;;   case statements --> if statements
;;   attempt to unroll for loops
;;   maybe if statements --> ?: format
;;   unlocalize decls (hard!  other xform)
;;
;; Resulting statements:
;;   If statements
;;   While loops
;;   Blocks
;;   Timing statements



;; I guess we don't want to expect signs/widths to be computed yet, but we
;; probably expect that unparameterization has already been done so that
;; parameters like width should have been reduced to constants already.


(defsection vl-waitstmt-rewrite

; wait (condition) body
;   -->
; begin
;   while(condition)
;     ; // <-- null statement
;   body
; end

  (defund vl-waitstmt-rewrite (condition body atts)
    (declare (xargs :guard (and (vl-expr-p condition)
                                (vl-stmt-p body)
                                (vl-atts-p atts))))
    (b* ((null      (make-vl-nullstmt))
         (while     (make-vl-whilestmt :condition condition
                                       :body null
                                       :atts (acons "VL_WAIT" nil atts)))
         (block     (make-vl-blockstmt :sequentialp t
                                       :stmts (list while body))))
        block))

  (local (in-theory (enable vl-waitstmt-rewrite)))

  (defthm vl-stmt-p-of-vl-waitstmt-rewrite
    (implies (and (vl-expr-p condition)
                  (vl-stmt-p body)
                  (vl-atts-p atts))
             (vl-stmt-p (vl-waitstmt-rewrite condition body atts)))))




(defsection vl-foreverstmt-rewrite

; forever body
;   -->
; while(1)
;   body

  (defund vl-foreverstmt-rewrite (body atts)
    (declare (xargs :guard (and (vl-stmt-p body)
                                (vl-atts-p atts))))
    (b* ((const-one (make-vl-constint :origwidth 1
                                      :origtype :vl-unsigned
                                      :value 1))
         (atom-one  (make-vl-atom :guts const-one))
         (while     (make-vl-whilestmt :condition atom-one
                                       :body body
                                       :atts (acons "VL_FOREVER" nil atts))))
        while))

  (local (in-theory (enable vl-foreverstmt-rewrite)))

  (defthm vl-stmt-p-of-vl-foreverstmt-rewrite
    (implies (and (force (vl-stmt-p body))
                  (force (vl-atts-p atts)))
             (vl-stmt-p (vl-foreverstmt-rewrite body atts)))))




(defsection vl-repeatstmt-rewrite

; repeat(n) body;   // with 0 <= n <= unroll-limit
;   -->
; begin
;   body   }
;   body   }  n times
;   ...    }
;   body   }
; end

  (defund vl-repeatstmt-rewrite (condition body atts warnings unroll-limit)
    "Returns (MV WARNINGS STMT-PRIME)"
    (declare (xargs :guard (and (vl-expr-p condition)
                                (vl-stmt-p body)
                                (vl-atts-p atts)
                                (vl-warninglist-p warnings)
                                (natp unroll-limit))))

; We actually use vl-rangeexpr-reduce to try to evaluate condition.  This will
; allow us to unroll things like "width - 1" after the unparameterization has
; occurred, in addition to ordinary constants.

    (let ((count (vl-rangeexpr-reduce condition)))

      (if (or (not count)
              (> count unroll-limit))

          (mv (cons (cond ((not count)
                           (make-vl-warning
                            :type :vl-unroll-fail
                            :msg "Cannot unroll repeat statement because the ~
                                  count, ~a0, did not resolve to a constant."
                            :args (list condition)
                            :fn 'vl-repeatstmt-rewrite))
                          (t
                           (make-vl-warning
                            :type :vl-unroll-fail
                            :msg "Refusing to unroll repeat statement.  The ~
                                  count expression, ~a0, resolved to ~x1, which ~
                                  exceeds the unroll limit of ~x2."
                            :args (list condition count unroll-limit)
                            :fn 'vl-repeatstmt-rewrite)))
                    warnings)

              ;; No changes if we hit these problems.
              (make-vl-repeatstmt :condition condition
                                  :body body
                                  :atts (acons "VL_UNROLL_REPEAT_FAIL" nil atts)))


        (mv warnings
            ;; This works even when N is 0 or 1.  (We expect our later block
            ;; cleaning rewrites to handle such cases).
            (make-vl-blockstmt :sequentialp t
                               :stmts (repeat body count)
                               :atts (acons "VL_UNROLL_REPEAT" nil atts))))))

  (local (in-theory (enable vl-repeatstmt-rewrite)))

  (defthm vl-warninglist-p-of-vl-repeatstmt-rewrite
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-repeatstmt-rewrite condition body atts
                                                           warnings unroll-limit)))))

  (defthm vl-stmt-p-of-vl-repeatstmt-rewrite
    (implies (and (force (vl-expr-p condition))
                  (force (vl-stmt-p body))
                  (force (vl-atts-p atts)))
             (vl-stmt-p (mv-nth 1 (vl-repeatstmt-rewrite condition body atts
                                                       warnings unroll-limit))))))




(defsection vl-ifstmt-combine-rewrite

; Rewrite #1.
;
; if (test1)
;   if (test2)
;      body
;
;  -->
;
; if (test1 && test2)
;     body
;
;
; Rewrite #2.
;
; if (test) [nullstmt] else [nullstmt];
;   -->
; [nullstmt]
;
; We could probably do better, and handle some elses, etc., but we'll just play
; it safe for now.

  (defund vl-ifstmt-combine-rewrite (condition truebranch falsebranch atts)
    (declare (xargs :guard (and (vl-expr-p condition)
                                (vl-stmt-p truebranch)
                                (vl-stmt-p falsebranch)
                                (vl-atts-p atts))
                    :guard-debug t))

    (b* ((fail-to-apply (make-vl-ifstmt :condition condition
                                        :truebranch truebranch
                                        :falsebranch falsebranch
                                        :atts atts))

         ((when (and (vl-fast-nullstmt-p truebranch)
                     (vl-fast-nullstmt-p falsebranch)))
          (make-vl-nullstmt))

         ((unless (and (vl-fast-compoundstmt-p truebranch)
                       (eq (vl-compoundstmt->type truebranch) :vl-ifstmt)))
          fail-to-apply)

         ;; Don't try to handle ifs with elses.
         ((unless (vl-fast-nullstmt-p falsebranch))
          fail-to-apply)

         (inner-condition   (vl-ifstmt->condition truebranch))
         (inner-truebranch  (vl-ifstmt->truebranch truebranch))
         (inner-falsebranch (vl-ifstmt->falsebranch truebranch))

         ;; Don't try to handle inner ifs with elses.
         ((unless (vl-fast-nullstmt-p inner-falsebranch))
          fail-to-apply)

         (new-condition    (make-vl-nonatom :op :vl-binary-logand
                                            :args (list condition inner-condition))))

        (make-vl-ifstmt :condition new-condition
                        :truebranch inner-truebranch
                        :falsebranch falsebranch
                        :atts (acons "VL_COMBINED_IF" nil atts))))

  (local (in-theory (enable vl-ifstmt-combine-rewrite)))

  (defthm vl-stmt-p-of-vl-ifstmt-combine-rewrite
    (implies (and (force (vl-expr-p condition))
                  (force (vl-stmt-p truebranch))
                  (force (vl-stmt-p falsebranch))
                  (force (vl-atts-p atts)))
             (vl-stmt-p (vl-ifstmt-combine-rewrite condition truebranch falsebranch atts)))))



(defund vl-stmtlist-all-null-p (x)
  (declare (xargs :guard (vl-stmtlist-p x)))
  (if (atom x)
      t
    (and (vl-fast-nullstmt-p (car x))
         (vl-stmtlist-all-null-p (cdr x)))))

(defsection vl-casestmt-rewrite

  (defund vl-casestmt-rewrite (casetype test exprs bodies default atts)

; Stupid rewrite:
;
;   case/casex/casez(expr):
;     expr1 : [null stmt];
;     expr2 : [null stmt];
;     ...
;     exprN : [null stmt];
;     default: [null stmt];
;   endcase
;    --->
;   [null stmt]

    (declare (xargs :guard (and (vl-casetype-p casetype)
                                (vl-expr-p test)
                                (vl-exprlist-p exprs)
                                (vl-stmtlist-p bodies)
                                (same-lengthp exprs bodies)
                                (vl-stmt-p default)
                                (vl-atts-p atts))))
    (if (and (vl-fast-nullstmt-p default)
             (vl-stmtlist-all-null-p bodies))
;; All statements are null, just turn into null.
        (make-vl-nullstmt)
;; Otherwise don't change it.  Eventually convert all case statements
;; into if statements?
      (make-vl-casestmt :casetype casetype
                        :test test
                        :exprs exprs
                        :bodies bodies
                        :default default
                        :atts atts)))

  (local (in-theory (enable vl-casestmt-rewrite)))

  (defthm vl-stmt-p-of-vl-casestmt-rewrite
    (implies (and (force (vl-casetype-p casetype))
                  (force (vl-expr-p test))
                  (force (vl-exprlist-p exprs))
                  (force (vl-stmtlist-p bodies))
                  (force (same-lengthp exprs bodies))
                  (force (vl-stmt-p default))
                  (force (vl-atts-p atts)))
             (vl-stmt-p
              (vl-casestmt-rewrite casetype test exprs bodies default atts)))))



(defsection vl-remove-null-statements

; Eliminate null statements from a list of statements, produce an updated
; list of statements with nulls removed.

  (defund vl-remove-null-statements (x)
    (declare (xargs :guard (vl-stmtlist-p x)))
    (cond ((atom x)
           nil)
          ((vl-fast-nullstmt-p (car x))
           (vl-remove-null-statements (cdr x)))
          (t
           (cons (car x)
                 (vl-remove-null-statements (cdr x))))))

  (local (in-theory (enable vl-remove-null-statements)))

  (defthm vl-stmtlist-p-of-vl-remove-null-statements
    (implies (force (vl-stmtlist-p x))
             (vl-stmtlist-p (vl-remove-null-statements x)))))


(defsection vl-flatten-blocks

; This function is used to collapse nested blocks like
;
;   begin
;     foo = a;
;     begin
;       bar = b;
;       baz = c;
;     end
;     goo = d;
;   end
;
; Into
;
;   begin
;     foo = a
;     bar = b;
;     baz = c;
;     goo = d;
;   end
;
; We can also collapse fork/join blocks with inner fork/join blocks.

  (defthm acl2-count-of-list-fix
    (<= (acl2-count (list-fix x))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (enable acl2-count))))

  (local (defthm termination-lemma
           (implies (consp stmts)
                    (< (+ (acl2-count (cdr stmts))
                          (acl2-count (list-fix (vl-blockstmt->stmts (first stmts)))))
                       (acl2-count stmts)))
           :hints(("Goal" :in-theory (enable acl2-count)))))

  (defund vl-flatten-blocks (sequentialp stmts)
    (declare (xargs :guard (and (booleanp sequentialp)
                                (vl-stmtlist-p stmts))
                    :measure (acl2-count stmts)))

; Inputs:
;
;   - Sequentialp says whether the block we're working in is sequential (begin/end)
;     or not (fork/join).  It's only sound to merge subblocks of the same type.
;
;   - Stmts are the statements from a block.
;
; We produce a new list of statements by replacing any compatible sub-blocks with
; their list of statements.

    (cond ((atom stmts)
           nil)

          ((and (vl-fast-compoundstmt-p (car stmts))
                (eq (vl-compoundstmt->type (car stmts)) :vl-blockstmt)
                (eq (vl-blockstmt->sequentialp (car stmts)) sequentialp)
                ;; Extra conditions!  Do not merge if the subblock has a
                ;; name or decls.
                (not (vl-blockstmt->name (car stmts)))
                (atom (vl-blockstmt->decls (car stmts))))

; I am not sure if we need to recursively flatten the sub-statements.  It might
; be expensive to do so given that our rewriter is going to walk over the term.
; But it might also be necessary to flatten all blocks.

           ;; Merge the sub-block's statements into the list of statements
           ;; we are returning
           (vl-flatten-blocks sequentialp
                              (append (redundant-list-fix (vl-blockstmt->stmts (car stmts)))
                                      (cdr stmts))))

          (t
           (cons (car stmts)
                 (vl-flatten-blocks sequentialp (cdr stmts))))))

  (local (in-theory (enable vl-flatten-blocks)))

  (defthm vl-stmtlist-p-of-vl-flatten-blocks
    (implies (and (force (booleanp sequentialp))
                  (force (vl-stmtlist-p stmts)))
             (vl-stmtlist-p (vl-flatten-blocks sequentialp stmts)))))




(defsection vl-blockstmt-rewrite

; We flatten sub-blocks and remove any null statements from the block.
;
; We collapse empty blocks (i.e., literally "begin end") into null statements,
; unless they have a name or decls.
;
; We rewrite "begin stmt end" to just "stmt", unless it has a name or decls.
;
; The name/decl restrictions are important, because if the block name is used
; somewhere in a hierarchical identifier, and we throw the block away, we're
; hosed.  Also, the decls need to be preserved.  I think we will need to handle
; decls ahead of time, in another, separate transform.  But by refusing to do
; the rewrite in this case, we ensure that this rewrite is at least sound.

  (defund vl-blockstmt-rewrite (sequentialp name decls stmts atts warnings)
    "Returns (MV WARNINGS STMT-PRIME)"
    (declare (xargs :guard (and (booleanp sequentialp)
                                (vl-maybe-string-p name)
                                (vl-blockitemlist-p decls)
                                (vl-stmtlist-p stmts)
                                (vl-atts-p atts)
                                (vl-warninglist-p warnings))))
    (let* ((stmts (vl-flatten-blocks sequentialp stmts))
           (stmts (vl-remove-null-statements stmts)))
      (cond ((and (or (not stmts)
                      (not (cdr stmts)))
                  (or name decls))
             ;; Make sure it's safe to collapse.
             (mv (cons (make-vl-warning
                        :type :vl-collapse-fail
                        ;; BOZO bad message
                        :msg "Not collapsing block since it has a name (~s0) or ~
                              declarations (~x0)."
                        :args (list name decls)
                        :fn 'vl-blockstmt-rewrite)
                       warnings)
                 (make-vl-blockstmt :sequentialp sequentialp
                                    :name name
                                    :decls decls
                                    :stmts stmts
                                    :atts (acons "VL_COLLAPSE_FAIL" nil atts))))

            ((not stmts)
             ;; begin end --> null
             (mv warnings
                 (make-vl-nullstmt :atts (acons "VL_COLLAPSE" nil atts))))

            ((not (cdr stmts))
             ;; begin stmt end --> stmt
             ;;
             ;; It might be nice to add a VL_COLLAPSE attribute, but that's
             ;; not entirely straightforward since this might be any kind of
             ;; statement.
             (mv warnings (car stmts)))

            (t
             ;; This might not be a no-op.  For instance, we might have
             ;; removed some null statements or flattened some blocks.
             (mv warnings (make-vl-blockstmt :sequentialp sequentialp
                                             :name name
                                             :decls decls
                                             :stmts stmts
                                             :atts atts))))))

  (local (in-theory (enable vl-blockstmt-rewrite)))

  (defthm vl-warninglist-p-of-vl-blockstmt-rewrite
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-blockstmt-rewrite sequentialp name decls
                                                          stmts atts warnings)))))

  (defthm vl-stmt-p-of-vl-blockstmt-rewrite
    (implies (and (force (booleanp sequentialp))
                  (force (vl-maybe-string-p name))
                  (force (vl-blockitemlist-p decls))
                  (force (vl-stmtlist-p stmts))
                  (force (vl-atts-p atts)))
             (vl-stmt-p (mv-nth 1 (vl-blockstmt-rewrite sequentialp name decls
                                                        stmts atts warnings))))))





(defund vl-$display-stmt-p (x)

; Display statements were fooling with our verror heuristics, so now we throw
; them away during statement rewriting.  This should be sound since they are
; effectively no-ops from a semantic perspective.

  (declare (xargs :guard (vl-stmt-p x)
                  :guard-debug t))
  (b* (((unless (vl-fast-enablestmt-p x))
        nil)
       ((vl-enablestmt x) x)
       ((unless (vl-fast-atom-p x.id))
        nil)
       ((vl-atom x.id) x.id)
       ((unless (vl-fast-sysfunname-p x.id.guts))
        nil)
       ((vl-sysfunname x.id.guts) x.id.guts))
      (equal x.id.guts.name "$display")))


(defund vl-$vcover-stmt-p (x)

; Centaur specific.  We throw away $vcover statements.

  (declare (xargs :guard (vl-stmt-p x)
                  :guard-debug t))
  (b* (((unless (vl-fast-enablestmt-p x))
        nil)
       ((vl-enablestmt x) x)
       ((unless (vl-fast-atom-p x.id))
        nil)
       ((vl-atom x.id) x.id)
       ((unless (vl-fast-sysfunname-p x.id.guts))
        nil)
       ((vl-sysfunname x.id.guts) x.id.guts))
      (equal x.id.guts.name "$vcover")))



(defsection vl-stmt-rewrite

; This is just a rewriter that applies the above rules.

  (mutual-recursion

   (defund vl-stmt-rewrite (x unroll-limit warnings)
     "Returns (MV WARNINGS X-PRIME)"
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (natp unroll-limit)
                                 (vl-warninglist-p warnings))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (cond ((vl-fast-atomicstmt-p x)
            ;; Eliminate $display statements
            (if (or (vl-$display-stmt-p x)
                    (vl-$vcover-stmt-p x))
                (mv warnings (make-vl-nullstmt))
              (mv warnings x)))

           ((not (mbt (consp x)))
            (prog2$
             (er hard 'vl-stmt-rewrite "Impossible case for termination.")
             (mv warnings x)))

           (t
            (case (vl-compoundstmt->type x)

              (:vl-waitstmt
               (b* ((atts               (vl-compoundstmt->atts x))
                    (condition          (vl-waitstmt->condition x))
                    (body               (vl-waitstmt->body x))
                    ((mv warnings body) (vl-stmt-rewrite body unroll-limit warnings))
                    (x-prime            (vl-waitstmt-rewrite condition body atts)))
                   (mv warnings x-prime)))

              (:vl-foreverstmt
               (b* ((atts               (vl-compoundstmt->atts x))
                    (body               (vl-foreverstmt->body x))
                    ((mv warnings body) (vl-stmt-rewrite body unroll-limit warnings))
                    (x-prime            (vl-foreverstmt-rewrite body atts)))
                   (mv warnings x-prime)))

              (:vl-repeatstmt
               (b* ((atts                  (vl-compoundstmt->atts x))
                    (expr                  (vl-repeatstmt->condition x))
                    (body                  (vl-repeatstmt->body x))
                    ((mv warnings body)    (vl-stmt-rewrite body unroll-limit warnings))
                    ((mv warnings x-prime) (vl-repeatstmt-rewrite expr body atts
                                                                  warnings unroll-limit)))
                   (mv warnings x-prime)))

              (:vl-ifstmt
               (b* ((atts                  (vl-compoundstmt->atts x))
                    (condition             (vl-ifstmt->condition x))
                    (truebr                (vl-ifstmt->truebranch x))
                    (falsebr               (vl-ifstmt->falsebranch x))
                    ((mv warnings truebr)  (vl-stmt-rewrite truebr unroll-limit warnings))
                    ((mv warnings falsebr) (vl-stmt-rewrite falsebr unroll-limit warnings))
                    (x-prime               (vl-ifstmt-combine-rewrite condition truebr
                                                                      falsebr atts)))
                   (mv warnings x-prime)))

              (:vl-blockstmt
               (b* ((atts                  (vl-compoundstmt->atts x))
                    (sequentialp           (vl-blockstmt->sequentialp x))
                    (name                  (vl-blockstmt->name x))
                    (decls                 (vl-blockstmt->decls x))
                    (stmts                 (vl-blockstmt->stmts x))
                    ((mv warnings stmts)   (vl-stmtlist-rewrite stmts unroll-limit warnings))
                    ((mv warnings x-prime) (vl-blockstmt-rewrite sequentialp name decls
                                                                 stmts atts warnings)))
                   (mv warnings x-prime)))

              (:vl-casestmt
               (b* ((atts                  (vl-compoundstmt->atts x))
                    (casetype              (vl-casestmt->casetype x))
                    (test                  (vl-casestmt->test x))
                    (exprs                 (vl-casestmt->exprs x))
                    (bodies                (vl-casestmt->bodies x))
                    (default               (vl-casestmt->default x))
                    (x-prime               (vl-casestmt-rewrite casetype test exprs
                                                                bodies default atts)))
                   (mv warnings x-prime)))

              (otherwise
               (b* ((stmts               (vl-compoundstmt->stmts x))
                    ((mv warnings stmts) (vl-stmtlist-rewrite stmts unroll-limit warnings))
                    (x-prime             (change-vl-compoundstmt x :stmts stmts)))
                   (mv warnings x-prime)))))))

   (defund vl-stmtlist-rewrite (x unroll-limit warnings)
     "Returns (MV WARNINGS X-PRIME)"
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (natp unroll-limit)
                                 (vl-warninglist-p warnings))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         (mv warnings nil)
       (b* (((mv warnings car-prime) (vl-stmt-rewrite (car x) unroll-limit warnings))
            ((mv warnings cdr-prime) (vl-stmtlist-rewrite (cdr x) unroll-limit warnings)))
           (mv warnings (cons car-prime cdr-prime))))))

  (flag::make-flag vl-flag-stmt-rewrite
                   vl-stmt-rewrite
                   :flag-mapping ((vl-stmt-rewrite . stmt)
                                  (vl-stmtlist-rewrite . list)))

  (local (defun my-induction (x unroll-limit warnings)
           (if (atom x)
               (mv warnings nil)
             (b* (((mv warnings car-prime) (vl-stmt-rewrite (car x) unroll-limit warnings))
                  ((mv warnings cdr-prime) (my-induction (cdr x) unroll-limit warnings)))
                 (mv warnings (cons car-prime cdr-prime))))))

  (defthm len-of-vl-stmtlist-rewrite
    (equal (len (mv-nth 1 (vl-stmtlist-rewrite x unroll-limit warnings)))
           (len x))
    :hints(("Goal"
            :induct (my-induction x unroll-limit warnings)
            :expand (vl-stmtlist-rewrite x unroll-limit warnings))))

  (defthm-vl-flag-stmt-rewrite lemma
    (stmt (implies (vl-warninglist-p warnings)
                   (vl-warninglist-p (mv-nth 0 (vl-stmt-rewrite x unroll-limit warnings))))
          :name vl-warninglist-p-of-vl-stmt-rewrite)
    (list (implies (vl-warninglist-p warnings)
                   (vl-warninglist-p (mv-nth 0 (vl-stmtlist-rewrite x unroll-limit warnings))))
          :name vl-warninglist-p-of-vl-stmtlist-rewrite)
    :hints(("Goal"
            :induct (vl-flag-stmt-rewrite flag x unroll-limit warnings)
            :expand ((vl-stmt-rewrite x unroll-limit warnings)
                     (vl-stmtlist-rewrite x unroll-limit warnings)))))

  (defthm-vl-flag-stmt-rewrite lemma
    (stmt (implies (vl-stmt-p x)
                   (vl-stmt-p (mv-nth 1 (vl-stmt-rewrite x unroll-limit warnings))))
          :name vl-stmt-p-of-vl-stmt-rewrite)
    (list (implies (vl-stmtlist-p x)
                   (vl-stmtlist-p (mv-nth 1 (vl-stmtlist-rewrite x unroll-limit warnings))))
          :name vl-stmtlist-p-of-vl-stmtlist-rewrite)
    :hints(("Goal"
            :induct (vl-flag-stmt-rewrite flag x unroll-limit warnings)
            :expand ((vl-stmt-rewrite x unroll-limit warnings)
                     (vl-stmtlist-rewrite x unroll-limit warnings)))))

  (verify-guards vl-stmt-rewrite))



(defsection vl-stmt-rewrite-top

  (defund vl-stmt-rewrite-top (x unroll-limit warnings)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (natp unroll-limit)
                                (vl-warninglist-p warnings))))
    (b* (((mv warnings x)
          (vl-stmt-rewrite x unroll-limit warnings))

         ;; Extra rewrite only valid at top level: @(...) [null] --> null
         ((when (and (vl-fast-compoundstmt-p x)
                     (eq (vl-compoundstmt->type x) :vl-timingstmt)
                     (vl-fast-nullstmt-p (vl-timingstmt->body x))))
          (mv warnings (make-vl-nullstmt))))

        (mv warnings x)))

  (local (in-theory (enable vl-stmt-rewrite-top)))

  (defthm vl-warninglist-p-of-vl-stmt-rewrite-top
    (implies (vl-warninglist-p warnings)
             (vl-warninglist-p (mv-nth 0 (vl-stmt-rewrite-top x unroll-limit warnings)))))

  (defthm vl-stmt-p-of-vl-stmt-rewrite-top
    (implies (vl-stmt-p x)
             (vl-stmt-p (mv-nth 1 (vl-stmt-rewrite-top x unroll-limit warnings))))))



(defsection vl-always-stmtrewrite

  (defund vl-always-stmtrewrite (x unroll-limit warnings)
    "Returns (MV WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-always-p x)
                                (natp unroll-limit)
                                (vl-warninglist-p warnings))))
    (b* (((mv warnings stmt)
          (vl-stmt-rewrite-top (vl-always->stmt x) unroll-limit warnings))
         (x-prime (change-vl-always x :stmt stmt)))
        (mv warnings x-prime)))

  (local (in-theory (enable vl-always-stmtrewrite)))

  (defthm vl-warninglist-p-of-vl-always-stmtrewrite
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-always-stmtrewrite x unroll-limit warnings)))))

  (defthm vl-always-p-of-vl-always-stmtrewrite
    (implies (and (force (vl-always-p x))
                  (force (natp unroll-limit)))
             (vl-always-p (mv-nth 1 (vl-always-stmtrewrite x unroll-limit warnings))))))



(defsection vl-alwayslist-stmtrewrite

  (defund vl-alwayslist-stmtrewrite (x unroll-limit warnings)
    "Returns (MV WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-alwayslist-p x)
                                (natp unroll-limit)
                                (vl-warninglist-p warnings))))
    (if (atom x)
        (mv warnings nil)
      (b* (((mv warnings car-prime)
            (vl-always-stmtrewrite (car x) unroll-limit warnings))
           ((mv warnings cdr-prime)
            (vl-alwayslist-stmtrewrite (cdr x) unroll-limit warnings)))
          ;; Throw away "always [null];"
          (mv warnings
              (if (vl-fast-nullstmt-p (vl-always->stmt car-prime))
                  cdr-prime
                (cons car-prime cdr-prime))))))

  (local (in-theory (enable vl-alwayslist-stmtrewrite)))

  (defthm vl-warninglist-p-of-vl-alwayslist-stmtrewrite
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-alwayslist-stmtrewrite x unroll-limit warnings)))))

  (defthm vl-alwayslist-p-of-vl-alwayslist-stmtrewrite
    (implies (and (force (vl-alwayslist-p x))
                  (force (natp unroll-limit)))
             (vl-alwayslist-p (mv-nth 1 (vl-alwayslist-stmtrewrite x unroll-limit warnings))))))



(defsection vl-initial-stmtrewrite

  (defund vl-initial-stmtrewrite (x unroll-limit warnings)
    "Returns (MV WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-initial-p x)
                                (natp unroll-limit)
                                (vl-warninglist-p warnings))))
    (b* (((mv warnings stmt)
          (vl-stmt-rewrite-top (vl-initial->stmt x) unroll-limit warnings))
         (x-prime (change-vl-initial x :stmt stmt)))
        (mv warnings x-prime)))

  (local (in-theory (enable vl-initial-stmtrewrite)))

  (defthm vl-warninglist-p-of-vl-initial-stmtrewrite
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-initial-stmtrewrite x unroll-limit warnings)))))

  (defthm vl-initial-p-of-vl-initial-stmtrewrite
    (implies (and (force (vl-initial-p x))
                  (force (natp unroll-limit)))
             (vl-initial-p (mv-nth 1 (vl-initial-stmtrewrite x unroll-limit warnings))))))



(defsection vl-initiallist-stmtrewrite

  (defund vl-initiallist-stmtrewrite (x unroll-limit warnings)
    "Returns (MV WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-initiallist-p x)
                                (natp unroll-limit)
                                (vl-warninglist-p warnings))))
    (if (atom x)
        (mv warnings nil)
      (b* (((mv warnings car-prime)
            (vl-initial-stmtrewrite (car x) unroll-limit warnings))
           ((mv warnings cdr-prime)
            (vl-initiallist-stmtrewrite (cdr x) unroll-limit warnings)))
          ;; Throw away "initial [null];"
          (mv warnings
              (if (vl-fast-nullstmt-p (vl-initial->stmt car-prime))
                  cdr-prime
                (cons car-prime cdr-prime))))))

  (local (in-theory (enable vl-initiallist-stmtrewrite)))

  (defthm vl-warninglist-p-of-vl-initiallist-stmtrewrite
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-initiallist-stmtrewrite x unroll-limit warnings)))))

  (defthm vl-initiallist-p-of-vl-initiallist-stmtrewrite
    (implies (and (force (vl-initiallist-p x))
                  (force (natp unroll-limit)))
             (vl-initiallist-p (mv-nth 1 (vl-initiallist-stmtrewrite x unroll-limit warnings))))))


(defsection vl-module-stmtrewrite

  (defund vl-module-stmtrewrite (x unroll-limit)
    "Returns X-PRIME"
    (declare (xargs :guard (and (vl-module-p x)
                                (natp unroll-limit))))
    (b* (((when (vl-module->hands-offp x))
          x)
         (alwayses (vl-module->alwayses x))
         (initials (vl-module->initials x))
         ;; Optimization: bail early on modules with no blocks.
         ((unless (or alwayses initials))
          x)

         (warnings (vl-module->warnings x))
         ((mv warnings alwayses-prime)
          (vl-alwayslist-stmtrewrite alwayses unroll-limit warnings))
         ((mv warnings initials-prime)
          (vl-initiallist-stmtrewrite initials unroll-limit warnings))
         (x-prime (change-vl-module x
                                    :warnings warnings
                                    :alwayses alwayses-prime
                                    :initials initials-prime)))
        x-prime))

  (local (in-theory (enable vl-module-stmtrewrite)))

  (defthm vl-module-p-of-vl-module-stmtrewrite
    (implies (and (force (vl-module-p x))
                  (force (natp unroll-limit)))
             (vl-module-p (vl-module-stmtrewrite x unroll-limit))))

  (defthm vl-module->name-of-vl-module-stmtrewrite
    (equal (vl-module->name (vl-module-stmtrewrite x unroll-limit))
           (vl-module->name x))))


(defsection vl-modulelist-stmtrewrite

  (defprojection vl-modulelist-stmtrewrite (x unroll-limit)
    (vl-module-stmtrewrite x unroll-limit)
    :guard (and (vl-modulelist-p x)
                (natp unroll-limit))
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-stmtrewrite)))

  (defthm vl-modulelist->names-of-vl-modulelist-stmtrewrite
    (equal (vl-modulelist->names (vl-modulelist-stmtrewrite x unroll-limit))
           (vl-modulelist->names x))))

