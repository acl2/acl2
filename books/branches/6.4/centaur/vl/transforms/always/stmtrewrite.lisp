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
(include-book "../xf-resolve-ranges")
(include-book "../../mlib/stmt-tools")
(local (include-book "../../util/arithmetic"))


(defxdoc stmtrewrite
  :parents (always-top)
  :short "Rewrite statements into simpler forms."

  :long "<p>This transform simplifies Verilog statements by applying rewrite
rules.  The idea is to make later statement processing simpler by reducing the
variety of statements that need to be supported.  This is somewhat similar to
how the @(see oprewrite) transform eliminates certain operators, leaving us
with fewer operators to support later on.  See @(see always-top) for how this
fits into our overall handling of @('always') blocks.</p>

<p>Note that, for instance, our rewrites eliminate @('$display') statements.
This is suitable when your goal is to analyze the functionality of the module
from a synthesis/build perspective, e.g., with @(see esim).  But it is
obviously <b>not suitable</b> if you want to use the resulting modules with a
Verilog simulator.</p>

<p>Notes:</p>

<ul>

<li>This transform should typically be run after @(see unparameterization) so
that, e.g., width parameters will have been propagated.  For instance, things
like @('repeat (n) body') won't get unrolled unless @('n') has already been
resolved.</li>

<li>It should typically run before sizing, since we generate unsized
expressions.</li>

</ul>

<p>Some implemented rewrites include:</p>

<ul>
 <li>@('$display(...)') &rarr; null</li>
 <li>pure-null if/case stmts &rarr; null</li>
 <li>eliminate null stmts from blocks</li>
 <li>empty blocks &rarr; null</li>
 <li>collapse singleton blocks (i.e., @('begin stmt end --> stmt)</li>
 <li>flatten compatible sub-blocks</li>
 <li>@('@(...) null') &rarr; @('null') (top level only)</li>
 <li>merge nested ifs (without elses)</li>
 <li>wait statements &rarr; while loops</li>
 <li>forever statements &rarr; while loops</li>
 <li>unroll some repeat statements (up to a limit)</li>
 <li>eliminate @('always null;')</li>
 <li>eliminate @('initial null;')</li>
</ul>

<p>BOZO we should eventually implement additional rewrites, such as:</p>

<ul>
 <li>case statements &rarr; if statements</li>
 <li>unroll simple while/for loops</li>
</ul>")


(define vl-waitstmt-rewrite ((condition vl-expr-p)
                             (body      vl-stmt-p)
                             (atts      vl-atts-p))
  :returns (stmt vl-stmt-p :hyp :fguard)
  :parents (stmtrewrite)
  :short "Convert wait statements into empty while loops."
  :long "<p>The basic rewrite this performs is:</p>

@({
 wait (condition) body
   -->
 begin
   while(condition)
     ; // this is just a null statement
   body
 end
})

<p>This might not be a very useful thing to do.  It seems hard to synthesize
arbitrary while loops.  On the other hand, it does eliminate any @('wait')
statement, perhaps simplifying the target language for later transforms to
implement.</p>

<p>BOZO is this sound?  Can we come up with some tests that establish it is
valid?  What if the condition is X/Z?</p>"

  (b* ((null      (make-vl-nullstmt))
       (while     (make-vl-whilestmt :condition condition
                                     :body null
                                     :atts (acons "VL_WAIT" nil atts)))
       (block     (make-vl-blockstmt :sequentialp t
                                     :stmts (list while body))))
    block))

(define vl-foreverstmt-rewrite ((body vl-stmt-p)
                                (atts vl-atts-p))
  :returns (stmt vl-stmt-p :hyp :fguard)
  :parents (stmtrewrite)
  :short "Convert forever statements into while loops."
  :long "<p>The basic rewrite this performs is:</p>

@({
 forever body
   -->
 while(1)
   body
})

<p>This might not be a very useful thing to do.  It seems hard to synthesize
arbitrary while loops.  On the other hand, it does eliminate any @('forever')
statement, simplifying the target language for later transforms to
implement.</p>"

  (b* ((const-one (make-vl-constint :origwidth 1
                                    :origtype :vl-unsigned
                                    :value 1))
       (atom-one  (make-vl-atom :guts const-one))
       (while     (make-vl-whilestmt :condition atom-one
                                     :body body
                                     :atts (acons "VL_FOREVER" nil atts))))
    while))

(define vl-repeatstmt-rewrite ((condition    vl-expr-p)
                               (body         vl-stmt-p)
                               (atts         vl-atts-p)
                               (warnings     vl-warninglist-p)
                               (unroll-limit natp))
  :returns (mv (warnings vl-warninglist-p :hyp :fguard)
               (stmt     vl-stmt-p        :hyp :fguard))
  :parents (stmtrewrite)
  :short "Unroll deterministic repeat statements."
  :long "<p>The basic rewrite this performs is:</p>

@({
 repeat(n) body;   // with 0 <= n <= unroll-limit
   -->
 begin
   body   }
   body   }  n times
   ...    }
   body   }
 end
})

<p>We only try to unroll when @('n') is easily resolved to a constant that is
less than the @('unroll-limit').  In particular, we use @(see
vl-rangeexpr-reduce) to try to evaluate the condition.  This lets us handle
things like @('repeat(width-1) body') after @(see unparameterization) has
occurred.</p>"

  (b* ((count (vl-rangeexpr-reduce condition))
       ((when (and count (<= count unroll-limit)))
        (mv warnings
            ;; This works even when N is 0 or 1.  We expect our later block
            ;; cleaning rewrites to further simplify those cases.
            (make-vl-blockstmt :sequentialp t
                               :stmts (repeat body count)
                               :atts (acons "VL_UNROLL_REPEAT" nil atts)))))
    (mv (warn :type :vl-unroll-fail
              ;; BOZO it'd be nice to have a context here
              :msg  (if count
                        "Cannot unroll repeat statement because the count, ~
                         ~a0, did not resolve to a constant."
                      "Cannot unroll repeat statement because the count, ~a0, ~
                       resolevd to ~x1, which exceeds the unroll limit of ~x2.")
              :args (list condition count unroll-limit))
        (make-vl-repeatstmt :condition condition
                            :body body
                            :atts (acons "VL_UNROLL_REPEAT_FAIL" nil atts)))))


(define vl-ifstmt-combine-rewrite ((condition   vl-expr-p)
                                   (truebranch  vl-stmt-p)
                                   (falsebranch vl-stmt-p)
                                   (atts        vl-atts-p))
  :returns (stmt vl-stmt-p :hyp :fguard)
  :parents (stmtrewrite)
  :short "Eliminate pure-null if statements and merge simply nested ifs."

  :long "<p>There are probably other things we could do here.  For now, we
just carry out two simple rewrites:</p>

@({
// Rewrite 1:

   if (test)      -->    null
      [null]
   else
      [null]

// Rewrite 2:

   if (test1)            if (test1 && test2)
     if (test2)   -->       body
       body
})"

  (b* ((fail-to-apply (make-vl-ifstmt :condition condition
                                      :truebranch truebranch
                                      :falsebranch falsebranch
                                      :atts atts))

       ((when (and (vl-fast-nullstmt-p truebranch)
                   (vl-fast-nullstmt-p falsebranch)))
        (make-vl-nullstmt))

       ((unless (vl-ifstmt-p truebranch))
        fail-to-apply)

       ;; Don't try to handle ifs with elses.
       ((unless (vl-fast-nullstmt-p falsebranch))
        fail-to-apply)

       ((vl-ifstmt inner) truebranch)

       ;; Don't try to handle inner ifs with elses.
       ((unless (vl-fast-nullstmt-p inner.falsebranch))
        fail-to-apply)

       (new-condition (make-vl-nonatom :op :vl-binary-logand
                                       :args (list condition inner.condition))))

    (make-vl-ifstmt :condition new-condition
                    :truebranch inner.truebranch
                    :falsebranch falsebranch
                    :atts (acons "VL_COMBINED_IF" nil atts))))



(define vl-stmtlist-all-null-p ((x vl-stmtlist-p))
  :parents (stmtrewrite)
  (if (atom x)
      t
    (and (vl-fast-nullstmt-p (car x))
         (vl-stmtlist-all-null-p (cdr x)))))


(define vl-casestmt-rewrite ((casetype vl-casetype-p)
                             (test    vl-expr-p)
                             (exprs   vl-exprlist-p)
                             (bodies  vl-stmtlist-p)
                             (default vl-stmt-p)
                             (atts    vl-atts-p))
  :guard (same-lengthp exprs bodies)
  :returns (stmt vl-stmt-p :hyp :fguard)
  :parents (stmtrewrite)
  :short "Eliminate pure-null case statements."
  :long "<p>This is a pretty silly rewrite:</p>
@({
   case/casex/casez(expr):    -->   [null stmt]
     expr1 : [null stmt];
     expr2 : [null stmt];
     ...
     exprN : [null stmt];
     default: [null stmt];
   endcase
})

<p>This seems safe and along with our other rewrites it lets us fizzle away,
e.g., case-based @('$display') statements into nothing.  But if we implement a
real case-statement &rarr; if-statement transform we shouldn't need this
anymore.</p>"

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


(define vl-remove-null-statements ((x vl-stmtlist-p))
  :returns (new-x vl-stmtlist-p :hyp :fguard)
  :parents (stmtrewrite)
  (cond ((atom x)
         nil)
        ((vl-fast-nullstmt-p (car x))
         (vl-remove-null-statements (cdr x)))
        (t
         (cons (car x) (vl-remove-null-statements (cdr x))))))

(define vl-flatten-blocks
  ((sequentialp booleanp "are we working with a sequential (begin/end) or
                          parallel (fork/join) block")
   (stmts       vl-stmtlist-p))
  :returns (new-stmts vl-stmtlist-p :hyp :fguard)
  :measure (acl2-count stmts)
  :parents (vl-blockstmt-rewrite)
  :short "Collapse nested @('begin/end') and @('fork/join') blocks."
  :long "<p>This function carries out rewrites such as:</p>

@({
   begin               begin
     foo = a;    -->     foo = a;
     begin               bar = b;
       bar = b;          baz = c;
       baz = c;          goo = d;
     end               end
     goo = d;
   end
})

<p>It can similarly collapse fork/join blocks with inner fork/join blocks.</p>

<p>We don't try to merge blocks that have their own scopes (i.e., names/decls).
Handling them correctly seems very tricky because of hierarchical identifiers,
etc.</p>

<p>BOZO.  We recursively flatten sub-blocks.  I'm not sure if we need to do
this, given the way that @(see vl-stmt-rewrite) works.  Well, it's probably
just some useless computation if it's not necessary.</p>"

  (b* (((when (atom stmts))
        nil)

       ((unless (and (vl-blockstmt-p (car stmts))
                     (eq (vl-blockstmt->sequentialp (car stmts)) sequentialp)
                     ;; Do not merge if the subblock has a name or decls!
                     (not (vl-blockstmt->name (car stmts)))
                     (atom (vl-blockstmt->decls (car stmts)))))
        ;; Not a sub-block, or too hard to merge.
        (cons (car stmts)
              (vl-flatten-blocks sequentialp (cdr stmts))))

       (merged-stmts
        ;; Merge the sub-block's statements into the rest of the super-block's
        ;; statements, then keep flattening.
        (append-without-guard (vl-blockstmt->stmts (car stmts))
                              (cdr stmts))))

    (vl-flatten-blocks sequentialp merged-stmts)))

(define vl-blockstmt-rewrite ((sequentialp booleanp)
                              (name        maybe-stringp)
                              (decls       vl-blockitemlist-p)
                              (stmts       vl-stmtlist-p)
                              (atts        vl-atts-p)
                              (warnings    vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p :hyp :fguard)
               (stmt     vl-stmt-p        :hyp :fguard))
  :parents (stmtrewrite)
  :short "Flatten sub-blocks, eliminate unnecessary blocks, and remove any null
statements from a block."

  :long "<p>This rewrite starts by flattening out nested, compatible blocks
with @(see vl-flatten-blocks) and removing null statements.  If then reduce the
resulting block with these rules:</p>

@({
  begin   --> null    // empty block rewrite
  end

  begin   --> stmt    // single statement rewrite
    stmt
  end
})

<p>We only do these extra rewrites when the block has no names/decls.  Handling
blocks with names/decls seems tricky due to hierarchical identifiers.</p>"

  (b* ((stmts (vl-flatten-blocks sequentialp stmts))
       (stmts (vl-remove-null-statements stmts))

       ((when (and (or (atom stmts)
                       (atom (cdr stmts)))
                   (or name decls)))
        (mv (warn :type :vl-collapse-fail
                  ;; BOZO bad error message, context would be good
                  :msg "Not collapsing ~s0 block ~x1 since it has a name or ~
                        declarations."
                  :args (list (if sequentialp "begin/end" "fork/join") name))
            (make-vl-blockstmt :sequentialp sequentialp
                               :name name
                               :decls decls
                               :stmts stmts
                               :atts (acons "VL_COLLAPSE_FAIL" nil atts))))

       ((when (atom stmts))
        ;; begin end --> null
        (mv warnings
            (make-vl-nullstmt :atts (acons "VL_COLLAPSE" nil atts))))

       ((when (atom (cdr stmts)))
        ;; begin stmt end --> stmt
        ;;
        ;; It might be nice to add a VL_COLLAPSE attribute, but that's
        ;; not entirely straightforward since this might be any kind of
        ;; statement.
        (mv warnings (car stmts))))

    ;; This might not be a no-op.  For instance, we might have removed some
    ;; null statements or flattened some blocks.
    (mv warnings (make-vl-blockstmt :sequentialp sequentialp
                                    :name name
                                    :decls decls
                                    :stmts stmts
                                    :atts atts))))



(define vl-$display-stmt-p ((x vl-stmt-p))
  :parents (stmtrewrite)
  :short "Recognize a @('$display') statement."
  (declare (xargs :guard (vl-stmt-p x)))
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

(define vl-$vcover-stmt-p ((x vl-stmt-p))
  :parents (stmtrewrite)
  :short "BOZO Centaur specific."
  (declare (xargs :guard (vl-stmt-p x)))
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
  :parents (stmtrewrite)
  :short "Core statement rewriter."

  (mutual-recursion

   (defund vl-stmt-rewrite (x unroll-limit warnings)
     "Returns (MV WARNINGS X-PRIME)"
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (natp unroll-limit)
                                 (vl-warninglist-p warnings))
                     :hints(("Goal" :in-theory (disable (force))))
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

           ((vl-waitstmt-p x)
            (b* (((vl-waitstmt x) x)
                 ((mv warnings body) (vl-stmt-rewrite x.body unroll-limit warnings))
                 (x-prime            (vl-waitstmt-rewrite x.condition body x.atts)))
              (mv warnings x-prime)))

           ((vl-foreverstmt-p x)
            (b* (((vl-foreverstmt x) x)
                 ((mv warnings body) (vl-stmt-rewrite x.body unroll-limit warnings))
                 (x-prime            (vl-foreverstmt-rewrite body x.atts)))
              (mv warnings x-prime)))

           ((vl-repeatstmt-p x)
            (b* (((vl-repeatstmt x) x)
                 ((mv warnings body)    (vl-stmt-rewrite x.body unroll-limit warnings))
                 ((mv warnings x-prime) (vl-repeatstmt-rewrite x.condition body x.atts
                                                               warnings unroll-limit)))
              (mv warnings x-prime)))

           ((vl-ifstmt-p x)
            (b* (((vl-ifstmt x) x)
                 ((mv warnings truebr)  (vl-stmt-rewrite x.truebranch unroll-limit warnings))
                 ((mv warnings falsebr) (vl-stmt-rewrite x.falsebranch unroll-limit warnings))
                 (x-prime               (vl-ifstmt-combine-rewrite x.condition truebr
                                                                   falsebr x.atts)))
              (mv warnings x-prime)))

           ((vl-blockstmt-p x)
            (b* (((vl-blockstmt x) x)
                 ((mv warnings stmts)   (vl-stmtlist-rewrite x.stmts unroll-limit warnings))
                 ((mv warnings x-prime) (vl-blockstmt-rewrite x.sequentialp x.name x.decls
                                                              stmts x.atts warnings)))
              (mv warnings x-prime)))

           ((vl-casestmt-p x)
            (b* (((vl-casestmt x) x)
                 ((mv warnings bodies)  (vl-stmtlist-rewrite x.bodies unroll-limit warnings))
                 ((mv warnings default) (vl-stmt-rewrite x.default unroll-limit warnings))
                 (x-prime               (vl-casestmt-rewrite x.casetype x.test x.exprs
                                                             bodies default x.atts)))
              (mv warnings x-prime)))

           (t
            (b* ((stmts               (vl-compoundstmt->stmts x))
                 ((mv warnings stmts) (vl-stmtlist-rewrite stmts unroll-limit warnings))
                 (x-prime             (change-vl-compoundstmt x :stmts stmts)))
              (mv warnings x-prime)))))

   (defund vl-stmtlist-rewrite (x unroll-limit warnings)
     "Returns (MV WARNINGS X-PRIME)"
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (natp unroll-limit)
                                 (vl-warninglist-p warnings))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (b* (((when (atom x))
           (mv warnings nil))
          ((mv warnings car-prime)
           (vl-stmt-rewrite (car x) unroll-limit warnings))
          ((mv warnings cdr-prime)
           (vl-stmtlist-rewrite (cdr x) unroll-limit warnings)))
       (mv warnings (cons car-prime cdr-prime)))))

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

  (defthm-vl-flag-stmt-rewrite
    (defthm return-type-of-vl-stmt-rewrite
      (implies (and (force (vl-stmt-p x))
                    (force (vl-warninglist-p warnings))
                    (force (natp unroll-limit)))
               (b* (((mv warnings new-x)
                     (vl-stmt-rewrite x unroll-limit warnings)))
                 (and (vl-warninglist-p warnings)
                      (vl-stmt-p new-x))))
      :flag stmt)
    (defthm return-type-of-vl-stmtlist-rewrite
      (implies (and (force (vl-stmtlist-p x))
                    (force (vl-warninglist-p warnings))
                    (force (natp unroll-limit)))
               (b* (((mv warnings new-x)
                     (vl-stmtlist-rewrite x unroll-limit warnings)))
                 (and (vl-warninglist-p warnings)
                      (vl-stmtlist-p new-x))))
      :flag list)
    :hints(("Goal"
            :induct (vl-flag-stmt-rewrite flag x unroll-limit warnings)
            :expand ((vl-stmt-rewrite x unroll-limit warnings)
                     (vl-stmtlist-rewrite x unroll-limit warnings)))))

  (verify-guards vl-stmt-rewrite))


(define vl-stmt-rewrite-top ((x            vl-stmt-p)
                             (unroll-limit natp)
                             (warnings     vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p :hyp :fguard)
               (new-x    vl-stmt-p        :hyp :fguard))
  :parents (stmtrewrite)
  :short "Wrapper for @(see vl-stmt-rewrite) that adds additional rewrites that
are valid only for top-level statements."

  :long "<p>Beyond the ordinary rewrites, we carry out:</p>

@({
  @(...) nullstmt  -->  nullstmt
})

<p>This isn't valid in general, because, e.g., a sequence such as:</p>

@({
  a = b;
  @(posedge clk) ; // nullstmt is here
  a = c;
})

<p>is much different than just doing the assignments sequentially.  But if we
have a whole @('always') or @('initial') block that does nothing more than
@('@(...) null'), we may as well get rid of it.</p>"

  (b* (((mv warnings x)
        (vl-stmt-rewrite x unroll-limit warnings))

       ((when (and (vl-timingstmt-p x)
                   (vl-fast-nullstmt-p (vl-timingstmt->body x))))
        (mv warnings (make-vl-nullstmt))))

    (mv warnings x)))


(define vl-always-stmtrewrite ((x            vl-always-p)
                               (unroll-limit natp)
                               (warnings     vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p :hyp :fguard)
               (new-x    vl-always-p      :hyp :fguard))
  :parents (stmtrewrite)
  (b* (((mv warnings stmt)
        (vl-stmt-rewrite-top (vl-always->stmt x) unroll-limit warnings))
       (x-prime (change-vl-always x :stmt stmt)))
    (mv warnings x-prime)))


(define vl-alwayslist-stmtrewrite ((x            vl-alwayslist-p)
                                   (unroll-limit natp)
                                   (warnings     vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p :hyp :fguard)
               (new-x    vl-alwayslist-p  :hyp :fguard))
  :parents (stmtrewrite)
  (b* (((when (atom x))
        (mv warnings nil))
       ((mv warnings car-prime)
        (vl-always-stmtrewrite (car x) unroll-limit warnings))
       ((mv warnings cdr-prime)
        (vl-alwayslist-stmtrewrite (cdr x) unroll-limit warnings)))
    ;; Throw away "always [null];"
    (mv warnings
        (if (vl-fast-nullstmt-p (vl-always->stmt car-prime))
            cdr-prime
          (cons car-prime cdr-prime)))))


(define vl-initial-stmtrewrite ((x           vl-initial-p)
                               (unroll-limit natp)
                               (warnings     vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p :hyp :fguard)
               (new-x    vl-initial-p     :hyp :fguard))
  :parents (stmtrewrite)
  (b* (((mv warnings stmt)
        (vl-stmt-rewrite-top (vl-initial->stmt x) unroll-limit warnings))
       (x-prime (change-vl-initial x :stmt stmt)))
    (mv warnings x-prime)))

(define vl-initiallist-stmtrewrite ((x            vl-initiallist-p)
                                    (unroll-limit natp)
                                    (warnings     vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p :hyp :fguard)
               (new-x    vl-initiallist-p  :hyp :fguard))
  :parents (stmtrewrite)
  (b* (((when (atom x))
        (mv warnings nil))
       ((mv warnings car-prime)
        (vl-initial-stmtrewrite (car x) unroll-limit warnings))
       ((mv warnings cdr-prime)
        (vl-initiallist-stmtrewrite (cdr x) unroll-limit warnings)))
    ;; Throw away "initial [null];"
    (mv warnings
        (if (vl-fast-nullstmt-p (vl-initial->stmt car-prime))
            cdr-prime
          (cons car-prime cdr-prime)))))

(define vl-module-stmtrewrite ((x            vl-module-p)
                               (unroll-limit natp))
  :returns (new-x vl-module-p :hyp :fguard)
  :parents (stmtrewrite)
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)

       ((unless (or x.alwayses x.initials))
       ;; Optimization: bail early on modules with no blocks.
        x)

       (warnings x.warnings)
       ((mv warnings alwayses)
        (vl-alwayslist-stmtrewrite x.alwayses unroll-limit warnings))
       ((mv warnings initials)
        (vl-initiallist-stmtrewrite x.initials unroll-limit warnings)))
    (change-vl-module x
                      :warnings warnings
                      :alwayses alwayses
                      :initials initials))
  ///
  (defthm vl-module->name-of-vl-module-stmtrewrite
    (equal (vl-module->name (vl-module-stmtrewrite x unroll-limit))
           (vl-module->name x))))


(defprojection vl-modulelist-stmtrewrite (x unroll-limit)
  (vl-module-stmtrewrite x unroll-limit)
  :guard (and (vl-modulelist-p x)
              (natp unroll-limit))
  :result-type vl-modulelist-p
  :rest
  ((defthm vl-modulelist->names-of-vl-modulelist-stmtrewrite
     (equal (vl-modulelist->names (vl-modulelist-stmtrewrite x unroll-limit))
            (vl-modulelist->names x)))))

