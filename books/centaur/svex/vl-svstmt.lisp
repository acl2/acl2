; SVEX - Symbolic, Vector-Level Hardware Description Library
; Copyright (C) 2014 Centaur Technology
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

(in-package "VL")

(include-book "svstmt-compile")
(include-book "vl-fns-called")
(include-book "vl-paramrefs")
(include-book "centaur/vl/transforms/always/util" :dir :system)
(local (include-book "centaur/vl/util/default-hints" :dir :system))
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system)
                           nfix natp)))

(defxdoc vl-svstmt
  :parents (vl-design->svex-design)
  :short "Discussion of creating svex assignments from combinational/latch-style
          always blocks."
  :long "<p>Verilog and SystemVerilog don't always cleanly translate to a
finite-state-machine semantics, especially when it comes to always blocks that
behave as latches.  We discuss some of the choices we made in this translation.</p>

<h2>Difference between @('always_comb'), @('always_latch'), and plain @('always')</h2>

<p>It isn't clear how Verilog simulators distinguish between these constructs.
For a simple latch of the form</p>
@({
  always_latch if (en) q = d;
 })

<p>Verilog simulators produce identical results if the @('always_latch') is
replaced by any of @('always_comb'), @('always @*'), or @('always @(en or d)').
However, we treat it differently in the @('always_comb') case,
because... (BOZO)</p>

")

(defxdoc vl-svstmt.lisp
  :parents (vl-svstmt))

(local (xdoc::set-default-parents vl-svstmt.lisp))



(define vl-assignstmt->svstmts ((lhs vl-expr-p)
                                (rhs vl-expr-p)
                                (blockingp booleanp)
                                (conf vl-svexconf-p))
  :returns (mv (ok)
               (warnings vl-warninglist-p)
               (res svex::svstmtlist-p))
  (b* ((warnings nil)
       ((wmv warnings svex-lhs lhs-type)
        (vl-expr-to-svex-lhs lhs (vl-svexconf->ss conf)))
       ((unless lhs-type)
        (mv nil warnings nil))
       ((wmv warnings svex-rhs)
        (vl-expr-to-svex-datatyped rhs lhs-type conf)))
    (mv t warnings
        (list (svex::make-svstmt-assign :lhs svex-lhs :rhs svex-rhs
                                        :blockingp blockingp))))
  ///
  (more-returns
   (res :name vars-of-vl-assignstmt->svstmts
        (svex::svarlist-addr-p
         (svex::svstmtlist-vars res)))))


(define vl-vardecllist->svstmts ((x vl-vardecllist-p)
                                 (conf vl-svexconf-p))
  :returns (mv (ok)
               (warnings vl-warninglist-p)
               (res (and (svex::svstmtlist-p res)
                         (svex::svarlist-addr-p
                          (svex::svstmtlist-vars res)))))
  (b* ((warnings nil)
       ((when (atom x)) (mv t (ok) nil))
       (x1 (vl-vardecl-fix (car x)))
       ((mv ok warnings rest)
        (vl-vardecllist->svstmts (cdr x) conf))
       ((unless ok) (mv nil warnings rest))
       ((vl-vardecl x1) x1)
       ;; skip if there's no initial value given
       ((unless x1.initval) (mv ok warnings rest))

       (lhs (vl-idexpr x1.name nil)))
    (vl-assignstmt->svstmts lhs x1.initval t conf)))
       
(local (in-theory (disable member append
                           svex::svarlist-addr-p-when-subsetp-equal
                           vl-warninglist-p-when-not-consp
                           acl2::true-listp-append
                           acl2::subsetp-when-atom-right
                           acl2::subsetp-when-atom-left)))

(defines vl-stmt->svstmts
  :prepwork ((local (in-theory (disable not))))
  (define vl-stmt->svstmts ((x vl-stmt-p)
                            (conf vl-svexconf-p)
                            (nonblockingp))
    :verify-guards nil
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (res (and (svex::svstmtlist-p res)
                           (svex::svarlist-addr-p
                            (svex::svstmtlist-vars res)))))
    :measure (vl-stmt-count x)
    (b* ((warnings nil)
         ((fun (fail warnings)) (mv nil warnings nil))
         (x (vl-stmt-fix x)))
      (vl-stmt-case x
        :vl-nullstmt (mv t (ok) nil)
        :vl-assignstmt
        (b* (((unless (or (eq x.type :vl-blocking)
                          (and nonblockingp
                               (eq x.type :vl-nonblocking))))
              (fail (warn :type :vl-stmt->svstmts-fail
                          :msg "Assignment type not supported: ~a0"
                          :args (list x))))
             (warnings (if x.ctrl
                           (warn :type :vl-stmt->svstmts-fail
                                 :msg "Ignoring delay or event control on ~
                                assignment: ~a0"
                                 :args (list x))
                         (ok)))
             ((wmv ok warnings res)
              (vl-assignstmt->svstmts x.lvalue x.expr (eq x.type :vl-blocking) conf)))
          (mv ok warnings res))
        :vl-ifstmt
        (b* (((wmv warnings cond ?type)
              (vl-expr-to-svex-untyped x.condition conf))
             ((wmv ok1 warnings true)
              (vl-stmt->svstmts x.truebranch conf nonblockingp))
             ((wmv ok2 warnings false)
              (vl-stmt->svstmts x.falsebranch conf nonblockingp)))
          (mv (and ok1 ok2) warnings
              (list (svex::make-svstmt-if :cond cond :then true :else false))))
        :vl-whilestmt
        (b* (((wmv warnings cond ?type)
              (vl-expr-to-svex-untyped x.condition conf))
             ((wmv ok warnings body)
              (vl-stmt->svstmts x.body conf nonblockingp)))
          (mv ok warnings (list (svex::make-svstmt-while :cond cond :body body))))
        :vl-forstmt
        (b* ((warnings (if (consp x.initdecls)
                           (warn :type :vl-stmt->svstmts-bozo
                                 :msg "Missing support for locally ~
                                       defined for loop vars: ~a0."
                                 :args (list x))
                         (ok)))
             ((wmv ok1 warnings initstmts1)
              (vl-vardecllist->svstmts x.initdecls conf))
             ((wmv ok2 warnings initstmts2)
              (vl-stmtlist->svstmts x.initassigns conf nonblockingp))
             ((wmv warnings cond ?type)
              (vl-expr-to-svex-untyped x.test conf))
             ((wmv ok3 warnings stepstmts)
              (vl-stmtlist->svstmts x.stepforms conf nonblockingp))
             ((wmv ok4 warnings body)
              (vl-stmt->svstmts x.body conf nonblockingp)))
          (mv (and ok1 ok2 ok3 ok4)
              warnings
              (append-without-guard
               initstmts1 initstmts2
               (list (svex::make-svstmt-while
                      :cond cond
                      :body (append-without-guard body stepstmts))))))
        :vl-blockstmt
        (b* (((unless (or x.sequentialp (<= (len x.stmts) 1)))
              (fail (warn :type :vl-stmt->svstmts-fail
                          :msg "We don't support fork/join block statements: ~a0."
                          :args (list x))))
             (warnings (if (or (consp x.vardecls)
                               (consp x.paramdecls))
                           (warn :type :vl-stmt->svstmts-bozo
                                 :msg "Missing support for block ~
                                       statements with local variables: ~a0."
                                 :args (list x))
                         (ok)))
             ;; ((wmv ok1 warnings initstmts)
             ;;  (vl-vardecllist->svstmts x.vardecls conf))
             ((wmv ok2 warnings bodystmts)
              (vl-stmtlist->svstmts x.stmts conf nonblockingp)))
          (mv (and ok2)
              warnings
              bodystmts))
        :otherwise
        (fail (warn :type :vl-stmt->svstmts-fail
                    :msg "Statement type not supported: ~a0."
                    :args (list x))))))

  (define vl-stmtlist->svstmts ((x vl-stmtlist-p)
                                (conf vl-svexconf-p)
                                (nonblockingp))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (res (and (svex::svstmtlist-p res)
                           (svex::svarlist-addr-p
                            (svex::svstmtlist-vars res)))))
    :measure (vl-stmtlist-count x)
    (b* ((warnings nil)
         ((when (atom x)) (mv t (ok) nil))
         ((wmv ok1 warnings x1) (vl-stmt->svstmts (car x) conf nonblockingp))
         ((wmv ok2 warnings x2) (vl-stmtlist->svstmts (cdr x) conf nonblockingp)))
      (mv (and ok1 ok2) warnings (append-without-guard x1 x2))))
  ///
  (verify-guards vl-stmt->svstmts)
  (deffixequiv-mutual vl-stmt->svstmts))







(define vl-fundecl-to-svex  ((x vl-fundecl-p)
                             (ss vl-scopestack-p
                                 "Scopestack including the function decl")
                             (fntable svex::svex-alist-p)
                             (paramtable svex::svex-alist-p))
  :returns (mv (warnings vl-warninglist-p)
               (svex svex::svex-p))
  (b* (((vl-fundecl x) (vl-fundecl-fix x))
       (warnings nil)
       (conf (make-vl-svexconf :ss ss :fns fntable :params paramtable))
       ;; nonblocking assignments not allowed
       ((wmv ok warnings svstmts) (vl-stmt->svstmts x.body conf nil))
       ((unless ok) (mv warnings (svex-x)))
       ((wmv ok warnings svstate)
        (svex::svstmtlist-compile svstmts (svex::make-svstate) 1000
                                  nil ;; nb-delayp
                                  ))
       ((unless ok) (mv warnings (svex-x)))
       ((svex::svstate svstate))
       (expr (svex::svex-lookup (svex::make-svar :name x.name) svstate.blkst))
       (- (svex::svstate-free svstate))
       ((unless expr)
        (mv (warn :type :vl-fundecl-to-svex-fail
                  :msg "Function has no return value"
                  :args (list x))
            (svex-x))))
    (mv (ok) expr))
  ///
  (more-returns
   (svex :name vars-of-vl-fundecl-to-svex
         (svex::svarlist-addr-p (svex::svex-vars svex)))))


(defines vl-funname-svex-compile
  :verify-guards nil
  :prepwork ((set-ruler-extenders '(mv-list return-last :lambdas)))
  :ruler-extenders :all
  :measure-debug t

  (define vl-expr-svex-compile ((x vl-expr-p)
                                (type vl-maybe-datatype-p)
                                (ss vl-scopestack-p)
                                &key ((rec-limit natp) '1000))
    :measure (acl2::nat-list-measure (list rec-limit 0 0))
    :returns (mv (warnings vl-warninglist-p)
                 (expr (and (svex::svex-p expr)
                            (svex::svarlist-addr-p (svex::svex-vars expr))))
                 (res-type (and (vl-maybe-datatype-p res-type)
                                (implies res-type
                                         (vl-datatype-resolved-p res-type)))))
    (b* ((x (vl-expr-fix x))
         (subfns (vl-expr-functions-called x))
         (subparams (vl-expr-parameter-refs x ss))
         (warnings nil)
         ((when (and (zp rec-limit)
                     (or (consp subfns) (consp subparams))))
          (mv (fatal :type :vl-expr-svex-compile-fail
                     :msg "Rec-Limit ran out compiling functions/warnings: ~a0"
                     :args (list x))
              (svex-x) nil))
         ((wmv warnings fntable)
          (if (consp subfns)
              (vl-funnames-svex-compile subfns ss (1- rec-limit))
            (mv nil nil)))
         ((wmv warnings paramtable)
          (if (consp subparams)
              (vl-paramrefs-svex-compile subparams (1- rec-limit))
            (mv nil nil)))
         (conf (make-vl-svexconf :ss ss :fns fntable :params paramtable)))
      (if type
          (b* (((mv err type) (vl-datatype-usertype-resolve type ss))
               ((when err)
                (mv (fatal :type :vl-expr-svex-compile-fail
                           :msg "Type ~a0 is not resolved"
                           :args (list type))
                    (svex-x)
                    nil))
               ((wmv warnings svex) (vl-expr-to-svex-datatyped x type conf)))
            (mv warnings svex type))
        (b* (((wmv warnings svex type) (vl-expr-to-svex-untyped x conf)))
          (mv warnings svex type)))))

  (define vl-funname-svex-compile ((x vl-scopeexpr-p "function name")
                                   (ss vl-scopestack-p)
                                   (rec-limit natp))
    :returns (mv (warnings vl-warninglist-p)
                 (name (implies name (svex::svar-p name)))
                 (expr (and (svex::svex-p expr)
                            (svex::svarlist-addr-p (svex::svex-vars expr)))
                       "The function's return value as an svex expression"))
    :measure (acl2::nat-list-measure (list rec-limit 0 0))
    (b* ((x (vl-scopeexpr-fix x))
         (warnings nil)
         ((mv err name trace) (vl-funname->svex-funname x ss))
         ((when err)
          (mv (fatal :type :vl-funname-svex-compile-fail
                     :msg "function declaration not found: ~@0"
                     :args (list (make-vl-index :scope x :part
                                                (vl-partselect-none))
                                 err))
              nil
              (svex-x)))
         ((vl-hidstep step) (car trace))
         ((unless (eq (tag step.item) :vl-fundecl))
          (mv (fatal :type :Vl-funname-svex-compile-fail
                     :msg "function declaration not found"
                     :args (list (make-vl-index :scope x :part
                                                (vl-partselect-none))
                                 err))
              nil (svex-x)))
         ((vl-fundecl decl) step.item)
         (fn-ss (vl-scopestack-push (vl-fundecl->blockscope decl) step.ss))
         (subfns (vl-stmt-functions-called decl.body))
         (subparams (vl-stmt-parameter-refs decl.body fn-ss))
         ((when (and (atom subfns) (atom subparams)))
          (b* (((mv warnings expr)
                (vl-fundecl-to-svex decl step.ss nil nil)))
            (mv warnings name expr)))
         ((when (zp rec-limit))
          (mv (warn :type :vl-funname-svex-compile-fail
                          :msg "Rec-Limit ran out compiling functions: ~
                                recursion or parameter loops present? (~a0)"
                          :args (list x))
              nil (svex-x)))
         ((wmv warnings fntable)
          (vl-funnames-svex-compile subfns fn-ss (1- rec-limit)))
         ((wmv warnings paramtable)
          (vl-paramrefs-svex-compile subparams (1- rec-limit)))
         ((wmv warnings expr)
          (vl-fundecl-to-svex decl fn-ss fntable paramtable)))
      (mv warnings name expr)))

  (define vl-paramref-svex-compile ((x vl-paramref-p)
                                    (rec-limit natp))
    :returns (mv (warnings vl-warninglist-p)
                 (name svex::svar-p)
                 (expr (and (svex::svex-p expr)
                            (svex::svarlist-addr-p (svex::svex-vars expr)))))
    :measure (acl2::nat-list-measure (list rec-limit 1 0))
    (b* (((vl-paramref x))
         (warnings nil)
         ((wmv warnings expr &)
          (vl-expr-svex-compile x.expr x.type x.ss :rec-limit rec-limit)))
      (mv warnings x.name expr)))

  (define vl-funnames-svex-compile ((x vl-scopeexprlist-p "function names")
                                    (ss vl-scopestack-p)
                                    (reclimit natp))
    :returns (mv (warnings vl-warninglist-p)
                 (fntable svex::svex-alist-p
                          "Table mapping function names to svex expressions"))
    :measure (acl2::nat-list-measure (list reclimit 2 (len x)))
    (b* (((when (atom x)) (mv nil nil))
         (warnings nil)
         ((wmv warnings name1 expr1) (vl-funname-svex-compile (car x) ss reclimit))
         ((wmv warnings rest) (vl-funnames-svex-compile (cdr x) ss reclimit)))
      (mv warnings
          (if name1
              (cons (cons name1 expr1)
                    rest)
            rest))))

  (define vl-paramrefs-svex-compile ((x vl-paramreflist-p)
                                     (reclimit natp))
    :returns (mv (warnings vl-warninglist-p)
                 (paramtable svex::svex-alist-p
                             "Table mapping parameter names to svex expressions"))
    :measure (acl2::nat-list-measure (list reclimit 2 (len x)))
    (b* (((when (atom x)) (mv nil nil))
         (warnings nil)
         ((wmv warnings name1 expr1) (vl-paramref-svex-compile (car x) reclimit))
         ((wmv warnings rest) (vl-paramrefs-svex-compile (cdr x) reclimit)))
      (mv warnings
          (cons (cons name1 expr1)
                rest))))
  ///
  (verify-guards vl-funname-svex-compile :guard-debug t)
  (deffixequiv-mutual vl-funname-svex-compile))


(define vl-expr-compile-fns ((x vl-expr-p)
                             (ss vl-scopestack-p))
  :short "Compiles any functions used by an expression into a svex alist."
  :returns (mv (warnings vl-warninglist-p)
               (fntable svex::svex-alist-p))
  (b* ((fns (vl-expr-functions-called x)))
    (vl-funnames-svex-compile fns ss 1000)))

(define vl-expr-compile-params ((x vl-expr-p)
                                (ss vl-scopestack-p))
  :short "Compiles any functions used by an expression into a svex alist."
  :returns (mv (warnings vl-warninglist-p)
               (paramtable svex::svex-alist-p))
  (b* ((params (vl-expr-parameter-refs x ss)))
    (vl-paramrefs-svex-compile params 1000)))

(define vl-consteval ((x vl-expr-p)
                      (ss vl-scopestack-p)
                      &key ((ctxsize maybe-natp) 'nil))
  :returns (mv (warnings1 vl-warninglist-p)
               (new-x vl-expr-p))
  (b* (((mv warnings fns) (vl-expr-compile-fns x ss))
       ((wmv warnings params) (vl-expr-compile-params x ss))
       ((wmv warnings & new-x)
        (vl-expr-consteval x (make-vl-svexconf :ss ss :fns fns :params params)
                           :ctxsize ctxsize)))
    (mv warnings new-x)))


(define vl-evatomlist-has-edge ((x vl-evatomlist-p))
  (if (atom x)
      nil
    (or (not (eq (vl-evatom->type (car x)) :vl-noedge))
        (vl-evatomlist-has-edge (cdr x)))))


(define vl-evatomlist->svex ((x vl-evatomlist-p)
                             (ss vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p)
               (trigger (and (svex::svex-p trigger)
                             (svex::svarlist-addr-p (svex::svex-vars trigger)))))
  :prepwork ((local (defthm vl-evatom->type-forward
                      (or (equal (vl-evatom->type x) :vl-noedge)
                          (equal (vl-evatom->type x) :vl-negedge)
                          (equal (vl-evatom->type x) :vl-posedge))
                      :hints (("goal" :use vl-evatomtype-p-of-vl-evatom->type
                               ::in-theory (e/d (vl-evatomtype-p)
                                                (vl-evatomtype-p-of-vl-evatom->type))))
                      :rule-classes ((:forward-chaining :trigger-terms ((vl-evatom->type x)))))))
  (b* (((when (atom x)) (mv nil (svex::svex-quote (svex::2vec 0))))
       ((vl-evatom x1) (car x))
       (warnings nil)
       ((wmv warnings expr ?type)
        (vl-expr-to-svex-untyped x1.expr (make-vl-svexconf :ss ss)))
       (delay-expr (svex::svex-add-delay expr 1))
       ;; Note: Ensure these expressions always evaluate to either -1 or 0.
       (trigger1 (case x1.type
                   (:vl-noedge
                    ;; expr and delay-expr are unequal
                    (svex::make-svex-call
                     :fn 'svex::bitnot
                     :args (list (svex::make-svex-call
                                  :fn 'svex::==
                                  :args (list expr delay-expr)))))
                   (:vl-posedge
                    ;; LSBs have a posedge
                    (svex::make-svex-call
                     :fn 'svex::uor
                     :args (list (svex::make-svex-call
                                  :fn 'svex::bitand
                                  :args (list (svex::make-svex-call
                                               :fn 'svex::bitnot
                                               :args (list (svex::make-svex-call
                                                            :fn 'svex::bitsel
                                                            :args (list (svex::svex-quote (svex::2vec 0))
                                                                        delay-expr))))
                                              (svex::make-svex-call
                                               :fn 'svex::bitsel
                                               :args (list (svex::svex-quote (svex::2vec 0))
                                                           expr)))))))
                   (:vl-negedge
                    (svex::make-svex-call
                     :fn 'svex::uor
                     :args (list (svex::make-svex-call
                                  :fn 'svex::bitand
                                  :args (list (svex::make-svex-call
                                               :fn 'svex::bitnot
                                               :args (list (svex::make-svex-call
                                                            :fn 'svex::bitsel
                                                            :args (list (svex::svex-quote (svex::2vec 0))
                                                                        expr))))
                                              (svex::make-svex-call
                                               :fn 'svex::bitsel
                                               :args (list (svex::svex-quote (svex::2vec 0))
                                                           delay-expr)))))))))
       ((wmv warnings rest)
        (vl-evatomlist->svex (cdr x) ss)))
    (mv warnings
        (svex::make-svex-call
         :fn 'svex::bitor
         :args (list trigger1 rest)))))




;; The Verilog flop problem: Translating edge-triggered Verilog blocks into
;; FSM-style stuff is hard.  Example:

#|

always @(posedge clk or negedge resetb) begin
  if (resetb) begin
    if (test)
       foo <= bar;
    else
       foo <= baz;
  end else
    foo <= 0;
end

|#

;; We want a formula for the current value of foo involving the current and
;; former values of clk, resetb, test, bar, and baz, and the former value of
;; foo.  This is basically impossible, as we'll show.  But we hope to come up
;; with a way to generate something plausible.  First, let's try a naive
;; translation (using a' to denote the previous phase's value of a):

#|

assign foo = ((~clk' & clk) | (resetb' & ~resetb)) ?
                  ( resetb ? (test ? bar : baz) : 0 )
                : foo';

|#

;; Here a posedge of clk or a negedge of resetb triggers an update of foo,
;; which otherwise keeps its previous value.  The problem here is that foo gets
;; updated with the current, not previous, values of bar/baz.  This isn't a
;; good model of a flip-flop, because we want a series of flops that all toggle
;; at once to pass values through a cycle at a time, not all at once.  Second try:

#|

assign foo = ((~clk' & clk) | (resetb' & ~resetb)) ?
                  ( resetb' ? (test' ? bar' : baz') : 0 )
                : foo';

|#

;; This is now correctly uses the previous values of bar', baz'.  But when
;; resetb has a negedge, this doesn't set foo to 0, because the mux is testing
;; the previous value of resetb', where it should be looking at the current one
;; (since that's what triggered the update in the first place).  Another
;; possibility is to use the current values of IF tests but the previous values
;; of RHSes:

#|

assign foo = ((~clk' & clk) | (resetb' & ~resetb)) ?
                  ( resetb ? (test ? bar' : baz') : 0 )
                : foo';

|#

;; This works (heuristically) in a lot of common cases, but this isn't one of
;; them.  It also wouldn't work if the flop was instead phrased as 

#|

always @(posedge clk or negedge resetb) begin
  foo <= resetb ? test ? bar : baz : 0;
end

|#

;; Another candidate: delay everything except the variables that are part of
;; the trigger:

#|

assign foo = ((~clk' & clk) | (resetb' & ~resetb)) ?
                  ( resetb ? (test' ? bar' : baz') : 0 )
                : foo';

|#

;; This seems like what we want.  One thing that isn't clear is what the
;; behavior should be when resetb has a __positive__ edge (and the clock does
;; too).  The problem is that this could go two different ways due to factors
;; external to the always block: namely, is resetb updated by a flop also, or
;; is it an input signal that might be updated at the same time as/earlier than
;; the clock?  In a continuous-time interpretation, if resetb toggles from 0 to
;; 1 slightly before the clock's posedge, we get a different answer than if it
;; does so slightly after.

;; So: another option is to use (resetb ? resetb' : resetb) for resetb, i.e.,
;; use the delayed value if we don't have a negedge, and the current value if
;; we do:

#|

assign foo = ((~clk' & clk) | (resetb' & ~resetb)) ?
                  ( ( resetb ? resetb' : resetb ) ? (test' ? bar' : baz') : 0 )
                : foo';

|#

;; This might get somewhat more correct answers than the previous version: it
;; gets it right if resetb is driven by a clk-driven flop, and it also gets it
;; right if reset generally arrives later than clk.  We'll go with this
;; approach for now.  If necessary, we can allow per-always configurations for
;; the order in which signals arrive.

;; This function creates the substitution mapping resetb to (resetb ? resetb' :
;; resetb), etc.



    
(define vl-evatomlist-delay-substitution ((x vl-evatomlist-p)
                                          (edge-dependent-delayp)
                                          (ss vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p)
               (subst (and (svex::svex-alist-p subst)
                           (svex::svarlist-addr-p (svex::svex-alist-vars subst))
                           (svex::svarlist-addr-p (svex::svex-alist-keys subst)))
                      :hints(("Goal" :in-theory (enable svex::svex-alist-keys
                                                        svex::svex-alist-vars)))))
  :prepwork ((local (defthm vl-evatom->type-forward
                      (or (equal (vl-evatom->type x) :vl-noedge)
                          (equal (vl-evatom->type x) :vl-negedge)
                          (equal (vl-evatom->type x) :vl-posedge))
                      :hints (("goal" :use vl-evatomtype-p-of-vl-evatom->type
                               ::in-theory (e/d (vl-evatomtype-p)
                                                (vl-evatomtype-p-of-vl-evatom->type))))
                      :rule-classes ((:forward-chaining :trigger-terms ((vl-evatom->type x))))))
             (local (in-theory (disable member-equal))))
  (b* (((when (atom x)) (mv nil nil))
       ((vl-evatom x1) (car x))
       (warnings nil)
       ((unless (vl-expr-case x1.expr
                  :vl-index (and (vl-partselect-case x1.expr.part :none)
                                 (atom x1.expr.indices))
                  :otherwise nil))
        ;; We're going to deal with all these sorts of problems elsewhere?
        (vl-evatomlist-delay-substitution (cdr x) edge-dependent-delayp ss))
       ((mv err opinfo) (vl-index-expr-typetrace x1.expr ss))
       ((when err)
        ;; We're going to deal with all these sorts of problems elsewhere?
        (vl-evatomlist-delay-substitution (cdr x) edge-dependent-delayp ss))
       ((vl-operandinfo opinfo))
       ((unless (and (vl-hidtrace-resolved-p opinfo.hidtrace)
                     (eql (vl-seltrace-unres-count opinfo.seltrace) 0)))
        ;; We're going to deal with all these sorts of problems elsewhere?
        (vl-evatomlist-delay-substitution (cdr x) edge-dependent-delayp ss))
       ((mv err var) (vl-seltrace-to-svar opinfo.seltrace opinfo ss))
       ((when err)
        ;; We're going to deal with all these sorts of problems elsewhere?
        (vl-evatomlist-delay-substitution (cdr x) edge-dependent-delayp ss))
       (expr (svex::make-svex-var :name var))
       (delay-expr (if edge-dependent-delayp
                       (case x1.type
                         (:vl-noedge
                          ;; always use the current value.
                          expr)
                         (:vl-posedge
                          ;; x ? x : x'
                          (svex::make-svex-call
                           :fn 'svex::?
                           :args (list (svex::make-svex-call
                                        :fn 'svex::bitsel
                                        :args (list (svex::svex-quote (svex::2vec 0))
                                                    expr))
                                       expr
                                       (svex::svex-add-delay expr 1))))
                         (:vl-negedge
                          ;; x ? x' : x
                          (svex::make-svex-call
                           :fn 'svex::?
                           :args (list (svex::make-svex-call
                                        :fn 'svex::bitsel
                                        :args (list (svex::svex-quote (svex::2vec 0))
                                                    expr))
                                       (svex::svex-add-delay expr 1)
                                       expr))))
                     expr))
       ((wmv warnings rest)
        (vl-evatomlist-delay-substitution (cdr x) edge-dependent-delayp ss)))
    (mv warnings
        (cons (cons var delay-expr) rest))))


       
(define vl-always->svex-checks ((x vl-always-p)
                                (ss vl-scopestack-p))
  :short "Checks that the always block is suitable for translating to svex, ~
          and returns the body statement and eventcontrol."
  :returns (mv (ok)
               (warnings vl-warninglist-p)
               (stmt (implies ok (vl-stmt-p stmt))
                     "on success, the body of the always block, without any eventcontrol")
               (trigger (and (iff (svex::svex-p trigger) trigger)
                             (implies trigger
                                      (svex::svarlist-addr-p (svex::svex-vars trigger))))
                        "If present, indicates a flop rather than a latch/combinational block.")
               (trigger-subst
                (and (svex::svex-alist-p trigger-subst)
                     (svex::svarlist-addr-p (svex::svex-alist-vars trigger-subst))
                     (svex::svarlist-addr-p (svex::svex-alist-keys trigger-subst)))))
  :prepwork ((local (defthm vl-evatomlist->svex-under-iff
                      (mv-nth 1 (vl-evatomlist->svex x ss))
                      :hints (("goal" :use return-type-of-vl-evatomlist->svex.trigger
                               :in-theory (disable return-type-of-vl-evatomlist->svex.trigger))))))
  (b* (((vl-always x) (vl-always-fix x))
       (warnings nil))
    (case x.type
      ((:vl-always-comb :vl-always-latch)
       (mv t (ok) x.stmt nil nil))
      (otherwise
       (b* (((unless (and (eq (vl-stmt-kind x.stmt) :vl-timingstmt)
                          (eq (tag (vl-timingstmt->ctrl x.stmt)) :vl-eventcontrol)))
             (mv nil
                 (warn :type :vl-always->svex-fail
                       :msg "We only support always and always_ff blocks ~
                             that have a sensitivity list."
                       :args (list x))
                 nil nil nil))
            ((vl-timingstmt x.stmt))
            ((when (or (vl-eventcontrol->starp x.stmt.ctrl)
                       (not (vl-evatomlist-has-edge (vl-eventcontrol->atoms x.stmt.ctrl)))))
             (b* ((warnings (if (eq x.type :vl-always-ff)
                                (warn :type :vl-always-ff-warning
                                      :msg "Always_ff is not edge-triggered."
                                      :args (list x))
                              (ok))))
               (mv t (ok) x.stmt.body nil nil)))

            ;; We have a flop. Collect its trigger.
            ((wmv warnings trigger) (vl-evatomlist->svex
                                     (vl-eventcontrol->atoms x.stmt.ctrl) ss))
            ((wmv warnings trigger-subst) (vl-evatomlist-delay-substitution
                                           (vl-eventcontrol->atoms x.stmt.ctrl)
                                           t ss)))
         (mv t
             warnings
             x.stmt.body
             trigger
             trigger-subst))))))
             
#!svex
(define svar->lhs-by-mask ((x svar-p)
                           (mask 4vmask-p))
  :short "Given a variable and a mask of bits, create an LHS that covers those bits."
  :long "<p>Fails by returning an empty LHS if the mask is negative, i.e. an ~
         infinite range of bits should be written.</p>"
  :returns (lhs lhs-p)
  (and (< 0 (4vmask-fix mask))
       (list (make-lhrange :w (integer-length (4vmask-fix mask))
                           :atom (make-lhatom-var :name x :rsh 0))))
  ///
  (defthm vars-of-svar->lhs-by-mask
    (implies (not (equal v (svar-fix x)))
             (not (member v (lhs-vars (svar->lhs-by-mask x mask)))))
    :hints(("Goal" :in-theory (enable lhatom-vars)))))

#!svex
(define svex-alist->assigns ((x svex-alist-p)
                             (masks 4vmask-alist-p))
  :short "Given an svex alist, return an assignment alist, i.e. transform the bound
          variables into LHSes based on the given masks, which represent the bits
          of the variables that are supposed to be written."
  :returns (assigns assigns-p)
  :measure (len (svex-alist-fix x))
  (b* ((x (svex-alist-fix x))
       (masks (4vmask-alist-fix masks))
       ((when (atom x)) nil)
       ((cons var rhs) (car x))
       (mask (or (cdr (hons-get var masks)) 0))
       (lhs (svar->lhs-by-mask var mask)))
    (cons (cons lhs
                (make-driver
                 :value (make-svex-call :fn 'bit?
                                        :args (list (svex::svex-quote (svex::2vec mask))
                                                    rhs
                                                    (svex-z)))))
          (svex-alist->assigns (cdr x) masks)))
  ///

  ;; (local
  ;;  (defthm not-consp-of-svex-alist-fix
  ;;    (implies (not (consp x))
  ;;             (equal (svex-alist-fix x) nil))
  ;;    :hints(("Goal" :in-theory (enable svex-alist-fix)))
  ;;    :rule-classes ((:rewrite :backchain-limit-lst 0))))

  (local
   (defthm expand-svex-alist-vars
     (equal (svex-alist-vars x)
            (if (consp (svex-alist-fix x))
                (union (svex-vars (cdar (svex-alist-fix x)))
                       (svex-alist-vars (cdr (svex-alist-fix x))))
              nil))
     :hints(("Goal" :in-theory (e/d (svex-alist-vars svex-alist-fix))))
     :rule-classes :definition))

  (local
   (defthm expand-svex-alist-keys
     (equal (svex-alist-keys x)
            (if (consp (svex-alist-fix x))
                (cons (svar-fix (caar (svex-alist-fix x)))
                      (svex-alist-keys (cdr (svex-alist-fix x))))
              nil))
     :hints(("Goal" :in-theory (e/d (svex-alist-keys svex-alist-fix))))
     :rule-classes :definition))

  (defthm vars-of-svex-alist->assigns
    (implies (and (not (member v (svex-alist-keys x)))
                  (not (member v (svex-alist-vars x))))
             (not (member v (assigns-vars (svex-alist->assigns x masks)))))
    :hints(("Goal" :in-theory (enable assigns-vars
                                      svex-alist-keys svex-alist-vars)
            :induct (svex-alist->assigns x masks)
            :expand ((svex-alist->assigns x masks))))))



#!svex
(define svarlist-delay-subst ((x svarlist-p))
  :short "Creates a substitution alist that maps the given variables to their 1-tick
          delayed versions.  Warns if the variables aren't of the expected
          form."
  :returns (subst svex-alist-p)
  (if (atom x)
      nil
    (cons (cons (svar-fix (car x))
                (make-svex-var :name (svar-add-delay (car x) 1)))
          (svarlist-delay-subst (cdr x))))
  :prepwork ((local (defthm svar-map-p-of-pairlis$
                      (implies (and (svarlist-p x)
                                    (svarlist-p y)
                                    (equal (len x) (len y)))
                               (svar-map-p (pairlis$ x y)))
                      :hints(("Goal" :in-theory (enable svar-map-p pairlis$))))))
  ///
  (defthm vars-of-svarlist-delay-subst
    (implies (svarlist-addr-p x)
             (svarlist-addr-p (svex-alist-vars (svarlist-delay-subst x))))
    :hints(("Goal" :in-theory (enable svex-alist-vars))))

  (defthm keys-of-svarlist-delay-subst
    (implies (and (not (member v (svarlist-fix x)))
                  (svar-p v))
             (not (svex-lookup v (svarlist-delay-subst x))))
    :hints(("Goal" :in-theory (enable svex-alist-keys
                                      svex-lookup)))))

#!svex
(define svarlist-x-subst ((x svarlist-p))
  :short "Creates a substitution alist that maps the given variables to X."
  :returns (subst svex-alist-p)
  (b* (((when (atom x)) nil))
    (cons (cons (svar-fix (car x))
                (svex-x))
          (svarlist-x-subst (cdr x))))
  ///
  (defthm svex-lookup-of-svarlist-x-subst
    (implies (and (not (member v (svarlist-fix x)))
                  (svar-p v))
             (not (svex-lookup v (svarlist-x-subst x))))
    :hints(("Goal" :in-theory (enable svex-alist-keys svex-lookup))))

  (defthm vars-of-svarlist-x-subst
    (equal (svex-alist-vars (svarlist-x-subst x)) nil)
    :hints(("Goal" :in-theory (enable svex-alist-vars)))))

(define vl-always->svex-latch-warnings ((write-masks svex::4vmask-alist-p)
                                        (read-masks svex::svex-mask-alist-p))
  :returns (warnings vl-warninglist-p)
  :measure (len (svex::4vmask-alist-fix write-masks))
  (b* ((warnings nil)
       (write-masks (svex::4vmask-alist-fix write-masks))
       ((when (atom write-masks)) (ok))
       ;; ((unless (mbt (consp (car write-masks))))
       ;;  (vl-always->svex-latch-warnings (cdr write-masks) read-masks))
       ((cons var wmask) (car write-masks))
       (var (svex::svar-fix var))
       (wmask (svex::4vmask-fix wmask))
       (rmask (svex::svex-mask-lookup (svex::make-svex-var :name var) read-masks))
       (overlap (logand wmask rmask))
       (warnings (if (eql overlap 0)
                     warnings
                   (warn :type :vl-always-comb-looks-like-latch
                         :msg "Variable ~a0 was both read and written ~
                               (or not always updated) in an always_comb ~
                               block.  We will treat it as initially X, but ~
                               this may cause mismatches with Verilog ~
                               simulators, which will treat it as a latch.  ~
                               Overlap of read and write bits: ~s1"
                         :args (list var (str::hexify overlap)))))
       ((wmv warnings)
        (vl-always->svex-latch-warnings (cdr write-masks) read-masks)))
    warnings))
                   

#!svex
(define svarlist-remove-delays ((x svarlist-p))
  (if (atom x)
      nil
    (cons (b* (((svar x1) (car x)))
            (make-svar :name x1.name))
          (svarlist-remove-delays (cdr x)))))



;; (local
;;  #!svex
;;  (encapsulate nil
   
;;    (defthm svex-lookup-in-fast-alist-clean
;;      (implies (svex-alist-p x)
;;               (iff (svex-lookup v (fast-alist-clean x))
;;                    (svex-lookup v x))))))

(define combine-mask-alists ((masks svex::4vmask-alist-p)
                             (acc svex::4vmask-alist-p))
  :returns (res svex::4vmask-alist-p)
  :measure (len (svex::4vmask-alist-fix masks))
  :prepwork ((local (defthm integerp-lookup-in-4vmask-alist
                      (implies (and (svex::4vmask-alist-p x)
                                    (hons-assoc-equal k x))
                               (integerp (cdr (hons-assoc-equal k x))))
                      :hints(("Goal" :in-theory (enable svex::4vmask-alist-p
                                                        hons-assoc-equal))))))
  (b* ((masks (svex::4vmask-alist-fix masks))
       (acc (svex::4vmask-alist-fix acc))
       ((When (atom masks)) acc)
       ((cons key val) (car masks))
       (look (or (cdr (hons-get key acc)) 0))
       (newval (logior val look)))
    (combine-mask-alists (cdr masks) (hons-acons key newval acc))))




    
(define vl-always-apply-trigger-to-updates ((trigger svex::svex-p)
                                            (x svex::svex-alist-p))
  :returns (new-x svex::svex-alist-p)
  :measure (len (svex::svex-alist-fix x))
  (b* ((x (svex::svex-alist-fix x))
       ((when (atom x)) nil)
       ((cons var upd) (car x))
       (prev-var (svex::make-svex-var :name (svex::svar-add-delay var 1)))
       (trigger-upd (svex::make-svex-call
                     :fn 'svex::?
                     :args (list trigger upd prev-var))))
    (cons (cons var trigger-upd)
          (vl-always-apply-trigger-to-updates trigger (cdr x))))
  ///
  (local (defthm svex-p-compound-recognizer
           (implies (svex::svex-p x) x)
           :rule-classes :compound-recognizer))
  (local (defthm svex-fix-type
           (svex::svex-p (svex::svex-fix x))
           :rule-classes ((:type-prescription :typed-term (svex::svex-fix x)))))
  (local (defthm cdar-of-svex-alist-fix
           (implies (consp (svex::svex-alist-fix x))
                    (cdar (svex::svex-alist-fix x)))
           :hints(("Goal" :in-theory (enable svex::svex-alist-fix)))))
  (more-returns
   (new-x :name keys-of-vl-always-apply-trigger-to-updates
          (iff (svex::svex-lookup v new-x)
               (svex::svex-lookup v x))
          :hints(("Goal" :in-theory (enable svex::svex-lookup
                                            hons-assoc-equal)))))
  (local (in-theory (disable svex::member-of-svarlist-add-delay)))

  (local
   (more-returns
    (new-x :name vars-of-vl-always-apply-trigger-to-updates-lemma
           (implies (and (not (member v (svex::svex-alist-vars x)))
                         (not (member v (svex::svex-vars trigger)))
                         (not (member v (svex::svarlist-add-delay
                                         (svex::svex-alist-keys x) 1)))
                         (svex::svex-alist-p x))
                    (not (member v (svex::svex-alist-vars new-x))))
           :hints(("Goal" :induct (vl-always-apply-trigger-to-updates trigger x)
                   :in-theory (enable svex::svex-alist-vars
                                      svex::svex-alist-keys))))))
  (more-returns
    (new-x :name vars-of-vl-always-apply-trigger-to-updates
           (implies (and (not (member v (svex::svex-alist-vars x)))
                         (not (member v (svex::svex-vars trigger)))
                         (not (member v (svex::svarlist-add-delay
                                         (svex::svex-alist-keys x) 1))))
                    (not (member v (svex::svex-alist-vars new-x))))
           :hints(("Goal" :induct (svex::svex-alist-fix x)
                   :expand ((vl-always-apply-trigger-to-updates trigger x)
                            (svex::svex-alist-vars x)
                            (svex::svex-alist-fix x)
                            (:free (a b) (svex::svex-alist-vars (cons a b)))
                            (svex::svex-alist-keys x))
                   :in-theory (enable svex::svex-alist-fix))))))


(define vl-always->svex ((x vl-always-p)
                         (ss vl-scopestack-p))
  :short "Translate a combinational or latch-type always block into a set of SVEX
          expressions."
  :returns (mv (warnings vl-warninglist-p)
               (assigns (and (svex::assigns-p assigns)
                             (svex::svarlist-addr-p (svex::assigns-vars assigns)))))
  :prepwork ((local
              #!svex (defthm cdr-last-when-svex-alist-p
                       (implies (svex-alist-p x)
                                (equal (cdr (last x)) nil))
                       :hints(("Goal" :in-theory (enable svex-alist-p)))))
             (local
              #!svex (defthm cdr-last-when-4vmask-alist-p
                       (implies (4vmask-alist-p x)
                                (equal (cdr (last x)) nil))
                       :hints(("Goal" :in-theory (enable 4vmask-alist-p)))))
             (local (defthm fast-alist-fork-nil
                      (equal (fast-alist-fork nil y) y)))
             (local (in-theory (disable fast-alist-fork)))
             (local (defthm lookup-in-svex-alist-under-iff
                      (implies (svex::svex-alist-p a)
                               (iff (cdr (hons-assoc-equal x a))
                                    (hons-assoc-equal x a)))
                      :hints(("Goal" :in-theory (enable svex::svex-alist-p)))))
             #!svex
             (local (Defthm svex-lookup-of-append
                      (iff (svex-lookup x (append a b))
                           (or (svex-lookup x a)
                               (svex-lookup x b)))
                      :hints(("Goal" :in-theory (enable svex-lookup)))))
             (local (in-theory (disable svex::member-of-svarlist-add-delay))))
  :guard-debug t
  (b* ((warnings nil)
       ((vl-always x) (vl-always-fix x))
       ((wmv ok warnings stmt trigger trigger-subst)
        (vl-always->svex-checks x ss))
       ((unless ok) (mv warnings nil))
       (fnnames (vl-stmt-functions-called stmt))
       (params  (vl-stmt-parameter-refs stmt ss))
       ((wmv warnings fntable) (vl-funnames-svex-compile fnnames ss 1000))
       ((wmv warnings paramtable) (vl-paramrefs-svex-compile params 1000))
       ((wmv ok warnings svstmts)
        (vl-stmt->svstmts stmt (make-vl-svexconf :ss ss :fns fntable :params paramtable) t))
       ((unless ok) (mv warnings nil))
       ;; Only use the nonblocking-delay strategy for flops, not latches
       ((wmv ok warnings st)
        (svex::svstmtlist-compile svstmts (svex::make-svstate) 1000 nil))
       ((unless ok) (mv warnings nil))

       ((svex::svstate st) (svex::svstate-clean st))


       (blk-written-vars (svex::svex-alist-keys st.blkst))
       (nb-written-vars  (svex::svex-alist-keys st.nonblkst))

       (both-written (acl2::hons-intersection blk-written-vars nb-written-vars))
       ((when both-written)
        (mv (warn :type :vl-always->svex-fail
                  :msg "~a0: Variables written by both blocking and ~
                        nonblocking assignments: ~x1"
                  :args (list x both-written))
            nil))

       (written-vars (append blk-written-vars nb-written-vars))
       ;; Set initial values of the registers in the expressions.  We'll
       ;; set these to Xes for always_comb and to their delay-1 values for
       ;; other types.
       (subst
        (if (eq x.type :vl-always-comb)
            (svex::svarlist-x-subst written-vars)
          (svex::svarlist-delay-subst written-vars)))

       (nb-read-vars (svex::svex-alist-vars st.nonblkst))

       ;; Note: Because we want to warn about latches in a combinational
       ;; context, we do a rewrite pass before substituting.
       (blkst-rw (svex::svex-alist-rewrite-fixpoint st.blkst))
       (nbst-rw  (svex::svex-alist-rewrite-fixpoint st.nonblkst))
       (read-masks (svex::svexlist-mask-alist
                    (append (svex::svex-alist-vals blkst-rw)
                            (svex::svex-alist-vals nbst-rw))))
       ((mv blkst-write-masks nbst-write-masks)
        (svex::svstmtlist-write-masks svstmts nil nil))
       (write-masks (fast-alist-clean
                     (combine-mask-alists blkst-write-masks nbst-write-masks)))

       ((wmv warnings)
        (if (eq x.type :vl-always-comb)
            (vl-always->svex-latch-warnings write-masks read-masks)
          warnings))
       
       ((with-fast subst))

       ;; Should we apply the substitution to the trigger?  This only matters
       ;; if we are triggering on some variable we're also writing to, which
       ;; seems like a bad case we should probably warn about.  For now we
       ;; won't worry.
       (blkst-subst (svex::svex-alist-compose blkst-rw subst))
       (nbst-subst (svex::svex-alist-compose nbst-rw subst))


       (nbst-trigger
        (if trigger
            ;; Add a tick-delay to all variables in the nbst, except for those
            ;; in the trigger list, except whey they can't be the ones
            ;; triggering.  See "The Verilog flop problem" above.
            (b* ((nb-delaysubst (append-without-guard
                                 trigger-subst
                                 (svex::svarlist-delay-subst nb-read-vars)))
                 (nbst-subst2 (with-fast-alist nb-delaysubst
                                (svex::svex-alist-compose nbst-subst nb-delaysubst))))
              (vl-always-apply-trigger-to-updates
               trigger nbst-subst2))
          (svex::svex-alist-add-delay nbst-subst 1)))

       (blkst-trigger (if trigger
                          (vl-always-apply-trigger-to-updates trigger blkst-subst)
                        blkst-subst))

       (updates (append nbst-trigger blkst-trigger))
      
       (updates-rw (svex::svex-alist-rewrite-fixpoint updates))

       ;; Compilation was ok.  Now we need to turn the state back into a list
       ;; of assigns.  Do this by getting the masks of what portion of each
       ;; variable was written, and use this to turn the alist into a set of
       ;; assignments.
       (assigns (svex::svex-alist->assigns updates-rw write-masks)))
    (mv warnings assigns)))

(define vl-alwayslist->svex ((x vl-alwayslist-p)
                             (ss vl-scopestack-p))
  :short "Translate a combinational or latch-type always block into a set of SVEX
          expressions."
  :returns (mv (warnings vl-warninglist-p)
               (assigns (and (svex::assigns-p assigns)
                             (svex::svarlist-addr-p (svex::assigns-vars assigns)))))
  (b* ((warnings nil)
       ((when (atom x)) (mv (ok) nil))
       ((wmv warnings assigns1)
        (vl-always->svex (car x) ss))
       ((wmv warnings assigns2)
        (vl-alwayslist->svex (cdr x) ss)))
    (mv warnings
        (append-without-guard assigns1 assigns2))))
