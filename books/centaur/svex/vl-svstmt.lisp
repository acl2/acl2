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
;; (include-book "vl-fns-called")
;; (include-book "vl-paramrefs")
(include-book "vl-expr")
(include-book "centaur/fty/visitor" :dir :system)
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


(define vl-index-expr-svex/size/type ((x vl-expr-p)
                                      (conf vl-svexconf-p))
  :guard (vl-expr-case x :vl-index)
  :returns (mv (ok)
               (warnings vl-warninglist-p)
               (svex svex::svex-p)
               (type (implies ok (vl-datatype-p type)))
               (size (implies ok (natp size)) :rule-classes :type-prescription))
  (b* ((warnings nil)
       ((wmv warnings svex type) (vl-index-expr-to-svex x conf))
       ((unless type) (mv nil warnings svex nil nil))
       ((mv err size) (vl-datatype-size type))
       ((when (or err (not size)))
        ;; (break$)
        (mv nil
            (fatal :type :vl-expr-to-svex-fail
                   :msg "Couldn't size the datatype ~a0 of ~
                                    LHS expression ~a1: ~@2"
                   :args (list type (vl-expr-fix x) (or err (vmsg "unsizeable"))))
            svex nil nil)))
    (mv t warnings svex type size))
  ///
  (defret vars-of-vl-index-expr-svex/size/type
    (svex::svarlist-addr-p (svex::svex-vars svex))))

;; #!svex
;; (define svex-resolve-single-assignment-aux ((w svex-p)
;;                                             (r svex-p)
;;                                             (v svex-p)
;;                                             (lhs svex-p)
;;                                             (rhs svex-p)
;;                                             (wholevar svex-p))

;;   :returns (mv (err (iff (vl::vl-msg-p err) err))
;;                (final-rhs (implies (not err) (svex-p final-rhs))))
;;   (b* (((unless (svex-equiv v wholevar))
;;         (mv (vl::vmsg "Variables mismatched: ~x0, ~x1"
;;                       (svex-fix lhs) (svex-fix wholevar)) nil))
;;        ((unless (svex-case w :quote))
;;         (mv (vl::vmsg "Variable width select in LHS: ~x0" (svex-fix lhs)) nil)))
;;     (mv nil
;;         (svcall concat r wholevar
;;                 (svcall concat w rhs
;;                         (svcall rsh (svcall + w r) wholevar)))))
;;   ///
;;   (std::defret vars-of-svex-resolve-single-assignment-aux
;;     (implies (and (not (member var (svex-vars w)))
;;                   (not (member var (svex-vars r)))
;;                   (not (member var (svex-vars v)))
;;                   (not (member var (svex-vars rhs)))
;;                   (not err))
;;              (not (member var (svex-vars final-rhs))))))


#!svex
(define svex-resolve-single-assignment ((lhs svex-p)
                                        (rhs svex-p)
                                        (wholevar svex-p))
  :measure (svex-count lhs)
  :returns (mv (err (iff (vl::vl-msg-p err) err))
               (final-rhs (implies (not err) (svex-p final-rhs))))
  (b* (((when (svex-equiv wholevar lhs)) (mv nil (svex-fix rhs)))
       ((mv ok al) (svex-unify (svcall concat 'w 'a 'b)
                               lhs nil))
       ((when ok)
        (b* ((w (svex-lookup 'w al))
             (a (svex-lookup 'a al))
             (b (svex-lookup 'b al))
             ((when (or (equal b (svex-x))
                        (equal b (svex-z))))
              ;; (concat w a Z) = rhs --> b = (concat w rhs (rsh w a))
              (svex-resolve-single-assignment
               a (svcall concat w rhs (svcall rsh w a)) wholevar))
             ((when (equal a (svex-x)))
              ;; (concat w Z b) = rhs --> b = (rsh w rhs)
              (svex-resolve-single-assignment
               b (svcall rsh w rhs) wholevar)))
          (mv (vl::vmsg "Unexpected form of svex assignment LHS: ~x0" (svex-fix lhs))
              nil)))
       ((mv ok al) (svex-unify (svcall rsh 'w 'v) lhs nil))
       ((when ok)
        (b* ((w (svex-lookup 'w al))
             (v (svex-lookup 'v al)))
          ;; (rsh w v) = rhs --> v = (concat w v rhs)
          (svex-resolve-single-assignment
           v (svcall concat w v rhs) wholevar))))
    (mv (vl::vmsg "Unexpected form of svex assignment LHS: ~x0 (variable: ~x1)"
                  (svex-fix lhs) (svex-fix wholevar))
        nil))
  ///
  (std::defret vars-of-svex-resolve-single-assignment
    (implies (and (not (member v (svex-vars lhs)))
                  (not (member v (svex-vars rhs)))
                  (not err))
             (not (member v (svex-vars final-rhs))))))


  ;;            ((unless (svex-equiv v wholevar))
  ;;             (mv (vl::vmsg "Variables mismatched: ~x0, ~x1" lhs wholevar) nil))
  ;;            ((unless (svex-case w :quote))
  ;;             (mv (vl::vmsg "Variable width select in LHS: ~x0" lhs) nil)))
  ;;         (mv nil
  ;;             (svcall concat w rhs
  ;;                     (svcall rsh w wholevar)))))
             
  ;; (svex-case lhs
  ;;   :quote (mv (vl::vmsg "Unexpectedly encountered constant: ~x0" lhs.val) nil) 
  ;;   :var (if (svex-equiv lhs wholevar)
  ;;            (mv nil rhs)
  ;;          (mv (vl::vmsg "Variables mismatched: ~x0, ~x1" lhs wholevar) nil))
  ;;   :call
  ;;   (case lhs.fn
  ;;     (rsh (b* (((unless (eql (len lhs.args) 2))
  ;;                (mv (vl::msg "Malformed: ~x0" lhs) nil)))
  ;;            (svex-resolve-single-assignment
  ;;             (second lhs.args)
  ;;             (svcall concat (first lhs.args) wholevar rhs)
                


(define vl-single-procedural-assign->svstmts ((lhs svex::svex-p)
                                              (lhssize natp)
                                              (wholevar svex::svex-p)
                                              (varsize natp)
                                              (rhs svex::svex-p)
                                              (blockingp booleanp))
  :returns (mv (ok)
               (warnings vl-warninglist-p)
               (res svex::svstmtlist-p))
  (b* ((warnings nil)
       (lhs-simp1 (svex::svex-concat lhssize (svex::svex-lhsrewrite lhs 0 lhssize)
                                     (svex::svex-z)))
       ((when (svex::lhssvex-p lhs-simp1))
        (mv t (ok)
            (list (svex::make-svstmt-assign
                   :lhs (svex::svex->lhs lhs-simp1)
                   :rhs rhs
                   :blockingp blockingp))))
       ;; Above covers the case where we have static indices.  Now try and deal
       ;; with dynamic indices.
       ;; BOZO This makes it important that svex rewriting normalize select
       ;; operations to concats and right shifts.  It does this now, and it
       ;; seems unlikely we'll want to change that.
       ;; First make sure we can process wholevar into an LHS.
       (varsvex (svex::svex-concat varsize (svex::svex-lhsrewrite wholevar 0 varsize)
                                   (svex::svex-z)))
       ((unless (svex::lhssvex-p varsvex))
        (mv nil
            (fatal :type :vl-assignstmt-fail
                   :msg "Failed to process whole variable as svex LHS -- ~
                         dynamic instance select or something? ~x0"
                   :args (list (svex::svex-fix wholevar)))
            nil))
       (var-lhs (svex::svex->lhs varsvex))

       (simp-lhs (svex::svex-rewrite lhs-simp1 (svex::svexlist-mask-alist (list lhs-simp1))))

       ((mv err final-rhs)
        (svex::svex-resolve-single-assignment simp-lhs rhs wholevar))

       ((when err)
        (mv nil
            (fatal :type :vl-assignstmt-fail
                   :msg "Failed to process LHS for dynamic select assignment: ~@0"
                   :args (list err))
            nil)))
    (mv t nil
        (list
         (svex::make-svstmt-assign :lhs var-lhs :rhs final-rhs :blockingp blockingp))))
  ///
  (defret vars-of-vl-single-procedural-assign->svstmts
    (implies (and (not (member v (svex::svex-vars lhs)))
                  (not (member v (svex::svex-vars rhs)))
                  (not (member v (svex::svex-vars wholevar))))
             (not (member v (svex::svstmtlist-vars res))))))


(defines vl-procedural-assign->svstmts
  (define vl-procedural-assign->svstmts ((lhs vl-expr-p)
                                         (rhssvex svex::svex-p)
                                         (blockingp booleanp)
                                         (conf vl-svexconf-p))
    :measure (vl-expr-count lhs)
    :verify-guards nil
    :returns (mv ok
                 (warnings vl-warninglist-p)
                 (svstmts svex::svstmtlist-p)
                 (shift (implies ok (natp shift)) :rule-classes :type-prescription))
    (b* ((warnings nil)
         (lhs (vl-expr-fix lhs)))
      (vl-expr-case lhs
        :vl-index
        (b* (((wmv ok warnings lhssvex ?type size)
              (vl-index-expr-svex/size/type lhs conf))
             ((unless ok)
              (mv nil warnings nil nil))
             ((vl-svexconf conf))
             ((mv err opinfo) (vl-index-expr-typetrace lhs conf.ss conf.typeov))
             ((when err)
              (mv nil
                  (fatal :type :vl-assignstmt-fail
                         :msg "Failed to get type of LHS ~a0: ~@1"
                         :args (list lhs err))
                  nil nil))
             ((vl-operandinfo opinfo))
             ((wmv ok warnings wholesvex ?wholetype wholesize)
              (vl-index-expr-svex/size/type
               (make-vl-index :scope opinfo.prefixname) conf))
             ((unless ok) (mv nil warnings nil nil))
             ((wmv ok warnings svstmts)
              (vl-single-procedural-assign->svstmts
               lhssvex size wholesvex wholesize rhssvex blockingp)))
          (mv ok warnings svstmts (and ok size)))
        :vl-concat
        (vl-procedural-assign-concat->svstmts lhs.parts rhssvex blockingp conf)
        :otherwise
        (mv nil
            (fatal :type :vl-assignstmt-fail
                   :msg "Bad expression in LHS: ~a0"
                   :args (list lhs))
            nil nil))))

  (define vl-procedural-assign-concat->svstmts ((parts vl-exprlist-p)
                                                (rhssvex svex::svex-p)
                                                (blockingp booleanp)
                                                (conf vl-svexconf-p))
    :measure (vl-exprlist-count parts)
    :returns (mv ok
                 (warnings vl-warninglist-p)
                 (svstmts svex::svstmtlist-p)
                 (shift (implies ok (natp shift)) :rule-classes :type-prescription))
    (b* (((when (atom parts)) (mv t nil nil 0))
         ((mv ok warnings svstmts2 shift2)
          (vl-procedural-assign-concat->svstmts (cdr parts) rhssvex blockingp conf))
         ((unless ok) (mv nil warnings nil nil))
         (rhs (svex::svcall svex::rsh (svex-int shift2) rhssvex))
         ((wmv ok warnings svstmts1 shift1)
          (vl-procedural-assign->svstmts (car parts) rhs blockingp conf))
         ((unless ok) (mv nil warnings nil nil)))
      (mv t warnings (append-without-guard svstmts1 svstmts2)
          (+ shift1 shift2))))
  ///
  (verify-guards vl-procedural-assign->svstmts)

  (defthm-vl-procedural-assign->svstmts-flag
    (defthm vars-of-vl-procedural-assign->svstmts
      (b* (((mv ?ok ?warnings ?svstmts ?shift)
            (vl-procedural-assign->svstmts lhs rhssvex blockingp conf)))
        (implies (svex::svarlist-addr-p (svex::svex-vars rhssvex))
                 (svex::svarlist-addr-p
                  (svex::svstmtlist-vars svstmts))))
      :flag vl-procedural-assign->svstmts)

    (defthm vars-of-vl-procedural-assign-concat->svstmts
      (b* (((mv ?ok ?warnings ?svstmts ?shift)
            (vl-procedural-assign-concat->svstmts parts rhssvex blockingp conf)))
        (implies (svex::svarlist-addr-p (svex::svex-vars rhssvex))
                 (svex::svarlist-addr-p
                  (svex::svstmtlist-vars svstmts))))
      :flag vl-procedural-assign-concat->svstmts)
    :hints ((acl2::just-expand-mrec-default-hint
             'vl-procedural-assign->svstmts id t world)))

  (deffixequiv-mutual vl-procedural-assign->svstmts))
         
          



(define vl-assignstmt->svstmts ((lhs vl-expr-p)
                                (rhs vl-expr-p)
                                (blockingp booleanp)
                                (conf vl-svexconf-p))
  :returns (mv (ok)
               (warnings vl-warninglist-p)
               (res svex::svstmtlist-p))
  (b* ((warnings nil)
       (lhs (vl-expr-fix lhs))
       (rhs (vl-expr-fix rhs)))
    (vl-expr-case lhs
      :vl-index
      ;; If it's an index expression we can look up its type and just process a
      ;; single assignment
      (b* (((vl-svexconf conf))
           ((mv err opinfo) (vl-index-expr-typetrace lhs conf.ss conf.typeov))
           ((when err)
            (mv nil
                (fatal :type :vl-assignstmt-fail
                       :msg "Failed to get type of LHS ~a0: ~@1"
                       :args (list lhs err))
                nil))
           ((vl-operandinfo opinfo))
           ((wmv warnings rhssvex)
            (vl-expr-to-svex-datatyped rhs opinfo.type conf))
           ((wmv ok warnings svstmts ?shift)
            (vl-procedural-assign->svstmts lhs rhssvex blockingp conf)))
        (mv ok warnings svstmts))
      :vl-concat
      (b* (((wmv warnings rhssvex ?rhssize)
            (vl-expr-to-svex-selfdet rhs nil conf))
           ((wmv ok warnings svstmts ?shift)
            (vl-procedural-assign->svstmts
             lhs rhssvex blockingp conf)))
        (mv ok warnings svstmts))
      :otherwise
      (mv nil
          (fatal :type :vl-lhs-malformed
                 :msg "Bad lvalue: ~a0"
                 :args (list lhs))
          nil)))
  ///
  (defret vars-of-vl-assignstmt->svstmts
    (svex::svarlist-addr-p (svex::svstmtlist-vars res))))

  ;; (b* ((warnings nil)
  ;;      ((wmv warnings svex-lhs lhs-type)
  ;;       (vl-expr-to-svex-lhs lhs conf))
  ;;      ((unless lhs-type)
  ;;       (mv nil warnings nil))
  ;;      ((wmv warnings svex-rhs)
  ;;       (vl-expr-to-svex-datatyped rhs lhs-type conf)))
  ;;   (mv t warnings
  ;;       (list (svex::make-svstmt-assign :lhs svex-lhs :rhs svex-rhs
  ;;                                       :blockingp blockingp))))
  ;; ///
  ;; (more-returns
  ;;  (res :name vars-of-vl-assignstmt->svstmts
  ;;       (svex::svarlist-addr-p
  ;;        (svex::svstmtlist-vars res)))))

;; (define vl-assignstmt->svstmts ((lhs vl-expr-p)
;;                                 (rhs vl-expr-p)
;;                                 (blockingp booleanp)
;;                                 (conf vl-svexconf-p))
;;   :returns (mv (ok)
;;                (warnings vl-warninglist-p)
;;                (res svex::svstmtlist-p))
;;   (b* ((warnings nil)
;;        ((wmv warnings svex-lhs lhs-type)
;;         (vl-expr-to-svex-lhs lhs conf))
;;        ((unless lhs-type)
;;         (mv nil warnings nil))
;;        ((wmv warnings svex-rhs)
;;         (vl-expr-to-svex-datatyped rhs lhs-type conf)))
;;     (mv t warnings
;;         (list (svex::make-svstmt-assign :lhs svex-lhs :rhs svex-rhs
;;                                         :blockingp blockingp))))
;;   ///
;;   (more-returns
;;    (res :name vars-of-vl-assignstmt->svstmts
;;         (svex::svarlist-addr-p
;;          (svex::svstmtlist-vars res)))))


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


(define vl-caselist->caseexprs ((x vl-caselist-p))
  :returns (caseexprs vl-exprlist-p)
  :measure (len (vl-caselist-fix x))
  (b* ((x (vl-caselist-fix x)))
    (if (atom x)
        nil
      (append (caar x)
              (vl-caselist->caseexprs (cdr x))))))


(define vl-caseexprs->svex-test ((x vl-exprlist-p)
                                 (test svex::svex-p)
                                 (size natp)
                                 (casetype vl-casetype-p)
                                 (conf vl-svexconf-p))
  :returns (mv (warnings vl-warninglist-p)
               (cond svex::svex-p))
  (if (atom x)
      (mv nil (svex-int 0))
    (b* (((mv warnings rest) (vl-caseexprs->svex-test (cdr x) test size casetype conf))
         ((wmv warnings first &) (vl-expr-to-svex-selfdet (car x) (lnfix size) conf)))
    (mv warnings
        (svex::svcall svex::bitor
                      (case (vl-casetype-fix casetype)
                        ((nil) (svex::svcall svex::== test first))
                        (otherwise (svex::svcall svex::==?? test first)))
                      rest))))
  ///
  (defret vars-of-vl-caseexprs->svex-test
    (implies (svex::svarlist-addr-p (svex::svex-vars test))
             (svex::svarlist-addr-p (svex::svex-vars cond)))))

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

        :vl-casestmt
        (b* ((caseexprs (cons x.test (vl-caselist->caseexprs x.caselist)))
             ((vl-svexconf conf))
             ((wmv warnings sizes)
              (vl-exprlist-selfsize caseexprs conf.ss conf.typeov))
             ((when (member nil (redundant-list-fix sizes)))
              ;; already warned
              (fail (warn :type :vl-stmt->svstmts-failed
                          :msg "Failed to size some case expression: ~a0"
                          :args (list x))))
             (size (max-nats sizes))
             ((wmv ok1 warnings default) (vl-stmt->svstmts x.default conf nonblockingp))
             ((wmv warnings test-svex &)
              (vl-expr-to-svex-selfdet x.test size conf))
             ((wmv ok2 warnings ans)
              (vl-caselist->svstmts x.caselist size test-svex default x.casetype conf nonblockingp)))
          (mv (and ok1 ok2) warnings ans))
                    

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

  (define vl-caselist->svstmts ((x vl-caselist-p)
                                (size natp)
                                (test svex::svex-p)
                                (default svex::svstmtlist-p)
                                (casetype vl-casetype-p)
                                (conf vl-svexconf-p)
                                (nonblockingp))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (res (and (svex::svstmtlist-p res)
                           (implies (and (svex::svarlist-addr-p (svex::svex-vars test))
                                         (svex::svarlist-addr-p (svex::svstmtlist-vars default)))
                                    (svex::svarlist-addr-p
                                     (svex::svstmtlist-vars res))))))
    :measure (vl-caselist-count x)
    (b* ((x (vl-caselist-fix x))
         ((when (atom x))
          (mv t nil (svex::svstmtlist-fix default)))
         ((cons tests stmt) (car x))
         ((mv ok1 warnings rest) (vl-caselist->svstmts (cdr x) size test default casetype conf nonblockingp))
         ((wmv ok2 warnings first) (vl-stmt->svstmts stmt conf nonblockingp))
         ((wmv warnings test)
          (vl-caseexprs->svex-test tests test size casetype conf)))
      (mv (and ok1 ok2)
          warnings
          (list (svex::make-svstmt-if :cond test :then first :else rest)))))

         
         

  ///
  (verify-guards vl-stmt->svstmts)
  (deffixequiv-mutual vl-stmt->svstmts))





(define vl-implicitvalueparam-final-type ((x vl-paramtype-p)
                                          (override vl-expr-p)
                                          (conf vl-svexconf-p
                                                "for expr"))
  :guard (vl-paramtype-case x :vl-implicitvalueparam)
  :returns (mv (warnings vl-warninglist-p)
               (err (iff (vl-msg-p err) err))
               (type (implies (not err) (vl-datatype-p type))))
  (b* ((override (vl-expr-fix override))
       ((vl-svexconf conf))
       ((vl-implicitvalueparam x) (vl-paramtype-fix x))
       (warnings nil)
       ((when x.range)
        ;; BOZO When do we ensure that the range is resolved?  Presumably
        ;; parameters are allowed to use other parameters in defining their
        ;; datatypes.
        (if (vl-range-resolved-p x.range)
            (mv warnings nil
                (make-vl-coretype :name :vl-logic
                                  :pdims (list (vl-range->packeddimension x.range))
                                  :signedp (eq x.sign :vl-signed)))
          (mv warnings (vmsg "Unresolved range") nil)))
       ((wmv warnings size) (vl-expr-selfsize override conf.ss conf.typeov))
       ((unless (posp size))
        (mv warnings
            (vmsg "Unsized or zero-size parameter override: ~a0" override)
            nil))
       (dims (list (vl-range->packeddimension
                    (make-vl-range :msb (vl-make-index (1- size)) :lsb (vl-make-index 0)))))
       ((when x.sign)
        (mv warnings nil
            (make-vl-coretype :name :vl-logic :pdims dims :signedp (eq x.sign :vl-signed))))
       ((wmv warnings signedness) (vl-expr-typedecide override conf.ss conf.typeov))
       ((unless signedness)
        (mv warnings
            (vmsg "Couldn't decide signedness of parameter override ~a0" override)
            nil)))
    (mv warnings nil
        (make-vl-coretype :name :vl-logic :pdims dims :signedp (eq signedness :vl-signed))))
  ///
  (defret vl-datatype-resolved-p-of-vl-implicitvalueparam-final-type
    (implies (not err)
             (vl-datatype-resolved-p type))))


(local (defthm len-of-cons
         (equal (len (cons a b))
                (+ 1 (len b)))))

(local (in-theory (disable len true-listp
                           acl2::subsetp-append1
                           (:t append)
                           default-car default-cdr not)))

;; (include-book "centaur/vl/mlib/allexprs" :dir :System)


         

;; (fty::defvisitor-template replace-exprs ((x :object)
;;                                          (exprs (and (vl-exprlist-p exprs)
;;                                                      (<= (len (<type>-allexprs x))
;;                                                          (len exprs)))))
;;   :returns (mv (new-x :update)
;;                (new-exprs (:acc exprs :fix (vl-exprlist-fix exprs))
;;                           (and (vl-exprlist-p new-exprs)
;;                                (equal (len new-exprs)
;;                                       (max 0 (- (len exprs)
;;                                                 (len (<type>-allexprs x))))))
;;                           :hints ((and stable-under-simplificationp
;;                                        '(:expand ((<type>-allexprs x)))))))
;;   :fnname-template <type>-replace-exprs
;;   :type-fns ((vl-expr (lambda (x exprs)
;;                         (declare (ignore x))
;;                         (mv (vl-expr-fix (car exprs))
;;                             (vl-exprlist-fix (cdr exprs)))))
;;              (vl-exprlist (lambda (x exprs)
;;                             (let ((len (len x)))
;;                               (mv (vl-exprlist-fix (take len exprs))
;;                                   (vl-exprlist-fix (nthcdr len exprs)))))))
;;   :field-fns ((atts :skip)))

;; (set-bogus-mutual-recursion-ok t)

;; (encapsulate nil
;;   ;; (local (include-book "arithmetic/top-with-meta" :dir :system))
;;   (local (in-theory (disable len)))
;;   (local (defthm vl-exprlist-allexprs-redef
;;            (equal (vl-exprlist-allexprs x)
;;                   (vl-exprlist-fix x))
;;            :hints(("Goal" :in-theory (enable vl-exprlist-allexprs
;;                                              vl-exprlist-fix
;;                                              len) 
;;                    :induct (len x)))))
;;   (local (defthm len-cdr
;;            (implies (<= 1 (len x))
;;                     (equal (len (cdr x))
;;                            (+ -1 (len x))))
;;            :hints(("Goal" :in-theory (enable len)))))
;;   (local (defthm len-of-atom
;;            (implies (not (consp x))
;;                     (equal (len x) 0))
;;            :hints(("Goal" :in-theory (enable len)))
;;            :rule-classes ((:rewrite :backchain-limit-lst 0))))
;;   (local (defthm neg-lt-0
;;            (iff (< (- x) 0)
;;                 (< 0 x))))
;;   (local (defthm cdr-of-vl-exprlist-fix
;;            (equal (cdr (vl-exprlist-fix x))
;;                   (vl-exprlist-fix (cdr x)))
;;            :hints(("Goal" :in-theory (enable vl-exprlist-fix)))))

;;   (local (defun find-lit-to-expand (clause)
;;            (if (atom clause)
;;                nil
;;              (let ((lit (car clause)))
;;                (case-match lit
;;                  (('< '(len exprs) ('len (fn 'x)))
;;                   `(:expand ((,fn x))))
;;                  ;; (('consp x)
;;                  ;;  (if (and (consp x)
;;                  ;;           (symbolp (car x)))
;;                  ;;      `(:expand ,x)
;;                  ;;    (find-lit-to-expand (cdr clause))))
;;                  (& (find-lit-to-expand (cdr clause))))))))
;;   (local (defun find-lit-to-expand2 (clause)
;;            (if (atom clause)
;;                nil
;;              (let ((lit (car clause)))
;;                (case-match lit
;;                  ;; (('< '(len exprs) ('len x))
;;                  ;;  `(:expand ,x))
;;                  (('consp (fn 'x))
;;                   (if (symbolp fn)
;;                       `(:expand ((,fn x)))
;;                     (find-lit-to-expand2 (cdr clause))))
;;                  (& (find-lit-to-expand2 (cdr clause))))))))

;;   (local (set-default-hints
;;           '((and stable-under-simplificationp
;;                  (or (find-lit-to-expand clause)
;;                      (find-lit-to-expand2 clause))))))

;;   (local (include-book "std/lists/nthcdr" :dir :system))

;;   (fty::defvisitors vl-stmt-replace-exprs
;;     :template replace-exprs
;;     :types (vl-stmt)))


;; (trace$ #!vl (vl-fundecl-to-svex
;;               :entry (list 'vl-fundecl-to-svex
;;                            (with-local-ps (vl-pp-fundecl x))
;;                            (b* (((vl-svexconf conf)))
;;                              (list :typeov (strip-cars conf.typeov)
;;                                    :params (strip-cars conf.params)
;;                                    :fns (strip-cars conf.fns))))
;;               :exit (list 'vl-fundecl-to-svex
;;                           (with-local-ps (vl-print-warnings (car values))))))

(define vl-fundecl-to-svex  ((x vl-fundecl-p)
                             (conf vl-svexconf-p
                                 "Svexconf for inside the function decl")
                             ;; (fntable svex::svex-alist-p)
                             ;; (paramtable svex::svex-alist-p)
                             )
  :returns (mv (warnings vl-warninglist-p)
               (svex svex::svex-p))
  (b* (((vl-fundecl x) (vl-fundecl-fix x))
       (warnings nil)
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

(define vl-elaborated-expr-consteval ((x vl-expr-p)
                                      (conf vl-svexconf-p)
                                      &key ((ctxsize maybe-natp) 'nil))
  :short "Assumes expression is already elaborated.  conf is read-only."
  :returns (mv (ok  "no errors")
               (constp "successfully reduced to constant")
               (warnings1 vl-warninglist-p)
               (new-x vl-expr-p)
               (svex svex::svex-p))
  (b* (((vl-svexconf conf))
       (x (vl-expr-fix x))
       ((mv warnings signedness) (vl-expr-typedecide x conf.ss conf.typeov))
       ((wmv warnings svex size) (vl-expr-to-svex-selfdet x ctxsize conf))
       ((unless (and (posp size) signedness))
        ;; presumably already warned about this?
        (mv nil nil warnings x (svex-x)))
       (svex (svex::svex-reduce-consts svex))
       (val (svex::svex-case svex :quote svex.val :otherwise nil))
       ((unless val)
        (mv t nil warnings x svex))
       (new-x (make-vl-value :val (vl-4vec-to-value val size :signedness signedness))))
    (mv t t warnings new-x svex)))

(define vl-consteval ((x vl-expr-p)
                      (conf vl-svexconf-p)
                      &key ((ctxsize maybe-natp) 'nil))
  :returns (mv (warnings vl-warninglist-p)
               (new-x vl-expr-p))
  (b* (((mv ?ok ?constant warnings new-x ?svex)
        (vl-elaborated-expr-consteval x conf :ctxsize ctxsize)))
    (mv warnings new-x)))



(fty::defvisitor-template elaborate ((x :object)
                                     (conf vl-svexconf-p)
                                     &key
                                     ((reclimit natp) '1000))
  :returns (mv (ok (:join (and ok1 ok)
                    :initial t
                    :tmp-var ok1))
               (warnings (:join (append-without-guard warnings1 warnings)
                          :initial nil
                          :tmp-var warnings1)
                         vl-warninglist-p)
               (new-x :update)
               (new-conf (:acc conf :fix (vl-svexconf-fix conf))
                         vl-svexconf-p))

    :type-fns ((vl-datatype vl-datatype-elaborate-fn)
               (vl-expr     vl-expr-elaborate-fn))
    :prod-fns ((vl-hidindex  (indices vl-indexlist-resolve-constants-fn))
               (vl-range     (msb vl-index-resolve-if-constant-fn)
                             (lsb vl-index-resolve-if-constant-fn))
               (vl-plusminus (base vl-index-resolve-if-constant-fn)
                             (width vl-index-resolve-constant-fn))
               (vl-arrayrange-index (expr vl-index-resolve-if-constant-fn))
               (vl-valuerange-single (expr vl-index-resolve-if-constant-fn))
               (vl-patternkey-expr   (key vl-index-resolve-if-constant-fn)) ;; BOZO this will break struct field names
               ;; skip these fields because they won't be done right automatically
               )
    :field-fns ((atts :skip)
                (mods :skip)
                (interfaces :skip)
                (packages :skip))

  :fnname-template <type>-elaborate)


  
(local (in-theory (disable cons-equal)))

(fty::defvisitor-multi vl-elaborate
  :defines-args (:ruler-extenders :all ;; :measure-debug t
                 )
  (fty::defvisitor :template elaborate
    :type expressions-and-datatypes
    :measure (acl2::nat-list-measure
              (list reclimit :order :count 0))
    :renames ((vl-expr vl-expr-elaborate-aux)
              (vl-datatype vl-datatype-elaborate-aux))
    
    :short "Resolve constant expressions, parameter values, and datatypes."
    :long "
<p>Parameters, datatypes, and functions may all be interrelated, but they should all be able to be resolved statically:</p>

<ul>
<li>datatypes resolved so that their dimensions all have constant indices and
usertypes are resolved</li>
<li>type parameters determined to be resolved datatypes</li>
<li>value parameters to constant values with resolved types</li>
<li>functions compiled to svex expressions in terms of their formals and with
resolved return types.</li>
</ul>

<p>As you might imagine, this involves a complicated mutual recursion.  We
don't want to replicate the work of @(see vl-expr-to-svex) or make it deal with
recursive resolution of parameters, functions, etc.  Instead, whenever we call
it, we first ensure that we've collected mappings for the resolved values above
in the @(see vl-svexconf) object passed in. So primarily, this function walks
over expressions collecting the necessary mappings.</p>


")
  
  (fty::defvisitors :template elaborate
    :dep-types (vl-fundecl)
    :order-base 1
    :measure (acl2::nat-list-measure
              (list reclimit :order :count 0))
    ;; BOZO Block and loop statements should perhaps also get their own scopes pushed
    )


  (fty::defvisitor :template elaborate
    :type vl-fundecl
    :renames ((vl-fundecl vl-fundecl-elaborate-aux))
    :type-fns ((vl-fundecl vl-fundecl-elaborate-fn))
    :order 100
    :measure (acl2::nat-list-measure
              (list reclimit :order :count 0)))

;; (trace$ #!vl (vl-fundecl-elaborate-fn
;;               :cond (equal (Vl-fundecl->name x) "DWF_lzd")
;;               :entry (list 'vl-fundecl-elaborate
;;                            "DWF_lzd"
;;                            (with-local-ps (vl-pp-fundecl x))
;;                            (b* (((vl-svexconf conf)))
;;                              (list :typeov (strip-cars conf.typeov)
;;                                    :params (strip-cars conf.params)
;;                                    :fns (strip-cars conf.fns))))
;;               :exit (list 'vl-fundecl-elaborate
;;                           "DWF_lzd"
;;                           (with-local-ps (vl-pp-fundecl (caddr values)))
;;                           (b* (((vl-svexconf conf) (cadddr values)))
;;                             (list :typeov (strip-cars conf.typeov)
;;                                   :params (strip-cars conf.params)
;;                                   :fns (strip-cars conf.fns))))))

;; (trace$ #!vl (vl-fundecl-elaborate-aux-fn
;;               :entry (list 'vl-fundecl-elaborate-aux
;;                            (vl-fundecl->name x)
;;                            (with-local-ps (vl-pp-fundecl x))
;;                            (b* (((vl-svexconf conf)))
;;                              (list :typeov (strip-cars conf.typeov)
;;                                    :params (strip-cars conf.params)
;;                                    :fns (strip-cars conf.fns))))
;;               :exit (list 'vl-fundecl-elaborate-aux
;;                            (vl-fundecl->name x)
;;                            (car values)
;;                            (with-local-ps (vl-print-warnings (cadr values)))
;;                           (with-local-ps (vl-pp-fundecl (caddr values)))
;;                           (b* (((vl-svexconf conf) (cadddr values)))
;;                             (list :typeov (strip-cars conf.typeov)
;;                                   :params (strip-cars conf.params)
;;                                   :fns (strip-cars conf.fns))))))


  (define vl-fundecl-elaborate ((x vl-fundecl-p)
                                (conf vl-svexconf-p)
                                &key ((reclimit natp) '1000))
    :guard-debug t
    :measure (acl2::nat-list-measure
              (list reclimit
                    1000 ;; this is kind of the top-level function, so choose a high order value
                    0 0))
  :returns (mv (ok)
               (warnings vl-warninglist-p)
               (new-x vl-fundecl-p)
               (new-conf vl-svexconf-p)) ;; unchanged

    (b* (((vl-svexconf orig-conf) (vl-svexconf-fix conf))
         (fnconf (make-vl-svexconf :ss (vl-scopestack-push (vl-fundecl->blockscope x)
                                                            orig-conf.ss)))
         ((mv ok warnings new-x fnconf)
          (vl-fundecl-elaborate-aux x fnconf :reclimit reclimit))
         ((unless ok)
          (vl-svexconf-free fnconf)
          (mv nil warnings new-x orig-conf))
         ((wmv warnings svex) (vl-fundecl-to-svex new-x fnconf))
         (localname (make-vl-scopeexpr-end
                       :hid (make-vl-hidexpr-end :name (vl-fundecl->name x))))
         ((vl-fundecl new-x))
         (conf (change-vl-svexconf
                orig-conf
                :fns (hons-acons localname svex orig-conf.fns)
                :fnports (hons-acons localname new-x.portdecls orig-conf.fnports)
                :typeov (hons-acons
                         localname new-x.rettype orig-conf.typeov))))
      (vl-svexconf-free fnconf)
      (mv ok warnings new-x conf)))

;; #|
;; (trace$ #!vl (vl-function-compile-and-bind-fn
;;               :entry (list 'vl-function-compile-and-bind
;;                            fnname)
;;               :exit (list 'vl-function-compile-and-bind
;;                           (car values)
;;                           (with-local-ps (vl-print-warnings (cadr values)))
;;                           (strip-cars (vl-svexconf->fns (caddr values))))))

;; |#

  (define vl-function-compile-and-bind ((fnname vl-scopeexpr-p)
                                        (conf vl-svexconf-p)
                                        &key ((reclimit natp) '1000))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-conf vl-svexconf-p))
    :measure (acl2::nat-list-measure
              (list reclimit 0 0 0)) ;; the only recursive call here will decrease the reclimit
    (b* (((vl-svexconf conf) (vl-svexconf-fix conf))
         (fnname (vl-scopeexpr-fix fnname))
         (warnings nil)
         ((mv err trace ?context tail)
          (vl-follow-scopeexpr fnname conf.ss :strictp t))
         ((when err)
          (mv nil
              (fatal :type :vl-function-compile-fail
                     :msg "Couldn't find function ~a0: ~@1"
                     :args (list fnname err))
              conf))
         ((unless (vl-hidexpr-case tail :end))
          (mv nil
              (fatal :type :vl-function-compile-fail
                     :msg "Data select into a function? ~a0"
                     :args (list fnname))
              conf))
         ((vl-hidstep step) (car trace))
         ((unless (eq (tag step.item) :vl-fundecl))
          (mv nil
              (fatal :type :vl-function-compile-fail
                     :msg "Reference to item ~a0 in function name context: ~a1"
                     :args (list step.item fnname))
              conf))
         ((when (zp reclimit))
          (mv nil
              (fatal :type :vl-function-compile-fail
                     :msg "Reclimit ran out on ~a0: dependency loop?"
                     :args (list fnname))
              conf))
         ((vl-fundecl decl) step.item)
         (same-scope (equal step.ss conf.ss))
         (fnconf (if same-scope conf (make-vl-svexconf :ss step.ss)))
         ((wmv ok warnings ?new-decl fnconf)
          (vl-fundecl-elaborate decl fnconf :reclimit (1- reclimit)))
         (conf (if same-scope fnconf conf))
         ((unless ok)
          (and (not same-scope) (vl-svexconf-free fnconf))
          (mv nil warnings conf))
         ((when same-scope) (mv t warnings conf))
         (local-name (make-vl-scopeexpr-end
                      :hid (make-vl-hidexpr-end :name  decl.name)))
         (svex (cdr (hons-get local-name (vl-svexconf->fns fnconf))))
         (type (cdr (hons-get local-name (vl-svexconf->typeov fnconf))))
         (portlook (hons-get local-name (vl-svexconf->fnports fnconf)))
         (conf (if svex
                   (change-vl-svexconf conf :fns (hons-acons fnname svex conf.fns))
                 conf))
         (conf (if type
                   (change-vl-svexconf conf :typeov (hons-acons fnname type conf.typeov))
                 conf))
         (conf (if portlook
                   (change-vl-svexconf conf :fnports (hons-acons fnname (cdr portlook) conf.fnports))
                 conf)))
      (vl-svexconf-free fnconf)
      (mv t warnings conf)))




  (define vl-expr-resolve-to-constant ((x vl-expr-p)
                                       (conf vl-svexconf-p)
                                       &key
                                       ((reclimit natp) '1000)
                                       ((ctxsize maybe-natp) 'nil))
    ;; Just calls vl-expr-maybe-resolve-to-constant, but produces a fatal
    ;; warning if it failed to reduce to a constant.
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-expr-count x) 10))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-expr-p)
                 (svex svex::svex-p)
                 (new-conf vl-svexconf-p))
    (b* ((orig-x (vl-expr-fix x))
         ((mv ok constantp warnings x svex conf)
          (vl-expr-maybe-resolve-to-constant x conf :reclimit reclimit
                                             :ctxsize ctxsize)))
      (mv (and ok constantp)
          (if (and ok (not constantp))
              (fatal :type :vl-expr-consteval-fail
                     :msg "Couldn't resolve ~a0 to constant (original: ~a1)"
                     :args (list x orig-x))
            warnings)
          x svex conf)))

  (define vl-expr-maybe-resolve-to-constant ((x vl-expr-p)
                                             (conf vl-svexconf-p)
                                             &key
                                             ((reclimit natp) '1000)
                                             ((ctxsize maybe-natp) 'nil))
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-expr-count x) 9))
    :returns (mv (ok)
                 (constantp)
                 (warnings vl-warninglist-p) 
                 (new-x vl-expr-p)
                 (svex svex::svex-p)
                 (new-conf vl-svexconf-p))
                 
    (b* (((mv ok warnings x conf)
          (vl-expr-elaborate x conf :reclimit reclimit))
         ((unless ok) (mv nil nil warnings x (svex-x) conf))
         ((mv ok constp warnings x svex)
          (vl-elaborated-expr-consteval x conf :ctxsize ctxsize)))
      (mv ok constp warnings x svex conf)))

  (define vl-index-resolve-if-constant ((x vl-expr-p)
                                        (conf vl-svexconf-p)
                                        &key ((reclimit natp) '1000))
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-expr-count x) 10))
    :returns (mv (ok)
                 (warnings vl-warninglist-p) 
                 (new-x vl-expr-p)
                 (new-conf vl-svexconf-p))
    (b* (((mv ok ?constantp warnings new-x ?svex new-conf)
          (vl-expr-maybe-resolve-to-constant x conf :reclimit reclimit)))
      (mv ok warnings new-x new-conf)))

  (define vl-index-resolve-constant ((x vl-expr-p)
                                     (conf vl-svexconf-p)
                                     &key ((reclimit natp) '1000))
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-expr-count x) 11))
    :returns (mv (ok)
                 (warnings vl-warninglist-p) 
                 (new-x vl-expr-p)
                 (new-conf vl-svexconf-p))
    (b* (((mv ok warnings new-x ?svex new-conf)
          (vl-expr-resolve-to-constant x conf :reclimit reclimit)))
      (mv ok warnings new-x new-conf)))
    
  (define vl-expr-resolve-to-constant-and-bind-param
    ((name vl-scopeexpr-p)
     (expr vl-expr-p)
     (exprconf vl-svexconf-p
               "svexconf for the expression scope")
     (nameconf vl-svexconf-p
               "svexconf for the name scope")
     &key
     ((reclimit natp) '1000))
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-expr-count expr) 20))
    
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-nameconf vl-svexconf-p)
                 (new-exprconf vl-svexconf-p))
    (b* (((vl-svexconf nameconf) (vl-svexconf-fix nameconf))
         ((vl-svexconf exprconf) (vl-svexconf-fix exprconf))
         (same-scope (equal exprconf.ss nameconf.ss))
         (name (vl-scopeexpr-fix name))
         (warnings nil)
         (lookup (hons-get name nameconf.params))
         ((when lookup) (mv t warnings nameconf exprconf))
         ((mv ok warnings ?new-x svex exprconf)
          (vl-expr-resolve-to-constant expr exprconf :Reclimit reclimit))
         (nameconf (if same-scope exprconf nameconf))
         ((unless ok) (mv nil warnings nameconf exprconf))
         (nameconf (change-vl-svexconf
                    nameconf
                    :params (hons-acons name svex nameconf.params)))
         (exprconf (if same-scope nameconf exprconf)))
      (mv t warnings nameconf exprconf)))
      



  (define vl-datatype-fully-resolve-and-bind ((name vl-scopeexpr-p)
                                              (type vl-datatype-p)
                                              (typeconf vl-svexconf-p
                                                        "svexconf for the scope
                                                          where the type was
                                                          defined")
                                              (nameconf vl-svexconf-p
                                                        "svexconf for the scope that
                                                     the name is relative to")
                                              &key
                                              ((reclimit natp) '1000))
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-datatype-count type) 20))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-type vl-datatype-p)
                 (new-nameconf vl-svexconf-p)
                 (new-typeconf vl-svexconf-p))
    
    (b* (((vl-svexconf nameconf) (vl-svexconf-fix nameconf))
         ((vl-svexconf typeconf) (vl-svexconf-fix typeconf))
         (name (vl-scopeexpr-fix name))
         (lookup (hons-get name nameconf.typeov))
         (warnings nil)
         ((when lookup)
          ;; done already
          (mv t warnings (cdr lookup) nameconf typeconf))
         (same-scope (equal nameconf.ss typeconf.ss))
         ;; resolve the type and add it to the conf
         ((wmv ok warnings new-type typeconf)
          (vl-datatype-elaborate type typeconf :reclimit reclimit))
         (nameconf (if same-scope typeconf nameconf))
         ((unless ok)
          (mv nil warnings new-type nameconf typeconf))
         (nameconf (change-vl-svexconf
                    nameconf
                    :typeov (hons-acons name new-type (vl-svexconf->typeov nameconf))))
         (typeconf (if same-scope nameconf typeconf)))
      (mv t warnings new-type nameconf typeconf)))



  (define vl-index-expr-resolve-paramref ((x vl-expr-p)
                                          (conf vl-svexconf-p)
                                          &key ((reclimit natp) '1000))
    ;; Call this AFTER indices within the hids have been maybe-resolved.
    :measure (acl2::nat-list-measure
              (list reclimit 0 0 10))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-conf vl-svexconf-p))
    :guard (vl-expr-case x :vl-index)

    (b* ((warnings nil)
         ((vl-svexconf conf) (vl-svexconf-fix conf))
         ((vl-index x) (vl-expr-fix x))
         ((unless (mbt (vl-expr-case x :vl-index)))
          (impossible) ;; need this case for measure
          (mv nil warnings conf))
         ((mv err hidtrace ?context tail)
          (vl-follow-scopeexpr x.scope conf.ss))
         ((when err)
          (mv t
              ;; It might just be a variable from a generate that isn't present yet.
              ;; (warn :type :vl-resolve-constants-fail
              ;;        :msg "Couldn't find ~a0"
              ;;        :args (list x))
              warnings
              conf))

         (prefix-name (vl-scopeexpr-replace-hid
                       x.scope
                       (vl-hid-prefix-for-subhid (vl-scopeexpr->hid x.scope) tail)))

         ((vl-hidstep hidstep) (car hidtrace))
         ((when (zp reclimit))
          (mv nil
              (fatal :type :vl-resolve-constants-fail
                     :msg "Recursion limit ran out processing ~a0 -- dependency loop?"
                     :args (list x))
              conf))

         ((when (or (eq (tag hidstep.item) :vl-modinst)
                    (eq (tag hidstep.item) :vl-interfaceport)))
          ;; If it's a modinst, it might be an interface, which is legitimate
          ;; in some situations
          (mv t warnings conf))

         ((when (eq (tag hidstep.item) :vl-vardecl))
          ;; It's not a paramdecl, so we can't resolve it to a constant.  But
          ;; we do want to make sure its type is resolved if it's a vardecl.
          ;; We are now in a different scope, so we can't use our same conf.
          (b* ((same-scope (equal hidstep.ss conf.ss))
               (typeconf (if same-scope conf (make-vl-svexconf :ss hidstep.ss)))
               ((mv ok warnings ?newtype conf typeconf)
                (vl-datatype-fully-resolve-and-bind
                 prefix-name
                 (vl-vardecl->type hidstep.item)
                 typeconf conf
                 :reclimit (1- reclimit))))
            (and (not same-scope) (vl-svexconf-free typeconf))
            (mv ok warnings conf)))

         ((unless (eq (tag hidstep.item) :vl-paramdecl))
          (mv nil
              (fatal :type :vl-resolve-constants-fail
                     :msg "~a0: Bad item for variable reference: ~a1"
                     :args (list x hidstep.item))
              conf))

         ((vl-paramdecl decl) hidstep.item))
      ;; Note: We're potentially in a new scope here, so everything we do needs
      ;; to involve just the hidstep.ss and no 
      (vl-paramtype-case decl.type
        :vl-typeparam
        (mv nil
            (fatal :type :vl-resolve-constants-fail
                   :msg "Type parameter referenced as expression: ~a0"
                   :args (list x))
            conf)
        :vl-explicitvalueparam
        (b* (((unless decl.type.default)
              (mv nil
                  (fatal :type :vl-resolve-constants-fail
                         :msg "Parameter with no default value: ~a0"
                         :args (list x))
                   conf))
             (same-scope (equal conf.ss hidstep.ss))
             (declconf (if same-scope conf (make-vl-svexconf :ss hidstep.ss)))
             ((wmv ok1 warnings ?newtype conf declconf)
              (vl-datatype-fully-resolve-and-bind
               prefix-name
               decl.type.type
               declconf conf :reclimit (1- reclimit)))
             ((wmv ok2 warnings conf ?declconf)
              (vl-expr-resolve-to-constant-and-bind-param
               prefix-name
               decl.type.default
               declconf
               conf
               :reclimit (1- reclimit))))
          (and (not same-scope) (vl-svexconf-free declconf))
          (mv (and ok1 ok2) warnings conf))

        :vl-implicitvalueparam
        (b* (((unless decl.type.default)
              (mv nil
                  (fatal :type :vl-resolve-constants-fail
                         :msg "Parameter with no default value: ~a0"
                         :args (list x))
                  conf))
             (same-scope (equal conf.ss hidstep.ss))
             (declconf (if same-scope conf (make-vl-svexconf :ss hidstep.ss)))
             ((mv ok warnings range declconf)
              (if decl.type.range
                  (b* (((vl-range range) decl.type.range)
                       ((wmv ok warnings msb ?svex declconf)
                        (vl-expr-resolve-to-constant
                         range.msb declconf :reclimit (1- reclimit)))
                       ((unless ok)
                        (mv nil warnings nil declconf))
                       ((wmv ok warnings lsb ?svex declconf)
                        (vl-expr-resolve-to-constant
                         range.lsb declconf :reclimit (1- reclimit))))
                    (mv ok warnings (make-vl-range :msb msb :lsb lsb) declconf))
                (mv t warnings nil declconf)))
             (conf (if same-scope declconf conf))
             ((unless ok)
              (and (not same-scope) (vl-svexconf-free declconf))
              (mv nil warnings conf))
             (paramtype (change-vl-implicitvalueparam decl.type :range range))
             ((wmv ok warnings ?val svex declconf)
              (vl-expr-resolve-to-constant
               decl.type.default declconf :reclimit (1- reclimit)))
             (conf (if same-scope declconf conf))
             ((unless ok)
              (and (not same-scope) (vl-svexconf-free declconf))
              (mv nil warnings conf))
             ((wmv warnings err type)
              (vl-implicitvalueparam-final-type paramtype val declconf))
             ((when err)
              (and (not same-scope) (vl-svexconf-free declconf))
              (mv nil
                  (fatal :type :vl-resolve-constants-fail
                         :msg "Error resolving parameter type for ~a0: ~@1"
                         :args (list x err))
                  conf))
             (conf (change-vl-svexconf
                    conf
                    :params (hons-acons prefix-name svex conf.params)
                    :typeov (hons-acons prefix-name type conf.typeov))))
          (and (not same-scope) (vl-svexconf-free declconf))
          (mv t warnings conf)))))


  (define vl-expr-elaborate ((x vl-expr-p)
                                     (conf vl-svexconf-p)
                                     &key ((reclimit natp) '1000))
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-expr-count x) 8))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-expr-p)
                 (new-conf vl-svexconf-p))
    (b* ((x (vl-expr-fix x))
         (conf (vl-svexconf-fix conf))
         (warnings nil))
      (vl-expr-case x
        :vl-index
        (b* (((wmv ok1 warnings new-scope conf)
              (vl-scopeexpr-elaborate x.scope conf :reclimit reclimit))
             ((wmv ok2 warnings new-indices conf)
              (vl-indexlist-resolve-constants x.indices conf :reclimit reclimit))
             ((wmv ok3 warnings new-partselect conf)
              (vl-partselect-elaborate x.part conf :reclimit reclimit))
             (new-x (change-vl-index x :scope new-scope :indices new-indices :part new-partselect))
             ((unless (and ok1 ok2 ok3))
              (mv nil warnings new-x conf))
             ((wmv ok warnings conf)
              (vl-index-expr-resolve-paramref new-x conf :reclimit reclimit)))
          (mv ok warnings new-x conf))

        :vl-multiconcat
        (b* (((wmv ok1 ?constantp warnings new-reps ?svex conf)
              (vl-expr-maybe-resolve-to-constant x.reps conf :reclimit reclimit))
             ((wmv ok2 warnings new-parts conf)
              (vl-exprlist-elaborate x.parts conf :reclimit reclimit))
             (new-x (change-vl-multiconcat x :reps new-reps :parts new-parts)))
          (mv (and ok1 ok2) warnings new-x conf))

        :vl-call
        (b* (((wmv ok1 warnings new-args conf)
              (vl-exprlist-elaborate x.args conf :reclimit reclimit))
             ((wmv ok2 warnings new-typearg conf)
              (if x.typearg
                  (vl-datatype-elaborate x.typearg conf :reclimit reclimit)
                (mv t nil nil conf)))
             ((wmv ok3 warnings new-fnname conf)
              (vl-scopeexpr-elaborate x.name conf :reclimit reclimit))
             (new-x (change-vl-call x :typearg new-typearg :args new-args :name new-fnname))
             ((when x.systemp) (mv (and ok1 ok2 ok3) warnings new-x conf))
             ((wmv ok4 warnings conf)
              (vl-function-compile-and-bind new-fnname conf :reclimit reclimit)))
          (mv (and ok1 ok2 ok3 ok4) warnings new-x conf))

        :vl-cast
        (b* (((wmv ok1 warnings new-casttype conf)
              (vl-casttype-elaborate x.to conf :reclimit reclimit))
             ((wmv ok2 warnings new-expr conf)
              (vl-expr-elaborate x.expr conf :reclimit reclimit))
             (new-x (change-vl-cast x :to new-casttype :expr new-expr)))
          (mv (and ok1 ok2) warnings new-x conf))

        ;; inside, stream, tagged, pattern
        
        :otherwise
        (vl-expr-elaborate-aux x conf :reclimit reclimit))))

  (define vl-indexlist-resolve-constants ((x vl-exprlist-p)
                                          (conf vl-svexconf-p)
                                          &key ((reclimit natp) '1000))
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-exprlist-count x) 12))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-exprlist-p)
                 (new-conf vl-svexconf-p))
    (b* ((conf (vl-svexconf-fix conf))
         ((when (atom x)) (mv t nil nil conf))
         ((mv ok2 warnings rest conf)
          (vl-indexlist-resolve-constants (cdr x) conf :reclimit reclimit))
         ((wmv ok1 ?constantp warnings first ?svex conf)
          (vl-expr-maybe-resolve-to-constant (car x) conf :reclimit reclimit)))
      (mv (and ok1 ok2) warnings (cons first rest) conf)))


  (define vl-datatype-elaborate ((x vl-datatype-p)
                                 (conf vl-svexconf-p)
                                 &key ((reclimit natp) '1000))
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-datatype-count x) 12))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-datatype-p)
                 (new-conf vl-svexconf-p))
    (vl-datatype-case x
      :vl-usertype
      (b* (((mv ok warnings res conf)
            (if x.res
                (vl-datatype-elaborate-aux x.res conf :reclimit reclimit)
              (vl-usertype-resolve x conf :reclimit reclimit)))
           ((wmv ok2 warnings pdims conf)
            (vl-packeddimensionlist-elaborate x.pdims conf :reclimit reclimit))
           ((wmv ok3 warnings udims conf)
            (vl-packeddimensionlist-elaborate x.udims conf :reclimit reclimit)))
        (mv (and ok ok2 ok3) warnings
            (change-vl-usertype
             x
             :res (and ok res)
             :pdims pdims :udims udims)
            conf))
      :otherwise
      (vl-datatype-elaborate-aux x conf :reclimit reclimit)))

  (define vl-usertype-resolve ((x vl-datatype-p)
                                 (conf vl-svexconf-p)
                                 &key ((reclimit natp) '1000))
    :guard (vl-datatype-case x :vl-usertype)
    :measure (acl2::nat-list-measure
              (list reclimit 0 (vl-datatype-count x) 11))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (new-x vl-datatype-p)
                 (new-conf vl-svexconf-p))
    (b* (((vl-usertype x) (vl-datatype-fix x))
         ((vl-svexconf conf) (vl-svexconf-fix conf))
         (warnings nil)
         (hid (vl-scopeexpr->hid x.name))
         ;; BOZO Maybe we should use a different type than scopeexpr for a usertype name
         ((unless (vl-hidexpr-case hid :end))
          (mv nil
              (fatal :type :vl-usertype-resolve-error
                     :msg "Type names cannot be specified with dotted ~
                                   paths, only package scopes: ~a0"
                     :args (list x))
              x conf))
         (look (hons-get x.name conf.typeov))
         ((when look)
          (mv t warnings (cdr look) conf))
         ((mv err trace ?context ?tail)
          (vl-follow-scopeexpr x.name conf.ss))
         ((when err)
          (mv nil
              (fatal :type :vl-usertype-resolve-error
                     :msg "Couldn't find type ~a0"
                     :args (list x))
              x conf))
         ((when (zp reclimit))
          (mv nil
              (fatal :type :vl-usertype-resolve-error
                     :msg "Recursion limit ran out on usertype ~a0"
                     :args (list x))
              x conf))
         ((vl-hidstep ref) (car trace))
         ((when (eq (tag ref.item) :vl-typedef))
          (b* (((vl-typedef item) ref.item)
               (same-scope (equal conf.ss ref.ss))
               (declconf (if same-scope conf (make-vl-svexconf :ss ref.ss)))
               ((wmv ok warnings res-type conf declconf)
                (vl-datatype-fully-resolve-and-bind
                 x.name item.type declconf conf
                 :reclimit (1- reclimit))))
            (and (not same-scope) (vl-svexconf-free declconf))
            (mv ok warnings res-type conf)))
         ((when (eq (tag ref.item) :vl-paramdecl))
          (b* (((vl-paramdecl item) ref.item))
            (vl-paramtype-case item.type
              :vl-typeparam 
              (if item.type.default
                  (b* ((same-scope (equal conf.ss ref.ss))
                       (declconf (if same-scope conf (make-vl-svexconf :ss ref.ss)))
                       ((wmv ok warnings res-type conf ?declconf)
                        (vl-datatype-fully-resolve-and-bind
                         x.name item.type.default declconf conf
                         :reclimit (1- reclimit))))
                    (and (not same-scope) (vl-svexconf-free declconf))
                    (mv ok warnings res-type conf))
                (mv nil
                    (fatal :type :vl-usertype-resolve-error
                           :msg "Reference to unresolved type parameter ~a0"
                           :args (list item))
                    x conf))
              :otherwise
              (mv nil
                  (fatal :type :vl-usertype-resolve-error
                         :msg "Reference to data parameter ~a0 in type context"
                         :args (list item))
                  x conf)))))
      (mv nil
          (fatal :type :vl-usertype-resolve-error
                 :msg "~a0: Didn't find a typedef or parameter reference, instead found ~a1"
                 :args (list x ref.item))
          x conf))))


(fty::defvisitors vl-genelement-deps-elaborate
  :template elaborate
  :dep-types (vl-genelement))

(fty::defvisitor vl-genelement-elaborate
  :template elaborate
  :type vl-genelement
  :omit-types (vl-genarrayblock vl-genarrayblocklist)
  ;; these all need different scopes
  :prod-fns ((vl-genloop (continue :skip)
                         (nextval :skip)
                         (body :skip))
             (vl-genif   (then :skip)
                         (else :skip))
             (vl-gencase (default :skip))
             (vl-genblock (elems :skip))
             (vl-genarray (blocks :skip))
             (vl-gencaselist (:val :skip))))


(fty::defvisitors vl-genblob-elaborate
  :template elaborate
  :types (vl-genblob))

(fty::defvisitors vl-design-elaborate-aux-deps
  :template elaborate
  :dep-types (vl-package vl-module vl-interface vl-design))

(fty::defvisitor vl-design-elaborate-aux
  :template elaborate
  :type vl-design
  :renames ((vl-design vl-design-elaborate-aux)))

(fty::defvisitor vl-package-elaborate-aux
  :template elaborate
  :type vl-package
  :renames ((vl-package vl-package-elaborate-aux)))
              





                                 

  ;; (define vl-exprlist-elaborate ((x vl-exprlist-p)
  ;;                                         (conf vl-svexconf-p)
  ;;                                         &key ((reclimit natp) '1000))
  ;;   :measure (acl2::nat-list-measure
  ;;             (list reclimit (vl-exprlist-count x) 12))
  ;;   :returns (mv (ok)
  ;;                (warnings vl-warninglist-p)
  ;;                (new-x vl-exprlist-p)
  ;;                (new-conf vl-svexconf-p))
  ;;   (b* ((conf (vl-svexconf-fix conf))
  ;;        ((when (atom x)) (mv t nil nil conf))
  ;;        ((mv ok2 warnings rest conf)
  ;;         (vl-exprlist-elaborate (cdr x) conf :reclimit reclimit))
  ;;        ((wmv ok1 warnings first conf)
  ;;         (vl-expr-elaborate (car x) conf :reclimit reclimit)))
  ;;     (mv (and ok1 ok2) warnings (cons first rest) conf)))

  ;; (define vl-scopeexpr-elaborate ((x vl-scopeexpr-p)
  ;;                                         (conf vl-svexconf-p)
  ;;                                         &key ((reclimit natp) '1000))
  ;;   :measure (acl2::nat-list-measure
  ;;             (list reclimit (vl-scopeexpr-count x) 12))
  ;;   :returns (mv (ok)
  ;;                (warnings vl-warninglist-p)
  ;;                (new-x vl-scopeexpr-p)
  ;;                (new-conf vl-svexconf-p))
  ;;   (vl-scopeexpr-case x
  ;;     :end (b* (((mv ok warnings new-hid conf)
  ;;                (vl-hidexpr-elaborate x.hid conf :reclimit reclimit)))
  ;;            (mv ok warnings (change-vl-scopeexpr-end x :hid new-hid) conf))
  ;;     :colon (b* (((mv ok warnings new-rest conf)
  ;;                  (vl-scopeexpr-elaborate x.rest conf :reclimit reclimit)))
  ;;              (mv ok warnings (change-vl-scopeexpr-colon x :rest new-rest) conf))))

  ;; (define vl-hidexpr-elaborate ((x vl-hidexpr-p)
  ;;                                         (conf vl-svexconf-p)
  ;;                                         &key ((reclimit natp) '1000))
  ;;   :measure (acl2::nat-list-measure
  ;;             (list reclimit (vl-hidexpr-count x) 12))
  ;;   :returns (mv (ok)
  ;;                (warnings vl-warninglist-p)
  ;;                (new-x vl-hidexpr-p)
  ;;                (new-conf vl-svexconf-p))
  ;;   (vl-hidexpr-case x
  ;;     :end (mv t nil (vl-hidexpr-fix x) (vl-svexconf-fix conf))
  ;;     :dot (b* (((vl-hidindex first) x.first)
  ;;               ((mv ok1 warnings indices conf)
  ;;                (vl-indexlist-elaborate first.indices conf :reclimit reclimit))
  ;;               ((wmv ok2 warnings rest conf)
  ;;                (vl-hidexpr-elaborate x.rest conf :reclimit reclimit)))
  ;;            (mv ok2 warnings
  ;;                (change-vl-hidexpr-dot
  ;;                 x :first (change-vl-hidindex first :indices indices)
  ;;                 :rest rest)
  ;;                conf))))

                
                                          
          









;; (define vl-fundecl-to-svex  ((x vl-fundecl-p)
;;                              (ss vl-scopestack-p
;;                                  "Scopestack including the function decl")
;;                              ;; (fntable svex::svex-alist-p)
;;                              ;; (paramtable svex::svex-alist-p)
;;                              )
;;   :returns (mv (warnings vl-warninglist-p)
;;                (svex svex::svex-p))
;;   (b* (((vl-fundecl x) (vl-fundecl-fix x))
;;        (warnings nil)
;;        (conf (make-vl-svexconf :ss ss :fns fntable :params paramtable))
;;        ;; nonblocking assignments not allowed
;;        ((wmv ok warnings svstmts) (vl-stmt->svstmts x.body conf nil))
;;        ((unless ok) (mv warnings (svex-x)))
;;        ((wmv ok warnings svstate)
;;         (svex::svstmtlist-compile svstmts (svex::make-svstate) 1000
;;                                   nil ;; nb-delayp
;;                                   ))
;;        ((unless ok) (mv warnings (svex-x)))
;;        ((svex::svstate svstate))
;;        (expr (svex::svex-lookup (svex::make-svar :name x.name) svstate.blkst))
;;        (- (svex::svstate-free svstate))
;;        ((unless expr)
;;         (mv (warn :type :vl-fundecl-to-svex-fail
;;                   :msg "Function has no return value"
;;                   :args (list x))
;;             (svex-x))))
;;     (mv (ok) expr))
;;   ///
;;   (more-returns
;;    (svex :name vars-of-vl-fundecl-to-svex
;;          (svex::svarlist-addr-p (svex::svex-vars svex)))))


;; (defines vl-funname-svex-compile
;;   :verify-guards nil
;;   :prepwork ((set-ruler-extenders '(mv-list return-last :lambdas)))
;;   :ruler-extenders :all
;;   :measure-debug t

;;   (define vl-expr-svex-compile ((x vl-expr-p)
;;                                 (type vl-maybe-datatype-p)
;;                                 (ss vl-scopestack-p)
;;                                 &key ((rec-limit natp) '1000))
;;     :measure (acl2::nat-list-measure (list rec-limit 0 0))
;;     :returns (mv (warnings vl-warninglist-p)
;;                  (expr (and (svex::svex-p expr)
;;                             (svex::svarlist-addr-p (svex::svex-vars expr))))
;;                  (res-type (and (vl-maybe-datatype-p res-type)
;;                                 (implies res-type
;;                                          (vl-datatype-resolved-p res-type)))))
;;     (b* ((x (vl-expr-fix x))
;;          (subfns (vl-expr-functions-called x))
;;          (subparams (vl-expr-parameter-refs x ss))
;;          (warnings nil)
;;          ((when (and (zp rec-limit)
;;                      (or (consp subfns) (consp subparams))))
;;           (mv (fatal :type :vl-expr-svex-compile-fail
;;                      :msg "Rec-Limit ran out compiling functions/warnings: ~a0"
;;                      :args (list x))
;;               (svex-x) nil))
;;          ((wmv warnings fntable)
;;           (if (consp subfns)
;;               (vl-funnames-svex-compile subfns ss (1- rec-limit))
;;             (mv nil nil)))
;;          ((wmv warnings paramtable)
;;           (if (consp subparams)
;;               (vl-paramrefs-svex-compile subparams (1- rec-limit))
;;             (mv nil nil)))
;;          (conf (make-vl-svexconf :ss ss :fns fntable :params paramtable)))
;;       (if type
;;           (b* (((mv err type) (vl-datatype-usertype-resolve type ss))
;;                ((when err)
;;                 (mv (fatal :type :vl-expr-svex-compile-fail
;;                            :msg "Type ~a0 is not resolved"
;;                            :args (list type))
;;                     (svex-x)
;;                     nil))
;;                ((wmv warnings svex) (vl-expr-to-svex-datatyped x type conf)))
;;             (mv warnings svex type))
;;         (b* (((wmv warnings svex type) (vl-expr-to-svex-untyped x conf)))
;;           (mv warnings svex type)))))

;;   (define vl-funname-svex-compile ((x vl-scopeexpr-p "function name")
;;                                    (ss vl-scopestack-p)
;;                                    (rec-limit natp))
;;     :returns (mv (warnings vl-warninglist-p)
;;                  (name (implies name (svex::svar-p name)))
;;                  (expr (and (svex::svex-p expr)
;;                             (svex::svarlist-addr-p (svex::svex-vars expr)))
;;                        "The function's return value as an svex expression"))
;;     :measure (acl2::nat-list-measure (list rec-limit 0 0))
;;     (b* ((x (vl-scopeexpr-fix x))
;;          (warnings nil)
;;          ((mv err name trace) (vl-funname->svex-funname x ss))
;;          ((when err)
;;           (mv (fatal :type :vl-funname-svex-compile-fail
;;                      :msg "function declaration not found: ~@0"
;;                      :args (list (make-vl-index :scope x :part
;;                                                 (vl-partselect-none))
;;                                  err))
;;               nil
;;               (svex-x)))
;;          ((vl-hidstep step) (car trace))
;;          ((unless (eq (tag step.item) :vl-fundecl))
;;           (mv (fatal :type :Vl-funname-svex-compile-fail
;;                      :msg "function declaration not found"
;;                      :args (list (make-vl-index :scope x :part
;;                                                 (vl-partselect-none))
;;                                  err))
;;               nil (svex-x)))
;;          ((vl-fundecl decl) step.item)
;;          (fn-ss (vl-scopestack-push (vl-fundecl->blockscope decl) step.ss))
;;          (subfns (vl-stmt-functions-called decl.body))
;;          (subparams (vl-stmt-parameter-refs decl.body fn-ss))
;;          ((when (and (atom subfns) (atom subparams)))
;;           (b* (((mv warnings expr)
;;                 (vl-fundecl-to-svex decl fn-ss nil nil)))
;;             (mv warnings name expr)))
;;          ((when (zp rec-limit))
;;           (mv (warn :type :vl-funname-svex-compile-fail
;;                           :msg "Rec-Limit ran out compiling functions: ~
;;                                 recursion or parameter loops present? (~a0)"
;;                           :args (list x))
;;               nil (svex-x)))
;;          ((wmv warnings fntable)
;;           (vl-funnames-svex-compile subfns fn-ss (1- rec-limit)))
;;          ((wmv warnings paramtable)
;;           (vl-paramrefs-svex-compile subparams (1- rec-limit)))
;;          ((wmv warnings expr)
;;           (vl-fundecl-to-svex decl fn-ss fntable paramtable)))
;;       (mv warnings name expr)))

;;   (define vl-paramref-svex-compile ((x vl-paramref-p)
;;                                     (rec-limit natp))
;;     :returns (mv (warnings vl-warninglist-p)
;;                  (name svex::svar-p)
;;                  (expr (and (svex::svex-p expr)
;;                             (svex::svarlist-addr-p (svex::svex-vars expr)))))
;;     :measure (acl2::nat-list-measure (list rec-limit 1 0))
;;     (b* (((vl-paramref x))
;;          (warnings nil)
;;          ((wmv warnings expr &)
;;           (vl-expr-svex-compile x.expr x.type x.ss :rec-limit rec-limit)))
;;       (mv warnings x.name expr)))

;;   (define vl-funnames-svex-compile ((x vl-scopeexprlist-p "function names")
;;                                     (ss vl-scopestack-p)
;;                                     (reclimit natp))
;;     :returns (mv (warnings vl-warninglist-p)
;;                  (fntable svex::svex-alist-p
;;                           "Table mapping function names to svex expressions"))
;;     :measure (acl2::nat-list-measure (list reclimit 2 (len x)))
;;     (b* (((when (atom x)) (mv nil nil))
;;          (warnings nil)
;;          ((wmv warnings name1 expr1) (vl-funname-svex-compile (car x) ss reclimit))
;;          ((wmv warnings rest) (vl-funnames-svex-compile (cdr x) ss reclimit)))
;;       (mv warnings
;;           (if name1
;;               (cons (cons name1 expr1)
;;                     rest)
;;             rest))))

;;   (define vl-paramrefs-svex-compile ((x vl-paramreflist-p)
;;                                      (reclimit natp))
;;     :returns (mv (warnings vl-warninglist-p)
;;                  (paramtable svex::svex-alist-p
;;                              "Table mapping parameter names to svex expressions"))
;;     :measure (acl2::nat-list-measure (list reclimit 2 (len x)))
;;     (b* (((when (atom x)) (mv nil nil))
;;          (warnings nil)
;;          ((wmv warnings name1 expr1) (vl-paramref-svex-compile (car x) reclimit))
;;          ((wmv warnings rest) (vl-paramrefs-svex-compile (cdr x) reclimit)))
;;       (mv warnings
;;           (cons (cons name1 expr1)
;;                 rest))))
;;   ///
;;   (verify-guards vl-funname-svex-compile :guard-debug t)
;;   (deffixequiv-mutual vl-funname-svex-compile))


;; (define vl-expr-compile-fns ((x vl-expr-p)
;;                              (ss vl-scopestack-p))
;;   :short "Compiles any functions used by an expression into a svex alist."
;;   :returns (mv (warnings vl-warninglist-p)
;;                (fntable svex::svex-alist-p))
;;   (b* ((fns (vl-expr-functions-called x)))
;;     (vl-funnames-svex-compile fns ss 1000)))

;; (define vl-expr-compile-params ((x vl-expr-p)
;;                                 (ss vl-scopestack-p))
;;   :short "Compiles any functions used by an expression into a svex alist."
;;   :returns (mv (warnings vl-warninglist-p)
;;                (paramtable svex::svex-alist-p))
;;   (b* ((params (vl-expr-parameter-refs x ss)))
;;     (vl-paramrefs-svex-compile params 1000)))




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
       ;; BOZO no typeov -- presumably ok since this is done after elaboration?
       ((mv err opinfo) (vl-index-expr-typetrace x1.expr ss nil))
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

(local (in-theory (enable len)))

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
       (conf (make-vl-svexconf :ss ss))
       ((mv ?ok warnings stmt conf)
        (vl-stmt-elaborate stmt conf))
       ((wmv ok warnings svstmts)
        (vl-stmt->svstmts stmt conf t))
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
