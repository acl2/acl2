; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
(include-book "expr")
(include-book "centaur/vl/mlib/writer" :dir :system) ;; bozo?
(include-book "centaur/vl/mlib/filter" :dir :system)
(include-book "centaur/vl/simpconfig" :dir :system)
(include-book "svstmt-compile")
(include-book "centaur/fty/visitor" :dir :system)
(include-book "centaur/misc/sneaky-load" :dir :system)
;; (include-book "vl-fns-called")
;; (include-book "vl-paramrefs")
;; (include-book "centaur/vl/transforms/always/util" :dir :system)
(local (include-book "centaur/vl/util/default-hints" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system)
                           nfix natp)))

(defxdoc vl-svstmt
  :parents (vl-design->sv-design)
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
                                      (ss vl-scopestack-p)
                                      (scopes vl-elabscopes-p))
  :guard (vl-expr-case x :vl-index)
  :returns (mv (ok)
               (vttree (and (vttree-p vttree)
                            (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
               (svex sv::svex-p)
               (type (implies ok (vl-datatype-p type)))
               (size (implies ok (natp size)) :rule-classes :type-prescription))
  (b* (((mv vttree svex type) (vl-index-expr-to-svex x ss scopes))
       ((unless type) (mv nil vttree svex nil nil))
       ((mv err size) (vl-datatype-size type))
       ((when (or err (not size)))
        ;; (break$)
        (mv nil
            (vfatal :type :vl-expr-to-svex-fail
                    :msg "Couldn't size the datatype ~a0 of ~
                                    LHS expression ~a1: ~@2"
                    :args (list type (vl-expr-fix x) (or err (vmsg "unsizeable"))))
            svex nil nil)))
    (mv t vttree svex type size))
  ///
  (defret vars-of-vl-index-expr-svex/size/type
    (sv::svarlist-addr-p (sv::svex-vars svex))))

;; #!sv
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



;; (define vl-single-procedural-assign->svstmts ((lhs sv::svex-p)
;;                                               (lhssize natp)
;;                                               (wholevar sv::svex-p)
;;                                               (varsize natp)
;;                                               (rhs sv::svex-p)
;;                                               (blockingp booleanp))
;;   :prepwork ((local (defthm consp-cdr-by-len
;;                       (implies (< 1 (len x))
;;                                (consp (cdr x)))
;;                       :hints(("Goal" :in-theory (enable len)))))
;;              (local (defthm consp-by-len
;;                       (implies (< 0 (len x))
;;                                (consp x))
;;                       :hints(("Goal" :in-theory (enable len))))))
;;   :returns (mv (ok)
;;                (warnings vl-warninglist-p)
;;                (res sv::svstmtlist-p))
;;   (b* ((warnings nil)
;;        (lhs-simp1 (sv::svex-concat lhssize (sv::svex-lhsrewrite lhs 0 lhssize)
;;                                      (sv::svex-z)))
;;        ((when (sv::lhssvex-p lhs-simp1))
;;         (mv t (ok)
;;             (list (sv::make-svstmt-assign
;;                    :lhs (sv::svex->lhs lhs-simp1)
;;                    :rhs rhs
;;                    :blockingp blockingp))))
;;        ;; Above covers the case where we have static indices.  Now try and deal
;;        ;; with dynamic indices.
;;        ;; BOZO This makes it important that svex rewriting normalize select
;;        ;; operations to concats and right shifts.  It does this now, and it
;;        ;; seems unlikely we'll want to change that.
;;        ;; First make sure we can process wholevar into an LHS.
;;        (wholevar (sv::svex-lhsrewrite wholevar 0 varsize))
;;        (varsvex (sv::svex-concat varsize wholevar (sv::svex-z)))
;;        ((unless (sv::lhssvex-p varsvex))
;;         (mv nil
;;             (fatal :type :vl-assignstmt-fail
;;                    :msg "Failed to process whole variable as svex LHS -- ~
;;                          dynamic instance select or something? ~x0"
;;                    :args (list (sv::svex-fix wholevar)))
;;             nil))
;;        (var-lhs (sv::svex->lhs varsvex))

;;        ((list simp-lhs wholevar) (sv::svexlist-rewrite-top (list lhs-simp1 wholevar)))

;;        ((mv err final-rhs)
;;         (sv::svex-resolve-single-assignment simp-lhs rhs wholevar))

;;        ((when err)
;;         (mv nil
;;             (fatal :type :vl-assignstmt-fail
;;                    :msg "Failed to process LHS for dynamic select assignment: ~@0"
;;                    :args (list err))
;;             nil)))
;;     (mv t nil
;;         (list
;;          (sv::make-svstmt-assign :lhs var-lhs :rhs final-rhs :blockingp blockingp))))
;;   ///
;;   (local #!sv (defthm svex-vars-of-car
;;                 (implies (not (member v (svexlist-vars x)))
;;                          (not (member v (svex-vars (car x)))))))
;;   (local #!sv (defthm svexlist-vars-of-cdr
;;                 (implies (not (member v (svexlist-vars x)))
;;                          (not (member v (svexlist-vars (cdr x)))))))

;;   (fty::defret vars-of-vl-single-procedural-assign->svstmts
;;     (implies (and (not (member v (sv::svex-vars lhs)))
;;                   (not (member v (sv::svex-vars rhs)))
;;                   (not (member v (sv::svex-vars wholevar))))
;;              (not (member v (sv::svstmtlist-vars res))))))








;;         (b* (((wmv ok warnings lhssvex ?type size)
;;               (vl-index-expr-svex/size/type lhs ss scopes))
;;              ((unless ok)
;;               (mv nil warnings nil nil))
;;              ((vl-svexconf ss scopes))
;;              ((mv err opinfo) (vl-index-expr-typetrace lhs conf.ss conf.typeov))
;;              ((when err)
;;               (mv nil
;;                   (fatal :type :vl-assignstmt-fail
;;                          :msg "Failed to get type of LHS ~a0: ~@1"
;;                          :args (list lhs err))
;;                   nil nil))
;;              ((vl-operandinfo opinfo))


;;              ;; This isn't quite right.  This is resulting in us writing to the
;;              ;; whole variable, where we really want the longest static prefix.
;;              ((wmv ok warnings wholesvex ?wholetype wholesize)
;;               (vl-index-expr-svex/size/type
;;                (make-vl-index :scope opinfo.prefixname) ss scopes))
;;              ((unless ok) (mv nil warnings nil nil))
;;              ((wmv ok warnings svstmts)
;;               (vl-single-procedural-assign->svstmts
;;                lhssvex size wholesvex wholesize rhssvex blockingp)))
;;           (mv ok warnings svstmts (and ok size)))


#!sv
(defines svex-set-nonblocking
  :verify-guards nil
  (define svex-set-nonblocking ((x svex-p))
    :measure (svex-count x)
    :returns (new-x (and (svex-p new-x)
                         (implies (svarlist-addr-p (svex-vars x))
                                  (svarlist-addr-p (svex-vars new-x))))
                    :hints('(:in-theory (e/d (svar-addr-p)
                                             (svex-set-nonblocking
                                              svexlist-set-nonblocking)))))
    (b* ((x (svex-fix x)))
      (svex-case x
        :var (change-svex-var x :name (change-svar x.name :nonblocking t))
        :quote x
        :call (change-svex-call x :args (svexlist-set-nonblocking x.args)))))

  (define svexlist-set-nonblocking ((x svexlist-p))
    :measure (svexlist-count x)
    :returns (new-x (and (svexlist-p new-x)
                         (implies (svarlist-addr-p (svexlist-vars x))
                                  (svarlist-addr-p (svexlist-vars new-x)))))
    (if (atom x)
        nil
      (cons (svex-set-nonblocking (car x))
            (svexlist-set-nonblocking (cdr x)))))
  ///
  (verify-guards svex-set-nonblocking)
  (deffixequiv-mutual svex-set-nonblocking))


#!sv
(defines svex-unset-nonblocking
  :verify-guards nil
  (define svex-unset-nonblocking ((x svex-p))
    :measure (svex-count x)
    :returns (new-x (and (svex-p new-x)
                         (implies (svarlist-addr-p (svex-vars x))
                                  (svarlist-addr-p (svex-vars new-x))))
                    :hints('(:in-theory (e/d (svar-addr-p)
                                             (svex-unset-nonblocking
                                              svexlist-unset-nonblocking)))))
    (b* ((x (svex-fix x)))
      (svex-case x
        :var (change-svex-var x :name (change-svar x.name :nonblocking nil))
        :quote x
        :call (change-svex-call x :args (svexlist-unset-nonblocking x.args)))))

  (define svexlist-unset-nonblocking ((x svexlist-p))
    :measure (svexlist-count x)
    :returns (new-x (and (svexlist-p new-x)
                         (implies (svarlist-addr-p (svexlist-vars x))
                                  (svarlist-addr-p (svexlist-vars new-x)))))
    (if (atom x)
        nil
      (cons (svex-unset-nonblocking (car x))
            (svexlist-unset-nonblocking (cdr x)))))
  ///
  (verify-guards svex-unset-nonblocking)
  (deffixequiv-mutual svex-unset-nonblocking)
  (memoize 'svex-unset-nonblocking :condition '(svex-case (svex-fix x) :call)))
  



(defines vl-procedural-assign->svstmts


;; (trace$
;;  #!vl (vl-procedural-assign->svstmts
;;        :entry (list 'vl-procedural-assign->svstmts
;;                     (with-local-ps (vl-pp-expr lhs))
;;                     rhssvex
;;                     (vl-scopestack->hashkey ss)
;;                     (strip-cars scopes))
;;        :exit (b* (((list ?ok ?warnings ?svstmts ?shift) values)
;;                   (end (and warnings
;;                             (list (with-local-ps (vl-print-warnings warnings))))))
;;                (list* 'vl-procedural-assign->svstmts
;;                       svstmts shift end))))


;; (trace$
;;  #!vl (vl-operandinfo-to-svex-longest-static-prefix
;;        :entry (list 'vl-operandinfo-to-svex-longest-static-prefix
;;                     (with-local-ps (vl-pp-expr (vl-operandinfo->orig-expr x)))
;;                     indices)
;;        :exit (b* (((list err lsp-expr lsp-type full-expr) values))
;;                (if err
;;                    (list 'vl-operandinfo-to-svex-longest-static-prefix
;;                          (with-local-ps (vl-cw "~@0" err)))
;;                  (list 'vl-operandinfo-to-svex-longest-static-prefix
;;                        lsp-expr
;;                        (with-local-ps (vl-pp-datatype lsp-type))
;;                        full-expr)))))

  (define vl-procedural-assign->svstmts ((lhs vl-expr-p)
                                         (rhssvex sv::svex-p)
                                         (blockingp booleanp)
                                         (ss vl-scopestack-p)
                                         (scopes vl-elabscopes-p))
    :measure (vl-expr-count lhs)
    :verify-guards nil
    :returns (mv ok
                 (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (assigns sv::svstmt-writelist-p)
                 (shift (implies ok (natp shift)) :rule-classes :type-prescription))
    :prepwork ((local (Defthmd consp-by-len
                        (implies (posp (len x))
                                 (consp x)))))
    (b* ((vttree nil)
         (lhs (vl-expr-fix lhs)))
      (vl-expr-case lhs
        :vl-index
        (b* (((mv err opinfo) (vl-index-expr-typetrace lhs ss scopes))
             ((when err)
              (mv nil
                  (vfatal :type :vl-assignstmt-fail
                         :msg "Failed to get type of LHS ~a0: ~@1"
                         :args (list lhs err))
                  nil nil))
             ((vl-operandinfo opinfo))
             ((vmv vttree indices ?sizes)
              (vl-exprlist-to-svex-selfdet (vl-operandinfo->indices opinfo) ss scopes))

             ((mv err dyn-size) (vl-datatype-size opinfo.type))
             ((unless (and (not err) dyn-size))
              (mv nil
                  (vfatal :type :vl-assignstmt-fail
                         :msg "Failed to size the dynamic part of LHS ~a0: ~@1"
                         :args (list lhs (or err "")))
                  nil nil))


             ;; Dynselect-expr is in terms of the special variable
             ;; *svex-longest-static-prefix-var*.
             ((mv err select paramval)
              (vl-operandinfo-to-svex-select opinfo indices ss scopes))
             ((when err)
              (mv nil
                  (vfatal :type :vl-assignstmt-fail
                         :msg "Failed to process LHS ~a0: ~@1"
                         :args (list lhs err))
                  nil nil))

             ((when paramval)
              (mv nil
                  (vfatal :type :vl-assignstmt-fail
                         :msg "Assignment to a parameter? ~a0"
                         :args (list lhs))
                  nil nil)))
          (mv t vttree
              (list (sv::make-svstmt-write
                     :lhs select
                     :rhs rhssvex))
              dyn-size))
        :vl-concat
        (vl-procedural-assign-concat->svstmts lhs.parts rhssvex blockingp ss scopes)
        :otherwise
        (mv nil
            (vfatal :type :vl-assignstmt-fail
                   :msg "Bad expression in LHS: ~a0"
                   :args (list lhs))
            nil nil))))

  (define vl-procedural-assign-concat->svstmts ((parts vl-exprlist-p)
                                                (rhssvex sv::svex-p)
                                                (blockingp booleanp)
                                                (ss vl-scopestack-p)
                                                (scopes vl-elabscopes-p))
    :measure (vl-exprlist-count parts)
    :returns (mv ok
                 (vttree (and (vttree-p vttree)
                              (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
                 (assigns sv::svstmt-writelist-p)
                 (shift (implies ok (natp shift)) :rule-classes :type-prescription))
    (b* (((when (atom parts)) (mv t nil nil 0))
         ((mv ok vttree assigns2 shift2)
          (vl-procedural-assign-concat->svstmts (cdr parts) rhssvex blockingp ss scopes))
         ((unless ok) (mv nil vttree nil nil))
         (rhs (sv::svcall sv::rsh (svex-int shift2) rhssvex))
         ((vmv ok vttree assigns1 shift1)
          (vl-procedural-assign->svstmts (car parts) rhs blockingp ss scopes))
         ((unless ok) (mv nil vttree nil nil)))
      (mv t vttree (append-without-guard assigns1 assigns2)
          (+ shift1 shift2))))
  ///
  (verify-guards vl-procedural-assign->svstmts
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable consp-by-len)))))

  ;; BOZO move these somewhere, seem like fine rules
  (local (defthm member-svex-vars-of-car
           (implies (not (member v (sv::svexlist-vars x)))
                    (not (member v (sv::svex-vars (car x)))))
           :hints(("Goal" :in-theory (enable sv::svexlist-vars)))))

  (local (defthm member-svex-vars-of-cadr
           (implies (not (member v (sv::svexlist-vars x)))
                    (not (member v (sv::svex-vars (cadr x)))))
           :hints(("Goal" :in-theory (enable sv::svexlist-vars)))))

  (local (defthm member-svex-vars-of-cdr
           (implies (not (member v (sv::svexlist-vars x)))
                    (not (member v (sv::svexlist-vars (cdr x)))))
           :hints(("Goal" :in-theory (enable sv::svexlist-vars)))))


  (local (defthm svex-alist-vars-of-single
           #!sv (equal (svex-alist-vars (list (cons a b)))
                       (and (svar-p a) (svex-vars b)))
           :hints(("Goal" :in-theory (enable sv::svex-alist-vars)))))

  (local (defthm svex-alist-keys-of-single
           #!sv (equal (svex-alist-keys (list (cons a b)))
                       (and (svar-p a) (list a)))
           :hints(("Goal" :in-theory (enable sv::svex-alist-keys)))))

  (local (defthm member-single
           (iff (member a (list b))
                (equal a b))
           :hints(("Goal" :in-theory (enable member)))))

  (local (in-theory (disable member)))

  (defthm svstmt-writelist-vars-of-append
    (equal (sv::svstmt-writelist-vars (append a b))
           (append (sv::svstmt-writelist-vars a)
                   (sv::svstmt-writelist-vars b)))
    :hints(("Goal" :in-theory (enable sv::svstmt-writelist-vars))))

  (defthm-vl-procedural-assign->svstmts-flag
    (defthm vars-of-vl-procedural-assign->svstmts
      (b* (((mv ?ok ?warnings ?assigns ?shift)
            (vl-procedural-assign->svstmts lhs rhssvex blockingp ss scopes)))
        (implies (sv::svarlist-addr-p (sv::svex-vars rhssvex))
                 (sv::svarlist-addr-p
                  (sv::svstmt-writelist-vars assigns))))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable ;; sv::vars-of-svex-compose-strong
                                        sv::svstmt-writelist-vars
                                        sv::svstmt-write-vars))))
      :flag vl-procedural-assign->svstmts)

    (defthm vars-of-vl-procedural-assign-concat->svstmts
      (b* (((mv ?ok ?warnings ?assigns ?shift)
            (vl-procedural-assign-concat->svstmts parts rhssvex blockingp ss scopes)))
        (implies (sv::svarlist-addr-p (sv::svex-vars rhssvex))
                 (sv::svarlist-addr-p
                  (sv::svstmt-writelist-vars assigns))))
      :flag vl-procedural-assign-concat->svstmts)
    :hints ((acl2::just-expand-mrec-default-hint
             'vl-procedural-assign->svstmts id t world)))

  (deffixequiv-mutual vl-procedural-assign->svstmts))





(define vl-assignstmt->svstmts ((lhs vl-expr-p)
                                (rhs vl-rhs-p)
                                (blockingp booleanp)
                                (ss vl-scopestack-p)
                                (scopes vl-elabscopes-p))
  :returns (mv (ok)
               (vttree (and (vttree-p vttree)
                            (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
               (res sv::svstmtlist-p))
  (b* ((vttree nil)
       ((unless (vl-rhs-case rhs :vl-rhsexpr))
        (mv nil
            (vfatal :type :vl-assignstmt-fail
                    :msg "Not yet supported: 'new' instances: ~a0"
                    :args (list (vl-rhs-fix rhs)))
            nil))
       (lhs (vl-expr-fix lhs))
       (rhs (vl-rhsexpr->guts rhs)))
    (vl-expr-case lhs
      :vl-index
      ;; If it's an index expression we can look up its type and just process a
      ;; single assignment
      (b* (((mv err opinfo) (vl-index-expr-typetrace lhs ss scopes))
           ((when err)
            (mv nil
                (vfatal :type :vl-assignstmt-fail
                       :msg "Failed to get type of LHS ~a0: ~@1"
                       :args (list lhs err))
                nil))
           ((vl-operandinfo opinfo))
           ((vmv vttree type-err rhssvex)
            (vl-expr-to-svex-datatyped rhs lhs opinfo.type ss scopes :compattype :assign))
           ((wvmv vttree) (vl-type-error-basic-warn
                           rhs nil type-err lhs opinfo.type ss))
           ((vmv ok vttree writes ?shift)
            (vl-procedural-assign->svstmts lhs rhssvex blockingp ss scopes))
           (svstmts (list (sv::make-svstmt-assign :writes writes :blockingp blockingp))))
        (mv ok vttree svstmts))
      :vl-concat
      ;; BOZO we don't currently get truncation warnings for this, maybe think
      ;; about whether we can fix it.
      (b* (((vmv vttree & lhssize)
            ;; BOZO really want to discard warnings?
            (vl-expr-to-svex-selfdet lhs nil ss scopes))
           ((vmv vttree rhssvex ?rhssize)
            (vl-expr-to-svex-selfdet rhs lhssize ss scopes))
           ((vmv ok vttree writes ?shift)
            (vl-procedural-assign->svstmts
             lhs rhssvex blockingp ss scopes))
           (svstmts (list (sv::make-svstmt-assign :writes writes :blockingp blockingp))))
        (mv ok vttree svstmts))
      :otherwise
      (mv nil
          (vfatal :type :vl-lhs-malformed
                 :msg "Bad lvalue: ~a0"
                 :args (list lhs))
          nil)))
  ///
  (defret vars-of-vl-assignstmt->svstmts
    (sv::svarlist-addr-p (sv::svstmtlist-vars res))))

  ;; (b* ((warnings nil)
  ;;      ((wmv warnings svex-lhs lhs-type)
  ;;       (vl-expr-to-svex-lhs lhs ss scopes))
  ;;      ((unless lhs-type)
  ;;       (mv nil warnings nil))
  ;;      ((wmv warnings svex-rhs)
  ;;       (vl-expr-to-svex-datatyped rhs lhs-type ss scopes)))
  ;;   (mv t warnings
  ;;       (list (sv::make-svstmt-assign :lhs svex-lhs :rhs svex-rhs
  ;;                                       :blockingp blockingp))))
  ;; ///
  ;; (more-returns
  ;;  (res :name vars-of-vl-assignstmt->svstmts
  ;;       (sv::svarlist-addr-p
  ;;        (sv::svstmtlist-vars res)))))

;; (define vl-assignstmt->svstmts ((lhs vl-expr-p)
;;                                 (rhs vl-expr-p)
;;                                 (blockingp booleanp)
;;                                 (conf vl-svexconf-p))
;;   :returns (mv (ok)
;;                (warnings vl-warninglist-p)
;;                (res sv::svstmtlist-p))
;;   (b* ((warnings nil)
;;        ((wmv warnings svex-lhs lhs-type)
;;         (vl-expr-to-svex-lhs lhs ss scopes))
;;        ((unless lhs-type)
;;         (mv nil warnings nil))
;;        ((wmv warnings svex-rhs)
;;         (vl-expr-to-svex-datatyped rhs lhs-type ss scopes)))
;;     (mv t warnings
;;         (list (sv::make-svstmt-assign :lhs svex-lhs :rhs svex-rhs
;;                                         :blockingp blockingp))))
;;   ///
;;   (more-returns
;;    (res :name vars-of-vl-assignstmt->svstmts
;;         (sv::svarlist-addr-p
;;          (sv::svstmtlist-vars res)))))


#||
(trace$ #!vl (vl-vardecllist->svstmts
              :entry (list 'vl-vardecllist->svstmts
                           (with-local-ps (vl-pp-vardecllist x)))
              :exit (b* (((list ok ?warnings locals stmts) values))
                      (list 'vl-vardecllist->svstmts
                            ok locals stmts))))

||#

(define vl-vardecllist->svstmts ((x vl-vardecllist-p)
                                 (ss vl-scopestack-p)
                                 (scopes vl-elabscopes-p))
  :returns (mv (ok)
               (vttree (and (vttree-p vttree)
                            (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
               (locals (and (sv::svarlist-p locals)
                            (sv::svarlist-addr-p locals))
                       :hints(("Goal" :in-theory (enable sv::svar-addr-p))))
               (res (and (sv::svstmtlist-p res)
                         (sv::svarlist-addr-p
                          (sv::svstmtlist-vars res)))))
  :verify-guards nil
  (b* (((when (atom x)) (mv t nil nil nil))
       (x1 (vl-vardecl-fix (car x)))
       ((mv ok vttree rest-locals rest-stmts)
        (vl-vardecllist->svstmts (cdr x) ss scopes))
       ((unless ok) (mv nil vttree rest-locals rest-stmts))
       ((vl-vardecl x1) x1)
       (locals (cons
                (sv::make-svar
                 :name (sv::make-address :path (sv::make-path-wire :name x1.name)
                                         :scope 0))
                rest-locals))
       ;; only make a local if there's no initial value given
       ((unless x1.initval)
        (mv ok vttree locals rest-stmts))

       (lhs (vl-idexpr x1.name))
       ((vmv ok vttree assign)
        (vl-assignstmt->svstmts lhs x1.initval t ss scopes)))
    (mv ok vttree locals (append-without-guard assign rest-stmts)))
  ///
  (verify-guards vl-vardecllist->svstmts
    :hints (("goal" :in-theory (enable sv::name-p)))))

(local (in-theory (disable member append
                           sv::svarlist-addr-p-when-subsetp-equal
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
                                 (test sv::svex-p)
                                 (size natp)
                                 (casetype vl-casetype-p)
                                 (casekey vl-casekey-p)
                                 (ss vl-scopestack-p)
                                 (scopes vl-elabscopes-p))
  :returns (mv (vttree (and (vttree-p vttree)
                            (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
               (cond sv::svex-p))
  (if (atom x)
      (mv nil (svex-int 0))
    (b* (((mv vttree rest) (vl-caseexprs->svex-test (cdr x) test size casetype casekey ss scopes))
         ((vmv vttree first &) (vl-expr-to-svex-selfdet (car x) (lnfix size) ss scopes)))
    (mv vttree
        (sv::svcall sv::bitor
                    (if (or (vl-casetype-fix casetype)
                            (vl-casekey-fix casekey))
                        (sv::svcall sv::==?? test first)
                      (sv::svcall sv::== test first))
                      rest))))
  ///
  (defret vars-of-vl-caseexprs->svex-test
    (implies (sv::svarlist-addr-p (sv::svex-vars test))
             (sv::svarlist-addr-p (sv::svex-vars cond)))))

(defconst *vl-no-op-system-functions*
  '("$display" "$displayb" "$displayo" "$displayh"
    "$monitor" "$monitorb" "$monitoro" "$monitorh"
    "$strobe" "$strobeb" "$strobeo" "$strobeh"
    "$write" "$writeb" "$writeo" "$writeh"
    "$fdisplay" "$fdisplayb" "$fdisplayo" "$fdisplayh"
    "$fmonitor" "$fmonitorb" "$fmonitoro" "$fmonitorh"
    "$fstrobe" "$fstrobeb" "$fstrobeo" "$fstrobeh"
    "$fwrite" "$fwriteb" "$fwriteo" "$fwriteh"
    "$monitoroff" "$monitoron"
    "$dumpoff" "$dumpon" "$dumpvars"
    "$fsdbDumpoff" "$fsdbDumpon" "$fsdbDumpvars" "$fsdbDumpvarsByFile"))

(fty::defprod svstmt-config
  ((nonblockingp booleanp)
   (uniquecase-conservative natp :default 0)
   (uniquecase-constraints booleanp)))

(define vl-caselist-none/multiple ((x vl-caselist-p)
                                   (size natp)
                                   (test sv::svex-p)
                                   (casetype vl-casetype-p)
                                   (casekey vl-casekey-p)
                                   (ss vl-scopestack-p)
                                   (scopes vl-elabscopes-p))
  :returns (mv (vttree (and (vttree-p vttree)
                            (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
               (nonematch sv::svex-p
                          "Expression (whose value is a bit) signifying that none of the cases match")
               (multimatch sv::svex-p
                           "Expression (whose value is a bit) signifying that more than 1 case matches"))
  :measure (len (vl-caselist-fix x))
  :verify-guards nil
  (b* ((x (vl-caselist-fix x))
       ((when (atom x))
        (mv nil 1 0))
       (tests (caar x))
       ((mv vttree none-rest multi-rest)
        (vl-caselist-none/multiple (cdr x) size test casetype casekey ss scopes))
       ((vmv vttree svtest) ;; this is 0 or -1 due to operators used
        (vl-caseexprs->svex-test tests test size casetype casekey ss scopes)))
    (mv vttree
        (sv::svcall sv::bitand
                    (sv::svcall sv::bitnot svtest)
                    none-rest)
        (sv::svcall sv::bitor
                    (sv::svcall sv::bitand
                                svtest
                                (sv::svex-zerox 1 (sv::svcall sv::bitnot none-rest)))
                    multi-rest)))
  ///
  (verify-guards vl-caselist-none/multiple)

  (defret svex-addr-p-of-vl-caselist-none/multiple
    (implies (sv::svarlist-addr-p (sv::svex-vars test))
             (and (sv::svarlist-addr-p (sv::svex-vars nonematch))
                  (sv::svarlist-addr-p (sv::svex-vars multimatch))))))

(define vl-casestmt-violation-conds ((x vl-stmt-p)
                                     (size natp)
                                     (test sv::svex-p)
                                     (ss vl-scopestack-p)
                                     (scopes vl-elabscopes-p)
                                     (config svstmt-config-p))
  :returns (mv (vttree (and (vttree-p vttree)
                            (sv::svarlist-addr-p (sv::constraintlist-vars (vttree->constraints vttree)))))
               (constraint sv::svstmtlist-p)
               (wrapper-xcond
                sv::svex-p
                "Expression (whose value is a bit) saying that all assignments should use X as the rhs")
               (full-conservative
                sv::svex-p
                "Expression (whose value is a bit) signifying that we should make all tests X")
               (part-conservative
                sv::svex-p
                "Expression (whose value is a bit) signifying that any selected
                 test should become X -- e.g., conservativity 1, unique case, multiple
                 signals match."))
  :guard (vl-stmt-case x :vl-casestmt)
  (b* (((vl-casestmt x))
       ((svstmt-config config))
       ((when (or (not x.check)
                  (eq x.check :vl-priority)))
        (mv nil nil 0 0 0))
       ((when (and (eql 0 config.uniquecase-conservative)
                   (not config.uniquecase-constraints)))
        (mv nil nil 0 0 0))
       ((mv vttree nonematch multimatch)
        (vl-caselist-none/multiple x.caselist size test x.casetype x.casekey ss scopes))
       ((mv full-conservative part-conservative)
        (case config.uniquecase-conservative
          (0 (mv 0 0))
          (1 (mv (if (and (eq x.check :vl-unique)
                          (vl-stmt-case x.default :vl-nullstmt))
                     nonematch
                   0)
                 multimatch))
          (2 (mv (if (and (eq x.check :vl-unique)
                          (vl-stmt-case x.default :vl-nullstmt))
                     (sv::svcall sv::bitor nonematch multimatch)
                   multimatch)
                 0))
          ;; note: basically using all Xes anyway
          (t (mv 0 0))))
       (wrapper-xcond (if (eql config.uniquecase-conservative 3)
                          (if (and (eq x.check :vl-unique)
                                   (vl-stmt-case x.default :vl-nullstmt))
                              (sv::svcall sv::bitor nonematch multimatch)
                            multimatch)
                        0))
       (constraint (and config.uniquecase-constraints
                        (b* ((name (cat (vl-casecheck-string x.check)
                                        " "
                                        (vl-casetype-string x.casetype)
                                        " at " (vl-location-string x.loc)))
                             (onehot (sv::svcall sv::bitnot (sv::svcall sv::uor multimatch)))
                             (cond (if (eq x.check :vl-unique)
                                       onehot
                                     (sv::svcall sv::bitor onehot nonematch))))
                          (list (sv::make-svstmt-constraints
                                 :constraints (list (sv::make-constraint :name name :cond cond))))))))
    (mv vttree constraint wrapper-xcond full-conservative part-conservative))
  ///
  

  (defret svex-addr-p-of-vl-caselist-violation-conds
    (implies (sv::svarlist-addr-p (sv::svex-vars test))
             (and (sv::svarlist-addr-p (sv::svex-vars wrapper-xcond))
                  (sv::svarlist-addr-p (sv::svex-vars full-conservative))
                  (sv::svarlist-addr-p (sv::svex-vars part-conservative))
                  (sv::svarlist-addr-p (sv::svstmtlist-vars constraint))))
    :hints(("Goal" :in-theory (enable sv::constraintlist-vars)))))

;; (define vl-case-conservative ((x vl-stmt-p)
;;                                (config svstmt-config-p))
;;   :guard (vl-stmt-case x :vl-casestmt)
;;   :returns (mv multi-conservative zero-conservative)
;;   (b* (((vl-casestmt x))
;;        ((svstmt-config config)))
;;     (if config.uniquecase-conservativep
;;         (mv (or (eq x.check :vl-unique)
;;                 (eq x.check :vl-unique0))
;;             (and (eq x.check :vl-unique)
;;                  ;; BOZO really need to know whether there was a default or not
;;                  ;; -- might be a problem if there is something like:
;;                  ;;   default: ;
;;                  (vl-stmt-case x.default :vl-nullstmt)))
;;       (mv nil nil))))

;; (define vl-case-constraint ((x vl-stmt-p)
;;                             (nonematch sv::svex-p)
;;                             (multimatch sv::svex-p)
;;                             (generate-constraint))
;;   :guard (vl-stmt-case x :vl-casestmt)
;;   :returns (constr sv::svstmtlist-p)
;;   (b* (((unless generate-constraint) nil)
;;        ((vl-casestmt x))
;;        ((when (not (or (eq x.check :vl-unique)
;;                        (eq x.check :vl-unique0))))
;;         nil)
;;        (name (cat (vl-casecheck-string x.check)
;;                   " "
;;                   (vl-casetype-string x.casetype)
;;                   " at " (vl-location-string x.loc)))
;;        (onehot (sv::svcall sv::bitnot (sv::svcall sv::uor multimatch)))
;;        (cond (if (eq x.check :vl-unique)
;;                  onehot
;;                (sv::svcall sv::bitor onehot nonematch))))
;;     (list (sv::make-svstmt-constraints :constraints (list (sv::make-constraint :name name :cond cond)))))
;;   ///
;;   (defret svarlist-addr-p-of-vl-case-constraint
;;     (implies (and (sv::svarlist-addr-p (sv::svex-vars nonematch))
;;                   (sv::svarlist-addr-p (sv::svex-vars multimatch)))
;;              (sv::svarlist-addr-p (sv::svstmtlist-vars constr)))
;;     :hints(("Goal" :in-theory (enable sv::constraintlist-vars)))))

(define vl-case-xcond-wrapper ((x sv::svstmtlist-p)
                               (full-conservative sv::svex-p)
                               (config svstmt-config-p))
  :returns (new-x sv::svstmtlist-p)
  (b* ((conservative (svstmt-config->uniquecase-conservative config))
       ((unless (and (<= 3 (lnfix conservative))
                     (not (equal (sv::svex-fix full-conservative) 0))))
        (sv::svstmtlist-fix x)))
    (list (sv::make-svstmt-xcond
           :cond full-conservative
           :body x)))
  ///
  (defret svarlist-addr-p-of-vl-case-xcond-wrapper
    (implies (and (sv::svarlist-addr-p (sv::svex-vars full-conservative))
                  (sv::svarlist-addr-p (sv::svstmtlist-vars x)))
             (sv::svarlist-addr-p (sv::svstmtlist-vars new-x)))))

(define vl-case-conservative-test-expr ((test sv::svex-p) ;; 0 or -1
                                        (full-conservative sv::svex-p) ;; 0 or 1
                                        (part-conservative sv::svex-p) ;; 0 or 1
                                        )
  :returns (full-test sv::svex-p) ;; 0 or -1
  (b* ((multi-test
        (if (equal (sv::svex-fix part-conservative) 0)
            (sv::svex-fix test)
          (sv::svcall sv::bitand test
                        (sv::svcall sv::? part-conservative (sv::svex-x) 1))))
       (none-test (if (equal (sv::svex-fix full-conservative) 0)
                      multi-test
                    (sv::svcall sv::? full-conservative (sv::svex-x) multi-test))))
    none-test)
  ///
  (defret svex-addr-p-of-vl-case-conservative-test-expr
    (implies (and (sv::svarlist-addr-p (sv::svex-vars test))
                  (sv::svarlist-addr-p (sv::svex-vars full-conservative))
                  (sv::svarlist-addr-p (sv::svex-vars part-conservative)))
             (sv::svarlist-addr-p (sv::svex-vars full-test)))))


(acl2::def-b*-binder vwmv
  :parents (vttree)
  :short "B* binder to automatically extract warnings from returned vttrees and join them to an accumulator"
  :body
  (b* (((mv ctx args)
        (b* ((mem (member :ctx acl2::args)))
          (if mem
              (mv (cadr mem)
                  (append (take (- (len acl2::args) (len mem)) acl2::args)
                          (cddr mem)))
            (mv nil args)))))
    `(b* (,(if (equal args '(vttree))
               `(vttree . ,acl2::forms)
             `((mv . ,args) . ,acl2::forms))
          (warnings (vttree->warnings-acc vttree ,ctx warnings)))
       ,acl2::rest-expr)))

(define vttree-constraints-to-svstmts ((x vttree-p))
  :returns (svstmts sv::svstmtlist-p)
  (b* ((constraints (vttree->constraints x)))
    (if (atom constraints)
        nil
      (list (sv::make-svstmt-constraints :constraints constraints))))
  ///
  (defret vars-of-vttree-constraints-to-svstmts
    (implies (not (member v (sv::constraintlist-vars (vttree->constraints x))))
             (not (member v (sv::svstmtlist-vars svstmts))))))

(defines vl-stmt->svstmts
  :prepwork ((local (in-theory (disable not))))
  (define vl-stmt->svstmts ((x vl-stmt-p)
                            (ss vl-scopestack-p)
                            (scopes vl-elabscopes-p)
                            (config svstmt-config-p)
                            (fnname vl-maybe-expr-p))
    :verify-guards nil
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (res (and (sv::svstmtlist-p res)
                           (sv::svarlist-addr-p
                            (sv::svstmtlist-vars res)))))
    :measure (vl-stmt-count x)
    (b* ((warnings nil)
         (fnname (vl-maybe-expr-fix fnname))
         ((fun (fail warnings)) (mv nil warnings nil))
         (x (vl-stmt-fix x)))
      (vl-stmt-case x
        :vl-nullstmt (mv t (ok) nil)
        :vl-assignstmt
        (b* (((mv warnings blockingp)
              (case x.type
                ((:vl-assign :vl-force)
                 (mv (fatal :type :vl-procedural-continuous-assignment
                            :msg "Procedural continuous assignments are ~
                                    unsupported: ~a0  Unsafely treating this ~
                                    as a blocking assignment."
                            :args (list x))
                     t))
                (:vl-nonblocking
                 (if (svstmt-config->nonblockingp config)
                     (mv warnings nil)
                   (mv (fatal :type :vl-bad-nonblocking-assignment
                              :msg "Nonblocking assignments are not ~
                                      supported in this context: ~a0  ~
                                      Unsafely treating this as a blocking ~
                                      assignment."
                              :args (list x))
                       t)))
                (otherwise ;; :vl-blocking
                 (mv warnings t))))
             (warnings (if x.ctrl
                           (warn :type :vl-delay-ignored
                                 :msg "Ignoring delay or event control on ~
                                       assignment statement: ~a0"
                                 :args (list x))
                         (ok)))
             ((vwmv ok vttree res)
              (vl-assignstmt->svstmts x.lvalue x.rhs blockingp ss scopes))
             (constraints (vttree-constraints-to-svstmts vttree)))
          (mv ok warnings (append-without-guard constraints res)))
        :vl-ifstmt
        (b* (((vwmv vttree cond ?type ?size)
              (vl-expr-to-svex-untyped x.condition ss scopes))
             (constraints (vttree-constraints-to-svstmts vttree))
             ((wmv ok1 warnings true)
              (vl-stmt->svstmts x.truebranch ss scopes config fnname))
             ((wmv ok2 warnings false)
              (vl-stmt->svstmts x.falsebranch ss scopes config fnname)))
          (mv (and ok1 ok2) warnings
              (append-without-guard constraints
                                    (list (sv::make-svstmt-if :cond cond :then true :else false)))))
        :vl-whilestmt
        (b* (((vwmv vttree cond ?type ?size)
              (vl-expr-to-svex-untyped x.condition ss scopes))
             (constraints (vttree-constraints-to-svstmts vttree))
             ((wmv ok warnings body)
              (vl-stmt->svstmts x.body ss scopes config fnname)))
          (mv ok warnings
              (append-without-guard constraints
                                    (list (sv::make-svstmt-while :cond cond :body body :next nil)))))
        :vl-dostmt
        ;; This is effectively just transforming:
        ;;     do { body } while (condition);
        ;;   -->
        ;;     body;
        ;;     while(condition) { body }
        (b* (((vwmv vttree cond ?type ?size)
              (vl-expr-to-svex-untyped x.condition ss scopes))
             (constraints (vttree-constraints-to-svstmts vttree))
             ((wmv ok warnings body)
              (vl-stmt->svstmts x.body ss scopes config fnname))
             (while-loop (sv::make-svstmt-while :cond cond :body body :next nil)))
          (mv ok warnings
              (append-without-guard constraints
                                    body
                                    (list while-loop))))

        :vl-forstmt
        (b* (;; (warnings (if (consp x.initdecls)
             ;;               (warn :type :vl-stmt-unsupported
             ;;                     :msg "Missing support for locally ~
             ;;                           defined for loop vars: ~a0"
             ;;                     :args (list x))
             ;;             (ok)))
             (blkscope (vl-forstmt->blockscope x))
             (blk-ss (vl-scopestack-push blkscope ss))
             (blk-scopes (vl-elabscopes-push-scope blkscope scopes))
             ((vwmv ok1 vttree locals initstmts1)
              (vl-vardecllist->svstmts x.initdecls blk-ss blk-scopes))
             (constraints1 (vttree-constraints-to-svstmts vttree))
             ((wmv ok2 warnings initstmts2)
              (vl-stmtlist->svstmts x.initassigns blk-ss blk-scopes config fnname))
             ((vwmv vttree cond ?type ?size)
              (vl-expr-to-svex-untyped x.test blk-ss blk-scopes))
             (constraints2 (vttree-constraints-to-svstmts vttree))
             ((wmv ok3 warnings stepstmts)
              (vl-stmtlist->svstmts x.stepforms blk-ss blk-scopes config fnname))
             ((wmv ok4 warnings body)
              (vl-stmt->svstmts x.body blk-ss blk-scopes config fnname)))
          (mv (and ok1 ok2 ok3 ok4)
              warnings
              (append-without-guard constraints1 constraints2
                                    (list (sv::make-svstmt-scope
                                           :locals locals
                                           :body
                                           (append-without-guard
                                            initstmts1 initstmts2
                                            (list (sv::make-svstmt-while
                                                   :cond cond
                                                   :body body
                                                   :next stepstmts))))))))
        :vl-blockstmt
        (b* (((unless (or (vl-blocktype-equiv x.blocktype :vl-beginend)
                          (<= (len x.stmts) 1)))
              (fail (fatal :type :vl-stmt-unsupported
                          :msg "We don't support fork/join block statements: ~a0"
                          :args (list x))))
             ;; (warnings (if (or (consp x.vardecls)
             ;;                   (consp x.paramdecls))
             ;;               (warn :type :vl-stmt-unsupported
             ;;                     :msg "Missing support for block ~
             ;;                           statements with local variables: ~a0"
             ;;                     :args (list x))
             ;;             (ok)))
             (blkscope (vl-blockstmt->blockscope x))
             (blk-ss (vl-scopestack-push blkscope ss))
             (blk-scopes (vl-elabscopes-push-scope blkscope scopes))
             ((vwmv ok1 vttree locals initstmts)
              (vl-vardecllist->svstmts x.vardecls blk-ss blk-scopes))
             (constraints (vttree-constraints-to-svstmts vttree))
             ((wmv ok2 warnings bodystmts)
              (vl-stmtlist->svstmts x.stmts blk-ss blk-scopes config fnname)))
          (mv (and ok1 ok2)
              warnings
              (append-without-guard constraints
                                    (if (or (consp initstmts) (consp bodystmts))
                                        (list (sv::make-svstmt-scope
                                               :locals locals
                                               :body (append-without-guard initstmts bodystmts)))
                                      nil))))

        :vl-casestmt
        (b* ((caseexprs (cons x.test (vl-caselist->caseexprs x.caselist)))
             ((wmv warnings sizes)
              (vl-exprlist-selfsize caseexprs ss scopes))
             ((when (member nil (list-fix sizes)))
              ;; already warned
              (fail (warn :type :vl-stmt->svstmts-failed
                          :msg "Failed to size some case expression: ~a0"
                          :args (list x))))
             (size (max-nats sizes))
             ((wmv ok1 warnings default) (vl-stmt->svstmts x.default ss scopes config fnname))
             ((mv ?vttree test-svex &)
              (vl-expr-to-svex-selfdet x.test size ss scopes))
             ((mv ?vttree constraintstmts wrapper-xcond full-conservative part-conservative)
              (vl-casestmt-violation-conds x size test-svex ss scopes config))
             ((wmv ok2 warnings ans)
              (vl-caselist->svstmts x.caselist size test-svex default x.casetype x.casekey ss scopes config fnname
                                    full-conservative part-conservative))
             (ans (vl-case-xcond-wrapper (append-without-guard constraintstmts ans)
                                         wrapper-xcond config)))
          (mv (and ok1 ok2) warnings ans))

        :vl-callstmt
        (b* (((when (and x.systemp
                         (vl-idscope-p x.id)
                         (member-equal (vl-idscope->name x.id)
                                       *vl-no-op-system-functions*)))
              (mv t warnings nil)))
          (fail (fatal :type :vl-stmt-unsupported
                      :msg "Statement type not supported: ~a0"
                      :args (list x))))
        :vl-returnstmt
        (b* (((when (and x.val (not fnname)))
              (fail (fatal :type :vl-stmt-unsupported
                           :msg "Trying to return a value, but not inside a function: ~a0"
                           :args (list x))))
             ((vwmv ok vttree assignstmts)
              (if x.val
                  (vl-assignstmt->svstmts fnname (make-vl-rhsexpr :guts x.val) t ss scopes)
                (mv t nil nil)))
             (constraints (vttree-constraints-to-svstmts vttree)))
          (mv ok warnings
              (append-without-guard constraints
                                    assignstmts
                                    (list (sv::make-svstmt-jump :type :return)))))
        :vl-breakstmt
        (mv t warnings (list (sv::make-svstmt-jump :type :break)))
        :vl-continuestmt
        (mv t warnings (list (sv::make-svstmt-jump :type :continue)))

        :vl-timingstmt
        (b* (((wmv ok warnings substmts)
              (vl-stmt->svstmts x.body ss scopes config fnname))
             ;; If the body is effectively empty (maybe because it was just a call of some no-ops),
             ;; then just ignore this.
             ((when (atom substmts))
              (mv ok warnings nil))
             ((unless (eq (tag x.ctrl) :vl-delaycontrol))
              (fail (fatal :type :vl-stmt-unsupported
                           :msg "~s0 control statement unsupported: ~a1"
                           :args (list (if (eq (tag x.ctrl) :vl-eventcontrol)
                                           "Event"
                                         "Repeat")
                                       x)))))
          (mv ok
              (warn :type :vl-delay-ignored
                    :msg "Ignoring delay control on statment ~a0"
                    :args (list x))
              substmts))

        :otherwise
        (fail (warn :type :vl-stmt-unsupported
                    :msg "Statement type not supported: ~a0"
                    :args (list x))))))

  (define vl-stmtlist->svstmts ((x vl-stmtlist-p)
                                (ss vl-scopestack-p)
                                (scopes vl-elabscopes-p)
                                (config svstmt-config-p)
                                (fnname vl-maybe-expr-p))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (res (and (sv::svstmtlist-p res)
                           (sv::svarlist-addr-p
                            (sv::svstmtlist-vars res)))))
    :measure (vl-stmtlist-count x)
    (b* ((warnings nil)
         ((when (atom x)) (mv t (ok) nil))
         ((wmv ok1 warnings x1) (vl-stmt->svstmts (car x) ss scopes config fnname))
         ((wmv ok2 warnings x2) (vl-stmtlist->svstmts (cdr x) ss scopes config fnname)))
      (mv (and ok1 ok2) warnings (append-without-guard x1 x2))))

  (define vl-caselist->svstmts ((x vl-caselist-p)
                                (size natp)
                                (test sv::svex-p)
                                (default sv::svstmtlist-p)
                                (casetype vl-casetype-p)
                                (casekey vl-casekey-p)
                                (ss vl-scopestack-p)
                                (scopes vl-elabscopes-p)
                                (config svstmt-config-p)
                                (fnname vl-maybe-expr-p)
                                (full-conservative sv::svex-p)
                                (part-conservative sv::svex-p))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (res (and (sv::svstmtlist-p res)
                           (implies (and (sv::svarlist-addr-p (sv::svex-vars test))
                                         (sv::svarlist-addr-p (sv::svex-vars full-conservative))
                                         (sv::svarlist-addr-p (sv::svex-vars part-conservative))
                                         (sv::svarlist-addr-p (sv::svstmtlist-vars default)))
                                    (sv::svarlist-addr-p
                                     (sv::svstmtlist-vars res))))))
    :measure (vl-caselist-count x)
    (b* ((x (vl-caselist-fix x))
         ((when (atom x))
          (mv t nil (sv::svstmtlist-fix default)))
         ((cons tests stmt) (car x))
         ((mv ok1 warnings rest)
          (vl-caselist->svstmts (cdr x) size test default casetype casekey ss scopes
                                config fnname full-conservative part-conservative))
         ((wmv ok2 warnings first) (vl-stmt->svstmts stmt ss scopes config fnname))
         ((vwmv vttree test)
          (vl-caseexprs->svex-test tests test size casetype casekey ss scopes))
         (constraints (vttree-constraints-to-svstmts vttree))
         (test (vl-case-conservative-test-expr test full-conservative part-conservative)))
      (mv (and ok1 ok2)
          warnings
          (append constraints (list (sv::make-svstmt-if :cond test :then first :else rest))))))




  ///
  (verify-guards vl-stmt->svstmts :guard-debug t)
  (deffixequiv-mutual vl-stmt->svstmts))



;; (define vl-vardecls-to-assigns ((x vl-vardecllist-p))
;;   :returns (assigns vl-stmtlist-p)
;;   (b* (((when (atom x)) nil)
;;        ((vl-vardecl x1) (car x))
;;        ((unless x1.initval)
;;         (vl-vardecls-to-assigns (cdr x))))
;;     (cons (make-vl-assignstmt :lvalue (vl-idexpr x1.name)
;;                               :type :vl-blocking
;;                               :expr x1.initval
;;                               :loc x1.loc)
;;           (vl-vardecls-to-assigns (cdr x)))))

;; (define vl-vardecls-remove-initvals ((x vl-vardecllist-p))
;;   :returns (new-x vl-vardecllist-p)
;;   (b* (((when (atom x)) nil)
;;        ((vl-vardecl x1) (car x)))
;;     (cons (change-vl-vardecl x1 :initval nil)
;;           (vl-vardecls-remove-initvals (cdr x)))))



;; (fty::defvisitor-template fix-vardecls ((x :object))
;;   :type-fns ((vl-stmt vl-stmt-fix-vardecls))
;;   :renames ((vl-stmt vl-stmt-fix-vardecls-aux))
;;   :returns (mv (new-x :update)
;;                (vardecls (:join (append-without-guard vardecls1 vardecls)
;;                           :tmp-var vardecls1
;;                           :initial nil)
;;                          vl-vardecllist-p))
;;     :fnname-template <type>-fix-vardecls)

;; (fty::defvisitor-multi vl-stmt-fix-vardecls
;;   (fty::defvisitors
;;     :measure (two-nats-measure :count 0)
;;     :template fix-vardecls
;;     :types (vl-stmt))

;;   (define vl-stmt-fix-vardecls ((x vl-stmt-p))
;;     :returns (mv (new-x vl-stmt-p)
;;                  (vardecls vl-vardecllist-p))
;;     :measure (two-nats-measure (vl-stmt-count x) 1)
;;     (b* (((mv x sub-vardecls) (vl-stmt-fix-vardecls-aux x)))
;;       (vl-stmt-case x
;;         :vl-blockstmt
;;         (b* ((own-vardecls (vl-vardecls-remove-initvals x.vardecls))
;;              (assigns (vl-vardecls-to-assigns x.vardecls)))
;;           (mv (change-vl-blockstmt x
;;                                    :vardecls nil
;;                                    :stmts (append-without-guard assigns x.stmts))
;;               (append-without-guard own-vardecls sub-vardecls)))
;;         :vl-forstmt
;;         (b* ((own-vardecls (vl-vardecls-remove-initvals x.initdecls))
;;              (assigns (vl-vardecls-to-assigns x.initdecls)))
;;           (mv (change-vl-forstmt x
;;                                  :initdecls nil
;;                                  :initassigns (append-without-guard assigns x.initassigns))
;;               (append-without-guard own-vardecls sub-vardecls)))
;;         :otherwise (mv x sub-vardecls)))))


#||

(trace$ #!vl (vl-implicitvalueparam-final-type
              :entry (list 'vl-implicitvalueparam-final-type
                           (with-local-ps (vl-pp-paramdecl (make-vl-paramdecl :name "foo" :type x :loc *vl-fakeloc*)))
                           (with-local-ps (vl-pp-expr override)))
              :exit (list 'vl-implicitvalueparam-final-type
                          (with-local-ps (vl-pp-datatype (nth 2 values))))))

||#

(define vl-implicitvalueparam-final-type ((x vl-paramtype-p)
                                          (override vl-expr-p)
                                          (ss vl-scopestack-p)
                                          (scopes vl-elabscopes-p
                                                  "for override"))
  ;; BOZO this is really subtle/tricky code and we should probably explain what
  ;; we're trying to do here and what the SystemVerilog rules are at a high
  ;; level.
  :guard (vl-paramtype-case x :vl-implicitvalueparam)
  :returns (mv (warnings vl-warninglist-p)
               (err (iff (vl-msg-p err) err))
               (type (implies (not err) (vl-datatype-p type))))
  (b* ((override (vl-expr-fix override))
       ((vl-implicitvalueparam x) (vl-paramtype-fix x))
       (warnings nil)
       ((when x.range)
        (if (vl-range-resolved-p x.range)
            (mv warnings nil
                (make-vl-coretype :name :vl-logic
                                  :pdims (list (vl-range->dimension x.range))
                                  :signedp (eq x.sign :vl-signed)))
          (mv warnings (vmsg "Unresolved range") nil)))
       ((wmv warnings size) (vl-expr-selfsize override ss scopes))
       ((unless (posp size))
        (mv warnings
            (vmsg "Unsized or zero-size parameter override: ~a0" override)
            nil))
       (dims (list (vl-range->dimension
                    (make-vl-range :msb (vl-make-index (1- size)) :lsb (vl-make-index 0)))))
       ((when x.sign)
        (mv warnings nil
            (make-vl-coretype :name :vl-logic :pdims dims :signedp (eq x.sign :vl-signed))))
       ((wmv warnings class) (vl-expr-typedecide override ss scopes))
       ((unless (vl-integer-arithclass-p class))
        ;; BOZO we might eventually try to extend this to support reals, but
        ;; we'd have to look at what happens when you do parameter p = 1.0 and
        ;; similar.  Also, note below that we return a coretype that is a logic.
        ;; Do we rely on that?  If so we'd have to rework it to handle other
        ;; kinds of types like reals.
        (mv warnings
            (vmsg "Couldn't decide signedness of parameter override ~a0" override)
            nil)))

    (mv warnings nil
        (if (and (eql size 32)
                 (vl-arithclass-equiv class :vl-signed-int-class))
            (make-vl-coretype :name :vl-integer
                              :signedp t)
          (make-vl-coretype :name :vl-logic
                            :pdims dims
                            :signedp (vl-arithclass-equiv class :vl-signed-int-class)))))
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

(fty::defvisitor-template strip-nullstmts ((x :object))
  :type-fns ((vl-stmtlist vl-stmtlist-strip-nullstmts))
  :returns (new-x :update)
  :fnname-template <type>-strip-nullstmts)

(fty::defvisitor-multi vl-stmt-strip-nullstmts
  (fty::defvisitors
    :template strip-nullstmts
    :types (vl-stmt))

  (define vl-stmtlist-strip-nullstmts ((x vl-stmtlist-p))
    :returns (new-x vl-stmtlist-p)
    :measure (vl-stmtlist-count x)
    (if (atom x)
        nil
      (b* ((x1 (car x)))
        (if (vl-stmt-case x1 :vl-nullstmt)
            (vl-stmtlist-strip-nullstmts (cdr x))
          (cons (vl-stmt-strip-nullstmts x1)
                (vl-stmtlist-strip-nullstmts (cdr x))))))))



(define vl-fundecl-to-svex  ((x vl-fundecl-p)
                             (ss vl-scopestack-p)
                             (scopes vl-elabscopes-p
                                     "Scope info for inside the function decl")
                             (config vl-simpconfig-p)
                             ;; (fntable sv::svex-alist-p)
                             ;; (paramtable sv::svex-alist-p)
                             )
  :returns (mv (warnings vl-warninglist-p)
               (svex sv::svex-p)
               (constraints sv::constraintlist-p))
  (b* (((vl-fundecl x) (vl-fundecl-fix x))
       (warnings nil)
       ((vwmv ok vttree localvars varstmts)
        (vl-vardecllist->svstmts (vl-delete-vardecls (cons x.name
                                                           (vl-portdecllist->names x.portdecls))
                                                     x.vardecls)
                                 ss scopes))
       (var-constraints (vttree-constraints-to-svstmts vttree))
       ((unless ok) (mv warnings (svex-x) nil))
       (x.body (vl-stmt-strip-nullstmts x.body))
       ((vl-simpconfig config))

       ;; nonblocking assignments not allowed
       ((wmv ok warnings svstmts) (vl-stmt->svstmts x.body ss scopes
                                                    (make-svstmt-config :nonblockingp nil
                                                                        :uniquecase-conservative
                                                                        config.uniquecase-conservative
                                                                        :uniquecase-constraints
                                                                        config.uniquecase-constraints)
                                                    (vl-idexpr x.name)))
       ((unless ok) (mv warnings (svex-x) nil))
       (svstmts (append-without-guard var-constraints
                                      (list (sv::make-svstmt-scope :locals localvars
                                                                   :body (append-without-guard varstmts svstmts)))))
       ((wmv ok warnings svstate constraints blk-masks nonblk-masks)
        (time$ (sv::svstmtlist-compile-top svstmts
                                           :sclimit config.sc-limit
                                           :nb-delayp nil)
               :mintime 1/2
               :msg "; vl-fundecl-to-svex: compiling ~s0: ~st sec, ~sa bytes"
               :args (list x.name)))
       (- (fast-alist-free blk-masks)
          (fast-alist-free nonblk-masks))
       ((unless ok) (mv warnings (svex-x) nil))
       ((sv::svstate svstate))
       (expr (sv::svstack-lookup (sv::make-svar :name x.name) svstate.blkst))
       (- (sv::svstate-free svstate))
       ((unless expr)
        (mv (warn :type :vl-fundecl-to-svex-fail
                  :msg "Function has no return value")
            (svex-x)
            nil)))
    (mv (ok) expr constraints))
  ///
  (defret vars-of-vl-fundecl-to-svex
    (and (sv::svarlist-addr-p (sv::svex-vars svex))
         (sv::svarlist-addr-p (sv::constraintlist-vars constraints)))))


         


#||

(trace$ #!vl (vl-elaborated-expr-consteval-fn
              :entry (list 'vl-elaborated-expr-consteval
                           (with-local-ps (vl-pp-expr x))
                           (vl-scopestack->hashkey ss)
                           (strip-cars scopes)
                           ctxsize
                           (and type (with-local-ps (vl-pp-datatype type))))
              :exit (b* (((list ?ok ?constp ?warnings ?new-x ?svex) values))
                      (list 'vl-elaborated-expr-consteval
                            ok constp
                            (with-local-ps (vl-print-warnings warnings))
                            (with-local-ps (vl-pp-expr new-x))
                            svex))))

||#

(define vl-elaborated-expr-consteval ((x vl-expr-p)
                                      (ss vl-scopestack-p)
                                      (scopes vl-elabscopes-p)
                                      &key
                                      ((ctxsize maybe-natp) 'nil)
                                      ((type vl-maybe-datatype-p) 'nil)
                                      ((lhs vl-maybe-expr-p) 'nil))
  :short "Assumes expression is already elaborated."
  :returns (mv (ok  "no errors")
               (constp "successfully reduced to constant")
               (warnings1 vl-warninglist-p)
               (new-x vl-expr-p)
               (svex sv::svex-p))
  :prepwork ((local (in-theory (enable vl-datatype-sizable))))
  (b* ((x (vl-expr-fix x))
       (type (vl-maybe-datatype-fix type))
       ((when (and type (not (vl-datatype-resolved-p type))))
        (mv nil nil
            (list (make-vl-warning
                   :type :vl-expression-type-unresolved
                   :msg "Datatype ~a0 unresolved when evaluating expression ~a1"
                   :args (list type x)))
            x (svex-x)))
       (warnings nil)
       ;; Note: not worrying about constraints here yet
       ((mv warnings svex size)
        (if type
            (b* (((mv ?err size) (vl-datatype-size type))
                 ;; Note: vl-expr-to-svex-datatyped is going to complain
                 ;; already if we don't get the size, so don't warn here.
                 ((vwmv vttree type-err svex)
                  ;; Note: We use :compattype :assign because the only place
                  ;; where the datatype argument is used is when computing the
                  ;; value for an explicitvalueparam, which is basically an
                  ;; assignment.
                  (vl-expr-to-svex-datatyped x nil type ss scopes :compattype :assign))
                 ((wmv warnings) (vl-type-error-basic-warn
                                  x nil type-err lhs type ss)))
              (mv warnings svex size))
          (if ctxsize
              (b* (((vwmv vttree svex size)
                    (vl-expr-to-svex-selfdet x ctxsize ss scopes)))
                (mv warnings svex size))
            (b* (((vwmv vttree svex ?type size)
                  (vl-expr-to-svex-untyped x ss scopes)))
              (mv warnings svex size)))))
       ((unless (posp size))
        ;; presumably already warned about this?
        (mv nil nil warnings x (svex-x)))
       (svex (sv::svex-reduce-consts svex))
       (val (sv::svex-case svex :quote svex.val :otherwise nil))
       ((unless val)
        (mv t nil warnings x svex))
       ((when type)
        (b* (((wmv warnings new-expr &)
              (vl-literal-expr-from-4vec type val))
             (new-expr (vl-expr-update-atts new-expr (cons (cons "VL_ORIG_EXPR" x) (vl-expr->atts x)))))
          (mv t t warnings new-expr svex)))
       ((wmv warnings class)
        (if type
            (b* (((mv ?caveat class) (vl-datatype-arithclass type)))
              (mv nil class))
          (vl-expr-typedecide x ss scopes)))
       (signedness (if (vl-integer-arithclass-p class)
                       (vl-integer-arithclass->exprsign class)
                     :vl-unsigned))
       (new-x (make-vl-literal
               :val (vl-4vec-to-value val size :signedness signedness)
               :atts (cons (cons "VL_ORIG_EXPR" x) (vl-expr->atts x)))))
    (mv t t warnings new-x svex)))

(define vl-consteval ((x vl-expr-p)
                      (ss vl-scopestack-p)
                      (scopes vl-elabscopes-p)
                      &key
                      ((ctxsize maybe-natp) 'nil)
                      ((type vl-maybe-datatype-p) 'nil)
                      ((lhs vl-maybe-expr-p) 'nil))
  :returns (mv (warnings vl-warninglist-p)
               (new-x vl-expr-p))
  (b* (((mv ?ok ?constant warnings new-x ?svex)
        (vl-elaborated-expr-consteval x ss scopes :ctxsize ctxsize :type type :lhs lhs)))
    (mv warnings new-x)))









(define vl-evatomlist-has-edge ((x vl-evatomlist-p))
  (if (atom x)
      nil
    (or (not (eq (vl-evatom->type (car x)) :vl-noedge))
        (vl-evatomlist-has-edge (cdr x)))))


(define vl-evatomlist->svex ((x vl-evatomlist-p)
                             (ss vl-scopestack-p)
                             (scopes vl-elabscopes-p))
  :returns (mv (warnings vl-warninglist-p)
               (trigger (and (sv::svex-p trigger)
                             (sv::svarlist-addr-p (sv::svex-vars trigger)))))
  :prepwork ((local (defthm vl-evatom->type-forward
                      (or (equal (vl-evatom->type x) :vl-noedge)
                          (equal (vl-evatom->type x) :vl-edge)
                          (equal (vl-evatom->type x) :vl-negedge)
                          (equal (vl-evatom->type x) :vl-posedge))
                      :hints (("goal" :use vl-evatomtype-p-of-vl-evatom->type
                               :in-theory (e/d (vl-evatomtype-p)
                                               (vl-evatomtype-p-of-vl-evatom->type))))
                      :rule-classes ((:forward-chaining :trigger-terms ((vl-evatom->type x))))))
             (local (in-theory (disable sv::svex-vars-of-svex-add-delay))))
  (b* (((when (atom x)) (mv nil (sv::svex-quote (sv::2vec 0))))
       ((vl-evatom x1) (car x))
       (warnings nil)
       ((vwmv vttree expr ?type ?size)
        (vl-expr-to-svex-untyped x1.expr ss scopes))
       ;; Note: ignoring constraints from the evatom expression.
       (delay-expr (sv::svex-add-delay expr 1))
       ;; Note: Ensure these expressions always evaluate to either -1 or 0.
       ;; BOZO Using bitsel in some of these places is weird because it
       ;; produces a zero-extended 1-bit value.  Therefore, e.g., the bitnot of
       ;; this value is either -1 or -2, which might not be what's intended.
       ;; However, in all these operations, such expressions are BITANDed with
       ;; another bitsel, which zeroes out the upper bits anyway.
       (trigger1 (case x1.type
                   (:vl-noedge
                    ;; expr and delay-expr are unequal
                    (sv::svcall sv::bitnot (sv::svcall sv::== expr delay-expr)))
                   (:vl-posedge
                    ;; SystemVerilog says a posedge is only detected for the LSB. (9.4.2 Event Control)
                    (sv::svcall sv::uor ;; Just reduction or on the 1-bit bitand to obey the Boolean Convention.
                                (sv::svcall sv::bitand
                                            (sv::svcall sv::bitnot (sv::svex-zerox 1 delay-expr))
                                            (sv::svex-zerox 1 expr))))
                   (:vl-negedge
                    ;; SystemVerilog says a negedge is only detected for the LSB. (9.4.2 Event Control)
                    (sv::svcall sv::uor ;; Just reduction or on the 1-bit bitand to obey the Boolean Convention.
                                (sv::svcall sv::bitand
                                            (sv::svcall sv::bitnot (sv::svex-zerox 1 expr))
                                            (sv::svex-zerox 1 delay-expr))))
                   (:vl-edge
                    ;; We want either a posedge or negedge but only on the LSB.
                    ;;  Posedge is AND(NOT(prev0), curr0)
                    ;;  Negedge is AND(prev0, NOT(curr0))
                    (sv::svcall sv::uor ;; Just reduction or on the 1-bit bitxor to obey the Boolean Convention.
                                (sv::svcall sv::bitxor
                                            (sv::svex-zerox 1 expr)
                                            (sv::svex-zerox 1 delay-expr))))))
       ((wmv warnings rest)
        (vl-evatomlist->svex (cdr x) ss scopes)))
    (mv warnings
        (sv::make-svex-call
         :fn 'sv::bitor
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
                                          (ss vl-scopestack-p)
                                          (scopes vl-elabscopes-p))
  :returns (mv (warnings vl-warninglist-p)
               (subst (and (sv::svex-alist-p subst)
                           (sv::svarlist-addr-p (sv::svex-alist-vars subst))
                           (sv::svarlist-addr-p (sv::svex-alist-keys subst)))
                      :hints(("Goal" :in-theory (enable sv::svex-alist-keys
                                                        sv::svex-alist-vars)))))
  :prepwork ((local (defthm vl-evatom->type-forward
                      (or (equal (vl-evatom->type x) :vl-noedge)
                          (equal (vl-evatom->type x) :vl-edge)
                          (equal (vl-evatom->type x) :vl-negedge)
                          (equal (vl-evatom->type x) :vl-posedge))
                      :hints (("goal" :use vl-evatomtype-p-of-vl-evatom->type
                               :in-theory (e/d (vl-evatomtype-p)
                                               (vl-evatomtype-p-of-vl-evatom->type))))
                      :rule-classes ((:forward-chaining :trigger-terms ((vl-evatom->type x))))))
             (local (in-theory (disable member-equal))))
  (b* (((when (atom x)) (mv nil nil))
       ((vl-evatom x1) (vl-evatom-fix (car x)))
       (warnings nil)
       ((unless (vl-expr-case x1.expr
                  :vl-index (and (vl-partselect-case x1.expr.part :none)
                                 (atom x1.expr.indices))
                  :otherwise nil))
        ;; We're going to deal with all these sorts of problems elsewhere?
        (vl-evatomlist-delay-substitution (cdr x) edge-dependent-delayp ss scopes))
       ((mv err opinfo) (vl-index-expr-typetrace x1.expr ss scopes))
       ((when err)
        ;; We're going to deal with all these sorts of problems elsewhere?
        (vl-evatomlist-delay-substitution (cdr x) edge-dependent-delayp ss scopes))
       ((vl-operandinfo opinfo))
       ((unless (and (vl-hidtrace-resolved-p opinfo.hidtrace)
                     (eql (vl-seltrace-unres-count opinfo.seltrace) 0)))
        ;; We're going to deal with all these sorts of problems elsewhere?
        (vl-evatomlist-delay-substitution (cdr x) edge-dependent-delayp ss scopes))

       (warnings
        (if (or opinfo.seltrace opinfo.part)
            (warn :type :vl-always-trigger-dubiously-translated
                  :msg "Event trigger expression ~a0 has selects on it; we ~
                        probably don't deal well with this yet."
                  :args (list x1))
          warnings))

       ;; note: this is only getting the variable; ideally we'd make a
       ;; substitution that is sensitive to selects.
       ((mv err var) (vl-operandinfo-base-svar opinfo ss))


       ((when err)
        ;; We're going to deal with all these sorts of problems elsewhere?
        (vl-evatomlist-delay-substitution (cdr x) edge-dependent-delayp ss scopes))
       (expr (sv::make-svex-var :name var))
       (delay-expr (if edge-dependent-delayp
                       (case x1.type
                         (:vl-noedge
                          ;; always use the current value.
                          expr)
                         (:vl-posedge
                          ;; x ? x : x'
                          (sv::make-svex-call
                           :fn 'sv::?
                           :args (list (sv::make-svex-call
                                        :fn 'sv::bitsel
                                        :args (list (sv::svex-quote (sv::2vec 0))
                                                    expr))
                                       expr
                                       (sv::svex-add-delay expr 1))))
                         (:vl-negedge
                          ;; x ? x' : x
                          (sv::make-svex-call
                           :fn 'sv::?
                           :args (list (sv::make-svex-call
                                        :fn 'sv::bitsel
                                        :args (list (sv::svex-quote (sv::2vec 0))
                                                    expr))
                                       (sv::svex-add-delay expr 1)
                                       expr)))
                         (:vl-edge
                          ;; No idea what to do here.  Always use the current
                          ;; value because that makes as much sense as anything.
                          expr))
                     expr))
       ((wmv warnings rest)
        (vl-evatomlist-delay-substitution (cdr x) edge-dependent-delayp ss scopes)))
    (mv warnings
        (cons (cons var delay-expr) rest))))



(define vl-always->svex-checks ((x vl-always-p)
                                (ss vl-scopestack-p)
                                (scopes vl-elabscopes-p))
  :short "Checks that the always block is suitable for translating to svex, ~
          and returns the body statement and eventcontrol."
  :returns (mv (ok)
               (warnings vl-warninglist-p)
               (stmt (implies ok (vl-stmt-p stmt))
                     "on success, the body of the always block, without any eventcontrol")
               (trigger (and (iff (sv::svex-p trigger) trigger)
                             (implies trigger
                                      (sv::svarlist-addr-p (sv::svex-vars trigger))))
                        "If present, indicates a flop rather than a latch/combinational block.")
               (trigger-subst
                (and (sv::svex-alist-p trigger-subst)
                     (sv::svarlist-addr-p (sv::svex-alist-vars trigger-subst))
                     (sv::svarlist-addr-p (sv::svex-alist-keys trigger-subst)))))
  :prepwork ((local (defthm vl-evatomlist->svex-under-iff
                      (mv-nth 1 (vl-evatomlist->svex x ss scopes))
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
                                     (vl-eventcontrol->atoms x.stmt.ctrl) ss scopes))
            ((wmv warnings trigger-subst) (vl-evatomlist-delay-substitution
                                           (vl-eventcontrol->atoms x.stmt.ctrl)
                                           t ss scopes)))
         (mv t
             warnings
             x.stmt.body
             trigger
             trigger-subst))))))

(local (defthm integer-length-when-posp
         (implies (posp x)
                  (posp (integer-length x)))
         :rule-classes :type-prescription))

#!sv
(define svar->lhs-by-mask ((x svar-p)
                           (mask 4vmask-p))
  :short "Given a variable and a mask of bits, create an LHS that covers those bits."
  :long "<p>Fails by returning an empty LHS if the mask is negative, i.e. an ~
         infinite range of bits should be written.</p>"
  :returns (lhs lhs-p)
  (and (sparseint-< 0 (4vmask-fix mask))
       (list (make-lhrange :w (sparseint-length (4vmask-fix mask))
                           :atom (make-lhatom-var :name x :rsh 0))))
  ///
  (defthm vars-of-svar->lhs-by-mask
    (implies (not (equal v (svar-fix x)))
             (not (member v (lhs-vars (svar->lhs-by-mask x mask)))))
    :hints(("Goal" :in-theory (enable lhatom-vars)))))


#!sv
(define svar->lhs-by-size ((x svar-p)
                           (size natp))
  :short "Given a variable and a size in bits, create an LHS that covers those bits."
  :returns (lhs lhs-p)
  (if (mbe :logic (zp size) :exec (eql size 0))
      nil
    (list (make-lhrange :w size
                        :atom (make-lhatom-var :name x :rsh 0))))
  ///
  (defthm vars-of-svar->lhs-by-size
    (implies (not (equal v (svar-fix x)))
             (not (member v (lhs-vars (svar->lhs-by-size x size)))))
    :hints(("Goal" :in-theory (enable lhatom-vars)))))

(local (in-theory (enable len)))

#!sv
(define svex-alist->assigns ((x svex-alist-p)
                             (sizes svar-size-alist-p)
                             (masks 4vmask-alist-p)
                             ;; (combinationalp 
                             ;;  booleanp
                             ;;  "This is a terrible hack.  For always_comb we attempt
                             ;;   to support writes to different parts of the same
                             ;;   variable by multiple blocks.  In this case we assign
                             ;;   Z to all the bits that aren't written under the
                             ;;   writemask.  But for flops/latches, we assume there
                             ;;   is only one always writing the variable, which means
                             ;;   if it is not written here, it's never written, so
                             ;;   we'll assign X instead of Z to those bits.")
                             )
  ;; BOZO This fails to account for flops that extend beyond the last bit
  ;; written.  We really need to know the full width of all these variables.
  :short "Given an svex alist, return an assignment alist, i.e. transform the bound
          variables into LHSes based on the given masks, which represent the bits
          of the variables that are supposed to be written."
  :returns (assigns assigns-p)
  :measure (len (svex-alist-fix x))
  ;; :prepwork ((local (defthm integerp-when-4vmask-p
  ;;                     (implies (4vmask-p x) (integerp x)))))
  (b* ((x (svex-alist-fix x))
       (masks (4vmask-alist-fix masks))
       (sizes (svar-size-alist-fix sizes))
       ((when (atom x)) nil)
       ((cons var rhs) (car x))
       (mask (or (cdr (hons-get var masks)) 0))
       (size (cdr (hons-get var sizes)))
       (- (or size (raise "error: expected all sizes to be bound")))
       (size (or size 0))
       (lhs (svar->lhs-by-size var size))
       (fullmaskp (sparseint-equal mask (sparseint-concatenate size -1 0)))
       ((when fullmaskp)
        ;; simple case: just write the whole thing.
        (cons (cons lhs (make-driver :value rhs))
              (svex-alist->assigns (cdr x) sizes masks))))
    ;; Otherwise, we want to drive it to its value where it's written and Z
    ;; elsewhere, so that elsewhere it can be overwritten by someone else.
    ;; However, we want it to go to X if it's not written by anyone.  So we add
    ;; two assignments: one regular one to its value where written and Z
    ;; elsewhere, and one weak one, to X everywhere.
    (list* (cons lhs
                 (make-driver
                  :value
                  (make-svex-call :fn 'bit?
                                  :args (list (sv::svex-quote (sv::2vec (sparseint-val mask)))
                                              rhs
                                              (svex-z)))))
           (cons lhs
                 (make-driver :value (svex-x) :strength 0))
           (svex-alist->assigns (cdr x) sizes masks)))
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
             (not (member v (assigns-vars (svex-alist->assigns x sizes masks)))))
    :hints(("Goal" :in-theory (enable assigns-vars
                                      svex-alist-keys svex-alist-vars)
            :induct (svex-alist->assigns x sizes masks)
            :expand ((svex-alist->assigns x sizes masks))))))



#!sv
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

(define vl-always->svex-latch-warnings ((write-masks sv::4vmask-alist-p)
                                        (read-masks sv::svex-mask-alist-p))
  :returns (warnings vl-warninglist-p)
  :measure (len (sv::4vmask-alist-fix write-masks))
  (b* ((warnings nil)
       (write-masks (sv::4vmask-alist-fix write-masks))
       ((when (atom write-masks)) (ok))
       ;; ((unless (mbt (consp (car write-masks))))
       ;;  (vl-always->svex-latch-warnings (cdr write-masks) read-masks))
       ((cons var wmask) (car write-masks))
       (var (sv::svar-fix var))
       (wmask (sv::4vmask-fix wmask))
       (rmask (sv::svex-mask-lookup (sv::make-svex-var :name var) read-masks))
       (overlap (sv::sparseint-bitand wmask rmask))
       (warnings (if (sv::sparseint-equal overlap 0)
                     warnings
                   (warn :type :vl-always-comb-looks-like-latch
                         :msg "Variable ~a0 was both read and written (or not ~
                               always updated) in an always_comb block.  ~
                               Verilog simulators may treat this variable as ~
                               a latch.  Overlap of read and write bits: ~s1"
                         :args (list var
                                     (if (< (sv::sparseint-length overlap) 40000)
                                         (str::hexify (sv::sparseint-val overlap))
                                       "<more than 10000 digits>")))))
       ((wmv warnings)
        (vl-always->svex-latch-warnings (cdr write-masks) read-masks)))
    warnings))


#!sv
(define svarlist-remove-delays ((x svarlist-p))
  :returns (new-x svarlist-p)
  (if (atom x)
      nil
    (cons (b* (((svar x1) (car x)))
            (make-svar :name x1.name))
          (svarlist-remove-delays (cdr x)))))



;; (local
;;  #!sv
;;  (encapsulate nil

;;    (defthm svex-lookup-in-fast-alist-clean
;;      (implies (svex-alist-p x)
;;               (iff (svex-lookup v (fast-alist-clean x))
;;                    (svex-lookup v x))))))

(define combine-mask-alists ((masks sv::4vmask-alist-p)
                             (acc sv::4vmask-alist-p))
  :returns (res sv::4vmask-alist-p)
  :measure (len (sv::4vmask-alist-fix masks))
  ;; :prepwork ((local (defthm integerp-lookup-in-4vmask-alist
  ;;                     (implies (and (sv::4vmask-alist-p x)
  ;;                                   (hons-assoc-equal k x))
  ;;                              (integerp (cdr (hons-assoc-equal k x))))
  ;;                     :hints(("Goal" :in-theory (enable sv::4vmask-alist-p
  ;;                                                       hons-assoc-equal))))))
  (b* ((masks (sv::4vmask-alist-fix masks))
       (acc (sv::4vmask-alist-fix acc))
       ((When (atom masks)) acc)
       ((cons key val) (car masks))
       (look (or (cdr (hons-get key acc)) 0))
       (newval (sv::sparseint-bitor val look)))
    (combine-mask-alists (cdr masks) (hons-acons key newval acc))))





(define vl-always-apply-trigger-to-updates ((trigger sv::svex-p)
                                            (x sv::svex-alist-p))
  :returns (new-x sv::svex-alist-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x)) (sv::svar-p (caar x)))))
        (vl-always-apply-trigger-to-updates trigger (cdr x)))
       ((cons var upd) (car x))
       (upd (sv::svex-fix upd))
       (prev-var (sv::make-svex-var :name (sv::svar-add-delay var 1)))
       (trigger-upd (sv::make-svex-call
                     :fn 'sv::?
                     :args (list trigger upd prev-var))))
    (cons (cons var trigger-upd)
          (vl-always-apply-trigger-to-updates trigger (cdr x))))
  ///
  (local (defthm svex-p-compound-recognizer
           (implies (sv::svex-p x) x)
           :rule-classes :compound-recognizer))
  (local (defthm svex-fix-type
           (sv::svex-p (sv::svex-fix x))
           :rule-classes ((:type-prescription :typed-term (sv::svex-fix x)))))
  (local (defthm cdar-of-svex-alist-fix
           (implies (consp (sv::svex-alist-fix x))
                    (cdar (sv::svex-alist-fix x)))
           :hints(("Goal" :in-theory (enable sv::svex-alist-fix)))))
  (defret keys-of-vl-always-apply-trigger-to-updates
    (iff (sv::svex-lookup v new-x)
         (sv::svex-lookup v x))
          :hints(("Goal" :in-theory (enable sv::svex-lookup
                                            hons-assoc-equal))))
  (local (in-theory (disable sv::member-of-svarlist-add-delay)))

  (local
   (defret vars-of-vl-always-apply-trigger-to-updates-lemma
     (implies (and (not (member v (sv::svex-alist-vars x)))
                   (not (member v (sv::svex-vars trigger)))
                   (not (member v (sv::svarlist-add-delay
                                   (sv::svex-alist-keys x) 1)))
                   (sv::svex-alist-p x))
              (not (member v (sv::svex-alist-vars new-x))))
     :hints(("Goal" :induct (vl-always-apply-trigger-to-updates trigger x)
             :in-theory (enable sv::svex-alist-vars
                                sv::svex-alist-keys)))))
  (defret vars-of-vl-always-apply-trigger-to-updates
    (implies (and (not (member v (sv::svex-alist-vars x)))
                  (not (member v (sv::svex-vars trigger)))
                  (not (member v (sv::svarlist-add-delay
                                  (sv::svex-alist-keys x) 1))))
             (not (member v (sv::svex-alist-vars new-x))))
    :hints(("Goal" :induct (sv::svex-alist-fix x)
            :expand ((vl-always-apply-trigger-to-updates trigger x)
                     (sv::svex-alist-vars x)
                     (sv::svex-alist-fix x)
                     (:free (a b) (sv::svex-alist-vars (cons a b)))
                     (sv::svex-alist-keys x))
            :in-theory (enable sv::svex-alist-fix))))

  (fty::deffixequiv vl-always-apply-trigger-to-updates :args (x)
    :hints (("goal" :induct (vl-always-apply-trigger-to-updates trigger x)
             :expand ((vl-always-apply-trigger-to-updates trigger x)
                      (vl-always-apply-trigger-to-updates trigger nil)
                      (:free (a b) (vl-always-apply-trigger-to-updates trigger (cons a b)))
                      (sv::svex-alist-fix x))))))


#!sv
(define svex-alist-unset-nonblocking ((x svex-alist-p))
  :returns (new-x (and (svex-alist-p new-x)
                       (implies (svarlist-addr-p (svex-alist-keys x))
                                (svarlist-addr-p (svex-alist-keys new-x)))
                       (implies (svarlist-addr-p (svex-alist-vars x))
                                (svarlist-addr-p (svex-alist-vars new-x))))
                  :hints(("Goal" :in-theory (enable svar-addr-p))))
  :prepwork ((local (defthmd svex-alist-vars-expand1
                      (equal (svex-alist-vars x)
                             (and (consp (svex-alist-fix x))
                                  (union (svex-vars (cdar (svex-alist-fix x)))
                                         (svex-alist-vars (cdr (svex-alist-fix x))))))
                      :hints(("Goal" :in-theory (enable svex-alist-vars
                                                        svex-alist-fix)))))
             (local (defthm svex-alist-vars-expand
                      (implies (consp (svex-alist-fix x))
                               (equal (svex-alist-vars x)
                                      (union (svex-vars (cdar (svex-alist-fix x)))
                                             (svex-alist-vars (cdr (svex-alist-fix x))))))
                      :hints(("Goal" :use  svex-alist-vars-expand1))))
             (local (defthmd svex-alist-keys-expand1
                      (equal (svex-alist-keys x)
                             (and (consp (svex-alist-fix x))
                                  (cons (caar (svex-alist-fix x))
                                        (svex-alist-keys (cdr (svex-alist-fix x))))))
                      :hints(("Goal" :in-theory (enable svex-alist-keys
                                                        svex-alist-fix)))))
             (local (defthm svex-alist-keys-expand
                      (implies (consp (svex-alist-fix x))
                               (equal (svex-alist-keys x)
                                      (cons (caar (svex-alist-fix x))
                                            (svex-alist-keys (cdr (svex-alist-fix x))))))
                      :hints(("Goal" :use svex-alist-keys-expand1)))))
  :measure (len (svex-alist-fix x))
  (b* ((x (svex-alist-fix x)))
    (if (atom x)
        nil
      (cons (cons (change-svar (caar x) :nonblocking nil)
                  (svex-unset-nonblocking (cdar x)))
            (svex-alist-unset-nonblocking (cdr x))))))

#!sv
(define 4vmask-alist-unset-nonblocking ((x 4vmask-alist-p))
  ;; :returns (new-x (and (4vmask-alist-p new-x)
  ;;                      (implies (svarlist-addr-p (4vmask-alist-keys x))
  ;;                               (svarlist-addr-p (4vmask-alist-keys new-x)))
  ;;                      (implies (svarlist-addr-p (4vmask-alist-vars x))
  ;;                               (svarlist-addr-p (4vmask-alist-vars new-x))))
  ;;                 :hints(("Goal" :in-theory (enable svar-addr-p))))
  ;; :prepwork ((local (defthmd 4vmask-alist-vars-expand1
  ;;                     (equal (4vmask-alist-vars x)
  ;;                            (and (consp (4vmask-alist-fix x))
  ;;                                 (union (svex-vars (cdar (4vmask-alist-fix x)))
  ;;                                        (4vmask-alist-vars (cdr (4vmask-alist-fix x))))))
  ;;                     :hints(("Goal" :in-theory (enable 4vmask-alist-vars
  ;;                                                       4vmask-alist-fix)))))
  ;;            (local (defthm 4vmask-alist-vars-expand
  ;;                     (implies (consp (4vmask-alist-fix x))
  ;;                              (equal (4vmask-alist-vars x)
  ;;                                     (union (svex-vars (cdar (4vmask-alist-fix x)))
  ;;                                            (4vmask-alist-vars (cdr (4vmask-alist-fix x))))))
  ;;                     :hints(("Goal" :use  4vmask-alist-vars-expand1))))
  ;;            (local (defthmd 4vmask-alist-keys-expand1
  ;;                     (equal (4vmask-alist-keys x)
  ;;                            (and (consp (4vmask-alist-fix x))
  ;;                                 (cons (caar (4vmask-alist-fix x))
  ;;                                       (4vmask-alist-keys (cdr (4vmask-alist-fix x))))))
  ;;                     :hints(("Goal" :in-theory (enable 4vmask-alist-keys
  ;;                                                       4vmask-alist-fix)))))
  ;;            (local (defthm 4vmask-alist-keys-expand
  ;;                     (implies (consp (4vmask-alist-fix x))
  ;;                              (equal (4vmask-alist-keys x)
  ;;                                     (cons (caar (4vmask-alist-fix x))
  ;;                                           (4vmask-alist-keys (cdr (4vmask-alist-fix x))))))
  ;;                     :hints(("Goal" :use 4vmask-alist-keys-expand1)))))
  :returns (new-x 4vmask-alist-p)
  :measure (len (4vmask-alist-fix x))
  (b* ((x (4vmask-alist-fix x)))
    (if (atom x)
        nil
      (cons (cons (change-svar (caar x) :nonblocking nil)
                  (cdar x))
            (4vmask-alist-unset-nonblocking (cdr x))))))
  



#!sv
(local (defthm svex-lookup-of-badguy-in-alist
         (implies (not (member (svar-fix v) (svex-alist-keys a)))
                  (not (svex-lookup v a)))))

#!sv
(define constraintlist-maybe-rewrite-fixpoint ((x constraintlist-p)
                                               (do-rewrite)
                                               &key
                                               ((count natp) '4)
                                               (verbosep 'nil))
  :returns (new-x constraintlist-p)
  (if do-rewrite
      (constraintlist-update-conds x (svexlist-rewrite-fixpoint
                                      (constraintlist->conds x)
                                      :count count :verbosep verbosep))
    (constraintlist-fix x))
  ///
  (defret vars-of-constraintlist-maybe-rewrite-fixpoint
    (implies (not (member v (constraintlist-vars x)))
             (not (member v (constraintlist-vars new-x))))))


;; (local (in-theory (disable sv::member-svex-alist-keys)))
#||
(trace$
 #!vl
 (vl-always->svex
  :cond (b* (((Vl-always x))
             ((vl-location x.loc)))
          (and (equal x.loc.filename "/n_mounts/f0-fs5/chiprel1/rel0517.cns/rtl/cns/lib/rtllib/rmuxdx4_im.v")
               (vl-scopestack-case ss
                 :local (equal (vl-scope->id ss.top) "rmuxdx4_im$width=1")
                 :otherwise nil)
               ))
  :entry (list 'vl-always->svex
               (with-local-ps (vl-pp-always x))
               (vl-scopestack->path ss)
               config)
  :exit (b* (((list ?warnings assigns) values))
          (list 'vl-always->svex assigns))))

||#

(define vl-always->svex ((x vl-always-p)
                         (ss vl-scopestack-p)
                         (scopes vl-elabscopes-p)
                         (config vl-simpconfig-p))
  :short "Translate a combinational or latch-type always block into a set of SVEX
          expressions."
  :returns (mv (warnings vl-warninglist-p)
               (assigns (and (sv::assigns-p assigns)
                             (sv::svarlist-addr-p (sv::assigns-vars assigns))))
               (constraints sv::constraintlist-p))
  :prepwork ((local
              #!sv (defthm cdr-last-when-svex-alist-p
                       (implies (svex-alist-p x)
                                (equal (cdr (last x)) nil))
                       :hints(("Goal" :in-theory (enable svex-alist-p)))))
             (local
              #!sv (defthm cdr-last-when-4vmask-alist-p
                       (implies (4vmask-alist-p x)
                                (equal (cdr (last x)) nil))
                       :hints(("Goal" :in-theory (enable 4vmask-alist-p)))))
             (local (defthm fast-alist-fork-nil
                      (equal (fast-alist-fork nil y) y)))
             (local (in-theory (disable fast-alist-fork)))
             (local (defthm lookup-in-svex-alist-under-iff
                      (implies (sv::svex-alist-p a)
                               (iff (cdr (hons-assoc-equal x a))
                                    (hons-assoc-equal x a)))
                      :hints(("Goal" :in-theory (enable sv::svex-alist-p)))))
             #!sv
             (local (Defthm svex-lookup-of-append
                      (iff (svex-lookup x (append a b))
                           (or (svex-lookup x a)
                               (svex-lookup x b)))
                      :hints(("Goal" :in-theory (enable svex-lookup)))))
             (local (in-theory (disable sv::member-of-svarlist-add-delay))))
  :guard-debug t
  (b* ((warnings nil)
       ((vl-simpconfig config))
       ((vl-always x) (vl-always-fix x))
       ((wmv ok warnings stmt trigger trigger-subst :ctx x)
        (vl-always->svex-checks x ss scopes))
       ((unless ok) (mv warnings nil nil))
       ;; Run this after elaboration, like everything else
       ;; ((mv ?ok warnings stmt conf)
       ;;  (vl-stmt-elaborate stmt conf))
       ((wmv ok warnings svstmts :ctx x)
        (vl-stmt->svstmts stmt ss scopes
                          (make-svstmt-config
                           :nonblockingp t
                           :uniquecase-conservative config.uniquecase-conservative
                           :uniquecase-constraints config.uniquecase-constraints)
                          nil)) ;; fnname
       ((unless ok) (mv warnings nil nil))
       ;; Only use the nonblocking-delay strategy for flops, not latches
       (locstring (vl-location-string x.loc))
       ((wmv ok warnings st constraints blkst-write-masks nbst-write-masks :ctx x)
        (time$ (sv::svstmtlist-compile-top svstmts
                                           :sclimit config.sc-limit
                                           :nb-delayp nil)
               :mintime 1/2
               :msg "; vl-always->svex: compiling statement at ~s0: ~st sec, ~sa bytes~%"
               :args (list locstring)))
       ((unless ok) (mv warnings nil nil))

       ((sv::svstate st) (sv::svstate-clean st))

       (- (sv::svstack-free st.blkst))
       (st.blkst (make-fast-alist (sv::svstack-to-svex-alist st.blkst)))
       (st.nonblkst (sv::svex-alist-unset-nonblocking st.nonblkst))
       (blk-written-vars (sv::svex-alist-keys st.blkst))
       (nb-written-vars  (sv::svex-alist-keys st.nonblkst))

       (both-written (acl2::hons-intersection blk-written-vars nb-written-vars))
       ((when both-written)
        (mv (warn :type :vl-always->svex-fail
                  :msg "~a0: Variables written by both blocking and ~
                        nonblocking assignments: ~x1"
                  :args (list x both-written))
            nil nil))

       (written-vars (append blk-written-vars nb-written-vars))
       ;; Set initial values of the registers in the expressions.  We'll
       ;; set these to Xes for always_comb and to their delay-1 values for
       ;; other types.
       (subst
        (if (eq x.type :vl-always-comb)
            (sv::svarlist-x-subst written-vars)
          (sv::svarlist-delay-subst written-vars)))

       (nb-read-vars (sv::svex-alist-vars st.nonblkst))

       ;; convenient insertion point for tracking some problematic loop
       (loc-of-interest nil)

       ;; Note: Because we want to warn about latches in a combinational
       ;; context, we do a rewrite pass before substituting.
       (- (and loc-of-interest
               (acl2::sneaky-save 'blkst st.blkst))
          (and loc-of-interest
               (acl2::sneaky-save 'nonblkst st.nonblkst)))
       (blkst-rw (time$ (sv::svex-alist-maybe-rewrite-fixpoint st.blkst config.sv-simplify :verbosep config.sv-simplify-verbosep)
                        :mintime (if loc-of-interest 0 1/2)
                        :msg "; vl-always->svex at ~s0: rewriting blocking assignments: ~st sec, ~sa bytes~%"
                        :args (list locstring)))
                 
       (nbst-rw  (time$ (sv::svex-alist-maybe-rewrite-fixpoint st.nonblkst config.sv-simplify :verbosep config.sv-simplify-verbosep)
                        :mintime (if loc-of-interest 0 1/2)
                        :msg "; vl-always->svex at ~s0: rewriting nonblocking assignments: ~st sec, ~sa bytes~%"
                        :args (list locstring)))

       (constraints-rw  (time$ (sv::constraintlist-maybe-rewrite-fixpoint constraints config.sv-simplify :verbosep config.sv-simplify-verbosep)
                               :mintime (if loc-of-interest 0 1/2)
                               :msg "; vl-always->svex at ~s0: rewriting constraints: ~st sec, ~sa bytes~%"
                               :args (list locstring)))
       
       (read-masks (time$ (sv::svexlist-mask-alist
                           (append (sv::svex-alist-vals blkst-rw)
                                   (sv::svex-alist-vals nbst-rw)))
                          :mintime (if loc-of-interest 0 1/2)
                          :msg "; vl-always->svex at ~s0: read masks: ~st sec, ~sa bytes~%"
                          :args (list locstring)))
       ;; ((mv blkst-write-masks nbst-write-masks)
       ;;  (sv::svstmtlist-write-masks svstmts nil nil))
       (nbst-write-masks (make-fast-alist
                          (sv::4vmask-alist-unset-nonblocking (fast-alist-free nbst-write-masks))))
       (- (clear-memoize-table 'sv::svex-unset-nonblocking)
          (clear-memoize-table 'sv::svex-set-nonblocking))

       (write-masks (fast-alist-clean
                     (combine-mask-alists blkst-write-masks nbst-write-masks)))

       ((wmv warnings :ctx x)
        (if (eq x.type :vl-always-comb)
            (vl-always->svex-latch-warnings write-masks read-masks)
          warnings))

       ((with-fast subst))

       ;; Should we apply the substitution to the trigger?  This only matters
       ;; if we are triggering on some variable we're also writing to, which
       ;; seems like a bad case we should probably warn about.  For now we
       ;; won't worry.
       (blkst-subst (sv::svex-alist-compose blkst-rw subst))
       (nbst-subst (sv::svex-alist-compose nbst-rw subst))
       (constraints-subst (sv::constraintlist-compose constraints-rw subst))


       (nbst-trigger
        (if trigger
            ;; Add a tick-delay to all variables in the nbst, except for those
            ;; in the trigger list, except whey they can't be the ones
            ;; triggering.  See "The Verilog flop problem" above.
            (b* ((nb-delaysubst (append-without-guard
                                 trigger-subst
                                 (sv::svarlist-delay-subst nb-read-vars)))
                 (nbst-subst2 (with-fast-alist nb-delaysubst
                                (sv::svex-alist-compose nbst-subst nb-delaysubst))))
              (vl-always-apply-trigger-to-updates
               trigger nbst-subst2))
          (if config.nb-latch-delay-hack
              (sv::svex-alist-add-delay nbst-subst 1)
            nbst-subst)))

       (blkst-trigger (if trigger
                          (vl-always-apply-trigger-to-updates trigger blkst-subst)
                        blkst-subst))

       (constraints-trigger (if trigger
                                (sv::constraintlist-add-pathcond trigger nil constraints-subst)
                              constraints-subst))

       (updates (append nbst-trigger blkst-trigger))
       (- (and loc-of-interest
               (acl2::sneaky-save 'updates updates)))
       (- (and loc-of-interest (break$)))
       (updates-rw (time$ (sv::svex-alist-maybe-rewrite-fixpoint updates config.sv-simplify :verbosep config.sv-simplify-verbosep)
                          :mintime (if loc-of-interest 0 1/2)
                          :msg "; vl-always->svex at ~s0: rewriting final updates: ~st sec, ~sa bytes~%"
                          :args (list (vl-location-string x.loc))))

       (lhs-sizes (make-fast-alist (sv::svstmtlist-lhs-var-sizes svstmts (list nil) nil)))
       ;; BOZO do something to check that these are consistent -- programming error otherwise

       ;; Compilation was ok.  Now we need to turn the state back into a list
       ;; of assigns.  Do this by getting the masks of what portion of each
       ;; variable was written, and use this to turn the alist into a set of
       ;; assignments.
       (assigns (sv::svex-alist->assigns updates-rw lhs-sizes write-masks)))
    (mv warnings assigns constraints-trigger))
  ///
  (defret vars-of-vl-always->svex
    (and (sv::svarlist-addr-p (sv::assigns-vars assigns))
         (sv::svarlist-addr-p (sv::constraintlist-vars constraints)))))

(define vl-alwayslist->svex ((x vl-alwayslist-p)
                             (ss vl-scopestack-p)
                             (scopes vl-elabscopes-p)
                             (config vl-simpconfig-p))
  :short "Translate a combinational or latch-type always block into a set of SVEX
          expressions."
  :returns (mv (warnings vl-warninglist-p)
               (assigns sv::assigns-p)
               (constraints sv::constraintlist-p))
  (b* ((warnings nil)
       ((when (atom x)) (mv (ok) nil nil))
       ((wmv warnings assigns1 constraints1)
        (time$ (vl-always->svex (car x) ss scopes config)
               :mintime 1
               :msg "; vl-always->svex at ~s0 total: ~st sec, ~sa bytes~%"
               :args (list (vl-location-string (vl-always->loc (car x))))))
       ((wmv warnings assigns2 constraints2)
        (vl-alwayslist->svex (cdr x) ss scopes config)))
    (mv warnings
        (append-without-guard assigns1 assigns2)
        (append-without-guard constraints1 constraints2)))
  ///
  (defret vars-of-vl-alwayslist->svex
    (and (sv::svarlist-addr-p (sv::assigns-vars assigns))
         (sv::svarlist-addr-p (sv::constraintlist-vars constraints)))))




(define vl-initial-size-warnings ((x vl-initial-p)
                                  (ss vl-scopestack-p)
                                  (scopes vl-elabscopes-p))
  :short "Generate any sizing warnings for an initial statement."
  :returns (warnings vl-warninglist-p)
  (b* (((vl-initial x) (vl-initial-fix x))
       ;; We don't actually care about the statements, we just want to get
       ;; things like truncation warnings.  BOZO we might even want to filter
       ;; out warnings here if there are other kinds of restrictions that the
       ;; statement compiler is enforcing.
       ((mv ?ok warnings ?svstmts)
        (vl-stmt->svstmts x.stmt ss scopes
                          (make-svstmt-config :nonblockingp t) nil)))
    warnings))

(define vl-initiallist-size-warnings ((x vl-initiallist-p)
                                      (ss vl-scopestack-p)
                                      (scopes vl-elabscopes-p))
  :returns (warnings vl-warninglist-p)
  (if (atom x)
      nil
    (append-without-guard (vl-initial-size-warnings (car x) ss scopes)
                          (vl-initiallist-size-warnings (cdr x) ss scopes))))


(define vl-final-size-warnings ((x vl-final-p)
                                (ss vl-scopestack-p)
                                (scopes vl-elabscopes-p))
  :short "Generate any sizing warnings for an final statement."
  :returns (warnings vl-warninglist-p)
  (b* (((vl-final x) (vl-final-fix x))
       ;; We don't actually care about the statements, we just want to get
       ;; things like truncation warnings.  BOZO we might even want to filter
       ;; out warnings here if there are other kinds of restrictions that the
       ;; statement compiler is enforcing.
       ((mv ?ok warnings ?svstmts)
        (vl-stmt->svstmts x.stmt ss scopes
                          (make-svstmt-config :nonblockingp t) nil)))
    warnings))

(define vl-finallist-size-warnings ((x vl-finallist-p)
                                    (ss vl-scopestack-p)
                                    (scopes vl-elabscopes-p))
  :returns (warnings vl-warninglist-p)
  (if (atom x)
      nil
    (append-without-guard (vl-final-size-warnings (car x) ss scopes)
                          (vl-finallist-size-warnings (cdr x) ss scopes))))
