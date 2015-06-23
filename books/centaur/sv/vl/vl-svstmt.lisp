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
(include-book "svstmt-compile")
;; (include-book "vl-fns-called")
;; (include-book "vl-paramrefs")
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
               (svex sv::svex-p)
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


#!sv
(define svex-resolve-single-assignment ((lhs svex-p)
                                        (rhs svex-p)
                                        (wholevar svex-p))
  ;; This function tries to take assignments such as
  ;;   my_arr[idx] = foo
  ;; and transform them into
  ;;   my_arr = { my_arr[max_idx:idx+1], foo, my_arr[idx-1:0] }.
  ;; But in actuality, the VL expression->svex transform turns dynamic indices
  ;; into horrible things, e.g., if we have
  ;;    logic [15:0] e;
  ;;    logic [3:0] a;
  ;; then e[a] becomes (after rewriting!)
  ;; (CONCAT 1
  ;;         (? (< (* 1 (CONCAT 4 "a" 0)) 0)
  ;;            (CONCAT (U- (* 1 (CONCAT 4 "a" 0)))
  ;;                    '(-1 . 0)
  ;;                    (CONCAT 16 "e" '(-1 . 0)))
  ;;            (RSH (* 1 (CONCAT 4 "a" 0))
  ;;                 (CONCAT 16 "e" '(-1 . 0))))
  ;;         '(0 . -1))
  ;; This is because we have to check the case where a is below the lowest
  ;; index of e -- in this case that's impossible, but in general it could be.

  ;; Fortunately, even in this mess there is some order.  We can recursively
  ;; descend through it until we get to the occurrences of e, transforming
  ;; things as follows (where here capital Z signifies X or Z, i.e. '(0 . -1)
  ;; or '(-1 . 0)):

  ;; (concat w a Z) = rhs --> a = (concat w rhs (rsh w a))
  ;; (concat w Z b) = rhs --> b = (rsh w rhs)
  ;; (zerox w a) = rhs --> a = (concat w rhs (rsh w a))
  ;; (signx w a) = rhs --> a = (concat w rhs (rsh w a))
  ;; (rsh w v) = rhs --> v = (concat w v rhs)

  ;; (? test then else) = rhs
  ;; is more complicated.  Resolve
  ;; then = rhs -->  var = then-val
  ;; else = rhs -->  var = else-val
  ;; and if both are successful, then result is
  ;; var = (? test then-val else-val).

  :measure (svex-count lhs)
  :returns (mv (err (iff (vl::vl-msg-p err) err))
               (final-rhs (implies (not err) (svex-p final-rhs))))
  :verify-guards nil
  (b* (((when (svex-equiv wholevar lhs)) (mv nil (svex-fix rhs)))
       ((mv ok al) (svex-unify (svcall concat 'w 'a 'b)
                               lhs nil))
       ((when ok)
        (b* ((w (svex-lookup 'w al))
             (a (svex-lookup 'a al))
             (b (svex-lookup 'b al))
             ((when (or (equal b (svex-x))
                        (equal b (svex-z))))
              ;; (concat w a Z) = rhs --> a = (concat w rhs (rsh w a))
              (svex-resolve-single-assignment
               a (svcall concat w rhs (svcall rsh w a)) wholevar))
             ((when (equal a (svex-x)))
              ;; (concat w Z b) = rhs --> b = (rsh w rhs)
              (svex-resolve-single-assignment
               b (svcall rsh w rhs) wholevar)))
          (mv (vl::vmsg "Unexpected form of svex assignment LHS: ~x0" (svex-fix lhs))
              nil)))
       ((mv ok al) (svex-unify (svcall zerox 'w 'a)
                               lhs nil))
       ((mv ok al) (if ok
                       (mv ok al)
                     (svex-unify (svcall signx 'w 'a)
                                 lhs nil)))
       ((when ok)
        (b* ((w (svex-lookup 'w al))
             (a (svex-lookup 'a al)))
          ;; (zerox/signx w a) = rhs --> a = (concat w rhs (rsh w a))
          (svex-resolve-single-assignment
           a (svcall concat w rhs (svcall rsh w a)) wholevar)))

       ((mv ok al) (svex-unify (svcall rsh 'w 'v) lhs nil))
       ((when ok)
        (b* ((w (svex-lookup 'w al))
             (v (svex-lookup 'v al)))
          ;; (rsh w v) = rhs --> v = (concat w v rhs)
          (svex-resolve-single-assignment
           v (svcall concat w v rhs) wholevar)))
       ((mv ok al) (svex-unify (svcall ? 'test 'then 'else) lhs nil))
       ((when ok)
        (b* ((test (svex-lookup 'test al))
             (then (svex-lookup 'then al))
             (else (svex-lookup 'else al))
             ;; (? test then else) = rhs
             ;; is more complicated.  Resolve
             ;; then = rhs -->  var = then-val
             ;; else = rhs -->  var = else-val
             ;; and if both are successful, then result is
             ;; var = (? test then-val else-val).
             ((mv err then-val) (svex-resolve-single-assignment then rhs wholevar))
             ((when err) (mv err nil))
             ((mv err else-val) (svex-resolve-single-assignment else rhs wholevar))
             ((when err) (mv err nil)))
          (mv nil (svcall ? test then-val else-val)))))
    (mv (vl::vmsg "Unexpected form of svex assignment LHS: ~x0 (variable: ~x1)"
                  (svex-fix lhs) (svex-fix wholevar))
        nil))
  ///
  (std::defret vars-of-svex-resolve-single-assignment
    (implies (and (not (member v (svex-vars lhs)))
                  (not (member v (svex-vars rhs)))
                  (not err))
             (not (member v (svex-vars final-rhs)))))

  (verify-guards svex-resolve-single-assignment))


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
;;               (vl-index-expr-svex/size/type lhs conf))
;;              ((unless ok)
;;               (mv nil warnings nil nil))
;;              ((vl-svexconf conf))
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
;;                (make-vl-index :scope opinfo.prefixname) conf))
;;              ((unless ok) (mv nil warnings nil nil))
;;              ((wmv ok warnings svstmts)
;;               (vl-single-procedural-assign->svstmts
;;                lhssvex size wholesvex wholesize rhssvex blockingp)))
;;           (mv ok warnings svstmts (and ok size)))



(defines vl-procedural-assign->svstmts
;; (trace$
;;  #!vl (vl-procedural-assign->svstmts
;;        :entry (list 'vl-procedural-assign->svstmts
;;                     (with-local-ps (vl-pp-expr lhs))
;;                     rhssvex)
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
                                         (conf vl-svexconf-p))
    :measure (vl-expr-count lhs)
    :verify-guards nil
    :returns (mv ok
                 (warnings vl-warninglist-p)
                 (svstmts sv::svstmtlist-p)
                 (shift (implies ok (natp shift)) :rule-classes :type-prescription))
    :prepwork ((local (Defthmd consp-by-len
                        (implies (posp (len x))
                                 (consp x)))))
    (b* ((warnings nil)
         (lhs (vl-expr-fix lhs)))
      (vl-expr-case lhs
        :vl-index
        (b* (((vl-svexconf conf))
             ((mv err opinfo) (vl-index-expr-typetrace lhs conf.ss conf.typeov))
             ((when err)
              (mv nil
                  (fatal :type :vl-assignstmt-fail
                         :msg "Failed to get type of LHS ~a0: ~@1"
                         :args (list lhs err))
                  nil nil))
             ((vl-operandinfo opinfo))
             ((wmv warnings indices ?sizes)
              (vl-exprlist-to-svex-selfdet (vl-operandinfo->indices opinfo) conf))

             ((mv err dyn-size) (vl-datatype-size opinfo.type))
             ((unless (and (not err) dyn-size))
              (mv nil
                  (fatal :type :vl-assignstmt-fail
                         :msg "Failed to size the dynamic part of LHS ~a0: ~@1"
                         :args (list lhs (or err "")))
                  nil nil))

             
             ;; Dynselect-expr is in terms of the special variable
             ;; *svex-longest-static-prefix-var*.
             ((mv err longest-static-prefix-svex lsp-type dynselect-expr)
              (vl-operandinfo-to-svex-longest-static-prefix
               opinfo indices conf.ss conf.params))
             (dynselect-trunc (sv::svcall sv::concat (svex-int dyn-size) dynselect-expr (svex-x)))
             ((when err)
              (mv nil
                  (fatal :type :vl-assignstmt-fail
                         :msg "Failed to process LHS ~a0: ~@1"
                         :args (list lhs err))
                  nil nil))

             ((list dynselect-final) (sv::svexlist-rewrite-top (list dynselect-trunc)))

             ((mv err dyn-rhs)
              (sv::svex-resolve-single-assignment
               dynselect-final rhssvex *svex-longest-static-prefix-var*))
             ((when err)
              (mv nil
                  (fatal :type :vl-assignstmt-fail
                         :msg "Failed to process dynamic select expression ~a0: ~@1"
                         :args (list lhs err))
                  nil nil))

             (final-rhs (sv::svex-replace-var dyn-rhs *svex-longest-static-prefix-var*
                                              longest-static-prefix-svex))
             (- (clear-memoize-table 'sv::svex-replace-var))

             ((mv err lsp-size) (vl-datatype-size lsp-type))
             ((unless (and (not err) lsp-size))
              (mv nil
                  (fatal :type :vl-assignstmt-fail
                         :msg "Failed to size the static part of LHS ~a0: ~@1"
                         :args (list lhs (or err "")))
                  nil nil))
             
             (lsp-simp (sv::svex-concat
                        lsp-size (sv::svex-lhsrewrite longest-static-prefix-svex 0 lsp-size)
                        (sv::svex-z)))
             
             ((unless (sv::lhssvex-p lsp-simp))
              (mv nil
                  (fatal :type :vl-assignstmt-fail
                         :msg "Programming error -- the static portion of LHS ~
                               ~a0 couldn't be turned into a proper LHS ~
                               expression."
                         :args (list lhs))
                  nil nil)))
          (mv t warnings
              (list (sv::make-svstmt-assign
                     :lhs (sv::svex->lhs lsp-simp)
                     :rhs final-rhs
                     :blockingp blockingp))
              dyn-size))
        :vl-concat
        (vl-procedural-assign-concat->svstmts lhs.parts rhssvex blockingp conf)
        :otherwise
        (mv nil
            (fatal :type :vl-assignstmt-fail
                   :msg "Bad expression in LHS: ~a0"
                   :args (list lhs))
            nil nil))))

  (define vl-procedural-assign-concat->svstmts ((parts vl-exprlist-p)
                                                (rhssvex sv::svex-p)
                                                (blockingp booleanp)
                                                (conf vl-svexconf-p))
    :measure (vl-exprlist-count parts)
    :returns (mv ok
                 (warnings vl-warninglist-p)
                 (svstmts sv::svstmtlist-p)
                 (shift (implies ok (natp shift)) :rule-classes :type-prescription))
    (b* (((when (atom parts)) (mv t nil nil 0))
         ((mv ok warnings svstmts2 shift2)
          (vl-procedural-assign-concat->svstmts (cdr parts) rhssvex blockingp conf))
         ((unless ok) (mv nil warnings nil nil))
         (rhs (sv::svcall sv::rsh (svex-int shift2) rhssvex))
         ((wmv ok warnings svstmts1 shift1)
          (vl-procedural-assign->svstmts (car parts) rhs blockingp conf))
         ((unless ok) (mv nil warnings nil nil)))
      (mv t warnings (append-without-guard svstmts1 svstmts2)
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
                       (svex-vars b))
           :hints(("Goal" :in-theory (enable sv::svex-alist-vars)))))

  (local (defthm svex-alist-keys-of-single
           #!sv (equal (svex-alist-keys (list (cons a b)))
                       (list (svar-fix a)))
           :hints(("Goal" :in-theory (enable sv::svex-alist-keys)))))

  (local (defthm member-single
           (iff (member a (list b))
                (equal a b))
           :hints(("Goal" :in-theory (enable member)))))


  (defthm-vl-procedural-assign->svstmts-flag
    (defthm vars-of-vl-procedural-assign->svstmts
      (b* (((mv ?ok ?warnings ?svstmts ?shift)
            (vl-procedural-assign->svstmts lhs rhssvex blockingp conf)))
        (implies (sv::svarlist-addr-p (sv::svex-vars rhssvex))
                 (sv::svarlist-addr-p
                  (sv::svstmtlist-vars svstmts))))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable sv::vars-of-svex-compose-strong))))
      :flag vl-procedural-assign->svstmts)

    (defthm vars-of-vl-procedural-assign-concat->svstmts
      (b* (((mv ?ok ?warnings ?svstmts ?shift)
            (vl-procedural-assign-concat->svstmts parts rhssvex blockingp conf)))
        (implies (sv::svarlist-addr-p (sv::svex-vars rhssvex))
                 (sv::svarlist-addr-p
                  (sv::svstmtlist-vars svstmts))))
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
               (res sv::svstmtlist-p))
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
    (sv::svarlist-addr-p (sv::svstmtlist-vars res))))

  ;; (b* ((warnings nil)
  ;;      ((wmv warnings svex-lhs lhs-type)
  ;;       (vl-expr-to-svex-lhs lhs conf))
  ;;      ((unless lhs-type)
  ;;       (mv nil warnings nil))
  ;;      ((wmv warnings svex-rhs)
  ;;       (vl-expr-to-svex-datatyped rhs lhs-type conf)))
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
;;         (vl-expr-to-svex-lhs lhs conf))
;;        ((unless lhs-type)
;;         (mv nil warnings nil))
;;        ((wmv warnings svex-rhs)
;;         (vl-expr-to-svex-datatyped rhs lhs-type conf)))
;;     (mv t warnings
;;         (list (sv::make-svstmt-assign :lhs svex-lhs :rhs svex-rhs
;;                                         :blockingp blockingp))))
;;   ///
;;   (more-returns
;;    (res :name vars-of-vl-assignstmt->svstmts
;;         (sv::svarlist-addr-p
;;          (sv::svstmtlist-vars res)))))


(define vl-vardecllist->svstmts ((x vl-vardecllist-p)
                                 (conf vl-svexconf-p))
  :returns (mv (ok)
               (warnings vl-warninglist-p)
               (res (and (sv::svstmtlist-p res)
                         (sv::svarlist-addr-p
                          (sv::svstmtlist-vars res)))))
  (b* ((warnings nil)
       ((when (atom x)) (mv t (ok) nil))
       (x1 (vl-vardecl-fix (car x)))
       ((mv ok warnings rest)
        (vl-vardecllist->svstmts (cdr x) conf))
       ((unless ok) (mv nil warnings rest))
       ((vl-vardecl x1) x1)
       ;; skip if there's no initial value given
       ((unless x1.initval) (mv ok warnings rest))

       (lhs (vl-idexpr x1.name)))
    (vl-assignstmt->svstmts lhs x1.initval t conf)))
       
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
                                 (conf vl-svexconf-p))
  :returns (mv (warnings vl-warninglist-p)
               (cond sv::svex-p))
  (if (atom x)
      (mv nil (svex-int 0))
    (b* (((mv warnings rest) (vl-caseexprs->svex-test (cdr x) test size casetype conf))
         ((wmv warnings first &) (vl-expr-to-svex-selfdet (car x) (lnfix size) conf)))
    (mv warnings
        (sv::svcall sv::bitor
                      (case (vl-casetype-fix casetype)
                        ((nil) (sv::svcall sv::== test first))
                        (otherwise (sv::svcall sv::==?? test first)))
                      rest))))
  ///
  (defret vars-of-vl-caseexprs->svex-test
    (implies (sv::svarlist-addr-p (sv::svex-vars test))
             (sv::svarlist-addr-p (sv::svex-vars cond)))))

(defines vl-stmt->svstmts
  :prepwork ((local (in-theory (disable not))))
  (define vl-stmt->svstmts ((x vl-stmt-p)
                            (conf vl-svexconf-p)
                            (nonblockingp))
    :verify-guards nil
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (res (and (sv::svstmtlist-p res)
                           (sv::svarlist-addr-p
                            (sv::svstmtlist-vars res)))))
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
        (b* (((wmv warnings cond ?type ?size)
              (vl-expr-to-svex-untyped x.condition conf))
             ((wmv ok1 warnings true)
              (vl-stmt->svstmts x.truebranch conf nonblockingp))
             ((wmv ok2 warnings false)
              (vl-stmt->svstmts x.falsebranch conf nonblockingp)))
          (mv (and ok1 ok2) warnings
              (list (sv::make-svstmt-if :cond cond :then true :else false))))
        :vl-whilestmt
        (b* (((wmv warnings cond ?type ?size)
              (vl-expr-to-svex-untyped x.condition conf))
             ((wmv ok warnings body)
              (vl-stmt->svstmts x.body conf nonblockingp)))
          (mv ok warnings (list (sv::make-svstmt-while :cond cond :body body))))
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
             ((wmv warnings cond ?type ?size)
              (vl-expr-to-svex-untyped x.test conf))
             ((wmv ok3 warnings stepstmts)
              (vl-stmtlist->svstmts x.stepforms conf nonblockingp))
             ((wmv ok4 warnings body)
              (vl-stmt->svstmts x.body conf nonblockingp)))
          (mv (and ok1 ok2 ok3 ok4)
              warnings
              (append-without-guard
               initstmts1 initstmts2
               (list (sv::make-svstmt-while
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
             ((when (member nil (list-fix sizes)))
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
                 (res (and (sv::svstmtlist-p res)
                           (sv::svarlist-addr-p
                            (sv::svstmtlist-vars res)))))
    :measure (vl-stmtlist-count x)
    (b* ((warnings nil)
         ((when (atom x)) (mv t (ok) nil))
         ((wmv ok1 warnings x1) (vl-stmt->svstmts (car x) conf nonblockingp))
         ((wmv ok2 warnings x2) (vl-stmtlist->svstmts (cdr x) conf nonblockingp)))
      (mv (and ok1 ok2) warnings (append-without-guard x1 x2))))

  (define vl-caselist->svstmts ((x vl-caselist-p)
                                (size natp)
                                (test sv::svex-p)
                                (default sv::svstmtlist-p)
                                (casetype vl-casetype-p)
                                (conf vl-svexconf-p)
                                (nonblockingp))
    :returns (mv (ok)
                 (warnings vl-warninglist-p)
                 (res (and (sv::svstmtlist-p res)
                           (implies (and (sv::svarlist-addr-p (sv::svex-vars test))
                                         (sv::svarlist-addr-p (sv::svstmtlist-vars default)))
                                    (sv::svarlist-addr-p
                                     (sv::svstmtlist-vars res))))))
    :measure (vl-caselist-count x)
    (b* ((x (vl-caselist-fix x))
         ((when (atom x))
          (mv t nil (sv::svstmtlist-fix default)))
         ((cons tests stmt) (car x))
         ((mv ok1 warnings rest) (vl-caselist->svstmts (cdr x) size test default casetype conf nonblockingp))
         ((wmv ok2 warnings first) (vl-stmt->svstmts stmt conf nonblockingp))
         ((wmv warnings test)
          (vl-caseexprs->svex-test tests test size casetype conf)))
      (mv (and ok1 ok2)
          warnings
          (list (sv::make-svstmt-if :cond test :then first :else rest)))))

         
         

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


(define vl-fundecl-to-svex  ((x vl-fundecl-p)
                             (conf vl-svexconf-p
                                 "Svexconf for inside the function decl")
                             ;; (fntable sv::svex-alist-p)
                             ;; (paramtable sv::svex-alist-p)
                             )
  :returns (mv (warnings vl-warninglist-p)
               (svex sv::svex-p))
  (b* (((vl-fundecl x) (vl-fundecl-fix x))
       (warnings nil)
       ;; nonblocking assignments not allowed
       ((wmv ok warnings svstmts) (vl-stmt->svstmts x.body conf nil))
       ((unless ok) (mv warnings (svex-x)))
       ((wmv ok warnings svstate)
        (sv::svstmtlist-compile svstmts (sv::make-svstate) 100000
                                  nil ;; nb-delayp
                                  ))
       ((unless ok) (mv warnings (svex-x)))
       ((sv::svstate svstate))
       (expr (sv::svex-lookup (sv::make-svar :name x.name) svstate.blkst))
       (- (sv::svstate-free svstate))
       ((unless expr)
        (mv (warn :type :vl-fundecl-to-svex-fail
                  :msg "Function has no return value"
                  :args (list x))
            (svex-x))))
    (mv (ok) expr))
  ///
  (more-returns
   (svex :name vars-of-vl-fundecl-to-svex
         (sv::svarlist-addr-p (sv::svex-vars svex)))))

(define vl-elaborated-expr-consteval ((x vl-expr-p)
                                      (conf vl-svexconf-p)
                                      &key ((ctxsize maybe-natp) 'nil))
  :short "Assumes expression is already elaborated.  conf is read-only."
  :returns (mv (ok  "no errors")
               (constp "successfully reduced to constant")
               (warnings1 vl-warninglist-p)
               (new-x vl-expr-p)
               (svex sv::svex-p))
  (b* (((vl-svexconf conf))
       (x (vl-expr-fix x))
       ((mv warnings signedness) (vl-expr-typedecide x conf.ss conf.typeov))
       ((wmv warnings svex size) (vl-expr-to-svex-selfdet x ctxsize conf))
       ((unless (and (posp size) signedness))
        ;; presumably already warned about this?
        (mv nil nil warnings x (svex-x)))
       (svex (sv::svex-reduce-consts svex))
       (val (sv::svex-case svex :quote svex.val :otherwise nil))
       ((unless val)
        (mv t nil warnings x svex))
       (new-x (make-vl-literal :val (vl-4vec-to-value val size :signedness signedness))))
    (mv t t warnings new-x svex)))

(define vl-consteval ((x vl-expr-p)
                      (conf vl-svexconf-p)
                      &key ((ctxsize maybe-natp) 'nil))
  :returns (mv (warnings vl-warninglist-p)
               (new-x vl-expr-p))
  (b* (((mv ?ok ?constant warnings new-x ?svex)
        (vl-elaborated-expr-consteval x conf :ctxsize ctxsize)))
    (mv warnings new-x)))









(define vl-evatomlist-has-edge ((x vl-evatomlist-p))
  (if (atom x)
      nil
    (or (not (eq (vl-evatom->type (car x)) :vl-noedge))
        (vl-evatomlist-has-edge (cdr x)))))


(define vl-evatomlist->svex ((x vl-evatomlist-p)
                             (conf vl-svexconf-p))
  :returns (mv (warnings vl-warninglist-p)
               (trigger (and (sv::svex-p trigger)
                             (sv::svarlist-addr-p (sv::svex-vars trigger)))))
  :prepwork ((local (defthm vl-evatom->type-forward
                      (or (equal (vl-evatom->type x) :vl-noedge)
                          (equal (vl-evatom->type x) :vl-negedge)
                          (equal (vl-evatom->type x) :vl-posedge))
                      :hints (("goal" :use vl-evatomtype-p-of-vl-evatom->type
                               :in-theory (e/d (vl-evatomtype-p)
                                               (vl-evatomtype-p-of-vl-evatom->type))))
                      :rule-classes ((:forward-chaining :trigger-terms ((vl-evatom->type x)))))))
  (b* (((when (atom x)) (mv nil (sv::svex-quote (sv::2vec 0))))
       ((vl-evatom x1) (car x))
       (warnings nil)
       ((wmv warnings expr ?type ?size)
        (vl-expr-to-svex-untyped x1.expr conf))
       (delay-expr (sv::svex-add-delay expr 1))
       ;; Note: Ensure these expressions always evaluate to either -1 or 0.
       (trigger1 (case x1.type
                   (:vl-noedge
                    ;; expr and delay-expr are unequal
                    (sv::make-svex-call
                     :fn 'sv::bitnot
                     :args (list (sv::make-svex-call
                                  :fn 'sv::==
                                  :args (list expr delay-expr)))))
                   (:vl-posedge
                    ;; LSBs have a posedge
                    (sv::make-svex-call
                     :fn 'sv::uor
                     :args (list (sv::make-svex-call
                                  :fn 'sv::bitand
                                  :args (list (sv::make-svex-call
                                               :fn 'sv::bitnot
                                               :args (list (sv::make-svex-call
                                                            :fn 'sv::bitsel
                                                            :args (list (sv::svex-quote (sv::2vec 0))
                                                                        delay-expr))))
                                              (sv::make-svex-call
                                               :fn 'sv::bitsel
                                               :args (list (sv::svex-quote (sv::2vec 0))
                                                           expr)))))))
                   (:vl-negedge
                    (sv::make-svex-call
                     :fn 'sv::uor
                     :args (list (sv::make-svex-call
                                  :fn 'sv::bitand
                                  :args (list (sv::make-svex-call
                                               :fn 'sv::bitnot
                                               :args (list (sv::make-svex-call
                                                            :fn 'sv::bitsel
                                                            :args (list (sv::svex-quote (sv::2vec 0))
                                                                        expr))))
                                              (sv::make-svex-call
                                               :fn 'sv::bitsel
                                               :args (list (sv::svex-quote (sv::2vec 0))
                                                           delay-expr)))))))))
       ((wmv warnings rest)
        (vl-evatomlist->svex (cdr x) conf)))
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
                                          (conf vl-svexconf-p))
  :returns (mv (warnings vl-warninglist-p)
               (subst (and (sv::svex-alist-p subst)
                           (sv::svarlist-addr-p (sv::svex-alist-vars subst))
                           (sv::svarlist-addr-p (sv::svex-alist-keys subst)))
                      :hints(("Goal" :in-theory (enable sv::svex-alist-keys
                                                        sv::svex-alist-vars)))))
  :prepwork ((local (defthm vl-evatom->type-forward
                      (or (equal (vl-evatom->type x) :vl-noedge)
                          (equal (vl-evatom->type x) :vl-negedge)
                          (equal (vl-evatom->type x) :vl-posedge))
                      :hints (("goal" :use vl-evatomtype-p-of-vl-evatom->type
                               :in-theory (e/d (vl-evatomtype-p)
                                               (vl-evatomtype-p-of-vl-evatom->type))))
                      :rule-classes ((:forward-chaining :trigger-terms ((vl-evatom->type x))))))
             (local (in-theory (disable member-equal))))
  (b* (((when (atom x)) (mv nil nil))
       ((vl-evatom x1) (car x))
       ((vl-svexconf conf))
       (warnings nil)
       ((unless (vl-expr-case x1.expr
                  :vl-index (and (vl-partselect-case x1.expr.part :none)
                                 (atom x1.expr.indices))
                  :otherwise nil))
        ;; We're going to deal with all these sorts of problems elsewhere?
        (vl-evatomlist-delay-substitution (cdr x) edge-dependent-delayp conf))
       ((mv err opinfo) (vl-index-expr-typetrace x1.expr conf.ss conf.typeov))
       ((when err)
        ;; We're going to deal with all these sorts of problems elsewhere?
        (vl-evatomlist-delay-substitution (cdr x) edge-dependent-delayp conf))
       ((vl-operandinfo opinfo))
       ((unless (and (vl-hidtrace-resolved-p opinfo.hidtrace)
                     (eql (vl-seltrace-unres-count opinfo.seltrace) 0)))
        ;; We're going to deal with all these sorts of problems elsewhere?
        (vl-evatomlist-delay-substitution (cdr x) edge-dependent-delayp conf))
       ((mv err var) (vl-seltrace-to-svar opinfo.seltrace opinfo conf.ss))
       ((when err)
        ;; We're going to deal with all these sorts of problems elsewhere?
        (vl-evatomlist-delay-substitution (cdr x) edge-dependent-delayp conf))
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
                                       expr))))
                     expr))
       ((wmv warnings rest)
        (vl-evatomlist-delay-substitution (cdr x) edge-dependent-delayp conf)))
    (mv warnings
        (cons (cons var delay-expr) rest))))


       
(define vl-always->svex-checks ((x vl-always-p)
                                (conf vl-svexconf-p))
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
                      (mv-nth 1 (vl-evatomlist->svex x conf))
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
                                     (vl-eventcontrol->atoms x.stmt.ctrl) conf))
            ((wmv warnings trigger-subst) (vl-evatomlist-delay-substitution
                                           (vl-eventcontrol->atoms x.stmt.ctrl)
                                           t conf)))
         (mv t
             warnings
             x.stmt.body
             trigger
             trigger-subst))))))
             
#!sv
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

#!sv
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
                                        :args (list (sv::svex-quote (sv::2vec mask))
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

#!sv
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
                   

#!sv
(define svarlist-remove-delays ((x svarlist-p))
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
  :prepwork ((local (defthm integerp-lookup-in-4vmask-alist
                      (implies (and (sv::4vmask-alist-p x)
                                    (hons-assoc-equal k x))
                               (integerp (cdr (hons-assoc-equal k x))))
                      :hints(("Goal" :in-theory (enable sv::4vmask-alist-p
                                                        hons-assoc-equal))))))
  (b* ((masks (sv::4vmask-alist-fix masks))
       (acc (sv::4vmask-alist-fix acc))
       ((When (atom masks)) acc)
       ((cons key val) (car masks))
       (look (or (cdr (hons-get key acc)) 0))
       (newval (logior val look)))
    (combine-mask-alists (cdr masks) (hons-acons key newval acc))))




    
(define vl-always-apply-trigger-to-updates ((trigger sv::svex-p)
                                            (x sv::svex-alist-p))
  :returns (new-x sv::svex-alist-p)
  :measure (len (sv::svex-alist-fix x))
  (b* ((x (sv::svex-alist-fix x))
       ((when (atom x)) nil)
       ((cons var upd) (car x))
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
  (more-returns
   (new-x :name keys-of-vl-always-apply-trigger-to-updates
          (iff (sv::svex-lookup v new-x)
               (sv::svex-lookup v x))
          :hints(("Goal" :in-theory (enable sv::svex-lookup
                                            hons-assoc-equal)))))
  (local (in-theory (disable sv::member-of-svarlist-add-delay)))

  (local
   (more-returns
    (new-x :name vars-of-vl-always-apply-trigger-to-updates-lemma
           (implies (and (not (member v (sv::svex-alist-vars x)))
                         (not (member v (sv::svex-vars trigger)))
                         (not (member v (sv::svarlist-add-delay
                                         (sv::svex-alist-keys x) 1)))
                         (sv::svex-alist-p x))
                    (not (member v (sv::svex-alist-vars new-x))))
           :hints(("Goal" :induct (vl-always-apply-trigger-to-updates trigger x)
                   :in-theory (enable sv::svex-alist-vars
                                      sv::svex-alist-keys))))))
  (more-returns
    (new-x :name vars-of-vl-always-apply-trigger-to-updates
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
                   :in-theory (enable sv::svex-alist-fix))))))


(define vl-always->svex ((x vl-always-p)
                         (conf vl-svexconf-p))
  :short "Translate a combinational or latch-type always block into a set of SVEX
          expressions."
  :returns (mv (warnings vl-warninglist-p)
               (assigns (and (sv::assigns-p assigns)
                             (sv::svarlist-addr-p (sv::assigns-vars assigns)))))
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
       ((vl-always x) (vl-always-fix x))
       ((wmv ok warnings stmt trigger trigger-subst)
        (vl-always->svex-checks x conf))
       ((unless ok) (mv warnings nil))
       ;; Run this after elaboration, like everything else
       ;; ((mv ?ok warnings stmt conf)
       ;;  (vl-stmt-elaborate stmt conf))
       ((wmv ok warnings svstmts)
        (vl-stmt->svstmts stmt conf t))
       ((unless ok) (mv warnings nil))
       ;; Only use the nonblocking-delay strategy for flops, not latches
       ((wmv ok warnings st)
        (sv::svstmtlist-compile svstmts (sv::make-svstate) 100000 nil))
       ((unless ok) (mv warnings nil))

       ((sv::svstate st) (sv::svstate-clean st))


       (blk-written-vars (sv::svex-alist-keys st.blkst))
       (nb-written-vars  (sv::svex-alist-keys st.nonblkst))

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
            (sv::svarlist-x-subst written-vars)
          (sv::svarlist-delay-subst written-vars)))

       (nb-read-vars (sv::svex-alist-vars st.nonblkst))

       ;; Note: Because we want to warn about latches in a combinational
       ;; context, we do a rewrite pass before substituting.
       (blkst-rw (sv::svex-alist-rewrite-fixpoint st.blkst))
       (nbst-rw  (sv::svex-alist-rewrite-fixpoint st.nonblkst))
       (read-masks (sv::svexlist-mask-alist
                    (append (sv::svex-alist-vals blkst-rw)
                            (sv::svex-alist-vals nbst-rw))))
       ((mv blkst-write-masks nbst-write-masks)
        (sv::svstmtlist-write-masks svstmts nil nil))
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
       (blkst-subst (sv::svex-alist-compose blkst-rw subst))
       (nbst-subst (sv::svex-alist-compose nbst-rw subst))


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
          (sv::svex-alist-add-delay nbst-subst 1)))

       (blkst-trigger (if trigger
                          (vl-always-apply-trigger-to-updates trigger blkst-subst)
                        blkst-subst))

       (updates (append nbst-trigger blkst-trigger))
      
       (updates-rw (sv::svex-alist-rewrite-fixpoint updates))

       ;; Compilation was ok.  Now we need to turn the state back into a list
       ;; of assigns.  Do this by getting the masks of what portion of each
       ;; variable was written, and use this to turn the alist into a set of
       ;; assignments.
       (assigns (sv::svex-alist->assigns updates-rw write-masks)))
    (mv warnings assigns)))

(define vl-alwayslist->svex ((x vl-alwayslist-p)
                             (conf vl-svexconf-p))
  :short "Translate a combinational or latch-type always block into a set of SVEX
          expressions."
  :returns (mv (warnings vl-warninglist-p)
               (assigns (and (sv::assigns-p assigns)
                             (sv::svarlist-addr-p (sv::assigns-vars assigns)))))
  (b* ((warnings nil)
       ((when (atom x)) (mv (ok) nil))
       ((wmv warnings assigns1)
        (vl-always->svex (car x) conf))
       ((wmv warnings assigns2)
        (vl-alwayslist->svex (cdr x) conf)))
    (mv warnings
        (append-without-guard assigns1 assigns2))))
