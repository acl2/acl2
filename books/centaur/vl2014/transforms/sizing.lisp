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
(include-book "expr-size")
(include-book "../mlib/blocks")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

; -----------------------------------------------------------------------------
;
;                    SIZING EXPRESSIONS THROUGHOUT A MODULE
;
; -----------------------------------------------------------------------------

(defmacro def-vl-exprsize (name &key fn body takes-ctx extra-formals (long '""))
  (b* ((mksym-package-symbol (pkg-witness "VL2014"))
       (fn   (or fn (mksym name '-exprsize)))
       (fix  (mksym name '-fix))
       (type (mksym name '-p)))
    `(define ,fn ((x      ,type)
                  (ss vl-scopestack-p)
                  ,@(and takes-ctx '((ctx vl-context-p)))
                  ,@extra-formals
                  (warnings vl-warninglist-p))
       :parents (expression-sizing)
       :short ,(cat "Compute sizes and types of expressions throughout a @(see " (symbol-name type) ")")
       :returns (mv (successp booleanp :rule-classes :type-prescription)
                    (warnings vl-warninglist-p)
                    (new-x    ,type))
       :long ,long
       (b* ((x        (,fix x))
            (warnings (vl-warninglist-fix warnings)))
         ,body))))

(defmacro def-vl-exprsize-list (name &key element takes-ctx extra-formals)
  ;; note: extra-formals assume the formals are listed as ((name guard) ...)
  ;; not just (name1 name2 ...), b/c we assume its strip-cars is the actual
  ;; list of variable names.
  (b* ((mksym-package-symbol (pkg-witness "VL2014"))
       (fn      (mksym name '-exprsize))
       (ctx-fn (mksym element '-exprsize))
       (type    (mksym name '-p))
       (formals (append '(x ss)
                        (if takes-ctx '(ctx) nil)
                        (strip-cars extra-formals)
                        '(warnings))))
    `(define ,fn ((x      ,type)
                  (ss vl-scopestack-p)
                  ,@(and takes-ctx '((ctx vl-context-p)))
                  ,@extra-formals
                  (warnings vl-warninglist-p))
       :returns (mv (successp booleanp :rule-classes :type-prescription)
                    (warnings vl-warninglist-p)
                    (new-x    ,type))
       :parents (expression-sizing)
       :short ,(cat "Compute sizes and types of expressions throughout a @(see " (symbol-name type) ").")
       (b* (((when (atom x))
             (mv t (ok) nil))
            ((mv car-successp warnings car-prime) (,ctx-fn . ,(subst '(car x) 'x formals)))
            ((mv cdr-successp warnings cdr-prime) (,fn . ,(subst '(cdr x) 'x formals)))
            (successp (and car-successp cdr-successp))
            (x-prime  (cons car-prime cdr-prime)))
         (mv successp warnings x-prime))
       ///
       (defthm ,(mksym 'true-listp-of- fn)
         (true-listp (mv-nth 2 (,fn . ,formals)))
         :rule-classes :type-prescription))))


(def-vl-exprsize vl-maybe-expr
  :fn vl-maybe-expr-size
  :takes-ctx t
  :body (if x
            (vl-expr-size nil x ss ctx warnings)
          (mv t warnings x)))

(def-vl-exprsize vl-range
  :takes-ctx t
  :body (b* (((vl-range x) x)
             ((mv msb-successp warnings msb-prime)
              (vl-expr-size nil x.msb ss ctx warnings))
             ((mv lsb-successp warnings lsb-prime)
              (vl-expr-size nil x.lsb ss ctx warnings))
             (successp (and msb-successp lsb-successp))
             (x-prime  (change-vl-range x
                                        :msb msb-prime
                                        :lsb lsb-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize vl-maybe-range
  :takes-ctx t
  :body (if x
            (vl-range-exprsize x ss ctx warnings)
          (mv t warnings x)))

(def-vl-exprsize-list vl-rangelist
  :takes-ctx t
  :element vl-range)

(def-vl-exprsize vl-packeddimension
  :takes-ctx t
  :body
  (b* ((x (vl-packeddimension-fix x)))
    (if (eq x :vl-unsized-dimension)
        (mv t warnings x)
      (vl-range-exprsize x ss ctx warnings))))

(def-vl-exprsize vl-maybe-packeddimension
  :takes-ctx t
  :body
  (if x
      (vl-packeddimension-exprsize x ss ctx warnings)
    (mv t warnings x)))

(def-vl-exprsize-list vl-packeddimensionlist
  :takes-ctx t
  :element vl-packeddimension)

(def-vl-exprsize vl-enumbasetype
  :takes-ctx t
  :body (b* (((vl-enumbasetype x) x)
             ((mv successp warnings dim)
              (vl-maybe-packeddimension-exprsize x.dim ss ctx warnings)))
          (mv successp warnings (change-vl-enumbasetype x :dim dim))))

(def-vl-exprsize vl-enumitem
  :takes-ctx t
  :body
  (b* (((vl-enumitem x) x)
       ((mv range-successp warnings new-range)
        (vl-maybe-range-exprsize x.range ss ctx warnings))
       ((mv value-successp warnings new-value)
        (vl-maybe-expr-size x.value ss ctx warnings))
       (successp (and range-successp value-successp))
       (new-x    (change-vl-enumitem x
                                     :range new-range
                                     :value new-value)))
    (mv successp warnings new-x)))

(def-vl-exprsize-list vl-enumitemlist
  :takes-ctx t
  :element vl-enumitem)


(defines vl-datatype-exprsize
  :verify-guards nil

  (define vl-datatype-exprsize ((x        vl-datatype-p)
                                (ss vl-scopestack-p)
                                (ctx     vl-context-p)
                                (warnings vl-warninglist-p))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-x    vl-datatype-p))
    :measure (vl-datatype-count x)
    (vl-datatype-case x
      (:vl-coretype
       (b* (((mv pdims-successp warnings new-pdims)
             (vl-packeddimensionlist-exprsize x.pdims ss ctx warnings))
            ((mv udims-successp warnings new-udims)
             (vl-packeddimensionlist-exprsize x.udims ss ctx warnings))
            (new-x (change-vl-coretype x :pdims new-pdims :udims new-udims)))
         (mv (and pdims-successp udims-successp) warnings new-x)))
      (:vl-struct
       (b* (((mv members-successp warnings new-members)
             (vl-structmemberlist-exprsize x.members ss ctx warnings))
            ((mv pdims-successp warnings new-pdims)
             (vl-packeddimensionlist-exprsize x.pdims ss ctx warnings))
            ((mv udims-successp warnings new-udims)
             (vl-packeddimensionlist-exprsize x.udims ss ctx warnings))
            (successp (and members-successp (and pdims-successp udims-successp)))
            (new-x    (change-vl-struct x :members new-members :pdims new-pdims :udims new-udims)))
         (mv successp warnings new-x)))
      (:vl-union
       (b* (((mv members-successp warnings new-members)
             (vl-structmemberlist-exprsize x.members ss ctx warnings))
            ((mv pdims-successp warnings new-pdims)
             (vl-packeddimensionlist-exprsize x.pdims ss ctx warnings))
            ((mv udims-successp warnings new-udims)
             (vl-packeddimensionlist-exprsize x.udims ss ctx warnings))
            (successp (and members-successp (and pdims-successp udims-successp)))
            (new-x    (change-vl-union x :members new-members :pdims new-pdims :udims new-udims)))
         (mv successp warnings new-x)))
      (:vl-enum
       (b* (((mv basetype-successp warnings new-basetype)
             (vl-enumbasetype-exprsize x.basetype ss ctx warnings))
            ((mv items-successp warnings new-items)
             (vl-enumitemlist-exprsize x.items ss ctx warnings))
            ((mv pdims-successp warnings new-pdims)
             (vl-packeddimensionlist-exprsize x.pdims ss ctx warnings))
            ((mv udims-successp warnings new-udims)
             (vl-packeddimensionlist-exprsize x.udims ss ctx warnings))
            (successp (and basetype-successp items-successp (and pdims-successp udims-successp)))
            (new-x    (change-vl-enum x
                                      :basetype new-basetype
                                      :items new-items
                                      :pdims new-pdims :udims new-udims)))
         (mv successp warnings new-x)))
      (:vl-usertype
       (b* (;; NOTE: We used to try to size x.kind, but typically it is an
            ;; identifier that refers to some typedef, which doesn't need to be
            ;; (and won't successfully be) sized.  We think sizes should never
            ;; matter in "type identifier expressions", so it seems safe to
            ;; just skip it.
            ((mv pdims-successp warnings new-pdims)
             (vl-packeddimensionlist-exprsize x.pdims ss ctx warnings))
            ((mv udims-successp warnings new-udims)
             (vl-packeddimensionlist-exprsize x.udims ss ctx warnings))
            (new-x    (change-vl-usertype x :pdims new-pdims :udims new-udims)))
         (mv (and pdims-successp udims-successp) warnings new-x)))))

  (define vl-structmemberlist-exprsize ((x        vl-structmemberlist-p)
                                        (ss vl-scopestack-p)
                                        (ctx     vl-context-p)
                                        (warnings vl-warninglist-p))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-x    vl-structmemberlist-p))
    :measure (vl-structmemberlist-count x)
    (b* (((when (atom x))
          (mv t (ok) nil))
         ((mv car-successp warnings new-car) (vl-structmember-exprsize (car x) ss ctx warnings))
         ((mv cdr-successp warnings new-cdr) (vl-structmemberlist-exprsize (cdr x) ss ctx warnings))
         (successp (and car-successp cdr-successp))
         (new-x    (cons new-car new-cdr)))
      (mv successp warnings new-x)))

  (define vl-structmember-exprsize ((x        vl-structmember-p)
                                    (ss vl-scopestack-p)
                                    (ctx     vl-context-p)
                                    (warnings vl-warninglist-p))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-x    vl-structmember-p))
    :measure (vl-structmember-count x)
    (b* (((vl-structmember x) x)
         ((mv type-successp warnings new-type)
          (vl-datatype-exprsize x.type ss ctx warnings))
         ((mv rhs-successp warnings new-rhs)
          (vl-maybe-expr-size x.rhs ss ctx warnings))
         (successp (and type-successp rhs-successp))
         (new-x    (change-vl-structmember x
                                           :type new-type
                                           :rhs new-rhs)))
      (mv successp warnings new-x)))
  ///
  (verify-guards vl-datatype-exprsize)
  (deffixequiv-mutual vl-datatype-exprsize))

(def-vl-exprsize vl-maybe-datatype
  :body
  (if x
      (vl-datatype-exprsize x ss ctx warnings)
    (mv nil (ok) nil))
  :takes-ctx t)

(def-vl-exprsize vl-gatedelay
  :takes-ctx t
  :body (b* (((vl-gatedelay x) x)
             ((mv rise-okp warnings rise-prime)
              (vl-expr-size nil x.rise ss ctx warnings))
             ((mv fall-okp warnings fall-prime)
              (vl-expr-size nil x.fall ss ctx warnings))
             ((mv high-okp warnings high-prime)
              (vl-maybe-expr-size x.high ss ctx warnings))
             (successp (and rise-okp fall-okp high-okp))
             (x-prime  (change-vl-gatedelay x
                                            :rise rise-prime
                                            :fall fall-prime
                                            :high high-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize vl-maybe-gatedelay
  :takes-ctx t
  :body (if x
            (vl-gatedelay-exprsize x ss ctx warnings)
          (mv t warnings x)))

; Truncation warnings are really, really good to have, and have found many
; bugs.  However, if we just issue a truncation warning about everything, we
; find that there are way too many nitpicky warnings and it's hard to go
; through them all.  So, we want to be clever and not warn in certain cases
; that we have seen where the truncation really doesn't matter.  Efficiency is
; of no concern because this is called so infrequently.
;
; Probably the biggest source of spurious truncation warnings is from the use
; of unsized numbers like 0 and 1.  It's a pretty good bet that any truncation
; from 32-bits to some other number of bits is no big deal and is just being
; caused by a unsized number.
;
; At any rate, we now have a notion of expression that are okay to truncate.
; We basically don't want to complain about things like
;
;    assign foo[3:0] = 0;              // 32 bits, but who cares, it fits
;
;    assign foo[3:0] = 5'd7;           // 5 bits, but who cares, it still fits
;
;    assign foo[3:0] = x0 ? 5'h0 :     // each are 5 bits, but who cares, they
;                      x1 ? 5'h1 :     // still fit.
;                      x2 ? 5'h2 :
;                      ...
;                      x14 ? 5'h14 :
;                      5'h15;

(define vl-okay-to-truncate-atom ((width natp)
                                  (x     vl-expr-p))
  :guard (vl-atom-p x)
  ;; Recognize:
  ;;
  ;; (1) atoms that were just ordinary constant integer numbers like 5, but
  ;;     which are not "negative" numbers (i.e., bit 31 should not be set), and
  ;;     whose value is small enough to fit into WIDTH many bits.
  ;;
  ;; (2) atoms that were sized but unsigned constant integers that can be
  ;;     chopped down to width-many bits without changing their value.
  (b* ((width   (lnfix width))
       (guts    (vl-atom->guts x))
       ((unless (vl-fast-constint-p guts))
        nil)
       ((vl-constint guts) guts))
    (or
     ;; Case 1:
     (and guts.wasunsized
          (= guts.origwidth 32)
          (not (logbitp 31 guts.value))
          (< guts.value (ash 1 width)))
     ;; Case 2:
     (and (eq guts.origtype :vl-unsigned)
          (< guts.value (ash 1 width)))))
  ///
  (local (assert!
          ;; Basic test to make sure it seems to be working right.
          (flet ((test (value)
                       (make-vl-atom :guts (make-vl-constint :value value
                                                             :origwidth 32
                                                             :origtype :vl-signed
                                                             :wasunsized t))))
                (and (vl-okay-to-truncate-atom 8 (test 0))
                     (vl-okay-to-truncate-atom 8 (test 255))
                     (not (vl-okay-to-truncate-atom 8 (test 256))))))))

(define vl-okay-to-truncate-expr ((width natp)
                                  (x     vl-expr-p))
  ;; Recognize okay to truncate atoms and nests of (A ? B : C) where all of the
  ;; final branches are okay to truncate atoms.
  :measure (vl-expr-count x)
  (b* (((when (vl-fast-atom-p x))
        (vl-okay-to-truncate-atom width x))
       (op   (vl-nonatom->op x))
       (args (vl-nonatom->args x))
       ((unless (eq op :vl-qmark))
        nil))
    (and (vl-okay-to-truncate-expr width (second args))
         (vl-okay-to-truncate-expr width (third args)))))

(define vl-unsized-atom-p ((x vl-expr-p))
  :guard (vl-atom-p x)
  (b* ((guts (vl-atom->guts x)))
    (or (and (vl-fast-constint-p guts)
             (vl-constint->wasunsized guts))
        (and (vl-fast-weirdint-p guts)
             (vl-weirdint->wasunsized guts)))))

(define vl-some-unsized-atom-p ((x vl-exprlist-p))
  :guard (vl-atomlist-p x)
  (if (atom x)
      nil
    (or (vl-unsized-atom-p (car x))
        (vl-some-unsized-atom-p (cdr x)))))

(define vl-maybe-warn-about-implicit-truncation
  ((lvalue   vl-expr-p)
   (expr     vl-expr-p)
   (ctx     vl-context-p)
   (warnings vl-warninglist-p))
  :returns (new-warnings vl-warninglist-p)
  (b* ((lvalue (vl-expr-fix lvalue))
       (expr   (vl-expr-fix expr))
       (ctx   (vl-context-fix ctx))

       (lw     (vl-expr->finalwidth lvalue))
       (ew     (vl-expr->finalwidth expr))

       ((when (and (natp lw)
                   (vl-okay-to-truncate-expr lw expr)))
        ;; Just ignore it, this is nothing to be worried about
        (ok))

       (probably-minor-p
        ;; We could probably improve this somewhat... if the RHS is 32 bits
        ;; and it at least has some atom that was originally unsized in it,
        ;; it's probably just a truncation because there's a plain number on
        ;; the rhs, and it probably isn't a real problem, so we'll call such
        ;; things minor.  This is something we couldn't check very well when
        ;; we were trying to handle truncation warnings as part of
        ;; assign-trunc, because by then the expressions had already been
        ;; split and the temp wires could hide unsized atoms.
        (and (equal ew 32)
             (vl-some-unsized-atom-p (vl-expr-atoms expr)))))

    (warn :type (if probably-minor-p
                    :vl-warn-truncation-minor
                  :vl-warn-truncation)
          :msg "~a0: implicit truncation from ~x1-bit expression ~
                to ~x2-bit lvalue.~%     ~
                 lhs: ~a3~%     ~
                 rhs: ~a4~%~%"
          :args (list ctx ew lw lvalue expr))))

#||

(trace$
 #!Vl (vl-assign-exprsize
       :entry (list 'vl-assign-exprsize
                    (with-local-ps (vl-pp-assign x)))
       :exit (list 'vl-assign-exprsize
                   (b* (((list & warnings-out res) values))
                     (with-local-ps
                       (vl-print-warnings (butlast warnings-out (len warnings))))
                     res))))

||#
(def-vl-exprsize vl-assign
  :body
  (b* (((vl-assign x) x)
       (ctx x)

       ;; Per Table 6-1 (Section 6; page 68), the left-hand side of the
       ;; assignment should be a net, bit-select, part-select, or
       ;; constant indexed part-select, recursively closed under
       ;; concatenation.  We explicitly check this with vl-expr-lvaluep
       ;; so that we can be sure the sizing algorithm won't do anything
       ;; weird like zero-extend some part of the lhs.
       ((unless (vl-expr-lvaluep x.lvalue))
        (mv nil
            (fatal :type :vl-bad-assignment
                   :msg "~a0: Illegal left-hand side: ~a1."
                   :args (list ctx x.lvalue))
            x))

       ((mv ok lhs-prime rhs-prime warnings)
        (vl-assigncontext-size x.lvalue x.expr ss ctx warnings))

       ((unless ok) (mv nil warnings x))

       (lhs-size (vl-expr->finalwidth lhs-prime))

       (warnings
        ;; By vl-expr->finalwidth-of-vl-expr-size-when-lhs-size, we know
        ;; that rhs-prime is at least as wide as lhs-size.  But it can be
        ;; wider, and in such cases we may wish to warn about truncation.
        (if (and (posp (vl-expr->finalwidth rhs-prime))
                 (< lhs-size (vl-expr->finalwidth rhs-prime)))
            (vl-maybe-warn-about-implicit-truncation lhs-prime rhs-prime
                                                     x warnings)
          warnings))

       ((mv delay-successp warnings delay-prime)
        (vl-maybe-gatedelay-exprsize x.delay ss ctx warnings))

       ((unless delay-successp)
        (mv nil warnings x))

       (x-prime
        (change-vl-assign x
                          :lvalue lhs-prime
                          :expr rhs-prime
                          :delay delay-prime)))
    (mv t warnings x-prime)))

(def-vl-exprsize-list vl-assignlist :element vl-assign)


(define vl-port-unpacked-datatype ((x vl-regularport-p)
                                   (ss vl-scopestack-p))
  :prepwork ((local (defthm vl-index-find-type-when-not-warning
                      (implies (not (mv-nth 0 (vl-index-find-type x ss ctx)))
                               (mv-nth 1 (vl-index-find-type x ss ctx)))
                      :hints (("goal" :use return-type-of-vl-index-find-type.type
                               :in-theory (disable return-type-of-vl-index-find-type.type)))))
             (local (defthm vl-partselect-expr-type-when-not-warning
                      (implies (not (mv-nth 0 (vl-partselect-expr-type x ss ctx)))
                               (mv-nth 1 (vl-partselect-expr-type x ss ctx)))
                      :hints (("goal" :use return-type-of-vl-partselect-expr-type.type
                               :in-theory (disable return-type-of-vl-partselect-expr-type.type))))))

  :returns (type (iff (vl-datatype-p type) type))
  (b* (((vl-regularport x))
       ((unless x.expr) nil))
    (vl-expr-case x.expr
      :atom (b* (((mv warn type) (vl-index-find-type x.expr ss (vl-regularport-fix x))))
              (and (not warn) type))
      :nonatom
      (case x.expr.op
        ((:vl-bitselect :vl-index)
         (b* (((mv warn type) (vl-index-find-type x.expr ss (vl-regularport-fix x))))
           (and (not warn) type)))
        ((:vl-select-colon
          :vl-select-pluscolon
          :vl-select-minuscolon
          :vl-partselect-colon
          :vl-partselect-pluscolon
          :vl-partselect-minuscolon)
         (b* (((mv warn type) (vl-partselect-expr-type x.expr ss (vl-context x))))
           (and (not warn) type)))
        (otherwise nil)))))

(def-vl-exprsize vl-plainarg
  :takes-ctx t
  :extra-formals ((port (or (vl-port-p port)
                            (not port)))
                  (submod-ss vl-scopestack-p))

  :long "<h3>Additional Notes</h3>

<p>Minor note: We don't attempt to size blanks.  If there is no expression, it
remains as a blank.</p>

<p>Expressions in argument lists don't have a left-hand side.  They do need to
ultimately agree with the target port, but I am feeling pretty confident that
the port's width does <b>not</b> play a role in sizing the expression.  A good
reason for this is that, if you go and read xf-replicate-insts, and look at the
rules for splitting up instance arrays, it seems like there is more than one
possibility for the context width in this case, namely @('FW') or @('N * FW'),
where @('FW') is the width of the formal and @('N') is the size of the array,
so it doesn't seem like the port's width could in any sensible way used to size
the expression.</p>"

  ;; BOZO Port connections are an assignment-like context, so we should get the
  ;; type of the port so that we can correctly deal with assignment patterns.

  :body (b* (((vl-plainarg x) x)
             ((unless x.expr)
              (mv t warnings x))
             (port (and port (vl-port-fix port)))
             ((when (eq (tag port) :vl-interfaceport))
              ;; check the interface...
              (b* (((vl-interfaceport port))
                   ((when port.udims)
                    (mv nil
                        (fatal :type :vl-bad-interface-port
                               :msg "~a0: Interface port with udims: ~a1"
                               :args (list (vl-context-fix ctx) port))
                        x))
                   ((unless (vl-idexpr-p x.expr))
                    (mv nil
                        (fatal :type :vl-bad-interface-port
                               :msg "~a0: Non-ID expr ~a1 connected to interface port ~a2"
                               :args (list (vl-context-fix ctx) x.expr port))
                        x))
                   (name (vl-idexpr->name x.expr))
                   (item (vl-scopestack-find-item name ss))
                   ((unless (and item
                                 (or (eq (tag item) :vl-modinst)
                                     (eq (tag item) :vl-interfaceport))))
                    (mv nil
                        (fatal :type :vl-bad-interface-port
                               :msg "~a0: Non-interface ~a1 connected to interface port ~a2"
                               :args (list (vl-context-fix ctx) x.expr port))
                        x))
                   (interfacetype (if (eq (tag item) :vl-modinst)
                                      (vl-modinst->modname item)
                                    (vl-interfaceport->ifname item)))
                   ((unless (equal interfacetype port.ifname))
                    (mv nil
                        (fatal :type :vl-bad-interface-port
                               :msg "~a0: Incompatible interface type for port ~a1; ~
                                     expected ~a2 but found ~a3."
                               :args (list (vl-context-fix ctx) port
                                           port.ifname interfacetype))
                        x)))
              (mv t warnings x)))
             (port-type (and port (vl-port-unpacked-datatype port submod-ss)))
             ((unless port-type)
              (b* (((mv successp warnings expr-prime)
                    (vl-expr-size nil x.expr ss ctx warnings))
                   (x-prime
                    (change-vl-plainarg x :expr expr-prime)))
                (mv successp warnings x-prime)))
             ((mv ok expr-prime warnings)
              (vl-expr-size-assigncontext
               port-type x.expr nil ss ctx warnings))
             ((mv ok warnings expr-prime)
              (if ok
                  (vl-expr-size nil expr-prime ss ctx warnings)
                (mv nil warnings expr-prime)))
             (x-prime (change-vl-plainarg x :expr expr-prime)))
          (mv ok warnings x-prime)))

(define vl-plainarglist-exprsize ((x vl-plainarglist-p)
                                  (ss vl-scopestack-p)
                                  (ctx vl-context-p)
                                  (ports vl-portlist-p)
                                  (submod-ss vl-scopestack-p)
                                  (warnings vl-warninglist-p))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (new-x    vl-plainarglist-p))
  :parents (expression-sizing)
  :short "Compute sizes and types of expressions throughout a @(see vl-plainarglist-p)."
  (b* (((when (atom x))
        (mv t (ok) nil))
       (ports (vl-portlist-fix ports))
       ((mv car-successp warnings car-prime)
        (vl-plainarg-exprsize (car x) ss ctx
                              (and (consp ports) (car ports))
                              submod-ss warnings))
       ((mv cdr-successp warnings cdr-prime)
        (vl-plainarglist-exprsize (cdr x) ss ctx
                                  (and (consp ports) (cdr ports))
                                  submod-ss warnings))
       (successp (and car-successp cdr-successp))
       (x-prime  (cons car-prime cdr-prime)))
    (mv successp warnings x-prime))
  ///
  (defthm true-listp-of-vl-plainarglist-exprsize
    (true-listp (mv-nth 2 (vl-plainarglist-exprsize x ss ctx ports submod-ss warnings)))
    :rule-classes :type-prescription))

(def-vl-exprsize vl-namedarg
  :takes-ctx t
  :long "<p>See also the notes in @(see vl-plainarg-exprsize).</p>"
  :body (b* (((vl-namedarg x) x)
             ((unless x.expr)
              (mv t warnings x))
             ((mv successp warnings expr-prime)
              (vl-expr-size nil x.expr ss ctx warnings))
             (x-prime
              (change-vl-namedarg x :expr expr-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-namedarglist
  :takes-ctx t
  :element vl-namedarg)

(encapsulate nil
  (local (defthm vl-scope-p-when-vl-module-or-interface
           (implies (or (vl-module-p x)
                        (vl-interface-p x))
                    (vl-scope-p x))))
  (def-vl-exprsize vl-arguments
    :takes-ctx t
    :extra-formals ((inst vl-modinst-p))
    :body
    (vl-arguments-case x
      :vl-arguments-named
      (b* (((mv successp warnings args-prime)
            (vl-namedarglist-exprsize x.args ss ctx warnings))
           (x-prime (change-vl-arguments-named x :args args-prime)))
        (mv successp warnings x-prime))
      :vl-arguments-plain
      (b* (((vl-modinst inst))
           ((mv submod submod-ss)
            (vl-scopestack-find-definition/ss inst.modname ss))
           ((mv ports submod-ss)
            (b* (((unless (and submod (or (eq (tag submod) :vl-module)
                                          (eq (tag submod) :vl-interface))))
                  (mv nil ;; no ports to match up
                      submod-ss)) ;; submod-ss irrelevant in that case
                 (submod-ss (vl-scopestack-push submod submod-ss))
                 (ports (if (eq (tag submod) :vl-module)
                            (vl-module->ports submod)
                          (vl-interface->ports submod))))
              (mv ports submod-ss)))
           ((mv successp warnings args-prime)
            (vl-plainarglist-exprsize x.args ss ctx ports submod-ss warnings))
           (x-prime (change-vl-arguments-plain x :args args-prime)))
        (mv successp warnings x-prime)))))


(def-vl-exprsize vl-paramvalue
  ;; BOZO Parameter value assignments/overrides are assignment-like contexts,
  ;; so we should deal with assignment patterns.
  :takes-ctx t
  :body
  (b* ((x (vl-paramvalue-fix x)))
    (vl-paramvalue-case x
      :expr (vl-expr-size nil x ss ctx warnings)
      :datatype (vl-datatype-exprsize x ss ctx warnings))))

(def-vl-exprsize-list vl-paramvaluelist
  :takes-ctx t
  :element vl-paramvalue)

(def-vl-exprsize vl-maybe-paramvalue
  :takes-ctx t
  :body
  (if x
      (vl-paramvalue-exprsize x ss ctx warnings)
    (mv t warnings nil)))

(def-vl-exprsize vl-namedparamvalue
  :takes-ctx t
  :body
  (b* (((vl-namedparamvalue x) x)
       ((mv successp warnings value)
        (vl-maybe-paramvalue-exprsize x.value ss ctx warnings))
       (x-prime (change-vl-namedparamvalue x :value value)))
    (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-namedparamvaluelist
  :takes-ctx t
  :element vl-namedparamvalue)

(def-vl-exprsize vl-paramargs
  :takes-ctx t
  :body
  (vl-paramargs-case x
    :vl-paramargs-named
    (b* (((mv successp warnings args)
          (vl-namedparamvaluelist-exprsize x.args ss ctx warnings))
         (x-prime (change-vl-paramargs-named x :args args)))
      (mv successp warnings x-prime))
    :vl-paramargs-plain
    (b* (((mv successp warnings args)
          (vl-paramvaluelist-exprsize x.args ss ctx warnings))
         (x-prime (change-vl-paramargs-plain x :args args)))
      (mv successp warnings x-prime))))


(def-vl-exprsize vl-modinst
  :body
  (b* (((vl-modinst x) x)
       (ctx x)
       ((mv successp1 warnings portargs-prime)
        (vl-arguments-exprsize x.portargs ss ctx x warnings))
       ((mv successp2 warnings paramargs-prime)
        (vl-paramargs-exprsize x.paramargs ss ctx warnings))
       ((mv successp3 warnings range-prime)
        (vl-maybe-range-exprsize x.range ss ctx warnings))
       ((mv successp4 warnings delay-prime)
        (vl-maybe-gatedelay-exprsize x.delay ss ctx warnings))
       (successp
        (and successp1 successp2 successp3 successp4))
       (x-prime
        (change-vl-modinst x
                           :portargs portargs-prime
                           :paramargs paramargs-prime
                           :range range-prime
                           :delay delay-prime)))
      (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-modinstlist :element vl-modinst)


(def-vl-exprsize vl-gateinst
  :body
  (b* (((vl-gateinst x) x)
       (ctx x)
       ((mv successp1 warnings args-prime)
        (vl-plainarglist-exprsize x.args ss ctx
                                  nil ;; empty portlist --> assignment patterns aren't allowed
                                  ss ;; empty portlist means submod scopestack is irrelevant
                                  warnings))
       ((mv successp2 warnings range-prime)
        (vl-maybe-range-exprsize x.range ss ctx warnings))
       ((mv successp3 warnings delay-prime)
        (vl-maybe-gatedelay-exprsize x.delay ss ctx warnings))
       (successp
        (and successp1 successp2 successp3))
       (x-prime
        (change-vl-gateinst x
                            :args args-prime
                            :range range-prime
                            :delay delay-prime)))
      (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-gateinstlist :element vl-gateinst)



(def-vl-exprsize vl-delaycontrol
  :takes-ctx t
  :body (b* (((vl-delaycontrol x) x)
             ((mv successp warnings value-prime)
              (vl-expr-size nil x.value ss ctx warnings))
             (x-prime
              (change-vl-delaycontrol x :value value-prime)))
            (mv successp warnings x-prime)))

(def-vl-exprsize vl-evatom
  :takes-ctx t
  :body (b* (((vl-evatom x) x)
             ((mv successp warnings expr-prime)
              (vl-expr-size nil x.expr ss ctx warnings))
             (x-prime
              (change-vl-evatom x :expr expr-prime)))
            (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-evatomlist
  :takes-ctx t
  :element vl-evatom)

(def-vl-exprsize vl-eventcontrol
  :takes-ctx t
  :body (b* (((vl-eventcontrol x) x)
             ((mv successp warnings atoms-prime)
              (vl-evatomlist-exprsize x.atoms ss ctx warnings))
             (x-prime
              (change-vl-eventcontrol x :atoms atoms-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize vl-repeateventcontrol
  :takes-ctx t
  :body (b* (((vl-repeateventcontrol x) x)
             ((mv successp1 warnings expr-prime)
              (vl-expr-size nil x.expr ss ctx warnings))
             ((mv successp2 warnings ctrl-prime)
              (vl-eventcontrol-exprsize x.ctrl ss ctx warnings))
             (successp
              (and successp1 successp2))
             (x-prime
              (change-vl-repeateventcontrol x
                                            :expr expr-prime
                                            :ctrl ctrl-prime)))
            (mv successp warnings x-prime)))

(def-vl-exprsize vl-delayoreventcontrol
  :takes-ctx t
  :body (case (tag x)
          (:vl-delaycontrol (vl-delaycontrol-exprsize x ss ctx warnings))
          (:vl-eventcontrol (vl-eventcontrol-exprsize x ss ctx warnings))
          (otherwise        (vl-repeateventcontrol-exprsize x ss ctx warnings))))

(def-vl-exprsize vl-maybe-delayoreventcontrol
  :takes-ctx t
  :body (if x
            (vl-delayoreventcontrol-exprsize x ss ctx warnings)
          (mv t warnings nil)))

(defthm vl-maybe-delayoreventcontrol-exprsize-under-iff
  (iff (mv-nth 2 (vl-maybe-delayoreventcontrol-exprsize x ss ctx warnings))
       x)
  :hints(("Goal" :in-theory (enable vl-maybe-delayoreventcontrol-exprsize))))

(def-vl-exprsize vl-vardecl
  ;; BOZO -- this probably isn't right.  We probably need to consider the size
  ;; of the variable as a context and pass that size in when sizing the initial value!!
  :body
  (b* (((vl-vardecl x) x)
       (ctx x)
       ((mv successp1 warnings type-prime)    (vl-datatype-exprsize x.type ss ctx warnings))
       ((mv successp3 warnings initval-prime) (vl-maybe-expr-size x.initval ss ctx warnings))
       ((mv successp4 warnings delay-prime)   (vl-maybe-gatedelay-exprsize x.delay ss ctx warnings))
       (successp (and successp1 successp3 successp4))
       (x-prime (change-vl-vardecl x
                                   :type    type-prime
                                   :initval initval-prime
                                   :delay   delay-prime)))
    (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-vardecllist :element vl-vardecl)


(def-vl-exprsize vl-paramdecl
  :body
  (b* (((vl-paramdecl x) (vl-paramdecl-fix x))
       (ctx x)
       ((mv ok warnings type)
        (vl-paramtype-case x.type
          :vl-implicitvalueparam
          (b* (((mv ok1 warnings range) (vl-maybe-range-exprsize x.type.range ss ctx warnings))
               ((mv ok2 warnings default) (vl-maybe-expr-size x.type.default ss ctx warnings)))
            (mv (and ok1 ok2) warnings (change-vl-implicitvalueparam
                                        x.type :range range :default default)))
          :vl-explicitvalueparam
          (b* (((mv ok1 warnings type) (vl-datatype-exprsize x.type.type ss ctx warnings))
               ((mv ok2 warnings default) (vl-maybe-expr-size x.type.default ss ctx warnings)))
            (mv (and ok1 ok2) warnings
                (change-vl-explicitvalueparam
                 x.type :type type :default default)))
          :vl-typeparam
          (b* (((mv ok warnings default) (vl-maybe-datatype-exprsize x.type.default ss ctx warnings)))
            (mv ok warnings (change-vl-typeparam x.type :default default))))))
    (mv ok warnings (change-vl-paramdecl x :type type))))

(def-vl-exprsize-list vl-paramdecllist :element vl-paramdecl)

(defthm vl-vardecllist-exprsize-under-iff
  (iff (mv-nth 2 (vl-vardecllist-exprsize x ss warnings))
       (consp x))
  :hints(("Goal" :in-theory (enable vl-vardecllist-exprsize))))

(defthm vl-paramdecllist-exprsize-under-iff
  (iff (mv-nth 2 (vl-paramdecllist-exprsize x ss warnings))
       (consp x))
  :hints(("Goal" :in-theory (enable vl-paramdecllist-exprsize))))


(defines vl-stmt-exprsize

  (define vl-stmt-exprsize
    ((x        vl-stmt-p)
     (ss vl-scopestack-p)
     (ctx     vl-context-p)
     (warnings vl-warninglist-p))
    :verify-guards nil
    :measure (vl-stmt-count x)
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-x    vl-stmt-p))
    (b* ((x        (vl-stmt-fix x))
         (ctx     (vl-context-fix ctx))
         (warnings (vl-warninglist-fix warnings))

         ((when (vl-atomicstmt-p x))
          (case (vl-stmt-kind x)
            (:vl-nullstmt
             (mv t warnings x))

            (:vl-assignstmt
             (b* (((vl-assignstmt x) x)

                  ;; This is very similar to vl-assign-exprsize.
                  ((unless (vl-expr-lvaluep x.lvalue))
                   (mv nil
                       (fatal :type :vl-bad-assignment
                              :msg "~a0: Illegal left-hand side: ~a1."
                              :args (list ctx x.lvalue))
                       x))

                  ((mv ok lhs-prime rhs-prime warnings)
                   (vl-assigncontext-size x.lvalue x.expr ss ctx warnings))

                  ((unless ok) (mv nil warnings x))

                  (lhs-size (vl-expr->finalwidth lhs-prime))

                  (warnings
                   ;; By vl-expr->finalwidth-of-vl-expr-size-when-lhs-size, we know
                   ;; that rhs-prime is at least as wide as lhs-size.  But it can be
                   ;; wider, and in such cases we may wish to warn about truncation.
                   (if (and (posp (vl-expr->finalwidth rhs-prime))
                            (< lhs-size (vl-expr->finalwidth rhs-prime)))
                       (vl-maybe-warn-about-implicit-truncation lhs-prime rhs-prime
                                                                ctx warnings)
                     warnings))

                  ((mv delay-successp warnings ctrl-prime)
                   (vl-maybe-delayoreventcontrol-exprsize x.ctrl ss ctx warnings))

                  (x-prime (change-vl-assignstmt x
                                                 :lvalue lhs-prime
                                                 :expr rhs-prime
                                                 :ctrl ctrl-prime)))
               (mv delay-successp warnings x-prime)))

            (:vl-deassignstmt
             (b* (((vl-deassignstmt x) x)
                  ((mv successp warnings lvalue-prime) (vl-expr-size nil x.lvalue ss ctx warnings))
                  (x-prime (change-vl-deassignstmt x :lvalue lvalue-prime)))
               (mv successp warnings x-prime)))

            (:vl-enablestmt
             (b* (((vl-enablestmt x) x)
                  ((mv successp1 warnings id-prime) (vl-expr-size nil x.id ss ctx warnings))
                  ((mv successp2 warnings args-prime) (vl-exprlist-size x.args ss ctx warnings))
                  (successp (and successp1 successp2))
                  (x-prime (change-vl-enablestmt x
                                                 :id id-prime
                                                 :args args-prime)))
               (mv successp warnings x-prime)))

            (:vl-disablestmt
             (b* (((vl-disablestmt x) x)
                  ((mv successp warnings id-prime) (vl-expr-size nil x.id ss ctx warnings))
                  (x-prime (change-vl-disablestmt x :id id-prime)))
               (mv successp warnings x-prime)))
            (:vl-returnstmt
             (b* (((vl-returnstmt x) x)
                  ((mv successp warnings val-prime)
                   (if x.val
                       (vl-expr-size nil x.val ss ctx warnings)
                     (mv t warnings x.val))))
               (mv successp warnings (change-vl-returnstmt x :val val-prime))))

            (otherwise
             (b* (((vl-eventtriggerstmt x) x)
                  ((mv successp warnings id-prime) (vl-expr-size nil x.id ss ctx warnings))
                  (x-prime (change-vl-eventtriggerstmt x :id id-prime)))
               (mv successp warnings x-prime)))))

         (ss (vl-stmt-case x
               :vl-blockstmt (vl-scopestack-push (vl-blockstmt->blockscope x) ss)
               :vl-forstmt (vl-scopestack-push (vl-forstmt->blockscope x) ss)
               :otherwise ss))
         (x.exprs (vl-compoundstmt->exprs x))
         (x.stmts (vl-compoundstmt->stmts x))
         (x.ctrl  (vl-compoundstmt->ctrl x))
         (x.vardecls (vl-compoundstmt->vardecls x))
         (x.paramdecls (vl-compoundstmt->paramdecls x))
         ((mv successp1 warnings exprs-prime) (vl-exprlist-size x.exprs ss ctx warnings))
         ((mv successp2 warnings stmts-prime) (vl-stmtlist-exprsize x.stmts ss ctx warnings))
         ((mv successp3 warnings ctrl-prime)  (vl-maybe-delayoreventcontrol-exprsize x.ctrl ss ctx warnings))
         ((mv successp4 warnings vardecls-prime) (vl-vardecllist-exprsize x.vardecls ss warnings))
         ((mv successp5 warnings paramdecls-prime) (vl-paramdecllist-exprsize x.paramdecls ss warnings))
         (successp (and successp1 successp2 successp3 successp4 successp5))
         (x-prime
          (change-vl-compoundstmt x
                                  :exprs exprs-prime
                                  :stmts stmts-prime
                                  :ctrl ctrl-prime
                                  :vardecls vardecls-prime
                                  :paramdecls paramdecls-prime)))
      (mv successp warnings x-prime)))

  (define vl-stmtlist-exprsize
    ((x        vl-stmtlist-p)
     (ss vl-scopestack-p)
     (ctx     vl-context-p)
     (warnings vl-warninglist-p))
    :measure (vl-stmtlist-count x)
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-x    (and (vl-stmtlist-p new-x)
                                (equal (len new-x) (len x)))))
    (b* (((when (atom x))
          (mv t (ok) nil))
         ((mv car-successp warnings car-prime) (vl-stmt-exprsize (car x) ss ctx warnings))
         ((mv cdr-successp warnings cdr-prime) (vl-stmtlist-exprsize (cdr x) ss ctx warnings))
         (successp (and car-successp cdr-successp))
         (x-prime  (cons car-prime cdr-prime)))
      (mv successp warnings x-prime)))

  ///
  (verify-guards vl-stmt-exprsize)
  (deffixequiv-mutual vl-stmt-exprsize))

(def-vl-exprsize vl-always
  :body (b* (((vl-always x) x)
             (ctx x)
             ((mv successp warnings stmt-prime)
              (vl-stmt-exprsize x.stmt ss ctx warnings))
             (x-prime (change-vl-always x :stmt stmt-prime)))
            (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-alwayslist :element vl-always)

(def-vl-exprsize vl-initial
  :body (b* (((vl-initial x) x)
             (ctx x)
             ((mv successp warnings stmt-prime)
              (vl-stmt-exprsize x.stmt ss ctx warnings))
             (x-prime (change-vl-initial x :stmt stmt-prime)))
            (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-initiallist :element vl-initial)

(def-vl-exprsize vl-interfaceport
  :body (b* (((vl-interfaceport x))
             ((mv udims-successp warnings new-udims)
              (vl-packeddimensionlist-exprsize x.udims ss (vl-context x) warnings)))
          (mv udims-successp warnings
              (change-vl-interfaceport x :udims new-udims))))

(def-vl-exprsize vl-regularport
  :body (b* (((vl-regularport x))
             ((mv expr-successp warnings new-expr)
              (vl-maybe-expr-size x.expr ss (vl-context x) warnings)))
          (mv expr-successp warnings
              (change-vl-regularport x :expr new-expr))))

(def-vl-exprsize vl-port
  :body (b* ((x (vl-port-fix x)))
          (if (eq (tag x) :vl-interfaceport)
              (vl-interfaceport-exprsize x ss warnings)
            (vl-regularport-exprsize x ss warnings))))

(def-vl-exprsize-list vl-portlist :element vl-port)


; It doesn't necessarily make a lot of sense to size the expressions in
; declarations, but on the other hand it doesn't seem like it's a bad thing to
; do.

(def-vl-exprsize vl-portdecl
  :body (b* (((vl-portdecl x) x)
             (ctx (vl-context x))
             ((mv successp warnings type-prime)
              (vl-datatype-exprsize x.type ss ctx warnings))
             (x-prime (change-vl-portdecl x :type type-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-portdecllist :element vl-portdecl)

(def-vl-exprsize vl-fundecl
  :body
  (b* (((vl-fundecl x) x)
       ((mv ok1 warnings portdecls) (vl-portdecllist-exprsize x.portdecls ss warnings))
       ((mv ok2 warnings rettype)   (vl-datatype-exprsize x.rettype ss x warnings))
       (ss (vl-scopestack-push (vl-fundecl->blockscope x) ss))
       ((mv ok3 warnings vardecls)
        (vl-vardecllist-exprsize x.vardecls ss warnings))
       ((mv ok4 warnings paramdecls)
        (vl-paramdecllist-exprsize x.paramdecls ss warnings))
       ((mv ok5 warnings body) (vl-stmt-exprsize x.body ss x warnings)))
    (mv (and ok1 ok2 ok3 ok4 ok5) warnings
        (change-vl-fundecl x
                           :portdecls portdecls
                           :rettype rettype
                           :vardecls vardecls
                           :paramdecls paramdecls
                           :body body))))

(def-vl-exprsize-list vl-fundecllist :element vl-fundecl)

;; BOZO should size task declarations too


(def-genblob-transform vl-genblob-exprsize ((ss vl-scopestack-p)
                                            (warnings vl-warninglist-p))
  :returns ((warnings vl-warninglist-p))
  ;; :verify-guards nil
  (b* (((vl-genblob x) x)
       (ss (vl-scopestack-push (vl-genblob-fix x) ss))

       ((mv & warnings assigns)    (vl-assignlist-exprsize    x.assigns    ss warnings))
       ((mv & warnings modinsts)   (vl-modinstlist-exprsize   x.modinsts   ss warnings))
       ((mv & warnings gateinsts)  (vl-gateinstlist-exprsize  x.gateinsts  ss warnings))
       ((mv & warnings alwayses)   (vl-alwayslist-exprsize    x.alwayses   ss warnings))
       ((mv & warnings initials)   (vl-initiallist-exprsize   x.initials   ss warnings))
       ((mv & warnings portdecls)  (vl-portdecllist-exprsize  x.portdecls  ss warnings))
       ((mv & warnings vardecls)   (vl-vardecllist-exprsize   x.vardecls   ss warnings))
       ((mv & warnings paramdecls) (vl-paramdecllist-exprsize x.paramdecls ss warnings))
       ((mv warnings generates)    (vl-generates-exprsize     x.generates  ss warnings))
       ((mv & warnings ports)      (vl-portlist-exprsize      x.ports      ss warnings))
       ((mv & warnings fundecls)   (vl-fundecllist-exprsize   x.fundecls   ss warnings)))

    (mv warnings
        (change-vl-genblob
         x
         :ports ports
         :assigns assigns
         :modinsts modinsts
         :gateinsts gateinsts
         :alwayses alwayses
         :initials initials
         :portdecls portdecls
         :vardecls vardecls
         :paramdecls paramdecls
         :generates generates
         :fundecls fundecls)))
  :apply-to-generates vl-generates-exprsize)

(define vl-module-exprsize ((x vl-module-p)
                            (ss vl-scopestack-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x) x)
       (genblob (vl-module->genblob x))
       ((mv warnings new-genblob) (vl-genblob-exprsize genblob ss x.warnings))
       (x-warn (change-vl-module x :warnings warnings)))
    (vl-genblob->module new-genblob x-warn)))


(defprojection vl-modulelist-exprsize ((x vl-modulelist-p) (ss vl-scopestack-p))
  :parents (expression-sizing)
  :returns (new-x vl-modulelist-p)
  (vl-module-exprsize x ss))

(define vl-design-exprsize
  :parents (expression-sizing)
  :short "Top-level @(see expression-sizing) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (ss (vl-scopestack-init x))
       (mods (vl-modulelist-exprsize x.mods ss))
       (warnings x.warnings)
       ((mv ?ok warnings fundecls)   (vl-fundecllist-exprsize   x.fundecls   ss warnings))
       ((mv ?ok warnings paramdecls) (vl-paramdecllist-exprsize x.paramdecls ss warnings))
       ((mv ?ok warnings vardecls)   (vl-vardecllist-exprsize   x.vardecls   ss warnings))
       ;; BOZO packages, interfaces, ...
       )
    (vl-scopestacks-free)
    (change-vl-design x
                      :mods       mods
                      :fundecls   fundecls
                      :warnings   warnings
                      :paramdecls paramdecls
                      :vardecls   vardecls)))

