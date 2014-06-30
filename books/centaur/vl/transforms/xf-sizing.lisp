; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "xf-expr-size")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

; -----------------------------------------------------------------------------
;
;                    SIZING EXPRESSIONS THROUGHOUT A MODULE
;
; -----------------------------------------------------------------------------

(defmacro def-vl-exprsize (name &key fn body takes-elem (long '""))
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (fn   (or fn (mksym name '-exprsize)))
       (fix  (mksym name '-fix))
       (type (mksym name '-p)))
    `(define ,fn ((x      ,type)
                  (mod    vl-module-p)
                  (ialist (equal ialist (vl-moditem-alist mod)))
                  ,@(and takes-elem '((elem vl-modelement-p)))
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

(defmacro def-vl-exprsize-list (name &key element takes-elem)
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (fn      (mksym name '-exprsize))
       (elem-fn (mksym element '-exprsize))
       (type    (mksym name '-p))
       (formals (append '(x mod ialist)
                        (if takes-elem '(elem) nil)
                        '(warnings))))
    `(define ,fn ((x      ,type)
                  (mod    vl-module-p)
                  (ialist (equal ialist (vl-moditem-alist mod)))
                  ,@(and takes-elem '((elem vl-modelement-p)))
                  (warnings vl-warninglist-p))
       :returns (mv (successp booleanp :rule-classes :type-prescription)
                    (warnings vl-warninglist-p)
                    (new-x    ,type))
       :parents (expression-sizing)
       :short ,(cat "Compute sizes and types of expressions throughout a @(see " (symbol-name type) ").")
       (b* (((when (atom x))
             (mv t (ok) nil))
            ((mv car-successp warnings car-prime) (,elem-fn . ,(subst '(car x) 'x formals)))
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
  :takes-elem t
  :body (if x
            (vl-expr-size nil x mod ialist elem warnings)
          (mv t warnings x)))

(def-vl-exprsize vl-range
  :takes-elem t
  :body (b* (((vl-range x) x)
             ((mv msb-successp warnings msb-prime)
              (vl-expr-size nil x.msb mod ialist elem warnings))
             ((mv lsb-successp warnings lsb-prime)
              (vl-expr-size nil x.lsb mod ialist elem warnings))
             (successp (and msb-successp lsb-successp))
             (x-prime  (change-vl-range x
                                        :msb msb-prime
                                        :lsb lsb-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize vl-maybe-range
  :takes-elem t
  :body (if x
            (vl-range-exprsize x mod ialist elem warnings)
          (mv t warnings x)))

(def-vl-exprsize-list vl-rangelist
  :takes-elem t
  :element vl-range)

(def-vl-exprsize vl-packeddimension
  :takes-elem t
  :body
  (b* ((x (vl-packeddimension-fix x)))
    (if (eq x :vl-unsized-dimension)
        (mv t warnings x)
      (vl-range-exprsize x mod ialist elem warnings))))

(def-vl-exprsize vl-maybe-packeddimension
  :takes-elem t
  :body
  (if x
      (vl-packeddimension-exprsize x mod ialist elem warnings)
    (mv t warnings x)))

(def-vl-exprsize-list vl-packeddimensionlist
  :takes-elem t
  :element vl-packeddimension)

(def-vl-exprsize vl-enumbasetype
  :takes-elem t
  :body (b* (((vl-enumbasetype x) x)
             ((mv successp warnings dim)
              (vl-maybe-packeddimension-exprsize x.dim mod ialist elem warnings)))
          (mv successp warnings (change-vl-enumbasetype x :dim dim))))

(def-vl-exprsize vl-enumitem
  :takes-elem t
  :body
  (b* (((vl-enumitem x) x)
       ((mv range-successp warnings new-range)
        (vl-maybe-range-exprsize x.range mod ialist elem warnings))
       ((mv value-successp warnings new-value)
        (vl-maybe-expr-size x.value mod ialist elem warnings))
       (successp (and range-successp value-successp))
       (new-x    (change-vl-enumitem x
                                     :range new-range
                                     :value new-value)))
    (mv successp warnings new-x)))

(def-vl-exprsize-list vl-enumitemlist
  :takes-elem t
  :element vl-enumitem)


(defines vl-datatype-exprsize
  :verify-guards nil

  (define vl-datatype-exprsize ((x        vl-datatype-p)
                                (mod      vl-module-p)
                                (ialist   (equal ialist (vl-moditem-alist mod)))
                                (elem     vl-modelement-p)
                                (warnings vl-warninglist-p))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-x    vl-datatype-p))
    :measure (vl-datatype-count x)
    (vl-datatype-case x
      (:vl-coretype
       (b* (((mv dims-successp warnings new-dims)
             (vl-packeddimensionlist-exprsize x.dims mod ialist elem warnings))
            (new-x (change-vl-coretype x :dims new-dims)))
         (mv dims-successp warnings new-x)))
      (:vl-struct
       (b* (((mv members-successp warnings new-members)
             (vl-structmemberlist-exprsize x.members mod ialist elem warnings))
            ((mv dims-successp warnings new-dims)
             (vl-packeddimensionlist-exprsize x.dims mod ialist elem warnings))
            (successp (and members-successp dims-successp))
            (new-x    (change-vl-struct x :members new-members :dims new-dims)))
         (mv successp warnings new-x)))
      (:vl-union
       (b* (((mv members-successp warnings new-members)
             (vl-structmemberlist-exprsize x.members mod ialist elem warnings))
            ((mv dims-successp warnings new-dims)
             (vl-packeddimensionlist-exprsize x.dims mod ialist elem warnings))
            (successp (and members-successp dims-successp))
            (new-x    (change-vl-union x :members new-members :dims new-dims)))
         (mv successp warnings new-x)))
      (:vl-enum
       (b* (((mv basetype-successp warnings new-basetype)
             (vl-enumbasetype-exprsize x.basetype mod ialist elem warnings))
            ((mv items-successp warnings new-items)
             (vl-enumitemlist-exprsize x.items mod ialist elem warnings))
            ((mv dims-successp warnings new-dims)
             (vl-packeddimensionlist-exprsize x.dims mod ialist elem warnings))
            (successp (and basetype-successp items-successp dims-successp))
            (new-x    (change-vl-enum x
                                      :basetype new-basetype
                                      :items new-items
                                      :dims new-dims)))
         (mv successp warnings new-x)))
      (:vl-usertype
       (b* (((mv kind-successp warnings new-kind)
             (vl-expr-size nil x.kind mod ialist elem warnings))
            ((mv dims-successp warnings new-dims)
             (vl-packeddimensionlist-exprsize x.dims mod ialist elem warnings))
            (successp (and kind-successp dims-successp))
            (new-x    (change-vl-usertype x :kind new-kind :dims new-dims)))
         (mv successp warnings new-x)))))

  (define vl-structmemberlist-exprsize ((x        vl-structmemberlist-p)
                                        (mod      vl-module-p)
                                        (ialist   (equal ialist (vl-moditem-alist mod)))
                                        (elem     vl-modelement-p)
                                        (warnings vl-warninglist-p))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-x    vl-structmemberlist-p))
    :measure (vl-structmemberlist-count x)
    (b* (((when (atom x))
          (mv t (ok) nil))
         ((mv car-successp warnings new-car) (vl-structmember-exprsize (car x) mod ialist elem warnings))
         ((mv cdr-successp warnings new-cdr) (vl-structmemberlist-exprsize (cdr x) mod ialist elem warnings))
         (successp (and car-successp cdr-successp))
         (new-x    (cons new-car new-cdr)))
      (mv successp warnings new-x)))

  (define vl-structmember-exprsize ((x        vl-structmember-p)
                                    (mod      vl-module-p)
                                    (ialist   (equal ialist (vl-moditem-alist mod)))
                                    (elem     vl-modelement-p)
                                    (warnings vl-warninglist-p))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-x    vl-structmember-p))
    :measure (vl-structmember-count x)
    (b* (((vl-structmember x) x)
         ((mv type-successp warnings new-type)
          (vl-datatype-exprsize x.type mod ialist elem warnings))
         ((mv dims-successp warnings new-dims)
          (vl-packeddimensionlist-exprsize x.dims mod ialist elem warnings))
         ((mv rhs-successp warnings new-rhs)
          (vl-maybe-expr-size x.rhs mod ialist elem warnings))
         (successp (and type-successp dims-successp rhs-successp))
         (new-x    (change-vl-structmember x
                                           :type new-type
                                           :dims new-dims
                                           :rhs new-rhs)))
      (mv successp warnings new-x)))
  ///
  (verify-guards vl-datatype-exprsize)
  (deffixequiv-mutual vl-datatype-exprsize))

(def-vl-exprsize vl-gatedelay
  :takes-elem t
  :body (b* (((vl-gatedelay x) x)
             ((mv rise-okp warnings rise-prime)
              (vl-expr-size nil x.rise mod ialist elem warnings))
             ((mv fall-okp warnings fall-prime)
              (vl-expr-size nil x.fall mod ialist elem warnings))
             ((mv high-okp warnings high-prime)
              (vl-maybe-expr-size x.high mod ialist elem warnings))
             (successp (and rise-okp fall-okp high-okp))
             (x-prime  (change-vl-gatedelay x
                                            :rise rise-prime
                                            :fall fall-prime
                                            :high high-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize vl-maybe-gatedelay
  :takes-elem t
  :body (if x
            (vl-gatedelay-exprsize x mod ialist elem warnings)
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
   (elem     vl-modelement-p)
   (warnings vl-warninglist-p))
  :returns (new-warnings vl-warninglist-p)
  (b* ((lvalue (vl-expr-fix lvalue))
       (expr   (vl-expr-fix expr))
       (elem   (vl-modelement-fix elem))

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
          :args (list elem ew lw lvalue expr))))

(def-vl-exprsize vl-assign
  :body
  (b* (((vl-assign x) x)
       (elem x)

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
                   :args (list elem x.lvalue))
            x))

       ((mv lhs-successp warnings lhs-prime)
        (vl-expr-size nil x.lvalue mod ialist elem warnings))
       ((unless lhs-successp)
        (mv nil warnings x))

       (lhs-size (vl-expr->finalwidth lhs-prime))
       ((unless (posp lhs-size))
        (mv nil
            (fatal :type :vl-bad-assignment
                   :msg "~a0: The size of the left-hand side ~a1 was not ~
                          a positive number?"
                   :args (list elem x.lvalue))
            x))

       ((mv rhs-successp warnings rhs-prime)
        (vl-expr-size lhs-size x.expr mod ialist elem warnings))

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
        (vl-maybe-gatedelay-exprsize x.delay mod ialist elem warnings))

       ((unless (and rhs-successp delay-successp))
        (mv nil warnings x))

       (x-prime
        (change-vl-assign x
                          :lvalue lhs-prime
                          :expr rhs-prime
                          :delay delay-prime)))
    (mv t warnings x-prime)))

(def-vl-exprsize-list vl-assignlist :element vl-assign)


(def-vl-exprsize vl-plainarg
  :takes-elem t

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

  :body (b* (((vl-plainarg x) x)
             ((unless x.expr)
              (mv t warnings x))
             ((mv successp warnings expr-prime)
              (vl-expr-size nil x.expr mod ialist elem warnings))
             (x-prime
              (change-vl-plainarg x :expr expr-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-plainarglist
  :takes-elem t
  :element vl-plainarg)

(def-vl-exprsize vl-namedarg
  :takes-elem t
  :long "<p>See also the notes in @(see vl-plainarg-exprsize).</p>"
  :body (b* (((vl-namedarg x) x)
             ((unless x.expr)
              (mv t warnings x))
             ((mv successp warnings expr-prime)
              (vl-expr-size nil x.expr mod ialist elem warnings))
             (x-prime
              (change-vl-namedarg x :expr expr-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-namedarglist
  :takes-elem t
  :element vl-namedarg)

(def-vl-exprsize vl-arguments
  :takes-elem t
  :body
  (vl-arguments-case x
    :named
    (b* (((mv successp warnings args-prime)
          (vl-namedarglist-exprsize x.args mod ialist elem warnings))
         (x-prime (change-vl-arguments-named x :args args-prime)))
      (mv successp warnings x-prime))
    :plain
    (b* (((mv successp warnings args-prime)
          (vl-plainarglist-exprsize x.args mod ialist elem warnings))
         (x-prime (change-vl-arguments-plain x :args args-prime)))
      (mv successp warnings x-prime))))

(def-vl-exprsize vl-modinst
  :body
  (b* (((vl-modinst x) x)
       (elem x)
       ((mv successp1 warnings portargs-prime)
        (vl-arguments-exprsize x.portargs mod ialist elem warnings))
       ((mv successp2 warnings paramargs-prime)
        (vl-arguments-exprsize x.paramargs mod ialist elem warnings))
       ((mv successp3 warnings range-prime)
        (vl-maybe-range-exprsize x.range mod ialist elem warnings))
       ((mv successp4 warnings delay-prime)
        (vl-maybe-gatedelay-exprsize x.delay mod ialist elem warnings))
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
       (elem x)
       ((mv successp1 warnings args-prime)
        (vl-plainarglist-exprsize x.args mod ialist elem warnings))
       ((mv successp2 warnings range-prime)
        (vl-maybe-range-exprsize x.range mod ialist elem warnings))
       ((mv successp3 warnings delay-prime)
        (vl-maybe-gatedelay-exprsize x.delay mod ialist elem warnings))
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
  :takes-elem t
  :body (b* (((vl-delaycontrol x) x)
             ((mv successp warnings value-prime)
              (vl-expr-size nil x.value mod ialist elem warnings))
             (x-prime
              (change-vl-delaycontrol x :value value-prime)))
            (mv successp warnings x-prime)))

(def-vl-exprsize vl-evatom
  :takes-elem t
  :body (b* (((vl-evatom x) x)
             ((mv successp warnings expr-prime)
              (vl-expr-size nil x.expr mod ialist elem warnings))
             (x-prime
              (change-vl-evatom x :expr expr-prime)))
            (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-evatomlist
  :takes-elem t
  :element vl-evatom)

(def-vl-exprsize vl-eventcontrol
  :takes-elem t
  :body (b* (((vl-eventcontrol x) x)
             ((mv successp warnings atoms-prime)
              (vl-evatomlist-exprsize x.atoms mod ialist elem warnings))
             (x-prime
              (change-vl-eventcontrol x :atoms atoms-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize vl-repeateventcontrol
  :takes-elem t
  :body (b* (((vl-repeateventcontrol x) x)
             ((mv successp1 warnings expr-prime)
              (vl-expr-size nil x.expr mod ialist elem warnings))
             ((mv successp2 warnings ctrl-prime)
              (vl-eventcontrol-exprsize x.ctrl mod ialist elem warnings))
             (successp
              (and successp1 successp2))
             (x-prime
              (change-vl-repeateventcontrol x
                                            :expr expr-prime
                                            :ctrl ctrl-prime)))
            (mv successp warnings x-prime)))

(def-vl-exprsize vl-delayoreventcontrol
  :takes-elem t
  :body (case (tag x)
          (:vl-delaycontrol (vl-delaycontrol-exprsize x mod ialist elem warnings))
          (:vl-eventcontrol (vl-eventcontrol-exprsize x mod ialist elem warnings))
          (otherwise        (vl-repeateventcontrol-exprsize x mod ialist elem warnings))))

(def-vl-exprsize vl-maybe-delayoreventcontrol
  :takes-elem t
  :body (if x
            (vl-delayoreventcontrol-exprsize x mod ialist elem warnings)
          (mv t warnings nil)))

(defthm vl-maybe-delayoreventcontrol-exprsize-under-iff
  (iff (mv-nth 2 (vl-maybe-delayoreventcontrol-exprsize x mod ialist elem warnings))
       x)
  :hints(("Goal" :in-theory (enable vl-maybe-delayoreventcontrol-exprsize))))

(defines vl-stmt-exprsize

  (define vl-stmt-exprsize
    ((x        vl-stmt-p)
     (mod      vl-module-p)
     (ialist   (equal ialist (vl-moditem-alist mod)))
     (elem     vl-modelement-p)
     (warnings vl-warninglist-p))
    :verify-guards nil
    :measure (vl-stmt-count x)
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-x    vl-stmt-p))
    (b* ((x        (vl-stmt-fix x))
         (elem     (vl-modelement-fix elem))
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
                              :args (list elem x.lvalue))
                       x))

                  ((mv lhs-successp warnings lhs-prime) (vl-expr-size nil x.lvalue mod ialist elem warnings))
                  ((unless lhs-successp)
                   (mv nil warnings x))
                  (lhs-size (vl-expr->finalwidth lhs-prime))
                  ((unless (posp lhs-size))
                   (mv nil
                       (fatal :type :vl-bad-assignment
                              :msg "~a0: The size of the left-hand side ~a1 ~
                                    was not a positive number?"
                              :args (list elem x.lvalue))
                       x))

                  ((mv rhs-successp warnings rhs-prime) (vl-expr-size lhs-size x.expr mod ialist elem warnings))
                  (warnings
                   ;; By vl-expr->finalwidth-of-vl-expr-size-when-lhs-size, we know
                   ;; that rhs-prime is at least as wide as lhs-size.  But it can be
                   ;; wider, and in such cases we may wish to warn about truncation.
                   (if (and (posp (vl-expr->finalwidth rhs-prime))
                            (< lhs-size (vl-expr->finalwidth rhs-prime)))
                       (vl-maybe-warn-about-implicit-truncation lhs-prime rhs-prime
                                                                elem warnings)
                     warnings))

                  ((mv delay-successp warnings ctrl-prime)
                   (vl-maybe-delayoreventcontrol-exprsize x.ctrl mod ialist elem warnings))
                  (successp (and rhs-successp delay-successp))
                  (x-prime (change-vl-assignstmt x
                                                 :lvalue lhs-prime
                                                 :expr rhs-prime
                                                 :ctrl ctrl-prime)))
               (mv successp warnings x-prime)))

            (:vl-deassignstmt
             (b* (((vl-deassignstmt x) x)
                  ((mv successp warnings lvalue-prime) (vl-expr-size nil x.lvalue mod ialist elem warnings))
                  (x-prime (change-vl-deassignstmt x :lvalue lvalue-prime)))
               (mv successp warnings x-prime)))

            (:vl-enablestmt
             (b* (((vl-enablestmt x) x)
                  ((mv successp1 warnings id-prime) (vl-expr-size nil x.id mod ialist elem warnings))
                  ((mv successp2 warnings args-prime) (vl-exprlist-size x.args mod ialist elem warnings))
                  (successp (and successp1 successp2))
                  (x-prime (change-vl-enablestmt x
                                                 :id id-prime
                                                 :args args-prime)))
               (mv successp warnings x-prime)))

            (:vl-disablestmt
             (b* (((vl-disablestmt x) x)
                  ((mv successp warnings id-prime) (vl-expr-size nil x.id mod ialist elem warnings))
                  (x-prime (change-vl-disablestmt x :id id-prime)))
               (mv successp warnings x-prime)))

            (otherwise
             (b* (((vl-eventtriggerstmt x) x)
                  ((mv successp warnings id-prime) (vl-expr-size nil x.id mod ialist elem warnings))
                  (x-prime (change-vl-eventtriggerstmt x :id id-prime)))
               (mv successp warnings x-prime)))))

         (x.exprs (vl-compoundstmt->exprs x))
         (x.stmts (vl-compoundstmt->stmts x))
         (x.ctrl  (vl-compoundstmt->ctrl x))
         (x.decls (vl-compoundstmt->decls x))
         ((mv successp1 warnings exprs-prime) (vl-exprlist-size x.exprs mod ialist elem warnings))
         ((mv successp2 warnings stmts-prime) (vl-stmtlist-exprsize x.stmts mod ialist elem warnings))
         ((mv successp3 warnings ctrl-prime)  (vl-maybe-delayoreventcontrol-exprsize x.ctrl mod ialist elem warnings))
         (warnings
          (if (atom x.decls)
              warnings
            (fatal :type :vl-unsupported-block
                   :msg "~a0: block ~s1 has declarations, which are not supported."
                   :args (list elem (vl-blockstmt->name x)))))
         (successp (and successp1 successp2 successp3))
         (x-prime
          (change-vl-compoundstmt x
                                  :exprs exprs-prime
                                  :stmts stmts-prime
                                  :ctrl ctrl-prime)))
      (mv successp warnings x-prime)))

  (define vl-stmtlist-exprsize
    ((x        vl-stmtlist-p)
     (mod      vl-module-p)
     (ialist   (equal ialist (vl-moditem-alist mod)))
     (elem     vl-modelement-p)
     (warnings vl-warninglist-p))
    :measure (vl-stmtlist-count x)
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-x    (and (vl-stmtlist-p new-x)
                                (equal (len new-x) (len x)))))
    (b* (((when (atom x))
          (mv t (ok) nil))
         ((mv car-successp warnings car-prime) (vl-stmt-exprsize (car x) mod ialist elem warnings))
         ((mv cdr-successp warnings cdr-prime) (vl-stmtlist-exprsize (cdr x) mod ialist elem warnings))
         (successp (and car-successp cdr-successp))
         (x-prime  (cons car-prime cdr-prime)))
      (mv successp warnings x-prime)))

  ///
  (verify-guards vl-stmt-exprsize)
  (deffixequiv-mutual vl-stmt-exprsize))

(def-vl-exprsize vl-always
  :body (b* (((vl-always x) x)
             (elem x)
             ((mv successp warnings stmt-prime)
              (vl-stmt-exprsize x.stmt mod ialist elem warnings))
             (x-prime (change-vl-always x :stmt stmt-prime)))
            (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-alwayslist :element vl-always)


(def-vl-exprsize vl-initial
  :body (b* (((vl-initial x) x)
             (elem x)
             ((mv successp warnings stmt-prime)
              (vl-stmt-exprsize x.stmt mod ialist elem warnings))
             (x-prime (change-vl-initial x :stmt stmt-prime)))
            (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-initiallist :element vl-initial)


(def-vl-exprsize vl-port
  :body (b* (((vl-port x) x)
             (elem x)
             ((mv successp warnings expr-prime)
              (vl-maybe-expr-size x.expr mod ialist elem warnings))
             (x-prime (change-vl-port x :expr expr-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-portlist :element vl-port)


; It doesn't necessarily make a lot of sense to size the expressions in
; declarations, but on the other hand it doesn't seem like it's a bad thing to
; do.

(def-vl-exprsize vl-portdecl
  :body (b* (((vl-portdecl x) x)
             (elem x)
             ((mv successp warnings range-prime)
              (vl-maybe-range-exprsize x.range mod ialist elem warnings))
             (x-prime (change-vl-portdecl x :range range-prime)))
          (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-portdecllist :element vl-portdecl)

(def-vl-exprsize vl-netdecl
  :body
  (b* (((vl-netdecl x) x)
       (elem x)
       ((mv successp1 warnings range-prime)   (vl-maybe-range-exprsize x.range mod ialist elem warnings))
       ((mv successp2 warnings arrdims-prime) (vl-rangelist-exprsize x.arrdims mod ialist elem warnings))
       ((mv successp3 warnings delay-prime)   (vl-maybe-gatedelay-exprsize x.delay mod ialist elem warnings))
       (successp (and successp1 successp2 successp3))
       (x-prime  (change-vl-netdecl x
                                    :range range-prime
                                    :arrdims arrdims-prime
                                    :delay delay-prime)))
    (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-netdecllist :element vl-netdecl)

(def-vl-exprsize vl-vardecl
  ;; BOZO -- this probably isn't right.  We probably need to consider the size
  ;; of the variable as a context and pass that size in!!!
  :body
  (b* (((vl-vardecl x) x)
       (elem x)
       ((mv successp1 warnings vartype-prime) (vl-datatype-exprsize x.vartype mod ialist elem warnings))
       ((mv successp2 warnings dims-prime)    (vl-packeddimensionlist-exprsize x.dims mod ialist elem warnings))
       ((mv successp3 warnings initval-prime) (vl-maybe-expr-size x.initval mod ialist elem warnings))
       (successp (and successp1 successp2 successp3))
       (x-prime (change-vl-vardecl x
                                   :vartype vartype-prime
                                   :dims    dims-prime
                                   :initval initval-prime)))
    (mv successp warnings x-prime)))

(def-vl-exprsize-list vl-vardecllist :element vl-vardecl)


(define vl-module-exprsize ((x vl-module-p))
  :parents (expression-sizing)
  :returns (new-x vl-module-p)
  (b* ((x (vl-module-fix x))
       ((when (vl-module->hands-offp x))
        x)

       ((vl-module x) x)
       (warnings  x.warnings)

       ((when x.paramdecls)
        (change-vl-module x :warnings
                          (fatal :type :vl-programming-error
                                 :msg "Trying to size module ~m0, which has parameters."
                                 :args (list x.name))))

       (ialist (vl-moditem-alist x))

       ((mv & warnings assigns)    (vl-assignlist-exprsize    x.assigns    x ialist warnings))
       ((mv & warnings modinsts)   (vl-modinstlist-exprsize   x.modinsts   x ialist warnings))
       ((mv & warnings gateinsts)  (vl-gateinstlist-exprsize  x.gateinsts  x ialist warnings))
       ((mv & warnings alwayses)   (vl-alwayslist-exprsize    x.alwayses   x ialist warnings))
       ((mv & warnings initials)   (vl-initiallist-exprsize   x.initials   x ialist warnings))
       ((mv & warnings ports)      (vl-portlist-exprsize      x.ports      x ialist warnings))
       ((mv & warnings portdecls)  (vl-portdecllist-exprsize  x.portdecls  x ialist warnings))
       ((mv & warnings netdecls)   (vl-netdecllist-exprsize   x.netdecls   x ialist warnings))
       ((mv & warnings vardecls)   (vl-vardecllist-exprsize   x.vardecls   x ialist warnings))
       )
    (fast-alist-free ialist)
    (change-vl-module x
                      :assigns assigns
                      :modinsts modinsts
                      :gateinsts gateinsts
                      :alwayses alwayses
                      :initials initials
                      :ports ports
                      :portdecls portdecls
                      :netdecls netdecls
                      :vardecls vardecls
                      :warnings warnings)))

(defprojection vl-modulelist-exprsize ((x vl-modulelist-p))
  :parents (expression-sizing)
  :returns (new-x vl-modulelist-p)
  (vl-module-exprsize x))

(define vl-design-exprsize
  :parents (expression-sizing)
  :short "Top-level @(see expression-sizing) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-exprsize x.mods))))

