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
(include-book "../primitives")
(include-book "../mlib/namefactory")
(include-book "../transforms/occform/gen-util")
(local (include-book "../util/arithmetic"))

; BOZO document this transform
;
; Ordering notes.  We need to do this before split.  Otherwise, when we see an
; assignment like:
;
;       assign #1 out = ~in;
;
; We end up creating:
;
;       VL_1_BIT_DELAY_1 mkdel (del, ~in) ;
;
; And the ~in argument to mkdel isn't split up, which can confuse later
; transforms.


(local (defthm crock
         (implies (vl-modulelist-p x)
                  (iff (first x)
                       (consp x)))))


(defund vl-make-m-bit-delay-insts (n basename modname outs ins)
  (declare (xargs :guard (and (natp n)
                              (stringp basename)
                              (stringp modname)
                              (vl-exprlist-p outs)
                              (vl-exprlist-p ins)
                              (same-lengthp outs ins))))
  (if (atom outs)
      nil
    (let ((args (list (make-vl-plainarg :expr (car outs) :dir :vl-output :portname "out")
                      (make-vl-plainarg :expr (car ins)  :dir :vl-input  :portname "in"))))
      (cons (make-vl-modinst :instname  (cat basename (natstr n))
                             :modname   modname
                             :paramargs (vl-arguments nil nil)
                             :portargs  (vl-arguments nil args)
                             :loc       *vl-fakeloc*)
            (vl-make-m-bit-delay-insts (+ n 1) basename modname (cdr outs) (cdr ins))))))

(defthm vl-modinstlist-p-of-vl-make-1-bit-delay-insts
  (implies (and (natp n)
                (stringp basename)
                (stringp modname)
                (vl-exprlist-p outs)
                (vl-exprlist-p ins)
                (same-lengthp outs ins))
           (vl-modinstlist-p (vl-make-m-bit-delay-insts n basename modname outs ins)))
  :hints(("Goal" :in-theory (enable vl-make-m-bit-delay-insts))))



(def-vl-modgen vl-make-1-bit-delay-m (m)
  :short "Generate a one-bit wide, M-tick delay module."
  :long "<p>The basic idea here is:</p>
@({
module VL_1_BIT_DELAY_M (out, in) ;
  output out;
  input in;

  wire [m-2:0] temp;
  VL_1_BIT_DELAY_1 del1     (temp[0],   in);
  VL_1_BIT_DELAY_1 del2     (temp[1],   temp[0]);
  ...
  VL_1_BIT_DELAY_1 del{m-1} (temp[m-2], temp[m-3]);
  VL_1_BIT_DELAY_1 del{m}   (out,       temp[m-2]);
endmodule
})"
  :guard (posp m)
  :body
  (b* (((when (= m 1))
        (list *vl-1-bit-delay-1*))

       (name  (cat "VL_1_BIT_DELAY_" (natstr m)))

       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv in-expr  in-port  in-portdecl  in-netdecl)  (vl-occform-mkport "in" :vl-input 1))

       ((mv temp-expr temp-netdecl) (vl-occform-mkwire "temp" (- m 1)))
       (temp-wires (vl-make-list-of-bitselects temp-expr 0 (- m 2)))

       (outs  (append temp-wires (list out-expr)))
       (ins   (cons in-expr temp-wires))
       (insts (vl-make-m-bit-delay-insts 1 "del"
                                         (vl-module->name *vl-1-bit-delay-1*)
                                         outs ins))

       (mod   (make-vl-module :name      name
                              :origname  name
                              :ports     (list out-port     in-port)
                              :portdecls (list out-portdecl in-portdecl)
                              :netdecls  (list out-netdecl  in-netdecl   temp-netdecl)
                              :modinsts  insts
                              :minloc    *vl-fakeloc*
                              :maxloc    *vl-fakeloc*)))
    (list mod *vl-1-bit-delay-1*)))

;(vl-pps-modulelist (vl-make-1-bit-delay-m 1))
;(vl-pps-modulelist (vl-make-1-bit-delay-m 2))
;(vl-pps-modulelist (vl-make-1-bit-delay-m 3))


(def-vl-modgen vl-make-n-bit-delay-m (n m)
  :short "Generate an N-bit wide, M-tick delay module."
  :guard (and (posp n)
              (posp m))
  :guard-debug t
  :body
  (b* ((base (vl-make-1-bit-delay-m m))

       ((when (= n 1))
        base)

       (name (cat "VL_" (natstr n) "_BIT_DELAY_" (natstr m)))

       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output n))
       ((mv in-expr  in-port  in-portdecl  in-netdecl)  (vl-occform-mkport "in" :vl-input n))

       (in-wires  (vl-make-list-of-bitselects in-expr  0 (- n 1)))
       (out-wires (vl-make-list-of-bitselects out-expr 0 (- n 1)))

       (insts (vl-make-m-bit-delay-insts 0 "bit"
                                         (vl-module->name (car base))
                                         out-wires in-wires))

       (mod (make-vl-module :name      name
                            :origname  name
                            :ports     (list out-port in-port)
                            :portdecls (list out-portdecl in-portdecl)
                            :netdecls  (list out-netdecl in-netdecl)
                            :modinsts  insts
                            :minloc    *vl-fakeloc*
                            :maxloc    *vl-fakeloc*)))
    (cons mod base)))



(defund vl-gatedelay-simple-p (x)
  (declare (xargs :guard (vl-gatedelay-p x)))
  (b* (((vl-gatedelay x) x))
    (and (vl-expr-resolved-p x.rise)
         (vl-expr-resolved-p x.fall)
         (= (vl-resolved->val x.rise) (vl-resolved->val x.fall))
         (or (not x.high)
             (and (vl-expr-resolved-p x.high)
                  (= (vl-resolved->val x.rise) (vl-resolved->val x.high)))))))

(defsection vl-gatedelay-amount

  (local (in-theory (enable vl-gatedelay-simple-p)))

  (defund vl-gatedelay-amount (x)
    (declare (xargs :guard (and (vl-gatedelay-p x)
                                (vl-gatedelay-simple-p x))))
    (vl-resolved->val (vl-gatedelay->rise x)))

  (local (in-theory (enable vl-gatedelay-amount)))

  (defthm natp-of-vl-gatedelay->amount
    (implies (and (force (vl-gatedelay-p x))
                  (force (vl-gatedelay-simple-p x)))
             (natp (vl-gatedelay-amount x)))
    :rule-classes :type-prescription))



(defsection vl-assign-assigndelays

  (defund vl-assign-assigndelays (x nf warnings)
    "Returns (MV WARNINGS' NEW-ASSIGNS ADD-NETDECLS ADD-MODINSTS ADD-MODS NF')"
    (declare (xargs :guard (and (vl-assign-p x)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* (((vl-assign x) x)
         ((unless x.delay)
          ;; No delay, leave this assignment alone.
          (mv warnings (list x) nil nil nil nf))

         ((unless (vl-gatedelay-simple-p x.delay))
          (mv (cons (make-vl-warning
                     :type :vl-delay-toohard
                     :msg "~a0: the delay on this assignment is too complex; we only ~
                         handle plain delays for now."
                     :args (list x)
                     :fatalp t
                     :fn 'vl-assign-assigndelays)
                    warnings)
              (list x) nil nil nil nf))

         ((unless (posp (vl-expr->finalwidth x.lvalue)))
          (mv (cons (make-vl-warning
                     :type :vl-bad-assign
                     :msg "~a0: expected widths to be computed and positive, but ~
                           lhs width is ~x1."
                     :args (list x (vl-expr->finalwidth x.lvalue))
                     :fatalp t
                     :fn 'vl-assign-assigndelays)
                    warnings)
              (list x) nil nil nil nf))

         (delay (vl-gatedelay-amount x.delay))

         ((when (= delay 0))
          ;; Goofy, explicit zero delay -- just drop it from this assignment.
          (mv warnings (list (change-vl-assign x :delay nil))
              nil nil nil nf))

         (width   (vl-expr->finalwidth x.lvalue))
         (addmods (vl-make-n-bit-delay-m width delay))

         ((mv temp-name nf) (vl-namefactory-indexed-name "vl_del" nf))
         ((mv instname nf)  (vl-namefactory-indexed-name "vl_mkdel" nf))
         ((mv temp-expr temp-netdecl) (vl-occform-mkwire temp-name width))

         ;; VL_N_BIT_DELAY_M mkdel (del, rhs);
         (modargs (list (make-vl-plainarg :expr temp-expr :dir :vl-output :portname "out")
                        (make-vl-plainarg :expr x.expr :dir :vl-input :portname "in")))
         (modinst (make-vl-modinst :instname  instname
                                   :modname   (vl-module->name (car addmods))
                                   :paramargs (vl-arguments nil nil)
                                   :portargs  (vl-arguments nil modargs)
                                   :loc       *vl-fakeloc*))

         ;; assign lhs = del;
         (new-x (change-vl-assign x :expr temp-expr :delay nil)))

      (mv warnings (list new-x) (list temp-netdecl) (list modinst) addmods nf)))

  (local (in-theory (enable vl-assign-assigndelays)))

  (defmvtypes vl-assign-assigndelays
    (nil true-listp true-listp true-listp true-listp nil))

  (defthm vl-assign-assigndelays-basics
    (implies (and (force (vl-assign-p x))
                  (force (vl-namefactory-p nf))
                  (force (vl-warninglist-p warnings)))
             (let ((ret (vl-assign-assigndelays x nf warnings)))
               (and (vl-warninglist-p (mv-nth 0 ret))
                    (vl-assignlist-p  (mv-nth 1 ret))
                    (vl-netdecllist-p (mv-nth 2 ret))
                    (vl-modinstlist-p (mv-nth 3 ret))
                    (vl-modulelist-p  (mv-nth 4 ret))
                    (vl-namefactory-p (mv-nth 5 ret)))))))


(defsection vl-assignlist-assigndelays

  (defund vl-assignlist-assigndelays (x nf warnings)
    "Returns (MV WARNINGS' NEW-ASSIGNS ADD-NETDECLS ADD-MODINSTS ADD-MODS NF')"
    (declare (xargs :guard (and (vl-assignlist-p x)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil nil nil nil nf))
         ((mv warnings car-assigns car-netdecls car-modinsts car-mods nf)
          (vl-assign-assigndelays (car x) nf warnings))
         ((mv warnings cdr-assigns cdr-netdecls cdr-modinsts cdr-mods nf)
          (vl-assignlist-assigndelays (cdr x) nf warnings)))
      (mv warnings
          (append car-assigns cdr-assigns)
          (append car-netdecls cdr-netdecls)
          (append car-modinsts cdr-modinsts)
          (append car-mods cdr-mods)
          nf)))

  (local (in-theory (enable vl-assignlist-assigndelays)))

  (defmvtypes vl-assignlist-assigndelays
    (nil true-listp true-listp true-listp true-listp nil))

  (defthm vl-assignlist-assigndelays-basics
    (implies (and (force (vl-assignlist-p x))
                  (force (vl-namefactory-p nf))
                  (force (vl-warninglist-p warnings)))
             (let ((ret (vl-assignlist-assigndelays x nf warnings)))
               (and (vl-warninglist-p (mv-nth 0 ret))
                    (vl-assignlist-p  (mv-nth 1 ret))
                    (vl-netdecllist-p (mv-nth 2 ret))
                    (vl-modinstlist-p (mv-nth 3 ret))
                    (vl-modulelist-p  (mv-nth 4 ret))
                    (vl-namefactory-p (mv-nth 5 ret)))))))



(defsection vl-make-delayed-args

  (defund vl-make-delayed-args (delaymod args nf)
    "Returns (MV SUCCESSP NETDECLS DELAYED-ARGS MODINSTS NF)"
    (declare (xargs :guard (and (vl-module-p delaymod)
                                (vl-plainarglist-p args)
                                (vl-namefactory-p nf))))
    (b* (((when (atom args))
          (mv t nil nil nil nf))

         ((mv cdr-successp cdr-netdecls cdr-delayed-args cdr-modinsts nf)
          (vl-make-delayed-args delaymod (cdr args) nf))
         ((unless cdr-successp)
          (mv nil nil nil nil nf))

         (expr (vl-plainarg->expr (car args)))
         (dir  (vl-plainarg->dir (car args)))

         ((when (eq dir :vl-inout))
          ;; This seems crazy, let's not try to support it.
          (mv nil nil nil nil nf))

         ((unless (and expr (eq dir :vl-input)))
          ;; We skip blanks just because it's easy.  We skip outputs because,
          ;; even though it seems somehow more elegant to delay the output, it
          ;; may be better to delay the inputs.  Why?  If we delay the inputs
          ;; we get the same drive strength on the output because the output is
          ;; still produced by this gate.  If we delay the outputs explicitly,
          ;; we end up driving them with a regular assignment and lose that
          ;; drive-strength information.  We could probably deal with this
          ;; better, but this seems sort of okay?
          (mv t cdr-netdecls (cons (car args) cdr-delayed-args) cdr-modinsts nf))

         (width (vl-expr->finalwidth expr))
         ((unless (equal width 1))
          ;; Fail, don't know how big of a wire to make
          (mv nil nil nil nil nf))

         ((mv del-name nf)   (vl-namefactory-indexed-name "del" nf))
         ((mv mkdel-name nf) (vl-namefactory-indexed-name "mkdel" nf))
         (del-netdecl (make-vl-netdecl :name del-name
                                       :type :vl-wire
                                       :range (vl-make-n-bit-range width)
                                       :loc *vl-fakeloc*))
         (del-expr    (vl-idexpr del-name width :vl-unsigned)) ;; bozo sign?
         (del-arg     (change-vl-plainarg (car args) :expr del-expr))
         (args        (list (make-vl-plainarg :expr del-expr :dir :vl-output :portname "out")
                            (make-vl-plainarg :expr expr :dir :vl-input :portname "in")))
         (mkdel-inst  (make-vl-modinst :instname  mkdel-name
                                       :modname   (vl-module->name delaymod)
                                       :paramargs (vl-arguments nil nil)
                                       :portargs  (vl-arguments nil args)
                                       :loc       *vl-fakeloc*)))

      (mv t
          (cons del-netdecl cdr-netdecls)
          (cons del-arg cdr-delayed-args)
          (cons mkdel-inst cdr-modinsts)
          nf)))

  (local (in-theory (enable vl-make-delayed-args)))

  (defmvtypes vl-make-delayed-args
    (booleanp true-listp true-listp true-listp nil))

  (defthm vl-make-delayed-args-basics
    (implies (and (force (vl-module-p delaymod))
                  (force (vl-plainarglist-p args))
                  (force (vl-namefactory-p nf)))
             (b* (((mv ?successp netdecls args modinsts nf)
                   (vl-make-delayed-args delaymod args nf)))
               (and (vl-netdecllist-p netdecls)
                    (vl-plainarglist-p args)
                    (vl-modinstlist-p modinsts)
                    (vl-namefactory-p nf))))))



(defsection vl-gateinst-gateinstdelays

  (defund vl-gateinst-gateinstdelays (x nf warnings)
    "Returns (MV WARNINGS' NEW-GATEINSTS ADD-NETDECLS ADD-MODINSTS ADD-MODS NF')"
    (declare (xargs :guard (and (vl-gateinst-p x)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* (((vl-gateinst x) x)
         ((unless x.delay)
          ;; No delay, leave this gateinst alone.
          (mv warnings (list x) nil nil nil nf))

         ((unless (vl-gatedelay-simple-p x.delay))
          (mv (cons (make-vl-warning
                     :type :vl-delay-toohard
                     :msg "~a0: the delay on this gate is too complex; we ~
                           only handle plain delays for now."
                     :args (list x)
                     :fatalp t
                     :fn 'vl-gateinst-gateinstdelays)
                    warnings)
              (list x) nil nil nil nf))

         (delay (vl-gatedelay-amount x.delay))

         ((when (= delay 0))
          ;; Goofy, explicit zero delay -- just drop it from this gateinst.
          (mv warnings
              (list (change-vl-gateinst x :delay nil))
              nil nil nil nf))

         (addmods  (vl-make-1-bit-delay-m delay))
         (delaymod (car addmods))

         ((mv successp del-netdecls del-args del-modinsts nf)
          (vl-make-delayed-args delaymod x.args nf))

         ((unless successp)
          (mv (cons (make-vl-warning
                     :type :vl-delay-failed
                     :msg "~a0: failed to add delays to the arguments of ~
                           this module instance, perhaps due to inouts or ~
                           unresolved/wrong widths."
                     :args (list x)
                     :fatalp t
                     :fn 'vl-gateinst-gateinstdelays)
                    warnings)
              (list x) nil nil nil nf))

         (new-x (change-vl-gateinst x :args del-args)))

      (mv warnings
          (list new-x)
          del-netdecls
          del-modinsts
          addmods
          nf)))

  (local (in-theory (enable vl-gateinst-gateinstdelays)))

  (defmvtypes vl-gateinst-gateinstdelays
    (nil true-listp true-listp true-listp true-listp nil))

  (defthm vl-gateinst-gateinstdelays-basics
    (implies (and (force (vl-gateinst-p x))
                  (force (vl-namefactory-p nf))
                  (force (vl-warninglist-p warnings)))
             (let ((ret (vl-gateinst-gateinstdelays x nf warnings)))
               (and (vl-warninglist-p  (mv-nth 0 ret))
                    (vl-gateinstlist-p (mv-nth 1 ret))
                    (vl-netdecllist-p  (mv-nth 2 ret))
                    (vl-modinstlist-p  (mv-nth 3 ret))
                    (vl-modulelist-p   (mv-nth 4 ret))
                    (vl-namefactory-p  (mv-nth 5 ret)))))))

(defsection vl-gateinstlist-gateinstdelays

  (defund vl-gateinstlist-gateinstdelays (x nf warnings)
    "Returns (MV WARNINGS' NEW-GATEINSTS ADD-NETDECLS ADD-MODINSTS ADD-MODS NF')"
    (declare (xargs :guard (and (vl-gateinstlist-p x)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil nil nil nil nf))
         ((mv warnings car-gateinsts car-netdecls car-modinsts car-mods nf)
          (vl-gateinst-gateinstdelays (car x) nf warnings))
         ((mv warnings cdr-gateinsts cdr-netdecls cdr-modinsts cdr-mods nf)
          (vl-gateinstlist-gateinstdelays (cdr x) nf warnings)))
      (mv warnings
          (append car-gateinsts cdr-gateinsts)
          (append car-netdecls cdr-netdecls)
          (append car-modinsts cdr-modinsts)
          (append car-mods cdr-mods)
          nf)))

  (local (in-theory (enable vl-gateinstlist-gateinstdelays)))

  (defmvtypes vl-gateinstlist-gateinstdelays
    (nil true-listp true-listp true-listp true-listp nil))

  (defthm vl-gateinstlist-gateinstdelays-basics
    (implies (and (force (vl-gateinstlist-p x))
                  (force (vl-namefactory-p nf))
                  (force (vl-warninglist-p warnings)))
             (let ((ret (vl-gateinstlist-gateinstdelays x nf warnings)))
               (and (vl-warninglist-p (mv-nth 0 ret))
                    (vl-gateinstlist-p  (mv-nth 1 ret))
                    (vl-netdecllist-p (mv-nth 2 ret))
                    (vl-modinstlist-p (mv-nth 3 ret))
                    (vl-modulelist-p  (mv-nth 4 ret))
                    (vl-namefactory-p (mv-nth 5 ret)))))))


(defsection vl-module-assigndelays

  (defund vl-module-assigndelays (x)
    "Returns (MV NEW-X ADD-MODS)"
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x)
         ((when (vl-module->hands-offp x))
          (mv x nil))
         (nf (vl-starting-namefactory x))
         ((mv warnings assigns add-netdecls1 add-modinsts1 add-mods1 nf)
          (vl-assignlist-assigndelays x.assigns nf x.warnings))
         ((mv warnings gateinsts add-netdecls2 add-modinsts2 add-mods2 nf)
          (vl-gateinstlist-gateinstdelays x.gateinsts nf warnings))
         (- (vl-free-namefactory nf))
         (new-x (change-vl-module x
                                  :assigns   assigns
                                  :gateinsts gateinsts
                                  :netdecls  (append add-netdecls1 add-netdecls2 x.netdecls)
                                  :modinsts  (append add-modinsts1 add-modinsts2 x.modinsts)
                                  :warnings  warnings)))
      (mv new-x (append add-mods1 add-mods2))))

  (local (in-theory (enable vl-module-assigndelays)))

  (defmvtypes vl-module-assigndelays (nil true-listp))

  (defthm vl-module-p-of-vl-module-assigndelays
    (implies (force (vl-module-p x))
             (vl-module-p (mv-nth 0 (vl-module-assigndelays x)))))

  (defthm vl-module->name-of-vl-module-assigndelays
    (equal (vl-module->name (mv-nth 0 (vl-module-assigndelays x)))
           (vl-module->name x)))

  (defthm vl-modulelist-p-of-vl-module-assigndelays
    (implies (force (vl-module-p x))
             (vl-modulelist-p (mv-nth 1 (vl-module-assigndelays x))))))



(defsection vl-modulelist-assigndelays-aux

  (defund vl-modulelist-assigndelays-aux (x)
    "Returns (MV NEW-X ADD-MODS)"
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* (((when (atom x))
          (mv nil nil))
         ((mv car-prime car-addmods) (vl-module-assigndelays (car x)))
         ((mv cdr-prime cdr-addmods) (vl-modulelist-assigndelays-aux (cdr x))))
      (mv (cons car-prime cdr-prime)
          (append car-addmods cdr-addmods))))

  (local (in-theory (enable vl-modulelist-assigndelays-aux)))

  (defmvtypes vl-modulelist-assigndelays-aux (true-listp true-listp))

  (defthm vl-modulelist-p-of-vl-modulelist-assigndelays-aux
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (mv-nth 0 (vl-modulelist-assigndelays-aux x)))))

  (defthm vl-modulelist->names-of-vl-modulelist-assigndelays-aux
    (equal (vl-modulelist->names (mv-nth 0 (vl-modulelist-assigndelays-aux x)))
           (vl-modulelist->names x)))

  (defthm vl-modulelist-p-of-vl-modulelist-assigndelays-aux-1
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (mv-nth 1 (vl-modulelist-assigndelays-aux x))))))



(defsection vl-modulelist-assigndelays

  (defund vl-modulelist-assigndelays (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* (((mv x-prime addmods)
          (vl-modulelist-assigndelays-aux x))
         (merged (mergesort (append x-prime addmods)))
         ((unless (uniquep (vl-modulelist->names merged)))
          (er hard? 'vl-modulelist-assigndelays
              "Name collision for ~&0."
              (duplicated-members (vl-modulelist->names merged)))))
      merged))

  (local (in-theory (enable vl-modulelist-assigndelays)))

  (defthm vl-modulelist-p-of-vl-modulelist-assigndelays
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-assigndelays x))))

  (defthm no-duplicatesp-equal-of-vl-modulelist->names-of-vl-modulelist-assigndelays
    (no-duplicatesp-equal (vl-modulelist->names (vl-modulelist-assigndelays x)))))


