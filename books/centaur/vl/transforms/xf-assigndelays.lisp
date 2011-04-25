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
(include-book "../mlib/namefactory")
(include-book "../transforms/occform/gen-util")
(local (include-book "../util/arithmetic"))


(local (defthm crock
         (implies (vl-modulelist-p x)
                  (iff (first x)
                       (consp x)))))


(defconst *vl-1-bit-delay-1*
  (b* ((name "VL_1_BIT_DELAY_1")
       (atts '(("VL_PRIMITIVE") ("VL_HANDS_OFF")))
       ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv in-expr  in-port  in-portdecl  in-netdecl)  (vl-occform-mkport "in"  :vl-input  1))
       (one    (vl-make-index 1))
       (delay  (make-vl-gatedelay :rise one :fall one :high one))
       (assign (make-vl-assign :lvalue out-expr :expr in-expr :delay delay :loc *vl-fakeloc*)))
    (make-honsed-vl-module :name      name
                           :origname  name
                           :ports     (list out-port     in-port)
                           :portdecls (list out-portdecl in-portdecl)
                           :netdecls  (list out-netdecl  in-netdecl)
                           :assigns   (list assign)
                           :minloc    *vl-fakeloc*
                           :maxloc    *vl-fakeloc*
                           :atts      atts)))


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
      (cons (make-vl-modinst :instname  (str::cat basename (str::natstr n))
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
<code>
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
</code>"
  :guard (posp m)
  :body
  (b* (((when (= m 1))
        (list *vl-1-bit-delay-1*))

       (name  (str::cat "VL_1_BIT_DELAY_" (str::natstr m)))

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

       (name (str::cat "VL_" (str::natstr n) "_BIT_DELAY_" (str::natstr m)))

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

         ((vl-gatedelay x.delay) x.delay)

         ((unless (and (vl-expr-resolved-p x.delay.rise)
                       (vl-expr-resolved-p x.delay.fall)
                       x.delay.high
                       (vl-expr-resolved-p x.delay.high)
                       (= (vl-resolved->val x.delay.rise) (vl-resolved->val x.delay.fall))
                       (= (vl-resolved->val x.delay.rise) (vl-resolved->val x.delay.high))))
          (mv (cons (make-vl-warning
                     :type :vl-delay-toohard
                     :msg "~a0: the delay on this assignment is too complex; we only ~
                         handle plain delays for now."
                     :args (list x)
                     :fatalp t
                     :fn 'vl-assign-assigndelays)
                    warnings)
              (list x) nil nil nil nf))

         ((unless (and (posp (vl-expr->finalwidth x.lvalue))
                       (posp (vl-expr->finalwidth x.expr))
                       (= (vl-expr->finalwidth x.lvalue)
                          (vl-expr->finalwidth x.expr))))
          (mv (cons (make-vl-warning
                     :type :vl-bad-assign
                     :msg "~a0: expected widths to be computed and in agreement, but lhs ~
                         width is ~x1 while rhs width is ~x2."
                     :args (list x
                                 (vl-expr->finalwidth x.lvalue)
                                 (vl-expr->finalwidth x.expr))
                     :fatalp t
                     :fn 'vl-assign-assigndelays)
                    warnings)
              (list x) nil nil nil nf))

         (delay (vl-resolved->val x.delay.rise))

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



(defsection vl-module-assigndelays

  (defund vl-module-assigndelays (x)
    "Returns (MV NEW-X ADD-MODS)"
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x)
         (nf (vl-starting-namefactory x))
         ((mv warnings assigns add-netdecls add-modinsts add-mods nf)
          (vl-assignlist-assigndelays x.assigns nf x.warnings))
         (- (vl-free-namefactory nf))
         (new-x (change-vl-module x
                                  :assigns  assigns
                                  :netdecls (append add-netdecls x.netdecls)
                                  :modinsts (append add-modinsts x.modinsts)
                                  :warnings warnings)))
      (mv new-x add-mods)))

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


