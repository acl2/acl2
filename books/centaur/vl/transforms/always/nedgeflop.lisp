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

#||

;; BOZO temporary junk, not working yet

(include-book
 "../occform/util")
(include-book
 "../../toe/toe-wirealist")
(include-book
 "centaur/4v-sexpr/sexpr-building" :dir :system)
(include-book
 "../../mlib/writer")       ;; bozo

(defxdoc nedgeflop
  :parents (synthalways primitives)
  :short "Generation of primitive flops.")

(local (xdoc::set-default-parents nedgeflop))

(defxdoc nedgeflop
  :parents (primitive)
  :short "Primitive modules to implement edge-triggered always blocks."

  :long "<p>For many years, VL had only limited support for flip-flops.  The
main VL primitive module was essentially:</p>

@({
module VL_1_BIT_FLOP (q, clk, d) ;
  output reg q;
  input clk;
  input d;

  always @@(posedge clk)
     q <= d;

endmodule
})

<p>And wider flip-flops could be built atop of this.</p>")


(define vl-nedgeflop-posedge-clks
  ((clk-exprs vl-exprlist-p "e.g., (clk1 clk2 ...)"))
  :returns (evatoms vl-evatomlist-p :hyp :fguard
                    "e.g., @(posedge clk1) or @(posedge clk2) or ...")
  (if (atom clk-exprs)
      nil
    (cons (make-vl-evatom :type :vl-posedge
                          :expr (car clk-exprs))
          (vl-nedgeflop-posedge-clks (cdr clk-exprs)))))

(define vl-nedgeflop-ifstmt
  ((q-expr     vl-expr-p     "e.g., q")
   (clk-exprs  vl-exprlist-p "e.g., (clk1 clk2 ...)")
   (data-exprs vl-exprlist-p "e.g., (d1 d2 ...)"))
  :returns (guts vl-stmt-p :hyp :fguard
                 "e.g., if (clk1) q <= d1; else if (clk2) q <= d2; ...")
  :guard (same-lengthp clk-exprs data-exprs)
  (b* (((when (atom data-exprs))
        (make-vl-nullstmt))
       (assign1 (make-vl-assignstmt :type :vl-nonblocking
                                    :lvalue q-expr
                                    :expr   (car data-exprs)
                                    :loc    *vl-fakeloc*)))
    (make-vl-ifstmt
     :condition   (car clk-exprs)
     :truebranch  assign1
     :falsebranch (vl-nedgeflop-ifstmt q-expr
                                       (cdr clk-exprs)
                                       (cdr data-exprs)))))

(define vl-nedgeflop-always
  ((q-expr     vl-expr-p     "e.g., q")
   (clk-exprs  vl-exprlist-p "e.g., (clk1 clk2 ...)")
   (data-exprs vl-exprlist-p "e.g., (d1 d2 ...)"))
  :guard (same-lengthp clk-exprs data-exprs)
  :returns (always vl-always-p :hyp :fguard
                 "e.g., always @(posedge clk1 or ...)
                         if (clk1) q <= d1;
                         else if (clk2) q <= d2; ...")
  (b* ((evatoms (vl-nedgeflop-posedge-clks clk-exprs))
       (evctrl  (make-vl-eventcontrol :starp nil
                                      :atoms evatoms))
       (body    (vl-nedgeflop-ifstmt q-expr clk-exprs data-exprs))
       (stmt    (make-vl-timingstmt :ctrl evctrl
                                    :body body)))
    (make-vl-always :stmt stmt
                    :loc *vl-fakeloc*)))

(define vl-nedgeflop-some-edge-sexpr
  :short "Build a 4v-sexpr that captures when any clock has just had a posedge."
  ((clks      "E wire names for current clock values.")
   (clk-prevs "E wire names for previous clock values."))
  :guard (and (consp clks)
              (same-lengthp clks clk-prevs))
  :returns 4v-sexpr
  :measure (+ 1 (len clks))
  (b* (((cons clk1      rest-clks)      clks)
       ((cons clk1-prev rest-clk-prevs) clk-prevs)
       (edge1
        ;; The first clock has an edge exactly when its previous value was F
        ;; and its new value is T.  This sexpr captures that:
        (acl2::4vs-and clk1 (acl2::4vs-not clk1-prev)))
       ((when (atom rest-clks))
        edge1))
    (acl2::4vs-or edge1
                  (vl-nedgeflop-some-edge-sexpr rest-clks rest-clk-prevs))))

(define vl-nedgeflop-update-sexpr
  :short "Build a 4v-sexpr with the update function upon a posedge."
  ((clks      "E wire names for the current clock values.")
   (dat-prevs "E wires names for the previous data values."))
  :guard (and (consp clks)
              (same-lengthp clks dat-prevs))
  :measure (+ 1 (len clks))
  (b* (((cons clk1      rest-clks)      clks)
       ((cons dat-prev1 rest-dat-prevs) dat-prevs)
       ((when (atom rest-clks))
        ;; Last choice -- no need to check clk1.  Why?  We only use the
        ;; update-sexpr when some clock has just had a posedge.  So, if we get
        ;; this far, no other clock is 1, so the last clock must be 1.
        dat-prev1))
    (acl2::4vs-ite*-dumb clk1
                         dat-prev1
                         (vl-nedgeflop-update-sexpr rest-clks rest-dat-prevs))))

(define vl-make-1-bit-n-edge-flop ((n posp))
  :returns (flop vl-module-p :hyp :fguard)
  (b* ((name (cat "VL_1_BIT_" (natstr n) "_EDGE_FLOP"))
       ((mv q-expr q-port q-portdecl ?q-netdecl)
        (vl-occform-mkport "q" :vl-output 1))
       (q-regdecl
        (make-vl-regdecl :name "q" :loc *vl-fakeloc*))
       ((mv d-exprs d-ports d-portdecls d-netdecls)
        (vl-occform-mkports "d" 0 n :dir :vl-input :width 1))
       ((mv clk-exprs clk-ports clk-portdecls clk-netdecls)
        (vl-occform-mkports "clk" 0 n :dir :vl-input :width 1))
       (always
        (vl-nedgeflop-always q-expr clk-exprs d-exprs))

       ;; Corresponding E module
       (q-wire    (car (vl-emodwires-from-msb-to-lsb "q" 0 0)))
       (q-prev    (car (vl-emodwires-from-msb-to-lsb "q_prev" 0 0)))
       (d-wires   (vl-emodwires-from-msb-to-lsb "d" (- n 1) 0))
       (d-prevs   (vl-emodwires-from-msb-to-lsb "dat_prev" (- n 1) 0))
       (clk-wires (vl-emodwires-from-msb-to-lsb "clk" (- n 1) 0))
       (clk-prevs (vl-emodwires-from-msb-to-lsb "clk_prev" (- n 1) 0))

       ;; Next states.  Every previous clock/data gets the new clock/data.
       (next-q-sexpr   (acl2::4vs-ite*-dumb
                        ;; if we just saw some posedge
                        (vl-nedgeflop-some-edge-sexpr clk-wires clk-prevs)
                        ;; update the register with its update expr
                        (vl-nedgeflop-update-sexpr clk-wires d-prevs)
                        ;; else just hold your value
                        q-prev))
       (nst-alist      (cons (cons q-prev next-q-sexpr)
                             (append (pairlis$ clk-prevs clk-wires)
                                     (pairlis$ d-prevs d-wires))))
       (out-alist      (list (cons q-wire next-q-sexpr)))
       (emod (list :n (vl-starname name)
                   :o (list (list q-wire))
                   :i (append (pairlis$ d-wires nil)
                              (pairlis$ clk-wires nil))
                   :x (list :out out-alist
                            :nst nst-alist))))

    (make-vl-module :name      name
                    :origname  name
                    :ports     (cons q-port (append d-ports clk-ports))
                    :portdecls (cons q-portdecl (append d-portdecls clk-portdecls))
                    :netdecls  (append d-netdecls clk-netdecls)
                    :regdecls  (list q-regdecl)
                    :alwayses  (list always)
                    :minloc    *vl-fakeloc*
                    :maxloc    *vl-fakeloc*
                    :atts      (list (cons (hons-copy "VL_HANDS_OFF") nil))
                    :esim      emod)))


(vl-pps-module (vl-make-1-bit-n-edge-flop 1))
(vl-pps-module (vl-make-1-bit-n-edge-flop 2))
(vl-pps-module (vl-make-1-bit-n-edge-flop 3))

(defconst acl2::*f2*
  (vl-module->esim (vl-make-1-bit-n-edge-flop 2)))

(in-package "ACL2")

(include-book
 "centaur/esim/esim-sexpr" :dir :system)
(include-book
 "centaur/esim/esim-primitives" :dir :system)
(good-esim-modulep *f2*)



(esim-sexpr-general *f2*)




(define nedgeflop-data-ports (n)


module VL_2_EDGE_FLOP (q, d1, d2, clk1, clk2);

  output q;

  input  d1, d2;
  input  clk1, clk2;

  reg 	 q;

  always @(posedge clk1 or posedge clk2)
    if (clk1)
      q <= d1;
    else if (clk2)
      q <= d2;

endmodule







(defun vl-make-nedge-flop (n)

  (b* 
                         


||#