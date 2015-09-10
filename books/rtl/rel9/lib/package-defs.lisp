; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

(set-enforce-redundancy t)

(local (include-book "../support/support/package-defs"))

;;Miscellaneous symbols that are not in *acl2-exports*:

(defmacro other-acl2-symbols ()
  ''(local-defun local-defthm local-in-theory
                 n ; clock argument
                 defbvecp ; macro written out by compiler
                 defclock ; macro written out by compiler
                 defperiodic
                 fast-clock  ;BOZO, is importing these into the packages, the right way to handle this?
                 slow-clock-one-quantum-wide
                 slow-clock-one-quantum-wide-shifted
                 slow-clock-two-quanta-wide
                 slow-clock-two-quanta-wide-shifted
                 always-1
                 posedge negedge edge ; for defclock macro, which we used to use
                 pedge nedge ;for defperiodic macro
                 $path ; path argument of signal functions
                 sub1-induction ; for bvecp lemma hints
                 ))

;;Symbols that occur in the RTL translation.  Formerly the symbol UNKNOWN was excluded from this
;;list so that the corresponding symbol in the "*" package could be assigned a different function
;;definition; but the first argument of unknown can be in any package desired.

(defmacro rtl-symbols ()
  ''(log= log<> log< log<= log> log>= lnot logand1 logior1 logxor1 shft lshft
          rshft cat mulcat bitn bits setbits setbitn mod+ mod* mod- bind
          case-select if1 cond1 reset reset2 land lior lxor lcat n! arr0 natp1
          as ag mk-bvarr mk-bvec ag2 as2
          abs trunc near minf inf sticky sig expo bitvec ; appeared May 2004 (from rpl_main.cc)
          expt ; appeared May 2004 (seems to come from r2s)
          prop gen
          unknown unknown2))

;;Functions that are defined in the FP library:

(defmacro fp-symbols ()
  ''(natp fl cg fl-half bvecp bv-arrp sumbits sigm kap tau lamt lamg lamz lam1 lam2 lam3 lam4 lam0 lamb
          expo sgn sig
          exactp fp+ bias esgnf eexpof esigf erepp eencodingp eencode edecode ndecode rebias-expo isgnf iexpof isigf
          nrepp drepp irepp nencodingp dencodingp iencodingp nencode dencode iencode ddecode idecode trunc away re
          near near-witness near+ sticky oddr kp inf minf ieee-mode-p rnd flip
          rnd-const drnd drnd-original))

;;ACL2 symbols that are imported by all packages:

(defmacro shared-symbols ()
  '(union-eq *acl2-exports*
    (union-eq *common-lisp-symbols-from-main-lisp-package*
     (union-eq (other-acl2-symbols)
      (union-eq (fp-symbols)
       (rtl-symbols))))))
