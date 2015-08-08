(in-package "ACL2")

;;Miscellaneous symbols that are not in *acl2-exports*:

(defmacro other-acl2-symbols ()
  ''(local-defun local-defthm local-in-theory
                 $path ; path argument of signal functions
                 ))

(defmacro rtl-symbols ()
  ''(log= log<> log< log<= log> log>= lnot logand1 logior1 logxor1 shft lshft
          rshft cat mulcat bitn bits setbits setbitn mod+ mod* mod- bind
          case-select if1 cond1 reset reset2 land lior lxor lcat n! arr0 natp1
          as ag mk-bvarr mk-bvec ag2 as2
          unknown unknown2))

;;Functions that are defined in the FP library:

(defmacro fp-symbols ()
  ''(natp fl cg fl-half bvecp bv-arrp sumbits sigm kap tau lamt lamg lamz lam1 lam2 lam3 lam4 lam0 lamb
          expo sgn sig
          exactp fp+ bias esgnf eexpof esigf erepp eencodingp eencode edecode ndecode rebias-expo isgnf iexpof isigf
          nrepp drepp irepp nencodingp dencodingp iencodingp nencode dencode iencode ddecode idecode trunc away re
          near near-witness near+ sticky oddr kp inf minf ieee-mode-p rnd flip rnd-const drnd))

;;ACL2 symbols that are imported by all packages:

(defmacro shared-symbols ()
  '(union-eq *acl2-exports*
    (union-eq *common-lisp-symbols-from-main-lisp-package*
     (union-eq (other-acl2-symbols)
      (union-eq (fp-symbols)
       (rtl-symbols))))))
