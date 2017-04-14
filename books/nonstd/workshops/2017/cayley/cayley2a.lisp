#|==========================================
 Cayley-Dickson Construction
   cayley2a.lisp

 In any composition algebra:
    Theorem. (Vp x) -> (V_norm x) = (V_dot x x) 

  31 March   2017

  Axioms and theory of composition algebras.

   Real Composition Algebra:
     A Real Vector Algebra with Identity:
       A Real Vector Space with Multiplication
       and a Multiplicative Identity.
   The Vector Algebra also has a real valued Norm
       and a real valued Dot (or Inner) Product
       satisfying the Composition Law
          Norm(xy) = Norm(x)Norm(y).

 References:

 J.H. Conway and D.A. Smith, On Quaternions and Octonions: Their Geometry,
 Arithmetic, and Symmetry, A K Peters, 2003, pages 67--73.

 H.-D. Ebbinghaus, H. Hermes, F. Hirzebruch, M. Koecher, K. Mainzer, 
 J. Neukirch, A. Prestel, and R. Remmert, Numbers, Springer, 1991, pp 265--274     

ACL2 Version 7.4(r) built March 30, 2017  08:51:54.
System books directory "/home/acl2/acl2-7.4r/acl2-7.4/books/".
ACL2 Version 7.4 built March 29, 2017  10:38:07.
System books directory "/home/acl2/acl2-7.4/acl2-7.4/books/".
===============================|#
#|====================================
To certify:
(certify-book "cayley2a"
             0   ;; world with no commands
             nil ;;compile-flg  
             ) 
===============================
To use:
(include-book 
          "cayley2a"  
          :uncertified-okp nil
          :defaxioms-okp nil 
          :skip-proofs-okp nil 
          ) 
=====================================|#
#|===============================================
:set-gag-mode t      ; enable gag-mode, suppressing most proof commentary
(set-gag-mode t)     ; same as above
:set-gag-mode :goals ; same as above, but print names of goals when produced
:set-gag-mode nil    ; disable gag-mode
==============|#
#|============================== 
(LD 
    "cayley2a.lisp")              ; read and evaluate each form in file 
==================|#

(in-package "ACL2")

(local
(include-book "arithmetic/top-with-meta" :dir :system
           :uncertified-okp nil
           :defaxioms-okp nil
           :skip-proofs-okp nil))

#+non-standard-analysis
(local
(in-theory (disable REALP-IMPLIES-ACL2-NUMBERP)))

#-non-standard-analysis
(local
(in-theory (disable RATIONALP-IMPLIES-ACL2-NUMBERP)))

(include-book "cayley2"  
          :uncertified-okp nil
          :defaxioms-okp nil 
          :skip-proofs-okp nil)

(defthmD
 not-Forall-u-V_dot-u-x=0_V_1
 (not (Forall-u-V_dot-u-x=0 (V_1)))
 :hints (("Goal"
       :in-theory (disable (:DEFINITION FORALL-U-V_DOT-U-X=0-DEF))
       :use (:instance
         Forall-u-V_dot-u-x=0->x=V_0
         (x (V_1))))))

(defthm
 Forall-u-V_dot-u-x=0-witness_V_1-lemma
 (and (Vp (Forall-u-V_dot-u-x=0-witness (V_1)))
      (not (equal (V_dot (V_1)
              (Forall-u-V_dot-u-x=0-witness (V_1)))
           0)))
 :hints (("Goal"
       :in-theory (disable (:DEFINITION V_DOT-DEF))
       :use not-Forall-u-V_dot-u-x=0_V_1)))

(defthm
 V_dot-V_1-Forall-u-V_dot-u-x=0-witness-V_1-lemma
 (equal (+ (V_dot (V_1)
           (Forall-u-V_dot-u-x=0-witness (V_1)))
        (V_dot (V_1)
           (Forall-u-V_dot-u-x=0-witness (V_1))))
     (* 2 (V_dot (V_1)
             (Forall-u-V_dot-u-x=0-witness (V_1)))))
 :hints (("Goal"
       :in-theory (disable (:DEFINITION V_DOT-DEF)))))

(defthm
 realp-V_dot-V_1-Forall-u-V_dot-u-x=0-witness-V_1
 (real/rationalp (V_dot (V_1)
             (Forall-u-V_dot-u-x=0-witness (V_1))))
 :rule-classes :type-prescription
 :hints (("Goal"
       :in-theory (disable (:DEFINITION V_DOT-DEF)))))

(defthm
 V_dot-V_1-V_1=1
 (equal (V_dot (V_1)(V_1))
     1)
 :hints (("Goal"
  :in-theory (disable (:DEFINITION V_DOT-DEF)
                   Exchange-Law)
       :use ((:instance
          Exchange-Law
          (u (Forall-u-V_dot-u-x=0-witness (V_1)))
          (x (V_1))
          (y (V_1))
          (z (V_1)))))))

(defthm
 V_norm-x=V_dot-x-x
 (implies (Vp x)
       (equal (V_norm x)
          (V_dot x x)))
 :hints (("Goal"
       :in-theory (disable (:DEFINITION V_DOT-DEF)
                   SCALING-LAW-LEFT
                   Realp>=0-V_norm)
       :use (Realp>=0-V_norm
         (:instance
          SCALING-LAW-LEFT
          (y (V_1))
          (z (V_1)))))))