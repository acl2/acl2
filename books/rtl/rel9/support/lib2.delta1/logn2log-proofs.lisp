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
(include-book "log")
(include-book "logn")


(local (include-book "../../arithmetic/top"))

;;;;
;;;;

(local
 (defthm bvecp-fl-1/2
   (implies (bvecp x (+ 1 n))
            (BVECP (FL (* 1/2 X)) n))
   :hints (("Goal" :in-theory (e/d (bvecp
                                    expt-2-reduce-leading-constant) ())))))

(local
 (defthm bvecp-mod-2
   (implies (integerp x)
            (BVECP (MOD X 2) 1))
   :hints (("Goal" :in-theory (e/d (bvecp) ())))))



(defthm land-logand
  (implies (and (bvecp x n)
                (bvecp y n)
                (natp n))
           (equal (land x y n)
                  (logand x y)))
  :hints (("Goal" :in-theory (e/d (binary-land)
                                  ())
           :induct (binary-land x y n))
          ("Subgoal *1/4" :use ((:instance logand-def
                                           (i x)
                                           (j y))))))


(defthm lior-logior
  (implies (and (bvecp x n)
                (bvecp y n)
                (natp n))
           (equal (lior x y n)
                  (logior x y)))
  :hints (("Goal" :in-theory (e/d (binary-lior)
                                  ())
           :induct (binary-lior x y n))
          ("Subgoal *1/4" :use ((:instance logior-def
                                           (i x)
                                           (j y))))))

(defthm lxor-logxor
  (implies (and (bvecp x n)
                (bvecp y n)
                (natp n))
           (equal (lxor x y n)
                  (logxor x y)))
  :hints (("Goal" :in-theory (e/d (binary-lxor)
                                  ())
           :induct (binary-lxor x y n))
          ("Subgoal *1/4" :use ((:instance logxor-def
                                           (i x)
                                           (j y))))))


;;;
;;; then we have the following in the log.lisp
;;;
(encapsulate ()
             (local (include-book "log"))

             (DEFTHM LOGIOR-BVECP
               (IMPLIES (AND (BVECP X N) (BVECP Y N))
                        (BVECP (LOGIOR X Y) N)))



             (DEFTHM LOGAND-BVECP
               (IMPLIES (AND (NATP N) (BVECP X N) (INTEGERP Y))
                        (BVECP (LOGAND X Y) N)))

             (defthm logxor-bvecp
               (implies (and (bvecp x n)
                             (bvecp y n)
                             (natp n))
                        (bvecp (logxor x y) n)))

             )


(encapsulate ()
  (local (include-book "bvecp-raw-helpers"))

  (defthm lnot-bvecp
    (implies (and (<= n k)
                  (case-split (integerp k)))
             (bvecp (lnot x n) k))))







