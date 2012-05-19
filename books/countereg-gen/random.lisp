#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#


#|

  A Simple Random Number Generator              Version 0.1 
  Jared Davis <jared@cs.utexas.edu>          February 25, 2004
  
  This file is in the public domain.  You can freely use it for any
  purpose without restriction. 
 
  This is just a basic pure multiplicative pseudorandom number gen-
  erator.  *M31* is the 31st mersenne prime, and *P1* is 7^5 which
  is a primitive root of *M31*, ensuring that our period is M31 - 1.
  This idea is described in "Elementary Number Theory and its Appli-
  cations" by Kenneth H. Rosen, Fourth Edition, Addison Wesley 1999,
  in Chapter 10.1, pages 356-358.
 
  The random number generator uses a stobj, rand, to store the seed.
  You will want to use the following functions:

    (genrandom <max> rand)
       Returns (mv k rand) where 0 <= k < max.
            
    (update-seed <newseed> rand)
       Manually switch to a new seed.  By default, a large messy num-
       ber will be used.  You probably don't need to change it, but 
       it might be good if you want to be able to reproduce your re-
       sults in the future.
 
  Normally we are not particularly interested in reasoning about ran-
  dom numbers.  However, we can say that the number k generated is an
  an integer, and that 0 <= k < max when max is a positive integer. 
  See the theorems genrandom-minimum and genrandom-maximum. 

  --
  
  Modified slightly by Peter Dillinger, 7 Feb 2008
  With significant additions by Dimitris Vardoulakis & Peter Dillinger where
    noted below.

|#

(in-package "ACL2")
(set-verify-guards-eagerness 2)


(defconst *M31* 2147483647)    
(defconst *P1* 16807)          

(defstobj rand
  (seed :type integer :initially 1382728371))



(defun getseed (rand)
  (declare (xargs :stobjs (rand)))
  (let ((s (seed rand)))
    (if (and (integerp s) (<= 0 s))
        s
      0)))

(local (defthm getseed-integer
  (and (integerp (getseed rand))
       (<= 0 (getseed rand)))
  :rule-classes :type-prescription))

(in-theory (disable getseed))

(defun genrandom (max rand)
  (declare (xargs :stobjs (rand)
                  :guard (posp max)))
  (let* ((new-seed (mod (* *P1* (getseed rand)) *M31*))
         (rand (update-seed new-seed rand)))
    (mv (if (zp max)
          0
          (mod new-seed max))
        rand)))

(encapsulate nil
 (local (include-book "arithmetic-2/floor-mod/floor-mod" :dir :system))

 (defthm genrandom-natural
   (natp (car (genrandom max rand)))
   :rule-classes :type-prescription)

 (defthm genrandom-minimum 
   (<= 0 (car (genrandom max rand)))
   :rule-classes :linear)
 
 (defthm genrandom-maximum
   (implies (posp max)
            (<= (car (genrandom max rand)) (1- max)))
   :rule-classes :linear))
 
(in-theory (disable genrandom))



;=====================================================================;
; 
; Begin additions by Peter Dillinger &  Dimitris Vardoulakis
; Last modified 7 February 2008
;
;=====================================================================;

(defun random-boolean (rand)
  (declare (xargs :stobjs (rand)))
  (mv-let (num rand)
          (genrandom 2 rand)
          (mv (= 1 num) rand)))

(defthm random-boolean-type
  (booleanp (car (random-boolean r)))
  :rule-classes :type-prescription)

(in-theory (disable random-boolean))

;generate naturals according to a pseudo-geometric distribution
(defun random-natural-basemax (base maxdigits rand)
  (declare (xargs :stobjs (rand)
                  :guard (and (posp base)
                              (natp maxdigits))))
  (if (or (zp maxdigits) (zp base))
    (mv 0 rand)
    (mv-let (v rand)
            (genrandom (* 2 base) rand)
            (if (>= v base)
              (mv-let (v2 rand)
                      (random-natural-basemax base (1- maxdigits) rand)
                      (mv (+ (- v base) (* base (nfix v2))) rand))
              (mv v rand)))))

(defun random-natural (rand)
  (declare (xargs :stobjs (rand)))
  (random-natural-basemax 10 6 rand))

(defun random-length (rand)
  (declare (xargs :stobjs (rand)))
  (random-natural-basemax 4 2 rand))

(defthm random-natural-basemax-type
  (natp (car (random-natural-basemax b d r)))
  :rule-classes :type-prescription)

(defthm random-natural-type
  (natp (car (random-natural r)))
  :rule-classes :type-prescription)

(defthm random-length-type
  (natp (car (random-length r)))
  :rule-classes :type-prescription)

(in-theory (disable random-natural-basemax
                    random-natural
                    random-length))




; generate indices uniformly within a specified length 
(defun random-index (len rand)
  (declare (xargs :stobjs (rand)
                  :guard (posp len)))
  (genrandom len rand))

             
;generate integers according to a pseudo-geometric distribution
(defun random-integer (rand)
  (declare (xargs :stobjs (rand)))
  (mv-let (sign rand)
          (random-boolean rand)
          (mv-let (nat rand)
                  (random-natural rand)
                  (mv (if sign nat (- nat))
                      rand))))

(defthm random-integer-type
  (integerp (car (random-integer r)))
  :rule-classes :type-prescription)

(in-theory (disable random-integer))


;or generate integers with a uniform distribution, between i & j (incl.)
(defun random-int-between (i j rand)
  (declare (xargs :stobjs (rand)
                  :guard (and (integerp i)
                              (integerp j))))
  (let ((low (ifix (min i j)))
        (high (ifix (max i j))))
    (mv-let
     (num rand)
     (genrandom (1+ (- high low)) rand)
     (mv (+ low num) rand))))

(defthm random-int-between-type
  (integerp (car (random-int-between i j r)))
  :rule-classes :type-prescription)

(defthm random-int-between-lower
  (implies (and (integerp i)
                (integerp j)
                (<= i j))
           (<= i (car (random-int-between i j r))))
  :rule-classes :linear)

(defthm random-int-between-upper
  (implies (and (integerp i)
                (integerp j)
                (<= i j))
           (>= j (car (random-int-between i j r))))
  :rule-classes :linear)

(in-theory (disable random-int-between))


; generate a signed rational with pseudo-geometric numerator & denominator 
(defun random-rational (rand)
  (declare (xargs :stobjs (rand)))
  (mv-let (numer rand)
          (random-integer rand)
          (mv-let (denom-1 rand)
                  (random-natural rand)
                  (mv (/ numer
                         (+ 1 denom-1))
                      rand))))

(defthm random-rational-type
  (rationalp (car (random-rational r)))
  :rule-classes :type-prescription)

(in-theory (disable random-rational))


; pseudo-uniform rational between 0 and 1 (inclusive)
(defun random-probability (rand)
  (declare (xargs :stobjs (rand)))
  (mv-let (a rand)
          (random-natural rand)
          (mv-let (b rand)
                  (random-natural rand)
                  (let ((denom (* (1+ a) (1+ b))))
                    (mv-let (numer rand)
                            (genrandom (1+ denom) rand)
                            (mv (/ numer denom) rand))))))

(defthm random-probability-type
  (rationalp (car (random-probability r)))
  :rule-classes :type-prescription)

(defthm random-probability>=0
  (<= 0 (car (random-probability r)))
  :rule-classes (:linear :type-prescription)) 

(encapsulate nil
  (local (include-book "arithmetic/rationals" :dir :system))

  #|
  (local
   (defthm numerator<=denominator-implies-<=1
     (implies (and (natp n)
                   (posp d)
                   (<= n d))
              (<= (* (/ d) n)
                  1))))
  |#
  
  (defthm random-probability<=1
    (<= (car (random-probability r)) 1)
    :rule-classes :linear))

(in-theory (disable random-probability))


;generate a random rational whose absolute value is lte x
(defun random-rational-between (x y rand)
  (declare (xargs :stobjs (rand)
                  :guard (and (rationalp x)
                              (rationalp y))))
  (mv-let (p rand)
          (random-probability rand)
          (mv (rfix
               (if (< x y)
                 (+ x (* p (- y x)))
                 (+ y (* p (- x y)))))
              rand)))

(defthm random-rational-between-type
  (rationalp (car (random-rational-between i j r)))
  :rule-classes :type-prescription)

(encapsulate nil
  (local (include-book "arithmetic-3/top" :dir :system))
  
  (defthm random-rational-between-lower
    (implies (and (rationalp i)
                  (rationalp j)
                  (<= i j))
             (<= i (car (random-rational-between i j r))))
    :rule-classes :linear)

  (local (defthm random-rational-between-upper-lemma2
           (implies (and (rationalp i)
                         (rationalp j)
                         (rationalp p)
                         (<= 0 p)
                         (<= p 1)
                         (< i j))
                    (<= (* i p)
                        (* j p)))
           :rule-classes nil))
  
  (local 
   (defthm random-rational-between-upper-lemma
     (implies (and (rationalp i)
                   (rationalp j)
                   (rationalp p)
                   (<= 0 p)
                   (<= p 1)
                   (< i j))
              (<= (+ i (* j p))
                  (+ j (* i p))))
     :hints (("Goal" :use (:instance
                           random-rational-between-upper-lemma2
                           (p (- 1 p)))))))

  (defthm random-rational-between-upper
    (implies (and (rationalp i)
                  (rationalp j)
                  (<= i j))
             (<= (car (random-rational-between i j r)) j))
    :rule-classes :linear))

(in-theory (disable random-rational-between))



;generate non-zero integers according to a pseudo-geometric distribution
(defun random-nonzero-integer (rand)
  (declare (xargs :stobjs (rand)))
  (mv-let (sign rand)
          (random-boolean rand)
          (mv-let (nat rand)
                  (random-natural rand)
                  (mv (if sign (+ 1 nat) (- -1 nat))
                      rand))))

(defthm random-nonzero-integer-type
  (and (integerp (car (random-nonzero-integer r)))
       (not (equal (car (random-nonzero-integer r)) 0)))
  :rule-classes :type-prescription)

(in-theory (disable random-nonzero-integer))




; generate a signed rational with pseudo-geometric numerator & denominator 
(defun random-nonzero-rational (rand)
  (declare (xargs :stobjs (rand)))
  (mv-let (numer rand)
          (random-nonzero-integer rand)
          (mv-let (denom-1 rand)
                  (random-natural rand)
                  (mv (/ numer
                         (+ 1 denom-1))
                      rand))))

(defthm random-nonzero-rational-type
  (and (rationalp (car (random-nonzero-rational r)))
       (not (equal (car (random-nonzero-rational r)) 0)))
  :rule-classes :type-prescription)

(in-theory (disable random-nonzero-rational))


; generate a (strictly) complex number from rationals
(defun random-complex (rand)
  (declare (xargs :stobjs (rand)))
  (mv-let (rpart rand)
          (random-rational rand)
          (mv-let (ipart rand)
                  (random-nonzero-rational rand)
                  (mv (complex rpart ipart) rand))))

(defthm random-complex-type
  (complex-rationalp (car (random-complex r)))
  :rule-classes :type-prescription)

(in-theory (disable random-complex))




(defmacro random-element (lst rand-rand)
  `(mv-let (random-element-macro-idx rand)
           (random-index (length ,lst) ,rand-rand)
           (mv (nth random-element-macro-idx ,lst) rand)))

(defmacro random-element-len (lst len rand-rand)
  `(if (mbt (<= ,len (len ,lst)))
     (mv-let (random-element-macro-idx rand)
             (random-index ,len ,rand-rand)
             (mv (nth random-element-macro-idx ,lst) rand))
     (mv (car ,lst) rand)))



(defconst *standard-chars-len*
  (len *standard-chars*))

(defun random-char (rand)
  (declare (xargs :stobjs (rand)))
  (random-element-len *standard-chars*
                      *standard-chars-len*
                      rand))

(defthm random-char-type
  (characterp (car (random-char r)))
  :rule-classes :type-prescription)

(in-theory (disable random-char))


(defun random-char-list-len (len rand)
  (declare (xargs :stobjs (rand)
                  :guard (natp len)))
  (if (zp len)
    (mv nil rand)
    (mv-let (c rand)
            (random-char rand)
            (mv-let (lst rand)
                    (random-char-list-len (1- len) rand)
                    (mv (cons c lst) rand)))))

(defthm random-char-list-len-type
  (character-listp (car (random-char-list-len l r)))
  :rule-classes :type-prescription)

(in-theory (disable random-char-list-len))


(defun random-string-len (len rand)
  (declare (xargs :stobjs (rand)
                  :guard (natp len)))
  (mv-let (lst rand)
          (random-char-list-len len rand)
          (mv (coerce lst 'string) rand)))

(defthm random-string-len-type
  (stringp (car (random-string-len l r)))
  :rule-classes :type-prescription)

(in-theory (disable random-string-len))


;generate a random string of pseudogeometric length
(defun random-string (rand)
  (declare (xargs :stobjs (rand)))
  (mv-let (len rand)
          (random-length rand)
          (random-string-len len rand)))

(defthm random-string-type
  (stringp (car (random-string r)))
  :rule-classes :type-prescription)

(in-theory (disable random-string))


;generate a random symbol of pseudogeometric length
(defun random-symbol-same-package (sym rand)
  (declare (xargs :stobjs (rand)
                  :guard (symbolp sym)))
  (mv-let (str rand)
          (random-string rand)
          (mv (intern-in-package-of-symbol str sym) rand)))

(defthm random-symbol-same-package-type
  (implies (symbolp sym)
           (symbolp (car (random-symbol-same-package sym r))))
  :rule-classes :type-prescription)

(defthmd random-symbol-same-package_expand-package
  (implies (symbolp sym)
           (equal (car (random-symbol-same-package sym r))
                  (intern-in-package-of-symbol
                   (symbol-name (car (random-symbol-same-package sym r)))
                   sym))))

(defthmd random-symbol-same-package_suck-package
  (implies (symbolp sym)
           (equal (intern-in-package-of-symbol
                   (symbol-name (car (random-symbol-same-package sym r)))
                   sym)
                  (car (random-symbol-same-package sym r)))))

(in-theory (disable random-symbol-same-package))


(defun random-keyword (rand)
  (declare (xargs :stobjs (rand)))
  (random-symbol-same-package :acl2-pkg-witness rand))

(defthm random-keyword-type
  (symbolp (car (random-keyword r)))
  :hints (("Goal" :use (:instance random-symbol-same-package_expand-package 
                        (sym :acl2-pkg-witness))))
  :rule-classes :type-prescription)

(local (defthm keyword-package-intern
         (implies (and (stringp str)
                       (keywordp key))
                  (equal (symbol-package-name
                          (intern-in-package-of-symbol str key))
                         "KEYWORD"))
         :hints (("Goal" :use (:instance keyword-package (x str) (y key))))))

(defthm random-keyword-keyword
  (equal (symbol-package-name (car (random-keyword r)))
         "KEYWORD")
  :hints (("Goal" :use (:instance random-symbol-same-package_expand-package 
                        (sym :acl2-pkg-witness)))))

(in-theory (disable random-keyword))






;some composites

(defun random-number (rand)
  (declare (xargs :stobjs (rand)))
  (mv-let (v rand)
          (random-index 4 rand)
          (case v
                (0 (random-natural rand))
                (1 (random-integer rand))
                (2 (random-rational rand))
                (t (random-complex rand)))))

(defthm random-number-type
  (acl2-numberp (car (random-number r)))
  :rule-classes :type-prescription)

(in-theory (disable random-number))


(defconst *acl2-exports-len*
  (len *acl2-exports*))
(defconst *common-lisp-symbols-from-main-lisp-package-len*
  (len *common-lisp-symbols-from-main-lisp-package*))

(with-output
 :off (prove observation event)
 (defun random-symbol (rand)
   (declare (xargs :stobjs (rand)))
   (mv-let (v rand)
           (random-index 8 rand)
           (case
            v
            (0 (random-boolean rand))
            (1 (random-element-len
                *acl2-exports*
                *acl2-exports-len*
                rand))
            (2 (random-element-len
                *common-lisp-symbols-from-main-lisp-package*
                *common-lisp-symbols-from-main-lisp-package-len*
                rand))
            (3 (random-keyword rand))
            (4 (random-symbol-same-package 'acl2::acl2-pkg-witness rand))
            (5 (random-symbol-same-package 'acl2-user::acl2-pkg-witness rand))
            (6 (random-symbol-same-package 'common-lisp::acl2-pkg-witness rand))
            (t (random-symbol-same-package 'acl2-pc::acl2-pkg-witness rand))))))

(local (defthm nth-symbol-list
         (implies (force (symbol-listp l))
                  (symbolp (nth i l)))
         :rule-classes :type-prescription))

(with-output
 :off (prove observation event)
 (defthm random-symbol-type
   (symbolp (car (random-symbol r)))
   :rule-classes :type-prescription))

(in-theory (disable random-symbol))



(with-output
 :off (prove observation event)
 (defun random-acl2-symbol (rand)
   (declare (xargs :stobjs (rand)))
   (mv-let (v rand)
           (random-index 5 rand) ; skew toward generated symbols
           (case
            v
            (0 (random-boolean rand))
            (1 (random-element-len
                *acl2-exports*
                *acl2-exports-len*
                rand))
            (2 (random-element-len
                *common-lisp-symbols-from-main-lisp-package*
                *common-lisp-symbols-from-main-lisp-package-len*
                rand))
            (t (random-symbol-same-package 'acl2::acl2-pkg-witness rand))))))

(with-output
 :off (prove observation event)
 (defthm random-acl2-symbol-type
   (symbolp (car (random-acl2-symbol r)))
   :hints (("Goal" :use (:instance random-symbol-same-package_expand-package 
                         (sym 'acl2::acl2-pkg-witness))))
   :rule-classes :type-prescription))

(in-theory (disable random-acl2-symbol))



(defun random-atom (rand)
  (declare (xargs :stobjs (rand)))
  (mv-let (v rand)
          (random-index 4 rand)
          (case
           v
           (0 (random-number rand))
           (1 (random-char rand))
           (2 (random-symbol rand))
           (t (random-string rand)))))

(defthm random-atom-type
  (atom (car (random-atom r)))
  :rule-classes :type-prescription)

(in-theory (disable random-atom))#|ACL2s-ToDo-Line|#








#|

(defconst *atomic-value-types*
  '(:atom
     :number
      :complex
       :rational
        :integer
         :natural

     :character

     :symbol
      :acl2-symbol
       :boolean
      :keyword
     
     :string))

(defun random-value (spec rand)
  (declare (xargs :stobjs (rand)))
  (if (consp spec)
    (if (symbolp (car spec))
      (case (car spec)
        (quote
         (if (and (consp (cdr spec))
                  (null (cddr spec)))
           (mv (cadr spec) rand)
           (mv (er hard? 'random-value "Invalid quoted value: ~x0" spec)
               rand)))
        (cons
         (if (and (consp (cdr spec))
                  (consp (cddr spec))
                  (null (cdddr spec)))
           (mv-let (carval rand)
                   (random-value (cadr spec) rand)
                   (mv-let (cdrval rand)
                           (random-value (caddr spec) rand)
                           (mv (cons carval cdrval) rand)))
           (mv (er hard? 'random-value "Cons should take two parameters, unlike in ~x0" spec)
               rand)))
        (listof
|#