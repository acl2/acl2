#|$ACL2s-Preamble$;
(ld "pkg.lsp")
(begin-book t);$ACL2s-Preamble$|#


(in-package "DEFDATA")
(set-verify-guards-eagerness 2)

(include-book "random-state-basis1")
;(include-book "num-list-fns") ;defines acl2-number-listp,pos-listp,naturals-listp

;=====================================================================;
; 
; by Peter Dillinger &  Dimitris Vardoulakis
; Last Major Updates: 7 February 2008
; Tweaked:  11 November 2008
; Tweaked:  24 November 2008 by harshrc
; Modified: 10 March 2012 by harshrc -- type declarations
;=====================================================================;

(defun random-boolean (state)
  (declare (xargs :stobjs (state)))
  (mv-let (num state)
          (genrandom-state 2 state)
          (mv (= 1 num) state)))

(defthm random-boolean-type
  (booleanp (car (random-boolean r)))
  :rule-classes :type-prescription)

(in-theory (disable random-boolean))


;generate naturals according to a pseudo-geometric distribution
;added strong type declarations for faster code

(defun random-natural-basemax1 (base maxdigits seed.)
  (declare (type (integer 1 16) base)
           (type (integer 0 9) maxdigits)
           (type (unsigned-byte 31) seed.)
           (xargs :guard (and (unsigned-byte-p 31 seed.)
                              (posp base)
                              (<= base 16) (> base 0) 
                              (natp maxdigits)
                              (< maxdigits 10) (>= maxdigits 0))))
  (if (zp maxdigits)
    (mv 0 seed.)
    (b* (((mv (the (integer 0 32) v) 
              (the (unsigned-byte 31) seed.))
          (genrandom (acl2::*f 2 base) seed.)))
     (if (>= v base)
         (b* (((mv v2 seed.); can do better type information here TODO
                 (random-natural-basemax1 base 
                                         (1- maxdigits) seed.)))
             (mv (+ (- v base) 
                    (* base (nfix v2))) 
                 seed.))
      
       (mv v seed.)))))

(defun random-natural-seed (seed.)
  (declare (type (unsigned-byte 31) seed.))
  (declare (xargs :guard (unsigned-byte-p 31 seed.)))
  (random-natural-basemax1 10 6 seed.))
      
(defthm random-natural-basemax1-type
  (implies (and (posp b) (natp d) (unsigned-byte-p 31 r))
           (natp (car (random-natural-basemax1 b d r))))
  
  :rule-classes (:rewrite :type-prescription))

(defthm random-natural-seed-type
  (implies (unsigned-byte-p 31 r)
           (natp (car (random-natural-seed r))))
  :rule-classes :type-prescription)
(in-theory (disable random-natural-basemax1
                    random-natural-seed))
(defun putseed (s state)
  (declare (xargs :stobjs (state)))
                  ;:guard (unsigned-byte-p 31 s)))
  ;(declare (type (unsigned-byte 31) s))
  (acl2::f-put-global 'random-seed s state))

(defun random-natural-basemax (base maxdigits state)
   (declare (type (integer 1 16) base)
            (type (integer 0 9) maxdigits)
            (xargs :stobjs (state)
                  :guard (and (posp base)
                              (<= base 16) (> base 0) 
                              (natp maxdigits)
                              (< maxdigits 10) (>= maxdigits 0))))
   (b* (((mv n seed.) (random-natural-basemax1 base maxdigits (getseed state)))
        (state (putseed seed. state)))
       (mv n state)))
                   
;;pseudo-geometric distribution
(defun random-natural (state)
  (declare (xargs :stobjs (state)))
  (random-natural-basemax 10 6 state))


;;pseudo-geometric distribution but smaller numbers
(defun random-small-natural (state)
  (declare (xargs :stobjs (state)))
  (random-natural-basemax 10 3 state))


;;added to be consistent with naming of the types
;; Type name = foo
;; Type predicate = foop
;; Type enum = nth-foo
;; Random generator = random-foo
(defun random-nat (state)
  (declare (xargs :stobjs (state)))
  (random-natural-basemax 10 6 state))

(defun random-length (state)
  (declare (xargs :stobjs (state)))
  (random-natural-basemax 4 2 state))

;create small lists upto length 4
(defun random-small-length (state)
  (declare (xargs :stobjs (state)))
  (random-natural-basemax 2 2 state))

(defthm random-natural-basemax-type
  (implies (and (posp b) (natp d))
  (natp (car (random-natural-basemax b d r))))
  :rule-classes :type-prescription)

(defthm random-natural-type
  (natp (car (random-natural r)))
  :rule-classes :type-prescription)

(defthm random-nat-type
  (natp (car (random-nat r)))
  :rule-classes :type-prescription)

(defthm random-length-type
  (natp (car (random-length r)))
  :rule-classes :type-prescription)

(defthm random-small-length-type
  (natp (car (random-small-length r)))
  :rule-classes :type-prescription)

(in-theory (disable random-small-length))
(in-theory (disable random-natural-basemax
                    random-natural
                    random-nat
                    random-length))




; generate indices uniformly within a specified length 
(defun random-index (len state)
  (declare (type (unsigned-byte 29) len)
           (xargs :stobjs (state)
                  :guard (posp len)))
  (genrandom-state len state))

(defun random-elem (lst state)
  (declare (xargs :stobjs (state)
                  :guard (and (true-listp lst)
                              (< (len lst) (expt 2 29)))))
  (cond ((endp lst) (value nil))
        ((endp (cdr lst)) (value (car lst)))
        (t
         (mv-let (ind state)
                 (random-index (len lst) state)
                 (value (nth ind lst))))))
        
             
;generate integers according to a pseudo-geometric distribution
(defun random-integer (state)
  (declare (xargs :stobjs (state)))
  (mv-let (sign state)
          (random-boolean state)
          (mv-let (nat state)
                  (random-natural state)
                  (mv (if sign nat (- nat))
                      state))))

(defthm random-integer-type
  (integerp (car (random-integer r)))
  :rule-classes :type-prescription)

(in-theory (disable random-integer))#|ACL2s-ToDo-Line|#


#| start commenting out code that is right now unnecessary for random-testing, refactor this later into a sep file
;or generate integers with a uniform distribution, between i & j (incl.)
(defun random-int-between (i j state)
  (declare (xargs :stobjs (state)
                  :guard (and (integerp i)
                              (integerp j))))
  (let ((low (ifix (min i j)))
        (high (ifix (max i j))))
    (mv-let
     (num state)
     (genrandom (1+ (- high low)) state)
     (mv (+ low num) state))))

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
(defun random-rational (state)
  (declare (xargs :stobjs (state)))
  (mv-let (numer state)
          (random-integer state)
          (mv-let (denom-1 state)
                  (random-natural state)
                  (mv (/ numer
                         (+ 1 denom-1))
                      state))))

(defthm random-rational-type
  (rationalp (car (random-rational r)))
  :rule-classes :type-prescription)

(in-theory (disable random-rational))


; pseudo-uniform rational between 0 and 1 (inclusive)
(defun random-probability (state)
  (declare (xargs :stobjs (state)))
  (mv-let (a state)
          (random-natural state)
          (mv-let (b state)
                  (random-natural state)
                  (let ((denom (* (1+ a) (1+ b))))
                    (mv-let (numer state)
                            (genrandom (1+ denom) state)
                            (mv (/ numer denom) state))))))

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
(defun random-rational-between (x y state)
  (declare (xargs :stobjs (state)
                  :guard (and (rationalp x)
                              (rationalp y))))
  (mv-let (p state)
          (random-probability state)
          (mv (rfix
               (if (< x y)
                 (+ x (* p (- y x)))
                 (+ y (* p (- x y)))))
              state)))

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
(defun random-nonzero-integer (state)
  (declare (xargs :stobjs (state)))
  (mv-let (sign state)
          (random-boolean state)
          (mv-let (nat state)
                  (random-natural state)
                  (mv (if sign (+ 1 nat) (- -1 nat))
                      state))))

(defthm random-nonzero-integer-type
  (and (integerp (car (random-nonzero-integer r)))
       (not (equal (car (random-nonzero-integer r)) 0)))
  :rule-classes :type-prescription)

(in-theory (disable random-nonzero-integer))

;;--added by harshrc
;;--generate positive integers according to a pseudo-geometric distribution
(defun random-pos (state)
  (declare (xargs :stobjs (state)))
  (mv-let (nat state)
          (random-natural state)
          (mv (+ 1 nat) state)))

(defthm random-pos-type
  (posp (car (random-pos r)))
  :rule-classes :type-prescription)

(in-theory (disable random-pos))



; generate a signed rational with pseudo-geometric numerator & denominator 
(defun random-nonzero-rational (state)
  (declare (xargs :stobjs (state)))
  (mv-let (numer state)
          (random-nonzero-integer state)
          (mv-let (denom-1 state)
                  (random-natural state)
                  (mv (/ numer
                         (+ 1 denom-1))
                      state))))

(defthm random-nonzero-rational-type
  (and (rationalp (car (random-nonzero-rational r)))
       (not (equal (car (random-nonzero-rational r)) 0)))
  :rule-classes :type-prescription)

(in-theory (disable random-nonzero-rational))


; generate a (strictly) complex number from rationals
(defun random-complex (state)
  (declare (xargs :stobjs (state)))
  (mv-let (rpart state)
          (random-rational state)
          (mv-let (ipart state)
                  (random-nonzero-rational state)
                  (mv (complex rpart ipart) state))))

(defthm random-complex-type
  (complex-rationalp (car (random-complex r)))
  :rule-classes :type-prescription)

(in-theory (disable random-complex))



(defmacro random-element (lst rand-state)
  `(mv-let (random-element-macro-idx state)
           (random-index (length ,lst) ,rand-state)
           (mv (nth random-element-macro-idx ,lst) state)))

(defmacro random-element-len (lst len rand-state)
  `(if (mbt (<= ,len (len ,lst)))
     (mv-let (random-element-macro-idx state)
             (random-index ,len ,rand-state)
             (mv (nth random-element-macro-idx ,lst) state))
     (mv (car ,lst) state)))



(defconst *standard-chars-len*
  (len *standard-chars*))

;;--slight modification of name char to character --harshrc
(defun random-character (state)
  (declare (xargs :stobjs (state)))
  (random-element-len *standard-chars*
                      *standard-chars-len*
                      state))

(defthm random-character-type
  (characterp (car (random-character r)))
  :rule-classes :type-prescription)

(in-theory (disable random-character))

(defun random-character-list-len (len state)
  (declare (xargs :stobjs (state)
                  :guard (natp len)))
  (if (zp len)
    (mv nil state)
    (mv-let (elem state)
            (random-character state)
            (mv-let (lst state)
                    (random-character-list-len (1- len) state)
                    (mv (cons elem lst) state)))))

(defthm random-character-list-len-type
  (character-listp (car (random-character-list-len l r)))
  :rule-classes :type-prescription)

(in-theory (disable random-character-list-len))

(defun random-character-list (state)
  (declare (xargs :stobjs (state)))
  (mv-let (len state)
          (random-length state)
          (random-character-list-len len state)))

(defthm random-character-list-type
  (character-listp (car (random-character-list r)))
  :rule-classes :type-prescription)

(in-theory (disable random-character-list))


(defun random-string-len (len state)
  (declare (xargs :stobjs (state)
                  :guard (natp len)))
  (mv-let (lst state)
          (random-character-list-len len state)
          (mv (coerce lst 'string) state)))

(defthm random-string-len-type
  (stringp (car (random-string-len l r)))
  :rule-classes :type-prescription)

(in-theory (disable random-string-len))


;generate a random string of pseudogeometric length
(defun random-string (state)
  (declare (xargs :stobjs (state)))
  (mv-let (len state)
          (random-length state)
          (random-string-len len state)))

(defthm random-string-type
  (stringp (car (random-string r)))
  :rule-classes :type-prescription)

(in-theory (disable random-string))


;generate a random symbol of pseudogeometric length
(defun random-symbol-same-package (sym state)
  (declare (xargs :stobjs (state)
                  :guard (symbolp sym)))
  (mv-let (str state)
          (random-string state)
          (mv (intern-in-package-of-symbol str sym) state)))

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


(defun random-keyword (state)
  (declare (xargs :stobjs (state)))
  (random-symbol-same-package :acl2-pkg-witness state))

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

(defun random-acl2-number (state)
  (declare (xargs :stobjs (state)))
  (mv-let (v state)
          (random-index 4 state)
          (case v
                (0 (random-natural state))
                (1 (random-integer state))
                (2 (random-rational state))
                (t (random-complex state)))))

(defthm random-acl2-number-type
  (acl2-numberp (car (random-acl2-number r)))
  :rule-classes :type-prescription)

(in-theory (disable random-acl2-number))


(defconst *acl2-exports-len*
  (len *acl2-exports*))
(defconst *common-lisp-symbols-from-main-lisp-package-len*
  (len *common-lisp-symbols-from-main-lisp-package*))

(with-output
 :off (prove observation event)
 (defun random-symbol (state)
   (declare (xargs :stobjs (state)))
   (mv-let (v state)
           (random-index 8 state)
           (case
            v
            (0 (random-boolean state))
            (1 (random-element-len
                *acl2-exports*
                *acl2-exports-len*
                state))
            (2 (random-element-len
                *common-lisp-symbols-from-main-lisp-package*
                *common-lisp-symbols-from-main-lisp-package-len*
                state))
            (3 (random-keyword state))
            (4 (random-symbol-same-package 'acl2::acl2-pkg-witness state))
            (5 (random-symbol-same-package 'acl2-user::acl2-pkg-witness state))
            (6 (random-symbol-same-package 'common-lisp::acl2-pkg-witness state))
            (t (random-symbol-same-package 'acl2-pc::acl2-pkg-witness state))))))

(encapsulate nil
  (local (defthm nth-symbol-list
           (implies (force (symbol-listp l))
                    (symbolp (nth i l)))))
  
  (with-output
   :off (prove observation event)
   (defthm random-symbol-type
     (symbolp (car (random-symbol r)))
     :rule-classes :type-prescription)))

(in-theory (disable random-symbol))



(with-output
 :off (prove observation event)
 (defun random-acl2-symbol (state)
   (declare (xargs :stobjs (state)))
   (mv-let (v state)
           (random-index 5 state) ; skew toward generated symbols
           (case
            v
            (0 (random-boolean state))
            (1 (random-element-len
                *acl2-exports*
                *acl2-exports-len*
                state))
            (2 (random-element-len
                *common-lisp-symbols-from-main-lisp-package*
                *common-lisp-symbols-from-main-lisp-package-len*
                state))
            (t (random-symbol-same-package 'acl2::acl2-pkg-witness state))))))

(encapsulate nil
  (local (defthm nth-symbol-list
           (implies (force (symbol-listp l))
                    (symbolp (nth i l)))))
  
  (with-output
   :off (prove observation event)
   (defthm random-acl2-symbol-type
     (symbolp (car (random-acl2-symbol r)))
     :hints (("Goal" :use (:instance random-symbol-same-package_expand-package 
                           (sym 'acl2::acl2-pkg-witness))))
     :rule-classes :type-prescription)))

(in-theory (disable random-acl2-symbol))



(defun random-atom (state)
  (declare (xargs :stobjs (state)))
  (mv-let (v state)
          (random-index 4 state)
          (case
           v
           (0 (random-acl2-number state))
           (1 (random-character state))
           (2 (random-symbol state))
           (t (random-string state)))))

(defthm random-atom-type
  (atom (car (random-atom r)))
  :rule-classes :type-prescription)

(in-theory (disable random-atom))

;;---------------------------------------------------------------------------
;;---------------------------------------------------------------------------
;;--modifications by harshrc
;;--add random-<atom>-list for each atom type of pseudo-geometric length upto 4
;;--generate true list of <atom> (<atom recognizer> <atom type-set>)



;;--generate true list of integers (integerp 11)
(defun random-integer-list-len (len state)
  (declare (xargs :stobjs (state)
                  :guard (natp len)))
  (if (zp len)
    (mv nil state)
    (mv-let (elem state)
            (random-integer state)
            (mv-let (lst state)
                    (random-integer-list-len (1- len) state)
                    (mv (cons elem lst) state)))))

(defthm random-integer-list-len-type
  (integer-listp (car (random-integer-list-len l r)))
  :rule-classes :type-prescription)

(in-theory (disable random-integer-list-len))

(defun random-integer-list (state)
  (declare (xargs :stobjs (state)))
  (mv-let (len state)
          (random-small-length state)
          (random-integer-list-len len state)))

(defthm random-integer-list-type
  (integer-listp (car (random-integer-list r)))
  :rule-classes :type-prescription)

(in-theory (disable random-integer-list))

;;--generate true list of positive integers  (posp 2)
(defun random-pos-list-len (len state)
  (declare (xargs :stobjs (state)
                  :guard (natp len)))
  (if (zp len)
    (mv nil state)
    (mv-let (elem state)
            (random-pos state)
            (mv-let (lst state)
                    (random-pos-list-len (1- len) state)
                    (mv (cons elem lst) state)))))

(defun pos-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l) (equal l nil))
        (t (and (posp (car l))
                (pos-listp (cdr l))))))


(defthm random-pos-list-len-type
  (pos-listp (car (random-pos-list-len l r)))
  :rule-classes :type-prescription)

(in-theory (disable random-pos-list-len))

(defun random-pos-list (state)
  (declare (xargs :stobjs (state)))
  (mv-let (len state)
          (random-small-length state)
          (random-pos-list-len len state)))

(defthm random-pos-list-type
  (pos-listp (car (random-pos-list r)))
  :rule-classes :type-prescription)

(in-theory (disable random-pos-list))




;;--generate true list of natural (natp 3)
(defun random-nat-list-len (len state)
  (declare (xargs :stobjs (state)
                  :guard (natp len)))
  (if (zp len)
    (mv nil state)
    (mv-let (elem state)
            (random-nat state)
            (mv-let (lst state)
                    (random-nat-list-len (1- len) state)
                    (mv (cons elem lst) state)))))
;;--just to be consistent with the naming
;;--naturalp is otherwise same as natp
;;--redefined in several books in acl2-sources, so commented out.
(local
(defun naturalp (x)
  (declare (xargs :guard t :mode :logic))
  (and (integerp x) (<= 0 x)))
)

(defun naturals-listp (x)
  (if (atom x)
    (null x)
    (and (natp (car x))
         (naturals-listp (cdr x)))))



(defthm random-nat-list-len-type
  (naturals-listp (car (random-nat-list-len l r)))
  :rule-classes :type-prescription)

(in-theory (disable random-nat-list-len))

(defun random-nat-list (state)
  (declare (xargs :stobjs (state)))
  (mv-let (len state)
          (random-small-length state)
          (random-nat-list-len len state)))

(defthm random-nat-list-type
  (naturals-listp (car (random-nat-list r)))
  :rule-classes :type-prescription)

(in-theory (disable random-nat-list))


;;--generate true list of rational (rationalp 31)
(defun random-rational-list-len (len state)
  (declare (xargs :stobjs (state)
                  :guard (natp len)))
  (if (zp len)
    (mv nil state)
    (mv-let (elem state)
            (random-rational state)
            (mv-let (lst state)
                    (random-rational-list-len (1- len) state)
                    (mv (cons elem lst) state)))))

(defthm random-rational-list-len-type
  (rational-listp (car (random-rational-list-len l r)))
  :rule-classes :type-prescription)

(in-theory (disable random-rational-list-len))

(defun random-rational-list (state)
  (declare (xargs :stobjs (state)))
  (mv-let (len state)
          (random-small-length state)
          (random-rational-list-len len state)))

(defthm random-rational-list-type
  (rational-listp (car (random-rational-list r)))
  :rule-classes :type-prescription)

(in-theory (disable random-rational-list))


;;--generate true list of complex  (complex-rationalp 32)
(defun random-complex-list-len (len state)
  (declare (xargs :stobjs (state)
                  :guard (natp len)))
  (if (zp len)
    (mv nil state)
    (mv-let (elem state)
            (random-complex state)
            (mv-let (lst state)
                    (random-complex-list-len (1- len) state)
                    (mv (cons elem lst) state)))))

(defun complex-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l) (equal l nil))
        (t (and (complex-rationalp (car l))
                (complex-listp (cdr l))))))

(defthm random-complex-list-len-type
  (complex-listp (car (random-complex-list-len l r)))
  :rule-classes :type-prescription)

(in-theory (disable random-complex-list-len))

(defun random-complex-list (state)
  (declare (xargs :stobjs (state)))
  (mv-let (len state)
          (random-small-length state)
          (random-complex-list-len len state)))

(defthm random-complex-list-type
  (complex-listp (car (random-complex-list r)))
  :rule-classes :type-prescription)

(in-theory (disable random-complex-list))



;;--generate true list of acl2-number (acl2-numberp 63)
(defun random-acl2-number-list-len (len state)
  (declare (xargs :stobjs (state)
                  :guard (natp len)))
  (if (zp len)
    (mv nil state)
    (mv-let (elem state)
            (random-acl2-number state)
            (mv-let (lst state)
                    (random-acl2-number-list-len (1- len) state)
                    (mv (cons elem lst) state)))))

(defun acl2-number-listp (x)
  (declare (xargs :guard t))
  (IF (ATOM X)
    (NULL X)
    (AND (ACL2-NUMBERP (CAR X))
         (ACL2-NUMBER-LISTP (CDR X)))))

(defthm random-acl2-number-list-len-type
  (acl2-number-listp (car (random-acl2-number-list-len l r)))
  :rule-classes :type-prescription)

(in-theory (disable random-acl2-number-list-len))

(defun random-acl2-number-list (state)
  (declare (xargs :stobjs (state)))
  (mv-let (len state)
          (random-small-length state)
          (random-acl2-number-list-len len state)))

(defthm random-acl2-number-list-type
  (acl2-number-listp (car (random-acl2-number-list r)))
  :rule-classes :type-prescription)

(in-theory (disable random-acl2-number-list))



;;--generate true list of boolean (booleanp 192)
(defun random-boolean-list-len (len state)
  (declare (xargs :stobjs (state)
                  :guard (natp len)))
  (if (zp len)
    (mv nil state)
    (mv-let (elem state)
            (random-boolean state)
            (mv-let (lst state)
                    (random-boolean-list-len (1- len) state)
                    (mv (cons elem lst) state)))))

(defthm random-boolean-list-len-type
  (boolean-listp (car (random-boolean-list-len l r)))
  :rule-classes :type-prescription)

(in-theory (disable random-boolean-list-len))

(defun random-boolean-list (state)
  (declare (xargs :stobjs (state)))
  (mv-let (len state)
          (random-small-length state)
          (random-boolean-list-len len state)))

(defthm random-boolean-list-type
  (boolean-listp (car (random-boolean-list r)))
  :rule-classes :type-prescription)

(in-theory (disable random-boolean-list))

;;--generate true list of symbol   (symbolp 448)
(defun random-symbol-list-len (len state)
  (declare (xargs :stobjs (state)
                  :guard (natp len)))
  (if (zp len)
    (mv nil state)
    (mv-let (elem state)
            (random-symbol state)
            (mv-let (lst state)
                    (random-symbol-list-len (1- len) state)
                    (mv (cons elem lst) state)))))

(defthm random-symbol-list-len-type
  (symbol-listp (car (random-symbol-list-len l r)))
  :rule-classes :type-prescription)

(in-theory (disable random-symbol-list-len))

(defun random-symbol-list (state)
  (declare (xargs :stobjs (state)))
  (mv-let (len state)
          (random-small-length state)
          (random-symbol-list-len len state)))

(defthm random-symbol-list-type
  (symbol-listp (car (random-symbol-list r)))
  :rule-classes :type-prescription)

(in-theory (disable random-symbol-list))


;;--generate true list of string   (characterp 4096)
(defun random-string-list-len (len state)
  (declare (xargs :stobjs (state)
                  :guard (natp len)))
  (if (zp len)
    (mv nil state)
    (mv-let (elem state)
            (random-string state)
            (mv-let (lst state)
                    (random-string-list-len (1- len) state)
                    (mv (cons elem lst) state)))))

(defthm random-string-list-len-type
  (string-listp (car (random-string-list-len l r)))
  :rule-classes :type-prescription)

(in-theory (disable random-string-list-len))

(defun random-string-list (state)
  (declare (xargs :stobjs (state)))
  (mv-let (len state)
          (random-small-length state)
          (random-string-list-len len state)))

(defthm random-string-list-type
  (string-listp (car (random-string-list r)))
  :rule-classes :type-prescription)

(in-theory (disable random-string-list))


;;--generate true list of atom   (atom -1537)
(defun random-atom-list-len (len state)
  (declare (xargs :stobjs (state)
                  :guard (natp len)))
  (if (zp len)
    (mv nil state)
    (mv-let (elem state)
            (random-atom state)
            (mv-let (lst state)
                    (random-atom-list-len (1- len) state)
                    (mv (cons elem lst) state)))))

(defthm random-atom-list-len-type
  (atom-listp (car (random-atom-list-len l r)))
  :rule-classes :type-prescription)


(defun random-atom-list (state)
  (declare (xargs :stobjs (state)))
  (mv-let (len state)
          (random-small-length state)
          (random-atom-list-len len state)))

(defthm random-atom-list-type
  (atom-listp (car (random-atom-list r)))
  :rule-classes :type-prescription)

(in-theory (disable random-atom-list-len
                    random-atom-list))

(defun random-atom-cons-dep (dep state)
  (declare (xargs :stobjs (state)
                  :guard (natp dep)))
  (if (zp dep)
    (random-atom state)
    (mv-let (cr state)
            (random-atom-cons-dep (1- dep) state)
            (mv-let (cdr state)
                    (random-atom-cons-dep (1- dep) state)
                    (mv (cons cr cdr) state)))))
#|
(defthm random-atom-cons-dep-type
  (consp (car (random-atom-cons-dep d r)))
  :rule-classes :type-prescription)
|#

(defun random-atom-cons (state)
  (declare (xargs :stobjs (state)))
  (mv-let (dep state)
          (random-small-length state)
          (random-atom-cons-dep (1+ dep) state)))
#|
(defthm random-atom-cons-type
  (consp (car (random-atom-cons r)))
  :rule-classes :type-prescription)
|#
(in-theory (disable random-atom-cons-dep
                    random-atom-cons))

(defun anyp (x)
  (declare (xargs :mode :logic
                  :guard t)
           (ignore x))
  t)

(defun random-any (state)
  (declare (xargs :stobjs (state)))
  (mv-let (v state)
          (random-index 10 state);skew towards atoms
          (case
           v
           (0 (random-atom-cons state))
           (1 (random-atom-list state))
           (t (random-atom state)))))
(defthm random-any-type
  (anyp (car (random-any r)))
  :rule-classes :type-prescription)

(in-theory (disable random-any))

(defun random-true-list-len (len state)
  (declare (xargs :stobjs (state)
                  :guard (natp len)
                  :measure len))
  (if (zp len)
    (mv nil state)
    (mv-let (elem state)
            (random-any state)
            (mv-let (lst state)
                    (random-atom-list-len (1- len) state)
                    (mv (cons elem lst) state)))))
#|
(defthm random-true-list-len-type
  (true-listp (car (random-true-list-len l r)))
  :rule-classes :type-prescription)
|#

(defun random-true-list (state)
  (declare (xargs :stobjs (state)))
  (mv-let (len state)
          (random-small-length state)
          (random-true-list-len len state)))
#|
(defthm random-true-list-type
  (true-listp (car (random-true-list r)))
  :rule-classes :type-prescription)
|#
(in-theory (disable random-true-list-len
                    random-true-list))

(defun random-cons-dep (dep1 dep2 state)
  (declare (xargs :stobjs (state)
                  :guard (and (natp dep1)
                              (natp dep2))))
  (if (or (zp dep1) (zp dep2))
    (random-any state)
    (mv-let (cr state)
            (random-atom-cons-dep (floor dep1 2) state)
            (mv-let (cdr state)
                    (random-atom-cons-dep (1- dep2) state)
                    (mv (cons cr cdr) state)))))


(defun random-cons (state)
  (declare (xargs :stobjs (state)))
  (mv-let (dep1 state)
          (random-small-length state)
          (mv-let (dep2 state)
                  (random-small-length state)
                  (random-cons-dep (1+ dep1) (1+ dep2) state))))

(defthm random-cons-type
  (consp (car (random-cons r)))
  :rule-classes :type-prescription)

(in-theory (disable random-cons-dep 
                    random-cons))

|# ;end commenting of all this code, refactor it into a seperate file later.


#|
(defun random-key-pair (key state)
  (declare (xargs :stobjs (state)))
  (mv-let (cdr state)
          (random-any state)
          (mv (cons key cdr) state))) 
;;random acons with keys as symbols (can it be parametrized without using macros?)
(defun random-acons-dep (dep state)
  (declare (xargs :stobjs (state)
                  :guard (natp dep)))
  (if (zp dep)
    (mv-let (key state)
            (random-symbol state)
            (random-key-pair key state))
    (mv-let (cr state)
            (random-acons-dep (1- dep) state)
            (mv-let (cdr state)
                    (random-acons-dep (1- dep) state)
                    (mv (cons cr cdr) state)))))

;;beware this function sometimes produces huge aconses. CHECK! exponential length..                  
(defun random-acons (state)
  (declare (xargs :stobjs (state)))
  (mv-let (dep state)
          (random-small-length state)
          (random-acons-dep (1+ dep) state)))

(defthm random-acons-type
  (aconsp (car (random-acons r)))
  :rule-classes :type-prescription)

(in-theory (disable random-acons))
|#

;;---------------------------------------------------------------------------
;;---------------------------------------------------------------------------


#|

(defun test-n-atoms (n state)
  (declare (xargs :stobjs (state)
                  :guard (natp n)))
  (if (zp n)
    (value t)
    (mv-let (a state)
            (random-atom state)
            (if (consp a)
              (value nil)
              (test-n-atoms (1- n) state)))))

(time$ (test-n-atoms 100000 state))

; SBCL, basis1
; (time$ (test-n-atoms 100000 state))
; 0.69 sec

; SBCL, basis2
; (time$ (test-n-atoms 100000 state))
; 0.60 sec

; SBCL, basis3
; (time$ (test-n-atoms 100000 state))
; 0.45 sec


;|#





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

(defun random-value (spec state)
  (declare (xargs :stobjs (state)))
  (if (consp spec)
    (if (symbolp (car spec))
      (case (car spec)
        (quote
         (if (and (consp (cdr spec))
                  (null (cddr spec)))
           (mv (cadr spec) state)
           (mv (er hard? 'random-value "Invalid quoted value: ~x0" spec)
               state)))
        (cons
         (if (and (consp (cdr spec))
                  (consp (cddr spec))
                  (null (cdddr spec)))
           (mv-let (carval state)
                   (random-value (cadr spec) state)
                   (mv-let (cdrval state)
                           (random-value (caddr spec) state)
                           (mv (cons carval cdrval) state)))
           (mv (er hard? 'random-value "Cons should take two parameters, unlike in ~x0" spec)
               state)))
        (listof
|#