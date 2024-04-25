#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t);$ACL2s-Preamble$|#

(in-package "DEFDATA")
(set-verify-guards-eagerness 2)

(include-book "random-state-basis1")
(include-book "builtin-combinators")
(include-book "number-enums-sampling")
;(include-book "num-list-fns") ;defines acl2-number-listp,pos-listp,naturals-listp

;=====================================================================;
; 
; by Peter Dillinger &  Dimitris Vardoulakis
; Last Major Updates: 7 February 2008
; Tweaked:  11 November 2008
; Tweaked:  24 November 2008 by harshrc
; Modified: 10 March 2012 by harshrc -- type declarations
; Modified: [2016-04-03 Sun] harshrc -- reduce bias to small random numbers
;=====================================================================;

(defun random-boolean (state)
  (declare (xargs :stobjs (state)))
  (mv-let (num state)
          (genrandom-state 2 state)
          (mv (= 1 num) state)))

(defthm random-boolean-type
  (booleanp (mv-nth 0 (random-boolean r)))
  :rule-classes :type-prescription)

(in-theory (disable random-boolean))


;generate naturals according to a pseudo-geometric distribution
;added strong type declarations for faster code

(defun random-natural-basemax1 (base maxdigits seed.)
  (declare (type (integer 1 16) base)
           (type (integer 0 19) maxdigits)
           (type (unsigned-byte 63) seed.)
           (xargs :guard (and (unsigned-byte-p 63 seed.)
                              (posp base)
                              (<= base 16) (> base 0) 
                              (natp maxdigits)
                              (< maxdigits 20) (>= maxdigits 0))))
  (if (zp maxdigits)
    (mv 0 seed.)
    (b* (((mv (the (integer 0 64) v) 
              (the (unsigned-byte 63) seed.))
          (genrandom-seed (acl2::*f 2 base) seed.)))
     (if (>= v base)
         (b* (((mv v2 seed.); can do better type information here TODO
                 (random-natural-basemax1 base 
                                         (1- maxdigits) seed.)))
             (mv (+ (- v base) 
                    (* base (nfix v2))) 
                 seed.))
      
       (mv v seed.)))))

(defun random-natural-seed/0.5 (seed.)
  (declare (type (unsigned-byte 63) seed.))
  (declare (xargs :guard (unsigned-byte-p 63 seed.)))
  (mbe :logic (if (unsigned-byte-p 63 seed.)
                    (random-natural-basemax1 10 6 seed.)
                  (random-natural-basemax1 10 6 1382728371)) ;random seed in random-state-basis1
       :exec  (random-natural-basemax1 10 6 seed.)))
      

(defun random-natural-basemax2 (base maxdigits seed.)
; less biased than random-natural-basemax1. rather than 0.5, use 0.25
  (declare (type (integer 1 16) base)
           (type (integer 0 20) maxdigits)
           (type (unsigned-byte 63) seed.)
           (xargs :guard (and (unsigned-byte-p 63 seed.)
                              (posp base)
                              (<= base 16) (> base 0) 
                              (natp maxdigits)
                              (< maxdigits 20) (>= maxdigits 0))))
  (if (zp maxdigits)
      (b* (((mv (the (integer 0 16) v) 
                (the (unsigned-byte 63) seed.))
            (genrandom-seed base seed.)))
        (mv v seed.))
    (b* (((mv (the (integer 0 64) v) 
              (the (unsigned-byte 63) seed.))
          (genrandom-seed (acl2::*f 4 base) seed.)))
     (if (>= v base)
         (b* (((mv v2 seed.); can do better type information here TODO
                 (random-natural-basemax2 base (1- maxdigits) seed.)))
             (mv (+ (- v base) (* base (nfix v2))) 
                 seed.))
      
       (mv v seed.)))))

(defun random-natural-seed/0.25 (seed.)
  (declare (type (unsigned-byte 63) seed.))
  (declare (xargs :guard (unsigned-byte-p 63 seed.)))
  (mbe :logic (if (unsigned-byte-p 63 seed.)
                    (random-natural-basemax2 10 6 seed.)
                  (random-natural-basemax2 10 6 1382728371)) ;random seed in random-state-basis1
       :exec  (random-natural-basemax2 10 6 seed.)))
      
;(defstub (random-natural-seed *) => (mv * *) :formals (seed.) :guard (unsigned-byte-p 63 seed.))
(encapsulate
 (((random-natural-seed *) => (mv * *) :formals (seed.) :guard (unsigned-byte-p 63 seed.)))
 (local (defun random-natural-seed (seed.)
          (declare (xargs :guard (unsigned-byte-p 63 seed.)))
          (mbe :logic (if (unsigned-byte-p 63 seed.)
                          (mv 0 seed.)
                        (mv 0 1382728371))
               :exec (mv 0 seed.))))

(defthm random-natural-seed-type-consp
  (consp (random-natural-seed r))
  :rule-classes (:type-prescription))

 (defthm random-natural-seed-type-car
  (implies (unsigned-byte-p 63 r)
           (natp (mv-nth 0 (random-natural-seed r))))
  :rule-classes (:type-prescription))

(defthm random-natural-seed-type-car-type
  (implies (natp r)
           (and (integerp (mv-nth 0 (random-natural-seed r)))
                (>= (mv-nth 0 (random-natural-seed r)) 0)))
  :rule-classes :type-prescription)

(defthm random-natural-seed-type-cadr
  (implies (unsigned-byte-p 63 r)
           (unsigned-byte-p 63 (mv-nth 1 (random-natural-seed r))))
  :rule-classes (:type-prescription))

(defthm random-natural-seed-type-cadr-linear
  (and (<= 0 (mv-nth 1 (random-natural-seed r)))
       (< (mv-nth 1 (random-natural-seed r)) 9223372036854775808))
  :rule-classes (:linear :tau-system))

(defthm random-natural-seed-type-cadr-type
  (and (integerp (mv-nth 1 (random-natural-seed r)))
       (>= (mv-nth 1 (random-natural-seed r)) 0))
  :rule-classes (:type-prescription))

 )


(defun random-small-natural-seed (seed.)
  (declare (type (unsigned-byte 63) seed.))
  (declare (xargs :guard (unsigned-byte-p 63 seed.)))
  (mbe :logic (if (unsigned-byte-p 63 seed.)
                  (random-natural-basemax1 10 3 seed.)
                (random-natural-basemax1 10 3 1382728371)) ;random seed in random-state-basis1
       :exec  (random-natural-basemax1 10 3 seed.)))

(defmacro random-index-seed (max seed.)
  `(genrandom-seed ,max ,seed.))


(defthm random-natural-basemax1-type-car
  (implies (and (posp b) (natp d) (natp r))
           (and (integerp (mv-nth 0 (random-natural-basemax1 b d r)))
                (>= (mv-nth 0 (random-natural-basemax1 b d r)) 0)))
  :rule-classes (:type-prescription))


(defthm random-natural-basemax1-type-cadr
  (implies (and (posp b) (natp d) (unsigned-byte-p 63 r))
           (unsigned-byte-p 63 (mv-nth 1 (random-natural-basemax1 b d r))))
  :rule-classes  :type-prescription)

(defthm random-natural-basemax1-type-cadr-0
  (implies (and (posp b) (natp d) (unsigned-byte-p 63 r))
           (and (<= 0 (mv-nth 1 (random-natural-basemax1 b d r)))
                (< (mv-nth 1 (random-natural-basemax1 b d r)) 9223372036854775808)))
  :rule-classes (:linear :type-prescription))

(defthm random-natural-basemax1-type-cadr-type
  (implies (and (posp b) (natp d) (natp r))
           (and (integerp (mv-nth 1 (random-natural-basemax1 b d r)))
                (>= (mv-nth 1 (random-natural-basemax1 b d r)) 0)))
  :rule-classes (:type-prescription))



(defthm random-natural-basemax2-type-car
  (implies (and (posp b) (natp d) (natp r))
           (and (integerp (mv-nth 0 (random-natural-basemax2 b d r)))
                (>= (mv-nth 0 (random-natural-basemax2 b d r)) 0)))
  :rule-classes (:type-prescription))


(defthm random-natural-basemax2-type-cadr
  (implies (and (posp b) (natp d) (unsigned-byte-p 63 r))
           (unsigned-byte-p 63 (mv-nth 1 (random-natural-basemax2 b d r))))
  :rule-classes  :type-prescription)

(defthm random-natural-basemax2-type-cadr-0
  (implies (and (posp b) (natp d) (unsigned-byte-p 63 r))
           (and (<= 0 (mv-nth 1 (random-natural-basemax2 b d r)))
                (< (mv-nth 1 (random-natural-basemax2 b d r)) 9223372036854775808)))
  :rule-classes (:linear :type-prescription))

(defthm random-natural-basemax2-type-cadr-type
  (implies (and (posp b) (natp d) (natp r))
           (and (integerp (mv-nth 1 (random-natural-basemax2 b d r)))
                (>= (mv-nth 1 (random-natural-basemax2 b d r)) 0)))
  :rule-classes (:type-prescription))







(defthm random-natural-seed-type/0.5-car
  (implies (unsigned-byte-p 63 r)
           (natp (mv-nth 0 (random-natural-seed/0.5 r))))
  :rule-classes (:type-prescription))

(defthm random-natural-seed-type/0.5-car-type
  (implies (natp r)
           (and (integerp (mv-nth 0 (random-natural-seed/0.5 r)))
                (>= (mv-nth 0 (random-natural-seed/0.5 r)) 0)))
  :rule-classes :type-prescription)

(defthm random-natural-seed-type/0.5-cadr
  (implies (unsigned-byte-p 63 r)
           (unsigned-byte-p 63 (mv-nth 1 (random-natural-seed/0.5 r))))
  :rule-classes (:type-prescription))

(defthm random-natural-seed-type/0.5-cadr-linear
;  (implies (unsigned-byte-p 63 r)
  (and (<= 0 (mv-nth 1 (random-natural-seed/0.5 r)))
       (< (mv-nth 1 (random-natural-seed/0.5 r)) 9223372036854775808))
;)
  :rule-classes (:linear :tau-system))

(defthm random-natural-seed-type/0.5-cadr-type
;  (implies (natp r)
           (and (integerp (mv-nth 1 (random-natural-seed/0.5 r)))
                (>= (mv-nth 1 (random-natural-seed/0.5 r)) 0))
;)
  :rule-classes (:type-prescription))







(defthm random-natural-seed-type/0.25-car
  (implies (unsigned-byte-p 63 r)
           (natp (mv-nth 0 (random-natural-seed/0.25 r))))
  :rule-classes (:type-prescription))

(defthm random-natural-seed-type/0.25-car-type
  (implies (natp r)
           (and (integerp (mv-nth 0 (random-natural-seed/0.25 r)))
                (>= (mv-nth 0 (random-natural-seed/0.25 r)) 0)))
  :rule-classes :type-prescription)

(defthm random-natural-seed-type/0.25-cadr
  (implies (unsigned-byte-p 63 r)
           (unsigned-byte-p 63 (mv-nth 1 (random-natural-seed/0.25 r))))
  :rule-classes (:type-prescription))

(defthm random-natural-seed-type/0.25-cadr-linear
;  (implies (unsigned-byte-p 63 r)
  (and (<= 0 (mv-nth 1 (random-natural-seed/0.25 r)))
       (< (mv-nth 1 (random-natural-seed/0.25 r)) 9223372036854775808))
;)
  :rule-classes (:linear :tau-system))

(defthm random-natural-seed-type/0.25-cadr-type
;  (implies (natp r)
           (and (integerp (mv-nth 1 (random-natural-seed/0.25 r)))
                (>= (mv-nth 1 (random-natural-seed/0.25 r)) 0))
;)
  :rule-classes (:type-prescription))


(defattach random-natural-seed random-natural-seed/0.25)
(in-theory (disable random-natural-basemax1
                    random-natural-seed/0.25
                    random-natural-seed/0.5
                    ))

(defun random-index-list-seed (k max seed.)
  (declare (type (unsigned-byte 63) seed.))
  (declare (xargs :verify-guards nil
                  :guard (unsigned-byte-p 63 seed.)))
  (if (zp k)
      (mv '() seed.)
    (b* (((mv rest seed.) (random-index-list-seed (1- k) max seed.))
         ((mv n1 seed.)   (if (zp max) (mv 0 seed.) (random-index-seed max seed.))))
      (mv (cons n1 rest) seed.))))

#|

There are lots of guard problems here. See below. 
On todo list for fixing.

(defun random-index-list-seed (k max seed.)
  (declare (type (unsigned-byte 63) seed.))
  (declare (xargs :verify-guards nil
                  :guard (and (natp k) (unsigned-byte-p 63 max) (unsigned-byte-p 63 seed.))))
  (if (zp k)
      (mv '() seed.)
    (b* (((mv rest seed.) (random-index-list-seed (1- k) max seed.))
         ((mv n1 seed.)   (if (zp max) (mv 0 seed.) (random-index-seed max seed.))))
      (mv (cons n1 rest) seed.))))

(in-theory (enable mv-nth))

(defthm random-index-seed-thm1
  (implies (and (posp k) (natp max) (unsigned-byte-p 63 seed.))
           (natp (caar (random-index-list-seed k max seed.)))))

(defthm random-index-seed-thm1
  (implies (and (posp k) (< k 1) (natp max) (unsigned-byte-p 63 seed.))
           (natp (cadar (random-index-list-seed k max seed.)))))

(verify-guards random-index-list-seed :guard-debug t )

|#

(defun random-natural-list-seed (k seed.)
  (declare (type (unsigned-byte 63) seed.))
  (declare (xargs :verify-guards nil
                  :guard (unsigned-byte-p 63 seed.)))
  (if (zp k)
      (mv '() seed.)
    (b* (((mv rest seed.) (random-natural-list-seed (1- k) seed.))
         ((mv n1 seed.)   (random-natural-seed seed.)))
      (mv (cons n1 rest) seed.))))

; pseudo-uniform rational between 0 and 1 (inclusive)
;optimize later (copied from below but simplified)
(defun random-probability-seed (seed.)
  (declare (type (unsigned-byte 63) seed.))
  (declare (xargs :verify-guards nil ;TODO
                  :guard (unsigned-byte-p 63 seed.)))
  (mbe :logic (if (unsigned-byte-p 63 seed.)
                  (mv-let (a seed.)
                          (random-natural-seed seed.)
                          ;; try to bias this to get more of small probabilities (close to 1)
                          (let ((denom (if (int= a 0)
                                           (1+ a)
                                         a)))
                            (mv-let (numer seed.)
                                    (genrandom-seed (1+ denom) seed.)
                                    (mv (/ numer denom) seed.))))
                (mv 0 seed.))
       :exec (mv-let (a seed.)
                     (random-natural-seed seed.)
                     (let ((denom (if (int= a 0)
                                           (1+ a)
                                         a)))
                       (mv-let (numer seed.)
                               (genrandom-seed (1+ denom) seed.)
                               (mv (/ numer denom) seed.))))))
                

;optimize later (copied from below)
(defun random-rational-between-seed (lo hi seed.)
  (declare (type (unsigned-byte 63) seed.))
  (declare (xargs :verify-guards nil
                  :guard (unsigned-byte-p 63 seed.)))
  (mv-let (p seed.)
          (random-probability-seed seed.)
          (mv (rfix (+ lo (* p (- hi lo)))) seed.)))


(defun random-integer-seed (seed.)
  (declare (type (unsigned-byte 63) seed.))
  (declare (xargs :guard (unsigned-byte-p 63 seed.)))
  (mv-let (num seed.)
          (genrandom-seed 2 seed.)
          (mv-let (nat seed.)
                  (random-natural-seed seed.)
                  (mv (if (int= num 0) nat (- nat))
                      seed.))))

(defun random-integer-between-seed (lo hi seed.)
  (declare (type (unsigned-byte 63) seed.)
           (type (signed-byte 62) lo)
           (type (signed-byte 62) hi))
  (declare (xargs :guard (and (unsigned-byte-p 63 seed.)
                              (integerp lo)
                              (integerp hi)
                              (signed-byte-p 62 lo)
                              (signed-byte-p 62 hi)
                              (natp (- hi lo)))))
  (mv-let (num seed.)
          (genrandom-seed (1+ (- hi lo)) seed.)
          (mv (+ lo num) seed.)))

(defun random-complex-rational-between-seed (lo hi seed.)
  (declare (xargs :verify-guards nil
                  :guard (unsigned-byte-p 63 seed.)))
  (declare (type (unsigned-byte 63) seed.))
  (b* (((mv rp seed.) (random-rational-between-seed (realpart lo) (realpart hi) seed.))
       ((mv ip seed.) (random-rational-between-seed (imagpart lo) (imagpart hi) seed.)))
    (mv (complex rp ip) seed.)))

(defun random-acl2-number-between-seed (lo hi seed.)
  (declare (xargs :verify-guards nil
                  :guard (unsigned-byte-p 63 seed.)))
  (b* (((mv choice seed.)
        (random-index-seed 6 seed.)))
    (case choice
          (0 (random-integer-between-seed lo hi seed.))
          (1 (random-rational-between-seed lo hi seed.))
          (5 (random-complex-rational-between-seed lo hi seed.))
          (t (random-integer-between-seed lo hi seed.)))))

(defun random-number-between-seed-fn (lo hi seed. type)
  (declare (xargs :verify-guards nil
                  :guard (unsigned-byte-p 63 seed.)))
  (case type
    (acl2s::integer (random-integer-between-seed lo hi seed.))
    (acl2s::rational (random-rational-between-seed lo hi seed.))
    (acl2s::complex-rational (random-complex-rational-between-seed lo hi seed.))
    (t (random-acl2-number-between-seed lo hi seed.))))

(defmacro random-number-between-seed (lo hi seed. &key type)
  `(random-number-between-seed-fn ,lo ,hi ,seed. (or ,type 'acl2s::acl2-number)))


#|
(defstub (sampling-dist-rec * *) => *
  :formals (min max)
  :guard (and (natp min) (posp max) (<= min max)))
|#
(logic)
(encapsulate
 (((sampling-dist-rec * *) => * :formals (min max) :guard (and (natp min) (posp max) (<= min max))))
 (local (defun sampling-dist-rec (min max)
          (declare (xargs :guard (and (natp min) (posp max) (<= min max))))
          (list min max))))

(defun sampling-dist-rec-builtin (min max)
  (declare (xargs :guard (and (natp min)
                              (posp max)
                              (<= min max))))
  (b* ((lo-1 (force-between *dist-lo1* min max))
       (hi-1 (force-between *dist-hi1* min max))
       (lo-2 (force-between *dist-lo2* min max))
       (hi-2 (force-between *dist-hi2* min max))
       (lo-3 (force-between *dist-lo3* min max))
       (hi-3 (force-between *dist-hi3* min max))
       (lo-4 (force-between *dist-lo4* min max))
       (hi-4 (force-between *dist-hi4* min max))
       (lo-5 (force-between *dist-lo5* min max))
       (hi-5 (force-between *dist-hi5* min max))
       (mid (floor (+ min max) 2))
       (mid-lo-1 (force-between (- mid hi-1) min max))
       (mid-hi-1 (force-between (+ mid hi-1) min max))
       (mid-lo-2 (force-between (- mid hi-2) min max))
       (mid-hi-2 (force-between (+ mid hi-2) min max))
       (mid-lo-3 (force-between (- mid hi-3) min max))
       (mid-hi-3 (force-between (+ mid hi-3) min max))
       (mid-lo-4 (force-between (- mid hi-4) min max))
       (mid-hi-4 (force-between (+ mid hi-4) min max))
       (mid-lo-5 (force-between (- mid hi-5) min max))
       (mid-hi-5 (force-between (+ mid hi-5) min max)))
    `((1 :eq ,min)
      (1 :eq ,max)
      (1 :eq ,mid)

      (4 :uniform ,lo-1 ,hi-1)
      (4 :uniform ,lo-2 ,hi-2)
      (4 :uniform ,lo-3 ,hi-3)
      (4 :uniform ,lo-4 ,hi-4)
      (4 :uniform ,lo-5 ,hi-5)

      (4 :uniform ,mid-lo-1 ,mid-hi-1)
      (4 :uniform ,mid-lo-2 ,mid-hi-2)
      (4 :uniform ,mid-lo-3 ,mid-hi-3)
      (4 :uniform ,mid-lo-4 ,mid-hi-4)
      (4 :uniform ,mid-lo-5 ,mid-hi-5)
      
      (5 :geometric :leq-bnd ,max ,min)
      (24 :geometric :geq-bnd ,min ,max)
      (14 :geometric :between ,min ,max)

      (14 :uniform ,min ,max))))

(defattach sampling-dist-rec sampling-dist-rec-builtin)
(include-book "switchnat")

(defun choose-size (min max seed.)
  (declare (type (unsigned-byte 63) seed.)
           (type (signed-byte 62) min)
           (type (signed-byte 62) max))
  (declare (xargs :verify-guards nil
                  :guard (and (unsigned-byte-p 63 seed.)
                              (natp min)
                              (natp max)
                              (signed-byte-p 62 min)
                              (signed-byte-p 62 max)
                              )))
  (b* ((ctx 'choose-size)
       ((mv idx (the (unsigned-byte 63) seed.))
        (defdata::random-index-seed 100 seed.))
       (sampling-dist (sampling-dist-rec min max))
       (weights (strip-cars sampling-dist))
       ((mv choice &) (defdata::weighted-switch-nat weights idx))
       (chosen (nth choice sampling-dist))
       (sp (cdr chosen))
       ((mv n (the (unsigned-byte 63) seed.))
        (random-small-natural-seed seed.))
       ((mv uniform-n (the (unsigned-byte 63) seed.))
        (defdata::random-integer-between-seed min max seed.))
       (size (case-match sp ;sampling type dispatch
               ((':eq x)                  x)
               ((':geometric ':around x) (geometric-int-around x n))
               ((':geometric ':leq x)    (geometric-int-leq x n))
               ((':geometric ':geq x)    (geometric-int-geq x n))
               ((':geometric ':around-bnd x lo hi) (geometric-int-around-bnd x lo hi n))
               ((':geometric ':leq-bnd x lo)       (geometric-int-leq-bnd x lo n))
               ((':geometric ':geq-bnd x hi)       (geometric-int-geq-bnd x hi n))
               ((':geometric ':between lo hi)      (geometric-int-between lo hi n))
               ((':uniform & &)         uniform-n)
               (& (er hard ctx "~| Unsupported case ~x0.~%" sp))))
       ;(- (cw  "~| Chosen size is ~x0~%" size))
       )
    (mv size (the (unsigned-byte 63) seed.))))
