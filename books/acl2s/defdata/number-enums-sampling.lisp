#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t);$ACL2s-Preamble$|#

(in-package "ACL2S")
(set-verify-guards-eagerness 2)

(include-book "acl2s/utilities" :dir :system)
(include-book "splitnat")
(include-book "switchnat")

;-------- define some enumerators --------;

(defun nth-nat-builtin (n)
  (declare (xargs :guard (natp n)))
  n)

(defun nat-index (n)
  (declare (xargs :guard (natp n)))
  n)

#|
(defthm nth-nat-index
  (equal (nat-index (nth-nat n))
         n))

(defthm nat-index-nth
  (equal (nth-nat (nat-index n))
         n))
|#

(defexec nth-pos-builtin (n)
  (declare (xargs :guard (natp n)))
  (mbe :logic
       (if (natp n)
         (1+ n)
         n)
       :exec (1+ n)))

(defthm nth-pos-builtin-is-posp
  (implies (natp x)
           (posp (nth-pos-builtin x)))
  :rule-classes (:rewrite :type-prescription))

(defexec pos-index (i)
  (declare (xargs :guard (posp i)))
  (mbe :logic
       (if (posp i)
         (1- i)
         i)
       :exec (1- i)))

#|
(defthm nth-pos-index
  (equal (pos-index (nth-pos n))
         n))

(defthm pos-index-nth
  (implies (and (integerp i)
                (>= i 1))
           (equal (nth-pos (pos-index i))
                  i)))
|#

#|
(defun pos-multiple-of-threep (v)
  (if (posp v)
    (equal 0 (mod v 3))
    nil)) 

(defun nth-pos-multiple-of-three (n)
 (if (natp n) 
   (* 3 (1+ n))
   3))

(defun pos-multiple-of-three-index (i)
  (if (pos-multiple-of-threep i)
         (1- (floor i 3))
         i))

|#

(defun negp (x)
  (declare (xargs :guard t))
  (and (integerp x) 
       (< x 0)))

(defun nth-neg-builtin (n)
  (declare (xargs :guard (natp n)))
  (- -1 n))

(defun non-pos-integerp (x)
  (declare (xargs :guard t))
  (and (integerp x) 
       (<= x 0)))

(defun nth-non-pos-integer-builtin (n)
  (declare (xargs :guard (natp n)))
  (- n))

(defun non-0-integerp (x)
  (declare (xargs :guard t))
  (and (integerp x) 
       (/= x 0)))

(defun nth-non-0-integer-builtin (n)
  (declare (xargs :guard (natp n)))
  (if (evenp n)
      (1+ (/ n 2))
    (- (/ (1+ n) 2))))

;;integers
(defun nth-integer-builtin (n)
  (declare (xargs :guard (natp n)))
  (let* (;(n (mod n 1000))
         (mag (floor n 2))
        (sign (rem n 2)))
    (if (= sign 0)
      mag
      (- -1 mag))))

(def-const *init-hash-num* 
  (floor (* 61803095516164791237/100000000000000000000 (expt 2 64)) 1))

(defun simple-hash (n range)
  (declare (xargs :guard (and (natp n) (natp range))))
  (let ((x (* n *init-hash-num*)))
    (mod x (1+ range))))

(defun nth-integer-between (n lo hi)
  (declare (xargs :guard (and (natp n)
                              (integerp lo)
                              (integerp hi)
                              (<= lo hi))))
  (let ((range (- hi lo)))
    (+ lo (simple-hash n range))))

(local (include-book "arithmetic-5/top" :dir :system))
       
(defun bitsize-aux (n acc)
  (declare (xargs :guard (and (natp n) (posp acc))))
  (if (and (integerp n) (> n 1))
      (bitsize-aux (floor (nfix n) 2) (1+ acc))
    acc))

(defthm bitsize-aux-posp
  (implies (and (natp n) (posp acc))
           (posp (bitsize-aux n acc))))

(defun bitsize (n)
  (declare (xargs :guard (natp n)))
  (bitsize-aux n 1))

; (bitsize 0)
; (bitsize 1)
; (bitsize 63)
; (bitsize 64)

(defun rounds (lo hi stop-bits)
  (declare (xargs :guard (and (integerp lo)
                              (integerp hi)
                              (<= lo hi)
                              (posp stop-bits))))
  (let* ((range (nfix (- hi lo)))
         (size (bitsize range)))
    (if (<= size stop-bits)
        1
      (- size (1- stop-bits)))))
    
; (rounds 0 1023 10)
; (rounds 0 1024 10)

(defun nth-integer-between-bits-mid (n lo hi bits)
  (declare (xargs :guard (and (natp n)
                              (integerp lo)
                              (integerp hi)
                              (<= lo hi)
                              (posp bits))))
  (let* ((fullrange (- hi lo))
         (brange (min fullrange (1- (expt 2 bits))))
         (fullmid (+ lo (floor fullrange 2)))
         (blo (- fullmid (floor brange 2))))
    (+ blo (simple-hash n brange))))

(defun nth-integer-between-bits-lo (n lo hi bits)
  (declare (xargs :guard (and (natp n)
                              (integerp lo)
                              (integerp hi)
                              (<= lo hi)
                              (posp bits))))
  (let* ((fullrange (- hi lo))
         (brange (min fullrange (1- (expt 2 bits)))))
    (+ lo (simple-hash n brange))))

;(nth-integer-between-bits-mid 1021312 0 10000 100)
;(nth-integer-between-bits-lo  1021312 0 10000 100)
;(nth-integer-between          1021312 0 10000)

;(nth-integer-between-bits-mid 1021312 0 10000 8)
;(nth-integer-between-bits-lo  1021312 0 10000 8)
;(nth-integer-between          1021312 0 10000)

(defun integer-index (i)
  (declare (xargs :guard (integerp i)))
  (if (< i 0)
      (1+ (* (- (1+ i)) 2))
    (* i 2)))

#|
(encapsulate nil
  (local 
   (include-book "arithmetic-5/top" :dir :system))

  (defthm nth-pos-multiple-three-type
    (pos-multiple-of-threep (nth-pos-multiple-of-three n)))
  
  
  (defthm nth-pos-multiple-of-three-index
    (implies (natp n)
             (equal (pos-multiple-of-three-index (nth-pos-multiple-of-three n))
                    n)))
  
  (defthm pos-multiple-of-three-index-nth
    (implies (pos-multiple-of-threep i)
             (equal (nth-pos-multiple-of-three (pos-multiple-of-three-index i))
                    i)))    

  
  (defthm nth-integer-index
    (implies 
     (and (integerp n)
          (>= n 0))
     (equal (integer-index (nth-integer n))
            n)))
  (defthm integer-index-nth
    (implies 
     (integerp i)
     (equal (nth-integer (integer-index i))
            i))))
||#

(defun neg-ratiop (x)
  (declare (xargs :guard t))
  (and (rationalp x)
       (not (integerp x))
       (< x 0)))

(defun base-defdata-insert (e l)
  (declare (xargs :guard (and (natp e) (nat-listp l))))
  (cond ((endp l) (list e))
        ((<= e (car l)) (cons e l))
        (t (cons (car l) (base-defdata-insert e (cdr l))))))

(defun base-defdata-isort (l)
  (declare (xargs :guard (nat-listp l)))
  (if (endp l)
      l
    (base-defdata-insert (car l) (base-defdata-isort (cdr l)))))

#|
 (defthm base-defdata-isort-listp
   (implies (nat-listp l)
            (nat-listp (base-defdata-isort l)))
   :rule-classes ((:forward-chaining) (:rewrite)))

  (defthm len-base-defdata-isort
   (equal (len (base-defdata-isort l)) (len l))
   :rule-classes ((:forward-chaining :trigger-terms ((base-defdata-isort l))) (:rewrite)))

 (defthm len-base-defdata-isort1
   (implies (and (nat-listp l) l) (base-defdata-isort l))
   :rule-classes ((:forward-chaining) (:rewrite)))

 (defthm len-base-defdata-isort2
   (implies (and (nat-listp l) (cdr l)) (cdr (base-defdata-isort l)))
   :rule-classes ((:forward-chaining) (:rewrite)))

 (defthm len-base-defdata-isort3
   (implies (and (nat-listp l) (cddr l)) (cddr (base-defdata-isort l)))
   :rule-classes ((:forward-chaining) (:rewrite)))
  
 (defthm weighted-split-nat--nat-listp-fc
   (nat-listp (defdata::weighted-split-nat weights x))
   :rule-classes ((:forward-chaining
                   :trigger-terms
                   ((defdata::weighted-split-nat weights x)))))

(skip-proofs
 (defthm len-wsn1
   (implies (and (nat-listp l) l (natp n))
            (defdata::weighted-split-nat l n))
   :rule-classes ((:forward-chaining) (:rewrite))))

(skip-proofs
 (defthm len-wsn2
   (implies (and (nat-listp l) (cdr l) (natp n))
            (cdr (defdata::weighted-split-nat l n)))
   :rule-classes ((:forward-chaining) (:rewrite))))

(skip-proofs
 (defthm len-wsn3
   (implies (and (nat-listp l) (cddr l) (natp n))
            (cddr (defdata::weighted-split-nat l n)))
   :rule-classes ((:forward-chaining) (:rewrite))))

(defthm base-defdata-isort-elements1
  (implies (and (nat-listp l)
                l)
           (natp (car l)))
  :rule-classes ((:rewrite)
                 (:forward-chaining :trigger-terms ((car l)))))
                                                     
(defthm base-defdata-isort-elements2
  (implies (and (nat-listp l)
                (cdr l))
           (natp (cadr l)))
  :rule-classes ((:rewrite)
                 (:forward-chaining :trigger-terms ((cadr l)))))

(defthm base-defdata-isort-elements3
  (implies (and (nat-listp l)
                (cddr l))
           (natp (caddr l)))
  :rule-classes ((:rewrite)
                 (:forward-chaining :trigger-terms ((caddr l)))))

(defthm wsn-elements1
  (implies (and (nat-listp l)
                l
                (natp n))
           (natp (car )))
  :rule-classes ((:rewrite)
                 (:forward-chaining :trigger-terms ((car l)))))
                                                     
(defthm wsn-elements2
  (implies (and (nat-listp l)
                (cdr l))
           (natp (cadr l)))
  :rule-classes ((:rewrite)
                 (:forward-chaining :trigger-terms ((cadr l)))))

(defthm wsn-elements3
  (implies (and (nat-listp l)
                (cddr l))
           (natp (caddr l)))
  :rule-classes ((:rewrite)
                 (:forward-chaining :trigger-terms ((caddr l)))))

#|
(i-am-here) ; proving stuff about weighted-split-nat is going to be a pain.
(thm
  (implies (and (posp k)
                (natp n))
           (nat-listp (defdata::split-nat k n))))

(thm (implies (natp k)
              (equal (len (acl2::repeat k n))
                     k)))

(skip-proofs
(defthm weighted-split-nat--len
  (equal (len (defdata::weighted-split-nat weights x))
         (max 1 (len weights)))))

(thm 
  (EQUAL (LEN (DEFDATA::WEIGHTED-SPLIT-NAT l n))
         (max 1 (len l)))
  :hints (("goal" :in-theory (enable defdata::weighted-split-nat)))))


(thm
  (implies (posp k)
           (equal (len (defdata::split-nat k n)) k)))
|#

(local
 (defthm natp-implies-acl2-numberp
  (implies (natp x)
           (acl2-numberp x))
  :rule-classes ((:rewrite) (:forward-chaining)))

(defthm posp-implies-acl2-numberp
  (implies (posp x)
           (acl2-numberp x))
  :rule-classes ((:rewrite) (:forward-chaining)))
 
(defthm integerp-implies-acl2-numberp
  (implies (integerp x)
           (acl2-numberp x))
  :rule-classes ((:rewrite) (:forward-chaining)))

(defthm rationalp-implies-acl2-numberp2
  (implies (rationalp x)
           (acl2-numberp x))
  :rule-classes ((:rewrite) (:forward-chaining)))

(defthm natp-implies-rationalp
  (implies (natp x)
           (rationalp x))
  :rule-classes ((:rewrite) (:forward-chaining)))

(defthm posp-implies-rationalp
  (implies (posp x)
           (rationalp x))
  :rule-classes ((:rewrite) (:forward-chaining)))

(defthm integerp-implies-rationalp
  (implies (integerp x)
           (rationalp x))
  :rule-classes ((:rewrite) (:forward-chaining)))
)

(defthm split-nat-len
  (implies (and (posp k)
                (natp n))
           (equal (len (defdata::split-nat k n)) k))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((defdata::split-nat k n)))))

(in-theory (enable defdata::nthcdr-weighted-split-nat defdata::split-nat))
(in-theory (disable
            DEFDATA::WEIGHTED-SPLIT-NAT--TO--NTHCDR-WEIGHTED-SPLIT-NAT
;            defdata::split-nat
            ))
|#

(defun pos-ratiop (x)
  (declare (xargs :guard t))
  (and (rationalp x)
       (not (integerp x))
       (> x 0)))

(defun nth-pos-ratio-builtin (n)
  (declare (xargs :guard (natp n) :verify-guards nil))
  (let* ((two-n-list (base-defdata-isort (defdata::split-nat 3 n)))
         (a (first two-n-list))
         (b (1+ (second two-n-list)))
         (c (1+ (third two-n-list)))
         (c (if (< b c) c (1+ c))))
    (+ a (/ b c))))

(defun nth-neg-ratio-builtin (n)
  (declare (xargs :guard (natp n) :verify-guards nil))
  (- (nth-pos-ratio-builtin n)))

#|

Notice that this is the same as pos-ratio, since
a ratio can't be an integer! So, I'm removing
this as a type.

(defun non-neg-ratiop (x)
  (declare (xargs :guard t))
  (and (rationalp x)
       (not (integerp x))
       (>= x 0)))

|#

#|

Notice that this is the same as neg-ratio, since a 
ratio can't be an integer! So, I'm removing this 
as a type.

(defun non-pos-ratiop (x)
  (declare (xargs :guard t))
  (and (rationalp x)
       (not (integerp x))
       (<= x 0)))

(defun nth-non-pos-ratio-builtin (n)
  (declare (xargs :guard (natp n) :verify-guards nil))
  (if (zp n)
      0
    (nth-neg-ratio-builtin n)))
|#

;(defdata rat (oneof 0 pos-ratio neg-ratio))
;DOESNT WORK so pos/neg ratio are not consistent types ;TODO
;(local (include-book "arithmetic-5/top" :dir :system))
;(thm (nat-listp (defdata::split-nat 2 n)))
;(thm (pos-ratiop (nth-pos-ratio n)))


#|
(defdata int (oneof 0 pos neg))
(thm (iff (integerp x) (intp x)))
|#

(defun neg-rationalp (x)
  (declare (xargs :guard t))
  (and (rationalp x) 
       (< x 0)))

(defun nth-neg-rational-builtin (n)
  (declare (xargs :guard (natp n)))
  (let* ((two-n-list (defdata::split-nat 2 n))
         (num (nth-neg-builtin (car two-n-list)))
         (den (nth-pos-builtin (cadr two-n-list))))
    (/ num den)))

(defun pos-rationalp (x)
  (declare (xargs :guard t))
  (and (rationalp x) 
       (> x 0)))

(defun nth-pos-rational-builtin (n)
  (declare (xargs :guard (natp n)))
  (let* ((two-n-list (defdata::split-nat 2 n))
         (num (nth-pos-builtin (car two-n-list)))
         (den (nth-pos-builtin (cadr two-n-list))))
    (/ num den)))

(defun non-neg-rationalp (x)
  (declare (xargs :guard t))
  (and (rationalp x) 
       (>= x 0)))

(defun nth-non-neg-rational-builtin (n)
  (declare (xargs :guard (natp n)))
  (let* ((two-n-list (defdata::split-nat 2 n))
         (num (nth-nat-builtin (car two-n-list)))
         (den (nth-pos-builtin (cadr two-n-list))))
    (/ num den)))

(defun non-pos-rationalp (x)
  (declare (xargs :guard t))
  (and (rationalp x) 
       (<= x 0)))

(defun nth-non-pos-rational-builtin (n)
  (declare (xargs :guard (natp n)))
  (let* ((two-n-list (defdata::split-nat 2 n))
         (num (nth-neg-builtin (car two-n-list)))
         (den (nth-pos-builtin (cadr two-n-list))))
    (/ num den)))

(defun non-0-rationalp (x)
  (declare (xargs :guard t))
  (and (rationalp x) 
       (/= x 0)))

(defun nth-non-0-rational-builtin (n)
  (declare (xargs :guard (natp n)))
  (let* ((two-n-list (defdata::split-nat 2 n))
         (num (nth-non-0-integer-builtin (car two-n-list)))
         (den (nth-pos-builtin (cadr two-n-list))))
    (/ num den)))

;(defdata rational (oneof 0 pos-rational neg-rational))
(defun nth-rational-builtin (n)
  (declare (xargs :guard (natp n)))
  (let* ((two-n-list (defdata::split-nat 2 n))
         (num (nth-integer-builtin (car two-n-list)))
         (den (nth-pos-builtin (cadr two-n-list))))
    (/ num den)))

(defthm nth-rat-is-ratp
  (implies (natp x)
           (rationalp (nth-rational-builtin x)))
  :rule-classes (:rewrite :type-prescription))

 ;lo included, hi included

(defun nth-rational-between (n lo hi);inclusive
  (declare (xargs :guard (and (natp n)
                              (rationalp lo)
                              (rationalp hi)
                              (<= lo hi))))
  (let* ((two-n-list (defdata::split-nat 2 n))
         (den (nth-pos-builtin (car two-n-list)))
         (num (nth-integer-between (cadr two-n-list) 0 den))
         (range (- hi lo)))
    (+ lo (* (/ num den) range))))

(defun nth-complex-rational-builtin (n)
  (declare (xargs :guard (natp n)))
  (let* ((two-n-list (defdata::split-nat 2 n))
         (rpart (nth-pos-rational-builtin (defdata::nfixg (car two-n-list))))
         (ipart (nth-pos-rational-builtin (defdata::nfixg (cadr two-n-list)))))
    (complex rpart ipart)))

(defun nth-complex-rational-between (n lo hi)
  (declare (xargs :guard (and (natp n)
                              (complex/complex-rationalp lo)
                              (complex/complex-rationalp hi)
                              (<= (realpart lo) (realpart hi))
                              (<= (imagpart lo) (imagpart hi)))))
  (b* ((rlo (realpart lo))
       (rhi (realpart hi))
       (ilo (imagpart lo))
       (ihi (imagpart hi))
       ((list n1 n2) (defdata::split-nat 2 n)))
    (complex (nth-rational-between n1 rlo rhi) (nth-rational-between n2 ilo ihi))))

;; (encapsulate 
;;  ((nth-acl2-number (n) t :guard (natp n)))
;;  (local (defun nth-acl2-number (n)
;;           (declare (xargs :guard (natp n)))
;;           (declare (ignore n))
;;           0)))

(defun nth-acl2-number-builtin (n)
  (declare (xargs :guard (natp n)))
  (b* (((mv choice seed)
        (defdata::switch-nat 4 n)))
    (case choice
          (0 (nth-nat-builtin seed))
          (1 (nth-integer-builtin seed))
          (2 (nth-rational-builtin seed))
          (t (nth-complex-rational-builtin seed)))))

;; (defattach nth-acl2-number nth-acl2-number-builtin)

(defun nth-acl2-number-between (n lo hi)
  (declare (xargs :verify-guards nil))
  (b* (((mv choice seed)
        (defdata::switch-nat 3 n)))
    (case choice
          (0 (nth-integer-between seed lo hi))
          (1 (nth-rational-between seed lo hi))
          (t (nth-complex-rational-between seed lo hi)))))

(defun nth-number-between-fn (n lo hi type)
  (declare (xargs :verify-guards nil))
  (case type
    (integer (nth-integer-between n lo hi))
    (rational (nth-rational-between n lo hi))
    (complex-rational (nth-complex-rational-between n lo hi))
    (t (nth-acl2-number-between n lo hi))))
  
(defmacro nth-number-between (n lo hi &key type)
  `(nth-number-between-fn ,n ,lo ,hi (or ,type 'acl2s::acl2-number)))


#!DEFDATA
(progn
  (defun geometric-int-around (x n)
    (declare (xargs :guard (and (integerp x) (natp n))
                    :verify-guards nil))
    (+ x (acl2s::nth-integer-builtin n)))

  (defun geometric-rat-around (x n)
    (declare (xargs :guard (and (rationalp x) (natp n))
                    :verify-guards nil))
    (+ x (acl2s::nth-rational-builtin n)))

  (defun geometric-int-leq (x n)
    (declare (xargs :guard (and (integerp x) (natp n))
                    :verify-guards nil))
    (- x (acl2s::nth-nat-builtin n)))

  (defun geometric-rat-leq (x n)
    (declare (xargs :guard (and (rationalp x) (natp n))
                    :verify-guards nil))
    (- x (acl2s::nth-non-neg-rational-builtin n)))

  (defun geometric-int-geq (x n)
    (declare (xargs :guard (and (integerp x) (natp n))
                    :verify-guards nil))
    (+ x (acl2s::nth-nat-builtin n)))

  (defun geometric-rat-geq (x n)
    (declare (xargs :guard (and (rationalp x) (natp n))
                    :verify-guards nil))
    (+ x (acl2s::nth-non-neg-rational-builtin n)))

  (defun geometric-int-around-bnd (x lo hi n)
    (declare (xargs :guard (and (integerp x) (natp n))
                    :verify-guards nil))
    (b* ((res (+ x (acl2s::nth-integer-builtin n)))
         (res (max lo res))
         (res (min hi res)))
      res))

  (defun geometric-rat-around-bnd (x lo hi n)
    (declare (xargs :guard (and (rationalp x) (natp n))
                    :verify-guards nil))
    (b* ((res (+ x (acl2s::nth-rational-builtin n)))
         (res (max lo res))
         (res (min hi res)))
      res))

  (defun geometric-int-leq-bnd (x lo n)
    (declare (xargs :guard (and (integerp x) (natp n))
                    :verify-guards nil))
    (b* ((res (- x (acl2s::nth-nat-builtin n)))
         (res (max lo res)))
      res))

  (defun geometric-rat-leq-bnd (x lo n)
    (declare (xargs :guard (and (rationalp x) (natp n))
                    :verify-guards nil))
    (b* ((res (- x (acl2s::nth-non-neg-rational-builtin n)))
         (res (max lo res)))
      res))

  (defun geometric-int-geq-bnd (x hi n)
    (declare (xargs :guard (and (integerp x) (natp n))
                    :verify-guards nil))
    (b* ((res (+ x (acl2s::nth-nat-builtin n)))
         (res (min hi res)))
      res))

  (defun geometric-rat-geq-bnd (x hi n)
    (declare (xargs :guard (and (rationalp x) (natp n))
                    :verify-guards nil))
    (b* ((res (+ x (acl2s::nth-non-neg-rational-builtin n)))
         (res (min hi res)))
      res))

  (defun geometric-int-between (lo hi n)
    (declare (xargs :guard (and (integerp lo) (integerp hi) (natp n) (<= lo hi))
                    :verify-guards nil))
    (b* ((mid (floor (+ lo hi) 2))
         (x (acl2s::nth-integer-builtin n))
         (res (+ mid x))
         (res (max lo res))
         (res (min hi res)))
      res))

  (defun geometric-rat-between (lo hi n)
    (declare (xargs :guard (and (rationalp lo) (rationalp hi) (natp n) (<= lo hi))
                    :verify-guards nil))
    (b* ((mid (/ (+ lo hi) 2))
         (x (acl2s::nth-rational-builtin n))
         (res (+ mid x))
         (res (max lo res))
         (res (min hi res)))
      res))
  )
