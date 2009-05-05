;; **********************************************************************
;;  Originally published as a supplemental material of ACL2 2004 paper 
;;   Created by Jun Sawada at IBM Austin Research Lab, 2003, 2004.
;; **********************************************************************
(in-package "BV")

(include-book "ihs")
(include-book "../../../../arithmetic-2/pass1/top")
(local (include-book "../../../../ihs/quotient-remainder-lemmas"))

(deflabel begin-bv)
(defun bvp (bv)
  (declare (xargs :guard t))
  (and (listp bv)
       (equal (len bv) 3)
       (integerp (caddr bv))
       (<= 0 (caddr bv))
       (integerp (cadr bv))
       (<= 0 (cadr bv))
       (< (cadr bv) (expt 2 (caddr bv)))))



(defun bv (val size)
  (declare (xargs :guard (and (integerp val)
			      (integerp size)
			      (<= 0 size))))
  (list 'bv (mod val (expt 2 size)) size))

(defthm bvp-bv
    (implies (and (integerp s) (<= 0 s) (integerp v))
	     (bvp (bv v s))))


(defun bv-val (bv)
  (declare (xargs :guard (bvp bv)))
  (cadr bv))

(defun bv-size (bv)
  (declare (xargs :guard (bvp bv)))
  (caddr bv))

(defthm type-bv-val
    (implies (bvp v) (and (integerp (bv-val v)) (<= 0 (bv-val v))))
  :rule-classes ((:type-prescription) (:rewrite)))

(defthm acl2-numberp-bv-val
    (implies (bvp v) (acl2-numberp (bv-val v)))
  :rule-classes ((:type-prescription) (:rewrite)))

(defthm type-bv-size
    (implies (bvp v) (and (integerp (bv-size v)) (<= 0 (bv-size v))))
  :rule-classes ((:type-prescription) (:rewrite)))


(defthm bv-size-bv (equal (bv-size (bv val size)) size))

(defthm bv-val-bv (equal (bv-val (bv val size)) (mod val (expt 2 size))))

(in-theory (disable bv bv-size bv-val bvp))

(defconst *b0* '(bit 0))
(defconst *b1* '(bit 1))

(defun bitp (b)
  (declare (xargs :guard t))
  (or (equal b *b1*) (equal b *b0*)))

(defun make-bit (val)
  (declare (xargs :guard (or (equal val 0) (equal val 1))))
  (if (zp val) *b0* *b1*))

(defun bit-val (b)
  (declare (xargs :guard (bitp b)))  
  (cadr b))

(defun b-not (b) 
  (declare (xargs :guard (bitp b)))  
  (make-bit (acl2::b-not (bit-val b))))
(defun b-ior (b0 b1)
  (declare (xargs :guard (and (bitp b0) (bitp b1))))
  (make-bit (acl2::b-ior (bit-val b0) (bit-val b1))))
(defun b-nor (b0 b1)
  (declare (xargs :guard (and (bitp b0) (bitp b1))))
  (make-bit (acl2::b-nor (bit-val b0) (bit-val b1))))
(defun b-and (b0 b1)
  (declare (xargs :guard (and (bitp b0) (bitp b1))))
  (make-bit (acl2::b-and (bit-val b0) (bit-val b1))))
(defun b-nand (b0 b1)
  (declare (xargs :guard (and (bitp b0) (bitp b1))))
  (make-bit (acl2::b-nand (bit-val b0) (bit-val b1))))
(defun b-xor (b0 b1)
  (declare (xargs :guard (and (bitp b0) (bitp b1))))
  (make-bit (acl2::b-xor (bit-val b0) (bit-val b1))))
(defun b-andc1 (b0 b1)
  (declare (xargs :guard (and (bitp b0) (bitp b1))))
  (make-bit (acl2::b-andc1 (bit-val b0) (bit-val b1))))
(defun b-andc2 (b0 b1)
  (declare (xargs :guard (and (bitp b0) (bitp b1))))
  (make-bit (acl2::b-andc2 (bit-val b0) (bit-val b1))))
(defun b-orc1 (b0 b1)
  (declare (xargs :guard (and (bitp b0) (bitp b1))))
  (make-bit (acl2::b-orc1 (bit-val b0) (bit-val b1))))
(defun b-orc2 (b0 b1)
  (declare (xargs :guard (and (bitp b0) (bitp b1))))
  (make-bit (acl2::b-orc2 (bit-val b0) (bit-val b1))))
(defun b-eqv (b0 b1)
  (declare (xargs :guard (and (bitp b0) (bitp b1))))
  (make-bit (acl2::b-eqv (bit-val b0) (bit-val b1))))


(defun b2bv (b)
  (declare (xargs :guard (bitp b)))
  (bv (bit-val b) 1))

(defthm bvp-b2bv
    (implies (bitp b) (bvp (b2bv b))))

(defthm bv-size-b2bv
    (equal (bv-size (b2bv b)) 1))

;(defconst *b0* (b2bv 0))
;(defconst *b1* (b2bv 1))
(defconst *bv-nil* (bv 0 0))

(defun bv-null? (bv)
  (declare (xargs :guard (bvp bv)))
  (zp (bv-size bv)))

(defthm bv-null-bv-size 
    (implies (bvp v) 
	     (iff (bv-null? v) (>= 0 (bv-size v)))))

(defun lsb (bv)
  (declare (xargs :guard (and (bvp bv) (< 0 (bv-size bv)))
		  :verify-guards nil))  
  (if (equal (bv-size bv) 0)
      *b0*
      (make-bit (logcar (bv-val bv)))))

(verify-guards lsb
   :hints (("goal" :use ((:instance logcar-type (acl2::i (bv-val bv))))
		   :in-theory (e/d (acl2::bitp) (LOGCAR-TYPE)))))

(defun msb (bv)
  (declare (xargs :guard (and (bvp bv) (< 0 (bv-size bv)))
		  :verify-guards nil))
  (if (equal (bv-size bv) 0)
      *b0*
      (make-bit (logbit (1- (bv-size bv)) (bv-val bv)))))

(verify-guards msb
   :hints (("goal" :use ((:instance logbit-type
				    (acl2::pos (+ -1 (BV-SIZE BV)))
				    (acl2::i (bv-val bv))))
		   :in-theory (e/d (acl2::bitp) (LOGBIT-TYPE)))))

(defthm bitp-lsb  (bitp (lsb bv)))

(defthm bitp-msb (bitp (msb bv)))

(in-theory (disable lsb msb))

;; suggested name msbv, lbv 
(defun msbits (bv)
  (declare (xargs :guard (and (bvp bv) (< 0 (bv-size bv)))
		  :verify-guards nil))
  (if (equal (bv-size bv) 0)
      (bv 0 0)
      (bv (logcdr (bv-val bv)) (1- (bv-size bv)))))

(verify-guards msbits)

(defun lsbits (bv)
  (declare (xargs :guard (and (bvp bv) (< 0 (bv-size bv)))))
  (if (equal (bv-size bv) 0)
      (bv 0 0)
      (bv (loghead  (1- (bv-size bv)) (bv-val bv))
	  (1- (bv-size bv)))))

(defthm bvp-msbits
    (implies (and (bvp bv) (not (bv-null? bv))) (bvp (msbits bv))))

(defthm bv-size-msbits
    (implies (and (bvp bv) (not (bv-null? bv)))
	     (equal (bv-size (msbits bv)) (1- (bv-size bv)))))

(defthm bvp-lsbits
    (implies (and (bvp bv) (not (bv-null? bv))) (bvp (lsbits bv))))

(defthm bv-size-lsbits
    (implies (and (bvp bv) (not (bv-null? bv)))
	     (equal (bv-size (lsbits bv)) (1- (bv-size bv)))))


(defun bitn (n bv)
  (declare (xargs :guard (and (integerp n) (bvp bv)
			      (<= 0 n) (< n (bv-size bv)))
		  :verify-guards nil))
  (make-bit (logbit (- (bv-size bv) (1+ n)) (bv-val bv))))

(verify-guards bitn
   :hints (("goal" :use ((:instance logbit-type
				    (acl2::pos (+ -1 (- N) (BV-SIZE BV)))
				    (acl2::i (bv-val bv))))
		   :in-theory (e/d (acl2::bitp) (LOGBIT-TYPE)))))


(defthm bitp-bitn (bitp (bitn n bv)))

;; A possible improved name is bv&b
(defun bv&b (bv b) 
  (declare (xargs :guard (and (bvp bv) (bitp b))))
  (bv (logcons (bit-val b) (bv-val bv)) (1+ (bv-size bv))))

(defthm bvp-bv&b
    (implies (and (bvp bv) (bitp b))
	     (bvp (bv&b bv b))))

(defthm bv-size-bv&b
    (implies (and (bvp bv) (bitp b))
	     (equal (bv-size (bv&b bv b)) (1+ (bv-size bv)))))

;; A possible improved name is b&bv
(defun b&bv (b bv) 
  (declare (xargs :guard (and (bvp bv) (bitp b))))
  (bv (logapp (bv-size bv) (bv-val bv) (bit-val b)) (1+ (bv-size bv))))


(defthm bvp-b&bv
    (implies (and (bvp bv) (bitp b))
	     (bvp (b&bv b bv))))

(defthm bv-size-b&bv
    (implies (and (bvp bv) (bitp b))
	     (equal (bv-size (b&bv b bv)) (1+ (bv-size bv)))))

(defun bits (bv i j)
  (declare (xargs :guard (and (bvp bv) (integerp i)
			      (integerp j) (>= j 0) (>= j i)
			      (>= i 0)
			      (> (bv-size bv) j))))
  (bv (loghead (1+ (- j i)) (logtail (1- (- (bv-size bv) j)) (bv-val bv)))
      (1+ (- j i))))
      
(defthm bvp-bits
    (implies (and (bvp bv) (integerp i) (integerp j) (>= j i))
	     (bvp (bits bv i j))))

(defthm bv-size-bits
    (implies (and (bvp bv) (integerp i) (integerp j) (> j i))
	     (equal (bv-size (bits bv i j)) (1+ (- j i)))))

; suggested name rbits
(defun bv-right (n bv)
  (declare (xargs :guard (and (integerp n) (<= 0 n) (bvp bv))))
  (bv (loghead n (bv-val bv)) n))


(defthm bvp-bv-right
    (implies (and (bvp bv) (integerp n) (<= 0 n))
	     (bvp (bv-right n bv))))

(defthm bv-size-bv-right
    (implies (and (bvp bv) (integerp n) (<= 0 n))
	     (equal (bv-size (bv-right n bv)) n)))

; suggested name lbits
(defun bv-left (n bv)
  (declare (xargs :guard (and (integerp n) (<= 0 n) (bvp bv)
			      (<= n (bv-size bv)))
		  :verify-guards nil))
  (bv (logtail (- (bv-size bv) n) (bv-val bv)) n))

(verify-guards bv-left
   :hints  (("subgoal 1" :in-theory (enable logtail ifloor expt))))


(defthm bvp-bv-left
    (implies (and (bvp bv) (integerp n) (<= 0 n)
		  (<= n (bv-size bv)))
	     (bvp (bv-left n bv))))

(defthm bv-size-bv-left
    (implies (and (bvp bv) (integerp n) (<= 0 n)
		  (<= n (bv-size bv)))
	     (equal (bv-size (bv-left n bv)) n)))


(defun bv& (a b)
  (declare (xargs :guard (and (bvp a) (bvp b))))
  (bv (logapp (bv-size b) (bv-val b) (bv-val a))
      (+ (bv-size a) (bv-size b))))

(defthm bvp-bv&
    (implies (and (bvp a) (bvp b)) (bvp (bv& a b))))

(defthm bv-size-bv&
    (implies (and (bvp a) (bvp b))
	     (equal (bv-size (bv& a b))
		    (+ (bv-size a) (bv-size b)))))

(defun b&-rec (arglist)
  (if (endp arglist)
      (bv 0 0)
      (if (endp (cdr arglist))
	  `(b2bv ,(car arglist))
	  `(b&bv ,(car arglist) ,(b&-rec (cdr arglist))))))

;; (log&& a b c)  appends all arguments to one vector
(defmacro b&& (&rest arglist)
  (b&-rec arglist))



(defun bv&-rec (arglist)
  (if (endp arglist)
      (bv 0 0)
      (if (endp (cdr arglist))
	  (car arglist)
	  `(bv& ,(car arglist) ,(bv&-rec (cdr arglist))))))

;; (log&& a b c)  appends all arguments to one vector
(defmacro bv&& (&rest arglist)
  (bv&-rec arglist))




(defun ones (n)
  (declare (xargs :guard (and (integerp n) (<= 0 n))))
  (bv (- (expt 2 n) 1) n))

(defun zeros (n)
  (declare (xargs :guard (and (integerp n) (<= 0 n))))
  (bv 0 n))


(defun pad1 (n)
  (declare (xargs :guard (and (integerp n) (<= 0 n))))
  (ones n))

(defun pad0 (n)
  (declare (xargs :guard (and (integerp n) (<= 0 n))))
  (zeros n))


;; fill0  fill0_at zeros_from_to  fill_zero fill_0 fill_1
(defun fill-0 (m n)
  (declare (xargs :guard (and (integerp n) (<= 0 n) (integerp m) (<= 0 m) (<= m n))))
  (zeros (1+ (- n m))))

(defun fill-1 (m n)
  (declare (xargs :guard (and (integerp n) (<= 0 n) (integerp m) (<= 0 m) (<= m n))))
  (ones (1+ (- n m))))


(defthm bvp-zeros
    (implies (and (integerp n) (<= 0 n))
	     (bvp (zeros n))))
(defthm bv-size-zeros
    (implies (and (integerp n) (<= 0 n))
	     (equal (bv-size (zeros n)) n)))

(defthm bvp-ones
    (implies (and (integerp n) (<= 0 n))
	     (bvp (ones n))))

(defthm bv-size-ones
    (implies (and (integerp n) (<= 0 n))
	     (equal (bv-size (ones n)) n)))


(defthm bvp-pad0
    (implies (and (integerp n) (<= 0 n))
	     (bvp (pad0 n))))

(defthm bv-size-pad0
    (implies (and (integerp n) (<= 0 n))
	     (equal (bv-size (pad0 n)) n)))

(defthm bvp-pad1
    (implies (and (integerp n) (<= 0 n))
	     (bvp (pad1 n))))
    
(defthm bv-size-pad1
    (implies (and (integerp n) (<= 0 n))
	     (equal (bv-size (pad1 n)) n)))

(defthm bvp-fill-0
    (implies (and (integerp n) (integerp m) (<= n m))
	     (bvp (fill-0 n m))))

(defthm bv-size-fill-0
    (implies (and (integerp n) (integerp m) (<= n m))
	     (equal (bv-size (fill-0 n m)) (1+ (- m n)))))

(defthm bvp-fill-1
    (implies (and (integerp n) (integerp m) (<= n m))
	     (bvp (fill-1 n m)))
    :hints (("goal" :in-theory (disable ones))))
    
(defthm bv-size-fill-1
    (implies (and (integerp n) (integerp m) (<= n m))
	     (equal (bv-size (fill-1 n m)) (1+ (- m n)))))


(defun b1p (b)
  (declare (xargs :guard (bitp b)))
  (not (equal b *b0*)))

(defun b-if (a b c)
  (declare (xargs :guard (and (bitp a) (bitp b) (bitp c))))
  (if (b1p a) b c))


(defthm bitp-b-if
    (implies (and (bitp a) (bitp b) (bitp c))
	     (bitp (b-if a b c))))

(defun bv-if (a b c)
  (declare (xargs :guard (and (bitp a) (bvp b) (bvp c))))
  (if (b1p a) b c))

(defthm bvp-bv-if
    (implies (and (bitp a) (bvp b) (bvp c))
	     (bvp (bv-if a b c))))

(defthm bv-size-bv-if
    (implies (and (bitp a) (bvp b) (bvp c) (equal (bv-size b) (bv-size c)))
	     (equal (bv-size (bv-if a b c)) (bv-size b))))


(defmacro b-cond (&rest clause)
  (if (endp clause)
      0
      (let ((cnd (caar clause))
	    (first (cadar clause))
	    (rest (cdr clause)))
	`(b-if ,cnd ,first (b-cond ,@rest)))))



(defmacro bv-cond (&rest clause)
  (if (endp clause)
      *bv-nil*
      (if (and (endp (cdr clause))
	       (equal (caar clause) 1))
	  (cadar clause)
	  (let ((cnd (caar clause))
		(first (cadar clause))
		(rest (cdr clause)))
	    `(bv-if ,cnd ,first (bv-cond ,@rest))))))


(defun bv-not (bv)
  (declare (xargs :guard (bvp bv)))
  (bv (lognotu (bv-size bv) (bv-val bv))
      (bv-size bv)))

(defthm bvp-bv-not
    (implies (bvp bv)
	     (bvp (bv-not bv))))

(defthm bv-size-bv-not
    (implies (bvp bv)
	     (equal (bv-size (bv-not bv)) (bv-size bv))))

(defun bv-and (bv1 bv2)
  (declare (xargs :guard (and (bvp bv1) (bvp bv2)
			      (equal (bv-size bv1) (bv-size bv2)))))
  (bv (logand (bv-val bv1) (bv-val bv2))
      (bv-size bv1)))


(defun bv-ior (bv1 bv2)
  (declare (xargs :guard (and (bvp bv1) (bvp bv2)
			      (equal (bv-size bv1) (bv-size bv2)))))
  (bv (logior (bv-val bv1) (bv-val bv2))
      (bv-size bv1)))

(defun bv-xor (bv1 bv2)
  (declare (xargs :guard (and (bvp bv1) (bvp bv2)
			      (equal (bv-size bv1) (bv-size bv2)))))
  (bv (logxor (bv-val bv1) (bv-val bv2))
      (bv-size bv1)))

(defthm bvp-bv-and
    (implies (and (bvp bv1) (bvp bv2)
		  (equal (bv-size bv1) (bv-size bv2)))
	     (bvp (bv-and bv1 bv2))))

(defthm bv-size-bv-and
    (implies (and (bvp bv1) (bvp bv2) (equal (bv-size bv1) (bv-size bv2)))
	     (equal (bv-size (bv-and bv1 bv2))
		    (bv-size bv1))))


(defthm bvp-bv-ior
    (implies (and (bvp bv1) (bvp bv2) (equal (bv-size bv1) (bv-size bv2)))
	     (bvp (bv-ior bv1 bv2))))

(defthm bv-size-bv-ior
    (implies (and (bvp bv1) (bvp bv2) (equal (bv-size bv1) (bv-size bv2)))
	     (equal (bv-size (bv-ior bv1 bv2))
		    (bv-size bv1))))


(defthm bvp-bv-xor
    (implies (and (bvp bv1) (bvp bv2))
	     (bvp (bv-xor bv1 bv2))))

(defthm bv-size-bv-xor
    (implies (and (bvp bv1) (bvp bv2) (equal (bv-size bv1) (bv-size bv2)))
	     (equal (bv-size (bv-xor bv1 bv2))
		    (bv-size bv1))))

(defun b-maj (a b c)
  (declare (xargs :guard (and (bitp a) (bitp b) (bitp c))))
  (b-and (b-ior a b) (b-and (b-ior b c) (b-ior c a))))

(defthm bitp-b-maj
    (implies (and (bitp a) (bitp b) (bitp c))
	     (bitp (b-maj a b c))))

(defun bv-uextend (a n)
  (declare (xargs :guard (and (bvp a) (integerp n) (<= 0 n))))
  (bv (bv-val a) n))

(defthm bvp-bv-uextend
    (implies (and (bvp bv1) (integerp n) (<= 0 n))
	     (bvp (bv-uextend bv1 n))))

(defthm bv-size-bv-uextend
    (implies (and (bvp a) (integerp n) (<= 0 n))
	     (equal (bv-size (bv-uextend a n)) n)))

(defun bv-sextend (a n)
  (declare (xargs :guard (and (bvp a) (< 0 (bv-size a))
			      (integerp n) (<= 0 n))))
  (bv (logextu n (bv-size a) (bv-val a)) n))

(defthm bvp-bv-sextend
    (implies (and (bvp bv1) (integerp n) (<= 0 n))
	     (bvp (bv-sextend bv1 n))))

(defthm bv-size-bv-sextend
    (implies (and (bvp a) (integerp n) (<= 0 n))
	     (equal (bv-size (bv-sextend a n)) n)))


(defun bv-lsh (n a)
  (declare (xargs :guard (and (bvp a) (integerp n))))
  (bv (lshu (bv-size a) (bv-val a) n) (bv-size a)))

(defthm bvp-bv-lsh
    (implies (and (bvp bv1) (integerp n))
	     (bvp (bv-lsh n bv1))))

(defthm bv-size-bv-lsh
    (implies (and (bvp bv1) (integerp n))
	     (equal (bv-size (bv-lsh n bv1)) (bv-size bv1))))


(defun bv-ash (n a)
  (declare (xargs :guard (and (bvp a) (integerp n)
			      (< 0 (bv-size a)))))
  (bv (ashu (bv-size a) (bv-val a) n) (bv-size a)))

(defthm bvp-bv-ash
    (implies (and (bvp bv1) (integerp n))
	     (bvp (bv-ash n bv1))))

(defthm bv-size-bv-ash
    (implies (and (bvp bv1) (integerp n))
	     (equal (bv-size (bv-ash n bv1)) (bv-size bv1))))


(defun bv-<< (bv sa)
  (declare (xargs :guard (and (bvp sa) (bvp bv))))
  (bv-lsh (bv-val sa) bv))

(defthm bvp-bv-<<
    (implies (and (bvp sa) (bvp bv))
	     (bvp (bv-<< bv sa))))

(defthm bv-size-bv-<<
    (implies (and (bvp sa) (bvp bv))
	     (equal (bv-size (bv-<< bv sa)) (bv-size bv))))

(defun bv->> (bv sa)
  (declare (xargs :guard (and (bvp sa) (bvp bv))))
  (bv-lsh (- (bv-val sa)) bv))

(defthm bvp-bv->>
    (implies (and (bvp sa) (bvp bv))
	     (bvp (bv->> bv sa))))


(defthm bv-size-bv->>
    (implies (and (bvp sa) (bvp bv))
	     (equal (bv-size (bv->> bv sa)) (bv-size bv))))


(defun bv-*>> (bv sa)
  (declare (xargs :guard (and (bvp sa) (bvp bv) (< 0 (bv-size bv)))))
  (bv-ash (- (bv-val sa)) bv))

(defthm bvp-bv-*>>
    (implies (and (bvp sa) (bvp bv))
	     (bvp (bv-*>> bv sa))))

(defthm bv-size-bv-*>>
    (implies (and (bvp sa) (bvp bv))
	     (equal (bv-size (bv-*>> bv sa)) (bv-size bv))))


(defun adder (a b c)
  (declare (xargs :measure (nfix (bv-size a))
		  :guard (and (bvp a) (bvp b) (bitp c))
		  :verify-guards nil))
  (if (bv-null? a)
      (b2bv c)
      (if (bv-null? b)
	  (b2bv c)
	  (bv&b (adder (msbits a) (msbits b) (b-maj (lsb a) (lsb b) c))
		(b-xor (b-xor (lsb a) (lsb b)) c)))))

(defthm bvp-adder
    (implies (and (bvp a) (bvp b) (bitp c))
	     (bvp (adder a b c))))

(defthm bv-size-adder
    (implies (and (bvp a) (bvp b) (bitp c)
		  (equal (bv-size a) (bv-size b)))
	     (equal (bv-size (adder a b c))
		    (1+ (bv-size a)))))
	     

(verify-guards adder
	       :hints (("goal" :in-theory (disable msbits b-maj bitp))))
      
;; There are two versions of bv+ that can be thought of as a natural
;; definition. One returns the bit-vector of the same size as the
;; original input and the other returns a bit vector of size
;; incremented by one.  There are pro and conses between these design
;; choices.  Let us list the advantage of the implementation. 
;; Advantage of the fixed size
;;  The commutative rule applies. 
;;  Most of the microprocessor instruction implements fixed sized
;;    add. 
;;  Carry output is defined as a separate function. 
;;  Adding arbitrary number of vectors can be described naturally.
;;  Incremented width subtract operation is not natural to define,
;;   because carry is inverted. 
;; Advantage of the incremented width.
;;  Does not overflow.
;;  May save explicit padding. 
;; Currently we implment fixed with sum and subtract operation. 
;; When overflow should be avoided, bit vector should be extended
;; before the operations. 
(defun bv+ (a b)
  (declare (xargs :guard (and (bvp a) (bvp b))))
  (bv (+ (bv-val a) (bv-val b)) (bv-size a)))

(defthm bvp-bv+
    (implies (and (bvp a) (bvp b))
	     (bvp (bv+ a b))))

(defthm bv-size-bv+
    (implies (and (bvp a) (bvp b) (equal (bv-size a) (bv-size b)))
	     (equal (bv-size (bv+ a b))
		    (bv-size a))))
    
(defun bv+carry (a b)
  (declare (xargs :guard (and (bvp a) (bvp b)
			      (equal (bv-size a) (bv-size b)))  ))
  (msb (bv+ (b&bv *b0* a) (b&bv *b0* b))))

(defthm bitp-bv+carry (bitp (bv+carry a b)))

;; Bit vector multiply.
;; I put a strong guard because a or b is not bvp, this function
;; may return an incorrect value. Consider (bv* (bv 7 2) (bv 7 2))
(defun bv* (a b)
  (declare (xargs :guard (and (bvp a) (bvp b))))
  (bv (* (bv-val a) (bv-val b)) (+ (bv-size a) (bv-size b))))

(defthm bvp-bv*
    (implies (and (bvp a) (bvp b))
	     (bvp (bv* a b))))

(defthm bv-size-bv*
    (implies (and (bvp a) (bvp b))
	     (equal (bv-size (bv* a b)) (+ (bv-size a) (bv-size b)))))


(defun bv-eq? (a b)
  (declare (xargs :guard (and (bvp a) (bvp b))))
  (if (equal a b) *b1* *b0*))

(defthm bitp-eq?
    (bitp (bv-eq? a b)))

(defun bv-neq? (a b)
  (declare (xargs :guard (and (bvp a) (bvp b))))
  (b-not (bv-eq? a b)))

(defthm bitp-bv-neq?
    (bitp (bv-neq? a b)))

(defun bv-all-ones? (bv)
  (declare (xargs :guard (bvp bv)))
  (bv-eq? bv (ones (bv-size bv))))

(defthm bitp-all-ones?
    (bitp (bv-all-ones? bv)))

(defun bv-all-zeros? (bv)
  (declare (xargs :guard (bvp bv)))
  (bv-eq? bv (zeros (bv-size bv))))

(defthm bitp-all-zeros?
    (bitp (bv-all-zeros? bv)))

(defun bv-and-all (bv)
  (declare (xargs :guard (bvp bv)))
  (bv-all-ones? bv))

(defthm bitp-bv-and-all
    (bitp (bv-and-all bv)))

(defun bv-ior-all (bv)
  (declare (xargs :guard (bvp bv)))
  (b-not (bv-all-zeros? bv)))

(defthm bitp-bv-ior-all
    (bitp (bv-ior-all bv)))

(defun bv-some-zeros? (bv)
  (declare (xargs :guard (bvp bv)))
  (b-not (bv-all-ones? bv)))

(defthm bitp-some-zeros?
  (bitp (bv-some-zeros? bv)))

(defun bv-some-ones? (bv)
  (declare (xargs :guard (bvp bv)))
  (b-not (bv-all-zeros? bv)))

(defthm bitp-some-ones?
  (bitp (bv-some-ones? bv)))

(defun bv-right-ior (bv sa)
  (declare (xargs :guard (and (bvp bv) (bvp sa))))
  (let ((w (expt 2 (bv-size sa))))
    (bv-some-ones? (bv-right w (bv->> (bv& bv (bv 0 w)) sa)))))

(defthm bitp-bv-right-ior (bitp (bv-right-ior bv sa)))

(defun bv-left-ior (bv sa)
  (declare (xargs :guard (and (bvp bv) (bvp sa))))
  (let ((w (expt 2 (bv-size sa))))
    (bv-some-ones? (bv-left w (bv-<< (bv& (bv 0 w) bv) sa)))))

(defthm bitp-bv-left-ior (bitp (bv-left-ior bv sa)))


(defun bv-inc (bv c)
  (declare (xargs :guard (and (bvp bv) (bitp c))))
  (bv (+ (bv-val bv) (bit-val c)) (bv-size bv)))

(defthm bvp-bv-inc
    (implies (and (bvp bv) (bitp c))
	     (bvp (bv-inc bv c))))

(defthm bv-size-bv-inc
    (implies (and (bvp bv) (bitp c))
	     (equal (bv-size (bv-inc bv c)) (bv-size bv))))

(defun bv++ (bv)
  (declare (xargs :guard (and (bvp bv))))
  (bv (1+ (bv-val bv)) (bv-size bv)))

(defthm bvp-bv++
    (implies (bvp bv) (bvp (bv++ bv))))


(defthm bv-size-bv++
    (implies (bvp bv)
	     (equal (bv-size (bv++ bv)) (bv-size bv))))

(defun bv-- (bv)
  (declare (xargs :guard (and (bvp bv))))
  (bv (1- (bv-val bv)) (bv-size bv)))

(defthm bvp-bv--
    (implies (bvp bv) (bvp (bv-- bv))))


(defthm bv-size-bv--
    (implies (bvp bv)
	     (equal (bv-size (bv-- bv)) (bv-size bv))))

(defun bv- (bv1 bv2)
  (declare (xargs :guard (and (bvp bv1) (bvp bv2))))
  (bv (- (bv-val bv1) (bv-val bv2)) (bv-size bv1)))

(defthm bvp-bv-
    (implies (and (bvp bv1) (bvp bv2)) (bvp (bv- bv1 bv2))))

(defthm bv-size-bv-
    (implies (and (bvp bv1) (bvp bv2) (equal (bv-size bv1) (bv-size bv2)))
	     (equal (bv-size (bv- bv1 bv2)) (bv-size bv1))))


(defun bv-neg (bv1)
  (declare (xargs :guard (bvp bv1)))    
  (bv++ (bv-not bv1)))

(defun bv-carry (bv1 bv2)
  (msb (bv++ (bv+ (b&bv *b0* bv1) (b&bv *b0* (bv-not bv2))))))

(defthm bitp-bv-carry
    (bitp (bv-carry bv1 bv2)))

(defun bv-gt? (bv1 bv2)
  (declare (xargs :guard (and (bvp bv1) (bvp bv2))))
  (if (> (bv-val bv1) (bv-val bv2)) *b1* *b0*))
      
(defthm bitp-bv-gt? (bitp (bv-gt? bv1 bv2)))

(defun bv-ge? (bv1 bv2)
  (declare (xargs :guard (and (bvp bv1) (bvp bv2))))
  (if (>= (bv-val bv1) (bv-val bv2)) *b1* *b0*))

(defthm bitp-bv-ge? (bitp (bv-ge? bv1 bv2)))

(defun bv-lt? (bv1 bv2)
  (declare (xargs :guard (and (bvp bv1) (bvp bv2))))
  (if (< (bv-val bv1) (bv-val bv2)) *b1* *b0*))

(defthm bitp-bv-lt? (bitp (bv-lt? bv1 bv2)))

(defun bv-le? (bv1 bv2)
  (declare (xargs :guard (and (bvp bv1) (bvp bv2))))
  (if (<= (bv-val bv1) (bv-val bv2)) *b1* *b0*))

(defthm bitp-bv-le? (bitp (bv-le? bv1 bv2)))

(defun bv-lz (bv w)
  (declare (xargs :guard (and (bvp bv) (integerp w) (<= 0 w))
		  :measure (nfix (bv-size bv))
		  :verify-guards nil))
  (if (bv-null? bv)
      (bv 0 w)
      (if (b1p (bitn 0 bv))
	  (bv 0 w)
	  (bv++ (bv-lz (lsbits bv) w)))))

(defthm bvp-bv-lz
  (implies (and (bvp bv) (integerp w) (<= 0 w))
	   (bvp (bv-lz bv w))))

(defthm bv-size-bv-lz
  (implies (and (bvp bv) (integerp w) (<= 0 w))
	   (equal (bv-size (bv-lz bv w)) w)))

(verify-guards bv-lz)

(deflabel end-bv)

;; auxiliary functions for integer expressions.
(defun fixint32 (a)
  (- (mod (+ (nfix a) (expt 2 31)) (expt 2 32))
     (expt 2 31)))

(defun int32p (a) (and (integerp a) (<= (- (expt 2 31)) a) (< a (expt 2 31))))
(defun int32+ (a b)  (fixint32 (+ a b)))
(defun int32- (a b)  (fixint32 (- a b)))
(defun int32* (a b)  (fixint32 (* a b)))
(defun int32** (a b)  (fixint32 (expt a b)))

(deftheory bv-theory  (set-difference-theories (function-theory 'end-bv)
					       (function-theory 'begin-bv)))


(defthm bitp-b-not
  (implies (bitp b) (bitp (b-not b)))
  :rule-classes (:rewrite :type-prescription))

(defthm bitp-b-and
  (implies (and (bitp a) (bitp b))
           (bitp (b-and a b)))
  :rule-classes (:rewrite :type-prescription))

(defthm bitp-b-and
  (implies (and (bitp a) (bitp b))
           (bitp (b-and a b)))
  :rule-classes (:rewrite :type-prescription))
(defthm bitp-b-ior
  (implies (and (bitp a) (bitp b))
           (bitp (b-ior a b)))
  :rule-classes (:rewrite :type-prescription))
(defthm bitp-b-xor
  (implies (and (bitp a) (bitp b))
           (bitp (b-xor a b)))
  :rule-classes (:rewrite :type-prescription))
(defthm bitp-b-nor
  (implies (and (bitp a) (bitp b))
           (bitp (b-nor a b)))
  :rule-classes (:rewrite :type-prescription))
(defthm bitp-b-nand
  (implies (and (bitp a) (bitp b))
           (bitp (b-nand a b)))
  :rule-classes (:rewrite :type-prescription))
(defthm bitp-b-andc1
  (implies (and (bitp a) (bitp b))
           (bitp (b-andc1 a b)))
  :rule-classes (:rewrite :type-prescription))
(defthm bitp-b-andc2
  (implies (and (bitp a) (bitp b))
           (bitp (b-andc2 a b)))
  :rule-classes (:rewrite :type-prescription))
(defthm bitp-b-orc1
  (implies (and (bitp a) (bitp b))
           (bitp (b-orc1 a b)))
  :rule-classes (:rewrite :type-prescription))
(defthm bitp-b-orc2
  (implies (and (bitp a) (bitp b))
           (bitp (b-orc2 a b)))
  :rule-classes (:rewrite :type-prescription))
(defthm bitp-b-eqv
  (implies (and (bitp a) (bitp b))
           (bitp (b-eqv a b)))
  :rule-classes (:rewrite :type-prescription))

(defthm bitn-type-prescription
  (bitp (bitn n bv))
  :rule-classes (:rewrite :type-prescription))

(in-theory (disable bv-theory))