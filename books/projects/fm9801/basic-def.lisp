;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Basic-def.lisp: 
; Author  Jun Sawada, University of Texas at Austin
;
; This file includes various underlying definition for the ISA and
; MA designs.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

(include-book "absolute-path")
(include-acl2-book "data-structures/array1")
(include-acl2-book "data-structures/deflist")
(include-acl2-book "data-structures/list-defthms")
(include-acl2-book "data-structures/structures")
(include-book "ihs")

(include-book "trivia")
(include-book "b-ops-aux")

(deflabel begin-basic-def)

(defmacro naturalp (x) `(and (integerp ,x) (<= 0 ,x)))
(defconst *addr-size* 16)
(defconst *page-offset-size* 10)

(defconst *rname-size* 4)
(defconst *immediate-size* 8)
(defconst *opcode-size* 4)
(defconst *word-size* 16)
(defconst *max-word-value* (expt 2 *word-size*))
(defconst *num-regs* (expt 2 *rname-size*))
(defconst *num-mem-words* (expt 2 *addr-size*))
(defconst *num-page-words* (expt 2 *page-offset-size*))
(defconst *num-pages* (expt 2 (- *addr-size* *page-offset-size*)))
(defbytetype word *word-size* :unsigned)
(defbytetype addr  *addr-size* :unsigned)
(defbytetype rname *rname-size* :unsigned)
(defbytetype immediate *immediate-size* :unsigned)
(defbytetype opcd  *opcode-size* :unsigned)

(defthm word-p-type
    (implies (word-p word)
	     (and (integerp word)
		  (>= word 0)
		  (< word *max-word-value*)))
  :hints (("Goal" :in-theory (enable word-p)))
  :rule-classes :forward-chaining)

(defthm word-p-type-def
    (iff (word-p x)
	 (and (integerp x) 
	      (<= 0 x) (< x (expt 2 16))))
  :hints (("goal" :in-theory (enable word-p unsigned-byte-p)))
  :rule-classes nil)

(defthm word-mod
    (implies (integerp x)
	     (equal (word x)
		    (mod x (expt 2 16))))
  :hints (("goal" :in-theory (enable word loghead)))
  :rule-classes nil)

(defthm word-idem
    (implies (word-p x) (equal (word x) x))
  :rule-classes nil)

(defthm rname-p-type
    (implies (rname-p rname)
	     (and (integerp rname)
		  (>= rname 0)
		  (< rname *num-regs*)))
  :hints (("Goal" :in-theory (enable rname-p)))
  :rule-classes :forward-chaining)

(defthm addr-p-type-def
    (iff (addr-p x)
	 (and (integerp x) 
	      (<= 0 x) (< x (expt 2 16))))
  :hints (("goal" :in-theory (enable addr-p unsigned-byte-p)))
  :rule-classes nil)

(defthm addr-mod
    (implies (integerp x)
	     (equal (addr x)
		    (mod x (expt 2 16))))
  :hints (("goal" :in-theory (enable addr loghead)))
  :rule-classes nil)

(defthm addr-idem
    (implies (addr-p x) (equal (addr x) x))
  :rule-classes nil)

(defthm addr-p-type
    (implies (addr-p ad)
	     (and (integerp ad)
		  (>= ad  0)
		  (< ad *num-mem-words*)))
  :hints (("Goal" :in-theory (enable addr-p)))
  :rule-classes :forward-chaining)

(defthm addr-word-double-casting
    (equal (addr (word i)) (addr i))
  :hints (("goal" :in-theory (enable addr word))))

(defthm word-addr-double-casting
    (equal (word (addr i)) (word i))
  :hints (("goal" :in-theory (enable addr word))))

(defthm word-addr-p
    (implies (addr-p x) (equal (word x) x))
  :hints (("goal" :in-theory (enable addr-p word))))

(defthm addr-word-p
    (implies (word-p x) (equal (addr x) x))
  :hints (("goal" :in-theory (enable addr word-p))))

(in-theory (disable word-addr-p addr-word-p))

(defthm word-p-logand
    (implies (and (word-p val1) (word-p val2))
	     (word-p (logand val1 val2)))
  :hints (("Goal" :in-theory (enable word-p))))

(defthm word-p-logxor
    (implies (and (word-p val1) (word-p val2))
	     (word-p (logxor val1 val2)))
  :hints (("Goal" :in-theory (enable word-p))))

(defthm word-p-logior
    (implies (and (word-p val1) (word-p val2))
	     (word-p (logior val1 val2)))
  :hints (("Goal" :in-theory (enable word-p))))

(defthm word-p-bv-eqv-iff-equal
    (implies (and (word-p wd0) (word-p wd1))
	     (equal (b1p (bv-eqv *word-size* wd0 wd1)) (equal wd0 wd1)))
  :hints (("Goal" :in-theory (enable word-p))))

(defthm addr-p-bv-eqv-iff-equal
    (implies (and (addr-p wd0) (addr-p wd1))
	     (equal (b1p (bv-eqv *addr-size* wd0 wd1)) (equal wd0 wd1)))
  :hints (("Goal" :in-theory (enable addr-p))))

(defthm rname-p-bv-eqv-iff-equal
    (implies (and (rname-p wd0) (rname-p wd1))
	     (equal (b1p (bv-eqv *rname-size* wd0 wd1)) (equal wd0 wd1)))
  :hints (("Goal" :in-theory (enable rname-p))))

(defthm immediate-p-bv-eqv-iff-equal
    (implies (and (immediate-p wd0) (immediate-p wd1))
	     (equal (b1p (bv-eqv *immediate-size* wd0 wd1)) (equal wd0 wd1)))
  :hints (("Goal" :in-theory (enable immediate-p))))

(defthm opcd-p-bv-eqv-iff-equal
    (implies (and (opcd-p wd0) (opcd-p wd1))
	     (equal (b1p (bv-eqv *opcode-size* wd0 wd1)) (equal wd0 wd1)))
  :hints (("Goal" :in-theory (enable opcd-p))))

(deflist word-listp (l)
  (declare (xargs :guard t))
  word-p)

(defun fixlen-word-listp (n lst)
  "test if list is a array of n words."
  (declare (xargs :guard (and (integerp n) (<= 0 n))))
  (and (word-listp lst) (equal (len lst) n)))

(defthm fixlen-word-true-listp
    (implies (fixlen-word-listp n x)
	     (true-listp x))
  :rule-classes :forward-chaining)

(in-theory (disable fixlen-word-listp))

; Register file is a fixed length true list of words.
(defun RF-p (RF)
  (declare (xargs :guard t))
  (fixlen-word-listp *num-regs* RF))

(defthm RF-p-true-listp
    (implies (RF-p x)
	     (true-listp x))
  :rule-classes :forward-chaining)

(defun read-reg (r RF)
  (declare (xargs :guard (and (rname-p r) (RF-p RF))))
  (nth r RF))

(defun write-reg (val r RF)
  (declare (xargs :guard (and (word-p val) (rname-p r) (RF-p RF))))
  (update-nth r val RF))

(defthm RF-p-write-reg
    (implies (and (word-p word)
		  (rname-p rname)
		  (RF-p RF))
	     (RF-p (write-reg word rname RF)))
  :hints (("Goal" :in-theory (enable RF-p fixlen-word-listp
				     rname-p UNSIGNED-BYTE-P
				     len-update-nth))))

(local
(defthm nth-content-word-listp
    (implies (and (integerp n)
		  (<= 0 n)
		  (word-listp lst)
		  (< n (len lst)))
	     (and (integerp (nth n lst))
		  (acl2-numberp (nth n lst))))
  :hints (("Goal" :use ((:instance word-listp-nth (n0 n) (l lst)))
		  :in-theory (disable word-listp-nth)))))

(defthm numberp-read-reg
    (implies (and (RF-p RF)
		  (rname-p rname))
	     (and (integerp (read-reg rname RF))
		  (acl2-numberp (read-reg rname RF))))
  :hints (("Goal" :in-theory (enable rname-p RF-p fixlen-word-listp)))
  :rule-classes
  ((:type-prescription) (:rewrite)))

(defthm word-p-read-reg
    (implies (and (RF-p RF)
		  (rname-p rname))
	     (word-p (read-reg rname RF)))
  :hints (("Goal" :in-theory (enable rname-p RF-p fixlen-word-listp))))

(defthm read-reg-write-reg
    (implies (and (rname-p r1)
		  (rname-p r2)
		  (RF-p RF))
	     (equal (read-reg r1 (write-reg val r2 RF))
		    (if (equal r1 r2) val (read-reg r1 RF))))
  :hints (("Goal" :in-theory (enable read-reg write-reg RF-p
				     nth-update-nth))))

(in-theory (disable RF-p write-reg read-reg))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Here we define the memory system.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defconst *no-access* 0)
(defconst *read-only* 1)
(defconst *read-write* 2)

;;  Definition of Address Transformers.
;;  page-num Address --> Page number 
;;  page-offset Address --> Page Offset
(defun page-num (addr)
  (declare (xargs :guard (addr-p addr)))
  (floor addr *num-page-words*))

(defun page-offset (addr)
  (declare (xargs :guard (addr-p addr)))
  (mod addr *num-page-words*))

(defthm page-num-type
    (implies (addr-p addr)
	     (and (integerp (page-num addr))
		  (<= 0 (page-num addr))))
  :rule-classes :type-prescription)

(defthm page-num-bound
    (implies (addr-p addr)
	     (< (page-num addr) *num-pages*))
  :hints (("Goal" :in-theory (enable addr-p unsigned-byte-p)))
  :rule-classes :linear)

(defthm page-offset-type
    (implies (addr-p addr)
	     (and (integerp (page-offset addr))
		  (<= 0 (page-offset addr))))
  :rule-classes :type-prescription)

(defthm page-offset-bound
    (implies (addr-p addr)
	     (< (page-offset addr) *num-page-words*))
  :rule-classes :linear)
	     
(in-theory (disable page-num page-offset))
;;  End of Address Transformers

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Definition of Memory Object
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Check if page is an array representing a page.
; Addr does not affect the value, but if the correct page tag is given,
; execution is faster.
(defun word-array-p (array)
  (declare (xargs :guard (alistp array)
		  :verify-guards nil))
  (cond ((endp array) t)
	((equal (caar array) ':header) (word-array-p (cdr array)))
	(t (and (word-p (cdar array))
		(word-array-p (cdr array))))))

(verify-guards word-array-p
	       :hints (("Goal" :in-theory (enable alistp))))

(defun page-array-p (tag page-array)
  (declare (xargs :guard t))
  (and (array1p tag page-array)
       (equal (car (dimensions tag page-array)) *num-page-words*)
       (word-p (default tag page-array))
       (word-array-p page-array)))

(defstructure page
  (tag (:assert (symbolp tag) :rewrite))
  (mode (:assert (integerp mode) :rewrite))
  (array (:assert (page-array-p tag array) :rewrite))
  (:options :guards))

(defun mem-array-p (array)
  (declare (xargs :guard (alistp array)
		  :verify-guards nil))
  (cond ((endp array) t)
	((equal (caar array) ':header) (mem-array-p (cdr array)))
	(t (and (let ((page (cdar array)))
		  (if (integerp page)
		      (or (equal page *no-access*) (equal page *read-only*)
			  (equal page *read-write*))
		      (page-p page)))
		(mem-array-p (cdr array))))))

(verify-guards mem-array-p :hints (("Goal" :in-theory (enable alistp))))

(defun mem-p (mem)
  (declare (xargs :guard t))
  (and (array1p 'mem mem)
       (equal (car (dimensions 'mem mem)) *num-pages*)
       (equal (default 'mem mem) *no-access*)
       (mem-array-p mem)))

(in-theory (disable word-array-p page-array-p mem-array-p mem-p))

(defthm page-p-type
    (implies (page-p p)
	     (consp p))
  :hints (("Goal" :in-theory (enable page-p)))
  :rule-classes :compound-recognizer)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  Definition of Read-mem 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmacro get-page (n mem)
  `(aref1 'mem ,mem ,n))

(defmacro set-page (page n mem)
  `(aset1 'mem ,mem ,n ,page))

(defun read-page (offset page)
  (declare (xargs :guard (and (page-p page)
			      (integerp offset) (<= 0 offset)
			      (< offset *num-page-words*))
		  :verify-guards nil))
  (aref1 (page-tag page) (page-array page) offset))

(defun read-mem (addr mem)
  (declare (xargs :guard (and (addr-p addr) (mem-p mem))
		  :verify-guards nil))
  (let ((page (get-page (page-num addr) mem)))
    (if (integerp page)
	0
	(read-page (page-offset addr) page))))

(verify-guards read-page
  :hints (("Goal" :in-theory (enable page-p page-array-p))))

(encapsulate nil
(local 
 (defthm page-p-assoc-mem-array
     (implies (and (mem-array-p mem)
		   (integerp pn)
		   (assoc pn mem)
		   (not (integerp (cdr (assoc pn mem)))))
	      (page-p (cdr (assoc pn mem))))
   :hints (("Goal" :in-theory (enable assoc mem-array-p)))))

(local 
 (defthm integerp-default-in-mem-array
     (implies (mem-p mem)
	      (integerp (default 'mem mem)))
   :hints (("Goal" :in-theory (enable mem-p)))))

(defthm page-p-get-page
    (implies (and (mem-p mem)
		  (integerp pn)
		  (not (integerp (get-page pn mem))))
	     (page-p (get-page pn mem)))
  :hints (("Goal" :in-theory (enable aref1 mem-p))))
)

(local   
 (defthm word-p-assoc-word-array
     (implies (and (word-array-p wa)
		   (integerp pn)
		   (assoc pn wa))
	      (word-p (cdr (assoc pn wa))))
   :hints (("Goal" :in-theory (enable word-array-p assoc)))))

(encapsulate nil
(defthm word-p-read-page
    (implies (and (page-p page)
		  (integerp offset))
	     (word-p (read-page offset page)))
  :hints (("Goal" :in-theory (enable page-p aref1 page-array-p))))
)

(in-theory (disable read-page read-mem))
(verify-guards read-mem
	       :hints (("goal" :in-theory (enable mem-p))))

(defthm word-p-read-mem
    (implies (and (mem-p mem)
		  (addr-p addr))
	     (word-p (read-mem addr mem)))
  :hints (("Goal" :in-theory (enable read-mem)))
  :rule-classes
  ((:rewrite)
   (:type-prescription :corollary
		       (implies (and (mem-p mem) (addr-p addr))
				(and (integerp (read-mem addr mem))
				     (>= (read-mem addr mem) 0))))
   (:rewrite :corollary
	     (implies (and (mem-p mem) (addr-p addr))
		      (acl2-numberp (read-mem addr mem))))))

   

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Definition of Write-Mem
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Page tag is calculated for fast array accesses. 
; The tag for the <n>'th page is given by page<n>.
(defun gen-page-tag (page-num)
  (declare (xargs :guard (and (integerp page-num)
			      (>= page-num 0))
		  :verify-guards nil))
  (pack-intern 'mem
       (coerce (append (coerce (symbol-name 'page) 'list)
                       ;; Matt K. mod: explode-nonnegative-integer now takes a
                       ;; base, so added argument of 10 here.
		       (explode-nonnegative-integer page-num 10 nil))
	       'string)))

(encapsulate nil
(local
 (defthm character-listp-explode-nonnegative-integer-help
     (implies (and (integerp n) (>= n 0)
		   (character-listp x))
              ;; Matt K. mod: explode-nonnegative-integer now takes a
              ;; base, so added argument of base here.
	      (character-listp (explode-nonnegative-integer n base x)))
   :hints (("goal" :in-theory (enable explode-nonnegative-integer
				      character-listp)))))

(local
 (defthm character-listp-explode-nonnegative-integer
     (implies (and (integerp n) (>= n 0))
              ;; Matt K. mod: explode-nonnegative-integer now takes a
              ;; base, so added argument of base here.
	      (character-listp (explode-nonnegative-integer n base nil)))))

; Matt K. mod: Avoid name conflict with built-in rule.
; (local
;  (defthm true-listp-explode-nonnegative-integer
;      (implies (true-listp x)
; 	        (true-listp (explode-nonnegative-integer n 10 x)))))
       
(verify-guards gen-page-tag
     :hints (("goal" :in-theory (enable U::coerce-string-designator-list
					U::STRING-DESIGNATOR-LISTP
					character-listp
					binary-append))))
)

(defun init-page (page-num mode)
  (declare (xargs :guard (and (integerp page-num) (<= 0 page-num)
			      (integerp mode))
		  :verify-guards nil))
  (let ((name (gen-page-tag page-num)))
    (page name
	  mode
	  (compress1 name `((:header :name ,name
			     :dimensions (,*num-page-words*)
			     :default 0
			     :maximum-length 4096))))))

(verify-guards init-page
 :hints (("Goal" :in-theory (enable array1p alistp
				    keyword-value-listp
				    assoc-eq
				    assoc-keyword
				    bounded-integer-alistp))))

(defun write-page (val offset page)
  (declare (xargs :guard (and (word-p val)
			      (integerp offset) (<= 0 offset)
			      (< offset *num-page-words*)
			      (page-p page))
		  :verify-guards nil))
  (update-page page
	       :array (aset1 (page-tag page) (page-array page) offset val)))

(defun write-mem (val addr mem)
  (declare (xargs :guard (and (word-p val) (addr-p addr) (mem-p mem))
		  :verify-guards nil))
  (let ((page (get-page (page-num addr) mem)))
    (if (integerp page)
	(let ((p (init-page (page-num addr) page)))
	  (set-page (write-page val (page-offset addr) p)
		    (page-num addr)
		    mem))
	(set-page (write-page val (page-offset addr) page)
		  (page-num addr)
		  mem))))

(verify-guards write-page
  :hints (("Goal" :in-theory (enable page-p page-array-p)))) 

(in-theory (disable  write-mem init-page gen-page-tag write-page))

(defthm page-p-init-page
    (implies (integerp mode)
	     (page-p (init-page pn mode)))
  :hints (("goal" :in-theory (enable page-p init-page page-array-p
				     default dimensions
				     header array1p word-array-p))))

(verify-guards write-mem
  :hints (("Goal" :in-theory (enable mem-p ))))

(local
(defthm word-array-p-compress11
    (implies (and (array1p tag array)
		  (word-array-p array)
		  (integerp i))
	     (word-array-p (compress11 tag array i dim default)))
  :hints (("Goal" :in-theory (enable word-array-p)))))

; Matt K. mod: Add the following lemma, needed for the proof of
; word-array-p-compress1.
(defthm word-array-p-revappend
  (implies (and (word-array-p x)
                (word-array-p y))
           (word-array-p (revappend x y)))
  :hints (("Goal" :in-theory (enable word-array-p))))

(defthm word-array-p-compress1
    (implies (and (array1p tag array)
		  (word-array-p array))
	     (word-array-p (compress1 tag array)))
  :hints (("Goal" :in-theory (enable compress1 word-array-p))))

(defthm word-array-p-aset1
    (implies (and (array1p tag page-array)
		  (word-array-p page-array)
		  (integerp index)
		  (>= index 0)
		  (> (car (dimensions tag page-array)) index)
		  (word-p val))
	     (word-array-p (aset1 tag page-array index val)))
  :hints (("goal" :in-theory (enable aset1 word-array-p ARRAY1P-CONS))))

(defthm page-array-p-aref1
    (implies (and (page-array-p tag page-array)
		  (word-p val)
		  (integerp offset)
		  (>= offset 0)
		  (> *num-page-words* offset))
	     (page-array-p tag (aset1 tag page-array offset val)))
  :hints (("Goal" :in-theory (enable page-array-p))))

(defthm page-p-write-page
    (implies (and (word-p val)
		  (integerp offset)
		  (>= offset 0)
		  (> *num-page-words* offset)
		  (page-p page))
	     (page-p (write-page val offset page)))
  :hints (("Goal" :in-theory (enable write-page))))

(local   
 (defthm valid-integer-assoc-mem-array
     (implies (and (mem-array-p ma) 
		   (integerp pn)
		   (assoc pn ma)
		   (integerp (cdr (assoc pn ma)))
		   (not (equal (cdr (assoc pn ma)) 0))
		   (not (equal (cdr (assoc pn ma)) 1)))
	      (equal (cdr (assoc pn ma)) 2))
   :hints (("Goal" :in-theory (enable mem-array-p assoc)))))

(local   
 (defthm page-p-assoc-mem-array
     (implies (and (mem-array-p ma) 
		   (integerp pn)
		   (assoc pn ma)
		   (not (integerp (cdr (assoc pn ma)))))
	      (page-p (cdr (assoc pn ma))))
   :hints (("Goal" :in-theory (enable mem-array-p assoc)))))

(local
(defthm mem-array-p-compress11
    (implies (and (array1p tag array)
		  (mem-array-p array)
		  (integerp i))
	     (mem-array-p (compress11 tag array i dim default)))
  :hints (("Goal" :in-theory (enable mem-array-p compress1)))))

; Matt K. mod: Add the following lemma, needed for the proof of
; mem-array-p-compress1.
(defthm mem-array-p-revappend
  (implies (and (mem-array-p x)
                (mem-array-p y))
           (mem-array-p (revappend x y)))
  :hints (("Goal" :in-theory (enable mem-array-p))))

(defthm mem-array-p-compress1
    (implies (and (array1p tag array)
		  (mem-array-p array))
	     (mem-array-p (compress1 tag array)))
  :hints (("Goal" :in-theory (enable mem-array-p compress1))))

(defthm mem-array-p-aset1
    (implies (and (array1p tag mem-array)
		  (mem-array-p mem-array)
		  (or (page-p page)
		      (equal page *no-access*)
		      (equal page *read-only*)
		      (equal page *read-write*))
		  (integerp pn)
		  (>= pn 0)
		  (> (car (dimensions tag mem-array)) pn))
	     (mem-array-p (aset1 tag mem-array pn page)))
  :hints (("Goal" :in-theory (enable mem-array-p aset1))))

(defthm mem-p-write-mem
    (implies (and (word-p val)
		  (addr-p addr)
		  (mem-p mem))
	     (mem-p (write-mem val addr mem)))
  :hints (("goal" :in-theory (enable mem-p write-mem))))

(defthm page-num-offset-extensionality
    (implies (and (addr-p addr1)
		  (addr-p addr2)
		  (equal (page-num addr1) (page-num addr2))
		  (equal (page-offset addr1) (page-offset addr2)))
	     (equal addr1 addr2))
  :hints (("Goal" :in-theory (enable addr-p page-num page-offset)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (addr-p addr1)
			   (addr-p addr2)
			   (equal (page-num addr1) (page-num addr2))
			   (not (equal addr1 addr2)))
		      (equal (equal (page-offset addr1) (page-offset addr2))
			     nil)))))

(defthm read-page-init-page
    (implies (integerp offset)
	     (equal (read-page offset (init-page pn mode)) 0))
  :hints (("Goal" :in-theory (enable init-page read-page aref1
				     default header))))

(defthm read-page-write-page
    (implies (and (page-p page)
		  (integerp offset1)
		  (>= offset1 0)
		  (> *num-page-words* offset1)
		  (integerp offset2)
		  (>= offset2 0)
		  (> *num-page-words* offset2))
	     (equal (read-page offset1 (write-page val offset2 page))
		    (if (equal offset1 offset2)
			val
			(read-page offset1 page))))
  :hints (("Goal" :in-theory (enable page-p read-page write-page
				     page-array-p))))

(defthm read-mem-write-mem
    (implies (and (addr-p a1)
		  (addr-p a2)
		  (mem-p mem))
	     (equal (read-mem a1 (write-mem val a2 mem))
		    (if (equal a1 a2) val (read-mem a1 mem))))
  :hints (("Goal" :in-theory (enable read-mem write-mem
				     mem-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Definition of Protection Checks.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun readable-addr-p (ad mem)
  (declare (xargs :guard (and (addr-p ad) (mem-p mem))
		  :verify-guards nil))
  (let ((page (get-page (page-num ad) mem)))
    (if (integerp page)
	(or (equal page *read-only*)
	    (equal page *read-write*))
	(or (equal (page-mode page) *read-only*)
	    (equal (page-mode page) *read-write*)))))

(verify-guards  readable-addr-p
 :hints (("Goal" :in-theory (enable mem-p))))

(defun readable-addr? (ad mem)
  (declare (xargs :guard (and (addr-p ad) (mem-p mem))))
  (if (readable-addr-p ad mem) 1 0))

(defthm bitp-readable-addr (bitp (readable-addr? ad mem)))

(defun writable-addr-p (ad mem)
  (declare (xargs :guard (and (addr-p ad) (mem-p mem))
		  :verify-guards nil))
  (let ((page (get-page (page-num ad) mem)))
    (if (integerp page)
	(equal page *read-write*)
	(equal (page-mode page) *read-write*))))

(verify-guards  writable-addr-p
 :hints (("Goal" :in-theory (enable mem-p))))

(defun writable-addr? (ad mem)
  (declare (xargs :guard (and (addr-p ad) (mem-p mem))))
  (if (writable-addr-p ad mem) 1 0))

(defthm bitp-writable-addr (bitp (writable-addr? ad mem)))

(defun set-page-mode (mode pn mem)
  (declare (xargs :guard (and (integerp mode)
			      (integerp pn) (<= 0 pn) (< pn *num-pages*)
			      (mem-p mem))
		  :verify-guards nil))
  (let ((page (get-page pn mem)))
    (if (integerp page)
	(set-page mode pn mem)
	(set-page (update-page page :mode mode) pn mem))))

(verify-guards set-page-mode
	:hints (("Goal" :in-theory (enable mem-p))))      

(defthm mem-p-set-page-mode
    (implies (and (mem-p mem)
		  (integerp mode)
		  (or (equal mode *no-access*)
		      (equal mode *read-only*)
		      (equal mode *read-write*))
		  (integerp pn) (<= 0 pn) (< pn *num-pages*))
	     (mem-p (set-page-mode mode pn mem)))
  :hints (("Goal" :in-theory (enable mem-p))))

(defthm page-mode-init-page
    (equal (page-mode (init-page page-num mode)) mode)
  :hints (("Goal" :in-theory (enable init-page))))

(defthm page-mode-write-page
    (equal (page-mode (write-page val offset page))
	   (page-mode page))
  :hints (("Goal" :in-theory (enable write-page))))

(defthm readable-addr-p-set-page-mode
    (implies (and (integerp mode)
		  (addr-p addr)
		  (integerp pn1) (<= 0 pn1) (< pn1 *num-pages*)
		  (mem-p mem))
	     (equal (readable-addr-p addr (set-page-mode mode pn1 mem))
		    (if (equal (page-num addr) pn1)
			(or (equal mode *read-only*) (equal mode *read-write*))
			(readable-addr-p addr mem))))
  :hints (("Goal" :in-theory (enable set-page-mode mem-p
				     readable-addr-p))))

(defthm readable-addr-set-page-mode
    (implies (and (integerp mode)
		  (addr-p addr)
		  (integerp pn1) (<= 0 pn1) (< pn1 *num-pages*)
		  (mem-p mem))
	     (equal (readable-addr? addr (set-page-mode mode pn1 mem))
		    (if (equal (page-num addr) pn1)
			(if (or (equal mode *read-only*)
				(equal mode *read-write*))
			    1 0)
			(readable-addr? addr mem))))
  :hints (("Goal" :in-theory (e/d (readable-addr?) (readable-addr-p
						    SET-PAGE-MODE)))))

(defthm writable-addr-p-set-page-mode
    (implies (and (integerp mode)
		  (addr-p addr)
		  (integerp pn1) (<= 0 pn1) (< pn1 *num-pages*)
		  (mem-p mem))
	     (equal (writable-addr-p addr (set-page-mode mode pn1 mem))
		    (if (equal (page-num addr) pn1)
			(equal mode *read-write*)
			(writable-addr-p addr mem))))
  :hints (("Goal" :in-theory (enable set-page-mode mem-p
				     writable-addr-p))))

(defthm writable-addr-set-page-mode
    (implies (and (integerp mode)
		  (addr-p addr)
		  (integerp pn1) (<= 0 pn1) (< pn1 *num-pages*)
		  (mem-p mem))
	     (equal (writable-addr? addr (set-page-mode mode pn1 mem))
		    (if (equal (page-num addr) pn1)
			(if (equal mode *read-write*) 1 0)
			(writable-addr? addr mem))))
  :hints (("Goal" :in-theory (e/d (writable-addr?)
				  (writable-addr-p SET-PAGE-MODE)))))

(defthm readable-addr-p-write-mem
    (implies (and (addr-p addr) (addr-p addr2) (word-p val) (mem-p mem))
	     (equal (readable-addr-p addr (write-mem val addr2 mem))
		    (readable-addr-p addr mem)))
  :hints (("Goal" :in-theory (enable readable-addr-p write-mem mem-p))))

(defthm readable-addr-write-mem
    (implies (and (addr-p addr) (addr-p addr2) (word-p val) (mem-p mem))
	     (equal (readable-addr? addr (write-mem val addr2 mem))
		    (readable-addr? addr mem)))
  :hints (("Goal" :in-theory (enable readable-addr?))))

(defthm writable-addr-p-write-mem
    (implies (and (addr-p addr) (addr-p addr2) (word-p val) (mem-p mem))
	     (equal (writable-addr-p addr (write-mem val addr2 mem))
		    (writable-addr-p addr mem)))
  :hints (("Goal" :in-theory (enable writable-addr-p write-mem mem-p))))

(defthm writable-addr-write-mem
    (implies (and (addr-p addr) (addr-p addr2) (word-p val) (mem-p mem))
	     (equal (writable-addr? addr (write-mem val addr2 mem))
		    (writable-addr? addr mem)))
  :hints (("Goal" :in-theory (enable writable-addr?))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Initialize Memory
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defconst *init-mem*
    (compress1 'mem (list `(:header :name mem
			    :dimensions (,*num-pages*)
			    :default ,*no-access*
			    :maximum-length 2048))))

(defthm mem-p-init-mem
    (mem-p *init-mem*))

(deflist mem-alist-p (l)
  (declare (xargs :guard t))
  (lambda (l) (and (consp l) (addr-p (car l)) (word-p (cdr l)))))

(defun load-mem-alist (alist mem)
  (declare (xargs :guard (and (mem-alist-p alist) (mem-p mem))))
  (if (endp alist)
      mem
      (load-mem-alist (cdr alist) (write-mem (cdar alist) (caar alist) mem))))

(defthm mem-p-load-mem-alist
    (implies (and (mem-alist-p alist)
		  (mem-p mem))
	     (mem-p (load-mem-alist alist mem))))
    
(in-theory (disable page-p page-array-p word-array-p mem-p))
(in-theory (disable read-reg))
(in-theory (disable write-reg))
(in-theory (disable read-mem))
(in-theory (disable write-mem))
(in-theory (disable writable-addr-p readable-addr-p
		    writable-addr? readable-addr? set-page-mode))

(defword* word-layout ((opcode 4 12)
		       (rc *rname-size* 8)
		       (ra *rname-size* 4)
		       (rb *rname-size* 0)
		       (im *immediate-size* 0))
  :conc-name ||)

(defthm opcd-p-opcode
    (opcd-p (opcode inst))
  :hints (("Goal" :in-theory (enable opcd-p))))

(defthm rname-p-rc
    (rname-p (rc inst))
  :hints (("Goal" :in-theory (enable rname-p))))

(defthm rname-p-ra
    (rname-p (ra inst))
  :hints (("Goal" :in-theory (enable rname-p))))

(defthm rname-p-rb
    (rname-p (rb inst))
  :hints (("Goal" :in-theory (enable rname-p))))

(defthm immediate-p-immediate-field
    (immediate-p (im inst))
  :hints (("Goal" :in-theory (enable immediate-p))))

(defthm word-p-immediate-field
    (word-p (im inst))
  :hints (("Goal" :in-theory (enable word-p))))

(defthm word-im
    (equal (word (im i)) (im i))
  :hints (("goal" :in-theory (enable word))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  Definition of Special registers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defconst *num-sregs* 2)

(defstructure SRF
  (su (:assert (bitp su) :rewrite ))
  (sr0 (:assert (word-p sr0) :rewrite))
  (sr1 (:assert (word-p sr1) :rewrite))
  (:options :guards))

(defun srname-p (rname)
  (declare (xargs :guard t))
  (and (rname-p rname) (< rname *num-sregs*)))

(defthm srname-p-type
    (implies (srname-p rname)
	     (and (integerp rname)
		  (>= rname 0)
		  (< rname *num-sregs*)))
  :hints (("Goal" :in-theory (enable rname-p srname-p)))
  :rule-classes :forward-chaining)

(defun read-sreg (r SRF)
  (declare (xargs :guard (and (rname-p r) (SRF-p SRF))))
  (if (equal r 0) (SRF-sr0 SRF)
      (if (equal r 1) (SRF-sr1 SRF)
	  0)))

(defun write-sreg (val r SRF)
  (declare (xargs :guard (and (word-p val) (rname-p r) (SRF-p SRF))))
  (if (equal r 0) (SRF (SRF-su SRF) val (SRF-sr1 SRF))
      (if (equal r 1) (SRF (SRF-su SRF) (SRF-sr0 SRF) val)
	  SRF)))

(defthm word-p-read-sreg
    (implies (and (rname-p r) (SRF-p SRF))
	     (word-p (read-sreg r SRF))))

(defthm numberp-read-sreg
    (implies (and (SRF-p SRF)
		  (rname-p rname))
	     (and (integerp (read-sreg rname SRF))
		  (acl2-numberp (read-sreg rname SRF))))
  :hints (("Goal" :in-theory (enable rname-p SRF-p fixlen-word-listp)))
  :rule-classes
  ((:type-prescription) (:rewrite)))

(defthm SRF-p-write-sreg
    (implies (and (word-p val) (rname-p r) (SRF-p SRF))
	     (SRF-p (write-sreg val r SRF))))

(defthm read-sreg-write-sreg
    (implies (and (srname-p r1)
		  (srname-p r2)
		  (SRF-p SRF))
	     (equal (read-sreg r1 (write-sreg val r2 SRF))
		    (if (equal r1 r2) val (read-sreg r1 SRF))))
  :hints (("Goal" :in-theory (enable read-sreg write-sreg SRF-p
				     srname-p))))

(in-theory (disable read-sreg write-sreg srname-p))
