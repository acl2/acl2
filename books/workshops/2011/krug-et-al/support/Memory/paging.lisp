
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; paging.lisp
;;;
;;; We use the low level memory model as developed in memory-low.lisp
;;; to set up a system modeling AMD's 2-9-21 nested page tables.
;;;
;;; Based on work by Alan Dunn and Warren Hunt.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;; uncomment and comment to get Alan's fast and raw memory
;;;(include-book "memory-low" :ttags (memory))
(include-book "memory-low")

(include-book "../Utilities/bytes-and-words")
(include-book "../Utilities/disjoint")
(include-book "../Utilities/records")
(include-book "std/util/bstar" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Address translation --- virtual to physical

(defconst *cr0-pg-bit* 31)

(defun get-bit-32 (bit n)
  ;; Get the bit-th bit (0 is the rightmost bit) in 32-bit value n
  ;;
  ;; bit should be 0 <= bit < 32
  ;; n should be an n32p
  (declare (xargs :guard (and (integerp n)
                              (integerp bit))))
  (not (equal (logand n (ash 1 bit))
              0)))

(defun set-bit-32 (bit st n)
  ;; Set the bit-th bit (0 is the rightmost bit) in 32-bit value n to
  ;; st
  ;;
  ;; bit should be 0 <= bit < 32
  ;; st should be boolean
  ;; n should be an n32p
  (declare (xargs :guard (and (integerp n)
                              (integerp bit))))
  (let ((n32-bit (ash 1 bit)))
    (if st
	(logior n n32-bit)
      (logand n (n32 (lognot n32-bit))))))

;;; RBK: This test for paging is not correct, but should be good
;;; enough for now.

(defun paging-p (st)
  ;; Check whether protected mode addressing (for our purposes ---
  ;; paging) is on
  ;; Or do I want to use (y86-guard st) as the guard
  (declare (xargs :guard (integerp (g :cr0 st))))
  (let ((cr0 (g :cr0 st)))
    (get-bit-32 *cr0-pg-bit* cr0)))

(defun set-paging (paging-p st)
  ;; Or do I want to use (y86-guard st) as the guard
  (declare (xargs :guard (integerp (g :cr0 st))))
  (let ((cr0 (g :cr0 st)))
    (s :cr0 (set-bit-32 *cr0-pg-bit* paging-p cr0)
       st)))

(defconst *pg-mask*
  ;; top 20 bits are on, low 12 bits are off.  4K pages
  (ash (+ -1 (expt 2 20)) 12))

(defun pg-align (addr)
  ;; mask off the bottom 12 bits, retaining the top 20.
  ;; returns the base address of the page to which addr refers.
  (declare (xargs :guard (integerp addr)))
  (logand addr *pg-mask*))

(defconst *big-pg-mask*
  ;; top 11 bits are on, low 21 bits are off.  2M pages
  (ash (+ -1 (expt 2 11)) 21))

(defun big-pg-align (addr)
  ;; mask off the bottom 21 bits, retaining the top 11.
  ;; returns the base address of the page to which addr refers.
  (declare (xargs :guard (integerp addr)))
  (logand addr *big-pg-mask*))

(defun pdpt-index (address)
  ;; Bits 31 -- 30
  (declare (xargs :guard (integerp address)))
  (ash address -30))

(defun pdt-index (address)
  ;; Bits 29 -- 21
  (declare (xargs :guard (integerp address)))
  (logand (ash address -21) (1- (expt 2 9))))

(defun addr-offset (address)
  ;; the final 21 bits
  (declare (xargs :guard (integerp address)))
  (logand address (1- (expt 2 21))))

(defun present-bit-p (entry)
  ;; is the page visible?
  (declare (xargs :guard (integerp entry)))
  (get-bit-32 0 entry))

(defun get-pa (va st)
  (declare (xargs :guard (and (integerp va)
                              (integerp (g :cr3 st))
                              (memoryp (g :mem st)))))
  (b* ((mem (g :mem st))
       ;; PDPT handling
       (pdpt-base (pg-align (g :cr3 st)))
       (pdpt-index (pdpt-index va))
       (pdpt-entry (r32-low (+ pdpt-base (* 8 pdpt-index)) mem))
       ((when (not (present-bit-p pdpt-entry)))
	:PAGE-FAULT)

       ;; PDT handling
       (pdt-base (pg-align pdpt-entry))
       (pdt-index (pdt-index va))
       (pdt-entry (r32-low (+ pdt-base (* 8 pdt-index)) mem))
       ((when (not (present-bit-p pdt-entry)))
	:PAGE-FAULT)

       ;; Page handling
       (addr-base (big-pg-align pdt-entry))
       (addr-offset (addr-offset va)))
      (n32 (+ addr-base addr-offset))))

(defun va-to-pa (addr st)
  (declare (xargs :guard (and (integerp addr)
                              (integerp (g :cr0 st))
                              (integerp (g :cr3 st))
                              (memoryp (g :mem st)))))
  (if (paging-p st)
      (get-pa addr st)
    addr))

(defun safe-address-p (addr st)
  (not (equal (va-to-pa addr st)
              :PAGE-FAULT)))

(in-theory (disable get-bit-32
                    set-bit-32
                    paging-p
                    set-paging
                    pg-align
                    big-pg-align
                    pdpt-index
                    pdt-index
                    addr-offset
                    present-bit-p
                    get-pa
                    va-to-pa
                    safe-address-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Some theorems

;;; Interactions with s and g

(defthm |(paging-p (s field val st))|
  (implies (not (equal field :CR0))
           (equal (paging-p (s field val st))
                  (paging-p st)))
  :hints (("Goal" :in-theory (enable paging-p))))

(defthm |(va-to-pa addr (s field val st))|
  (implies (and (not (equal field :CR0))
                (not (equal field :CR3))
                (not (equal field :mem)))
           (equal (va-to-pa addr (s field val st))
                  (va-to-pa addr st)))
  :hints (("Goal" :in-theory (enable va-to-pa
                                     get-pa))))

;;; types and predicates

(defthm |(n32p (va-to-pa addr st))|
  (implies (and (n32p addr)
                (safe-address-p addr st))
           (n32p (va-to-pa addr st)))
  :hints (("goal" :in-theory (enable safe-address-p
                                     va-to-pa
                                     get-pa)))
  :rule-classes ((:rewrite)
                 (:rewrite
                  :hints (("Goal" :in-theory (enable paging-p
                                                     va-to-pa)))
                  :corollary
                  (implies (and (n32p addr)
                                (not (paging-p st)))
                           (n32p (va-to-pa addr st))))))

;; I would like to make this a type-prescription
(defthm |(integerp (va-to-pa addr st))|
  (implies (integerp addr)
           (equal (integerp (va-to-pa addr st))
                  (safe-address-p addr st)))
  :hints (("goal" :in-theory (enable safe-address-p
                                     va-to-pa
                                     get-pa)))
  :rule-classes ((:rewrite)
                 (:rewrite
                  :hints (("Goal" :in-theory (enable paging-p
                                                     va-to-pa
                                                     safe-address-p)))
                  :corollary
                  (implies (and (integerp addr)
                                (not (paging-p st)))
                           (safe-address-p addr st)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; address translation

(defthm |(va-to-pa addr st)|
  (implies (not (paging-p st))
           (equal (va-to-pa addr st)
                  addr))
  :hints (("Goal" :in-theory (enable va-to-pa))))

(defun page-table-ranges (st)
  (b* ((mem (g :mem st))
       ;; PDPT
       (pdpt-base (pg-align (g :cr3 st)))
       (pdpt-entry-0 (r32-low (+ pdpt-base (* 8 0)) mem))
       ;; first PDT
       (pdt-base-0 (pg-align pdpt-entry-0))
       (pdpt-entry-1 (r32-low (+ pdpt-base (* 8 1)) mem))
       ;; second PDT
       (pdt-base-1 (pg-align pdpt-entry-1))
       (pdpt-entry-2 (r32-low (+ pdpt-base (* 8 2)) mem))
       ;; third PDT
       (pdt-base-2 (pg-align pdpt-entry-2))
       (pdpt-entry-3 (r32-low (+ pdpt-base (* 8 3)) mem))
       ;; fourth PDT
       (pdt-base-3 (pg-align pdpt-entry-3)))
      (append (range pdpt-base 0 32)
             (range pdt-base-0 0 4096)
             (range pdt-base-1 0 4096)
             (range pdt-base-2 0 4096)
             (range pdt-base-3 0 4096))))


(encapsulate
 ()

 (local
  (include-book "arithmetic-5/top" :dir :system))

 (local
  (defthm crock-0
    (implies (n32p x)
             (and (integerp (pdpt-index x))
                  (<= 0 (pdpt-index x))
                  (< (pdpt-index x) 4)))
    :hints (("goal" :in-theory (enable pdpt-index)))
    :rule-classes ((:type-prescription
                    :corollary (implies (n32p x)
                                        (and (integerp (pdpt-index x))
                                             (<= 0 (pdpt-index x)))))
                   (:linear :corollary (implies (n32p x)
                                                (and (<= 0 (pdpt-index x))
                                                     (< (pdpt-index x) 4)))))))

 (local
  (defthm crock-1
    (and (integerp (pdt-index x))
         (<= 0 (pdt-index x))
         (< (pdt-index x) 512))
    :hints (("Goal" :in-theory (enable pdt-index)))
    :rule-classes ((:type-prescription
                    :corollary
                    (and (integerp (pdt-index x))
                         (<= 0 (pdt-index x))))
                   (:linear
                    :corollary
                    (and (<= 0 (pdt-index x))
                         (< (pdt-index x) 512))))))

 (local
  (defthm crock-2
    (implies (n32p x)
             (n32p (pg-align x)))
    :hints (("Goal" :in-theory (enable pg-align)))))

 (local
  (defthm crock-3
    (implies (and (integerp c)
                  (<= 0 c)
                  (< c 4096))
             (and (n32p (+ c
                           (PG-ALIGN
                            y)))
                  (n32p (+ (PG-ALIGN
                            y)
                           c))))
    :hints (("Goal" :in-theory (enable pg-align)))))

 (local
  (defthm crock-4
    (implies (and (n32p x)
                  (n32p y))
             (n32p (+ (ADDR-OFFSET x)
                      (BIG-PG-ALIGN
                       y))))
    :hints (("Goal" :in-theory (enable addr-offset
                                       big-pg-align)))))

 (local
  (defthm crock-10
    (N32P (+ (ADDR-OFFSET x)
             (BIG-PG-ALIGN y)))
    :hints (("Goal" :in-theory (enable addr-offset
                                       big-pg-align)))))

 (local
  (defthm crock-11
    (implies (n32p addr1)
             (N32P (+ 3 (* 8 (PDT-INDEX ADDR1)) (PG-ALIGN x))))
    :hints (("Goal" :in-theory (e/d (pdt-index
                                     pg-align)
                                    (logand-constant-mask))))))

;;; The use the case split is irritating, but perhaps necessary.
;;; Without it we fail with goals such as:
 #||
 (IMPLIES
 (AND
 (N32P ADDR1)
 (N32P ADDR2)
 (WORD-ALIGNED-P ADDR2)
 (N32P (G :CR3 ST))
 (MEMORYP (G :MEM ST))
 (PAGING-P ST)
 (NOT
 (PRESENT-BIT-P (R32-LOW (+ (* 8 (PDT-INDEX ADDR2))
 (PG-ALIGN (R32-LOW (+ (PG-ALIGN (G :CR3 ST))
 (* 8 (PDPT-INDEX ADDR2)))
 (G :MEM ST))))
 (G :MEM ST))))
 (DISJOINTP (LIST (RANGE ADDR2 0 4)
 (RANGE (PG-ALIGN (G :CR3 ST)) 0 32)
 (RANGE (PG-ALIGN (R32-LOW (PG-ALIGN (G :CR3 ST))
 (G :MEM ST)))
 0 4096)
 (RANGE (PG-ALIGN (R32-LOW (+ 8 (PG-ALIGN (G :CR3 ST)))
 (G :MEM ST)))
 0 4096)
 (RANGE (PG-ALIGN (R32-LOW (+ 16 (PG-ALIGN (G :CR3 ST)))
 (G :MEM ST)))
 0 4096)
 (RANGE (PG-ALIGN (R32-LOW (+ 24 (PG-ALIGN (G :CR3 ST)))
 (G :MEM ST)))
 0 4096)))
 (PRESENT-BIT-P (R32-LOW (+ (PG-ALIGN (G :CR3 ST))
 (* 8 (PDPT-INDEX ADDR1)))
 (G :MEM ST)))
 (PRESENT-BIT-P (R32-LOW (+ (* 8 (PDT-INDEX ADDR1))
 (PG-ALIGN (R32-LOW (+ (PG-ALIGN (G :CR3 ST))
 (* 8 (PDPT-INDEX ADDR1)))
 (G :MEM ST))))
 (W32-LOW ADDR2 VAL (G :MEM ST)))))
 (PRESENT-BIT-P (R32-LOW (+ (* 8 (PDT-INDEX ADDR1))
 (PG-ALIGN (R32-LOW (+ (PG-ALIGN (G :CR3 ST))
 (* 8 (PDPT-INDEX ADDR1)))
 (G :MEM ST))))
 (G :MEM ST))))
 ||#
;;; Consider the term:
 #||
 (R32-LOW (+ (* 8 (PDT-INDEX ADDR1))
 (PG-ALIGN (R32-LOW (+ (PG-ALIGN (G :CR3 ST))
 (* 8 (PDPT-INDEX ADDR1)))
 (G :MEM ST))))
 (W32-LOW ADDR2 VAL (G :MEM ST)))
 ||#
;;; in the final hypothesis.  To which range does the read address
;;; belong?  This can only be known if we know the value of
;;; (PDPT-INDEX ADDR1).
;;;
;;; Is this a sign that my approach is wrong-headed?

;;; What is the proper form for this rule?

;;; Should I add a predicate for a set of well formed tables --- that
;;; all entries are (at least) page aligned?

 (local
  (defthm crock-20-1
    (implies (subrangep x y)
             (subrangep x (append y z)))
    :hints (("Goal" :in-theory (enable subrangep
                                       memberp)))))

 (local
  (defthm crock-20-2
    (implies (subrangep x z)
             (subrangep x (append y z)))
    :hints (("Goal" :in-theory (enable subrangep
                                       memberp)))))

 (local
  (defthm crock-20
    (implies (or (subrangep x (RANGE (PG-ALIGN (G :CR3 ST)) 0 32))
                 (subrangep x (RANGE (PG-ALIGN (R32-LOW (PG-ALIGN (G :CR3 ST))
                                                        (G :MEM ST)))
                                     0 4096))
                 (subrangep x (RANGE (PG-ALIGN (R32-LOW (+ 8 (PG-ALIGN (G :CR3 ST)))
                                                        (G :MEM ST)))
                                     0 4096))
                 (subrangep x (RANGE (PG-ALIGN (R32-LOW (+ 16 (PG-ALIGN (G :CR3 ST)))
                                                        (G :MEM ST)))
                                     0 4096))
                 (subrangep x (RANGE (PG-ALIGN (R32-LOW (+ 24 (PG-ALIGN (G :CR3 ST)))
                                                        (G :MEM ST)))
                                     0 4096)))
             (subrangep x (page-table-ranges st)))))

 (defthm |(va-to-pa addr1 (w08-low addr2 val mem))|
   (implies (and (n32p addr1)
                 (n32p addr2)
                 (disjointp (list (list addr2)
                                  (page-table-ranges st)))
                 (n32p (g :CR3 st))
                 (memoryp (g :mem st)))
            (equal (va-to-pa addr1 (s :mem
                                      (w08-low addr2 val (g :mem st))
                                      st))
                   (va-to-pa addr1 st)))
   :hints (("Goal" :in-theory (e/d (va-to-pa
                                    get-pa)
                                   (page-table-ranges))
            :cases ((equal (PDPT-INDEX ADDR1) 0)
                    (equal (PDPT-INDEX ADDR1) 1)
                    (equal (PDPT-INDEX ADDR1) 2)
                    (equal (PDPT-INDEX ADDR1) 3)))))

 (defthm |(va-to-pa addr1 (w32-low addr2 val mem))|
   (implies (and (n32p addr1)
                 (n32p addr2)
                 (n32p (+ 3 addr2))
                 (disjointp (list (range addr2 0 4)
                                  (page-table-ranges st)))
                 (n32p (g :CR3 st))
                 (memoryp (g :mem st)))
            (equal (va-to-pa addr1 (s :mem
                                      (w32-low addr2 val (g :mem st))
                                      st))
                   (va-to-pa addr1 st)))
   :hints (("Goal" :in-theory (enable va-to-pa
                                      get-pa)
            :cases ((equal (PDPT-INDEX ADDR1) 0)
                    (equal (PDPT-INDEX ADDR1) 1)
                    (equal (PDPT-INDEX ADDR1) 2)
                    (equal (PDPT-INDEX ADDR1) 3)))))
 )

(in-theory (disable page-table-ranges))
