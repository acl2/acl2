
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; memory-low.lisp
;;;
;;; Uses memory-acl2 (potentially, memory-raw) to set up a model of
;;; the X86's physical address 32-bit memory system.  Addresses are
;;; (assumed to be) 32-bit, values are (assumed to
;;; be) 32-bit.
;;;
;;; From work by Warren Hunt and/or Alan Dunn.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../Utilities/bytes-and-words")
(include-book "../Utilities/disjoint")

(include-book "memory-acl2")

;;; uncomment to get Alan's fast and raw memory
;;;(include-book "memory-raw" :ttags (memory)) ; must be included second

(local
 (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Basic definitions

(defun r08-low (addr mem)
  (declare (xargs :guard t))
  (read-mem-byte addr mem))

(defun w08-low (addr val mem)
  (declare (xargs :guard (integerp addr)))
  (write-mem-byte addr val mem))

(defun r32-low (addr mem)
  ;; We prove equivalence with a simpler definition below, given our
  ;; assumptions about addresses.
  (declare (xargs :guard (integerp addr)))
  (let ((byte0 (ifix (read-mem-byte         addr  mem)))
        (byte1 (ifix (read-mem-byte (n32+ 1 addr) mem)))
        (byte2 (ifix (read-mem-byte (n32+ 2 addr) mem)))
        (byte3 (ifix (read-mem-byte (n32+ 3 addr) mem))))
    (n32+ (ash byte3 24)
          (n32+ (ash byte2 16)
                (n32+ (ash byte1 8)
                      byte0)))))

(defun w32-low (addr val mem)
  ;; We prove equivalence with a simpler definition below, given our
  ;; assumptions about addresses and values.
  (declare (xargs :guard (and (integerp addr)
                              (integerp val))))
  (let ((byte0 (n08          val))
	(byte1 (n08 (ash val  -8)))
	(byte2 (n08 (ash val -16)))
	(byte3 (n08 (ash val -24))))
    (let* ((mem (write-mem-byte         addr  byte0 mem))
	   (mem (write-mem-byte (n32+ 1 addr) byte1 mem))
	   (mem (write-mem-byte (n32+ 2 addr) byte2 mem))
	   (mem (write-mem-byte (n32+ 3 addr) byte3 mem)))
      mem)))

(local
 (defthm crock-1
   (and (implies (and (n08p n1)
                      (n08p n2))
                 (n32p (+ n1
                          (* 256
                             n2))))
        (implies (and (n08p n1)
                      (n08p n2)
                      (n08p n3))
                 (n32p (+ n1
                          (* 256
                             n2)
                          (* 65536
                             n3))))
        (implies (and (n08p n1)
                      (n08p n2)
                      (n08p n3)
                      (n08p n4))
                 (n32p (+ n1
                          (* 256
                             n2)
                          (* 65536
                             n3)
                          (* 16777216
                             n4)))))))

(defthm r32-low-alt-def
  (implies (and (n32p addr)
                (n32p (+ 3 addr))
                (memoryp mem))
           (equal (r32-low addr mem)
                  (let ((byte0 (read-mem-byte      addr  mem))
                        (byte1 (read-mem-byte (+ 1 addr) mem))
                        (byte2 (read-mem-byte (+ 2 addr) mem))
                        (byte3 (read-mem-byte (+ 3 addr) mem)))
                    (+ (ash byte3 24)
                       (+ (ash byte2 16)
                          (+ (ash byte1 8)
                             byte0))))))
  :rule-classes :definition)

 (defthm w32-low-alt-def
   (implies (and (n32p addr)
                 (n32p (+ 3 addr))
                 (memoryp mem))
            (equal (w32-low addr val mem)
                   (let ((byte0 (n08          val))
                         (byte1 (n08 (ash val  -8)))
                         (byte2 (n08 (ash val -16)))
                         (byte3 (n08 (ash val -24))))
                     (let* ((mem (write-mem-byte      addr  byte0 mem))
                            (mem (write-mem-byte (+ 1 addr) byte1 mem))
                            (mem (write-mem-byte (+ 2 addr) byte2 mem))
                            (mem (write-mem-byte (+ 3 addr) byte3 mem)))
                       mem))))
   :rule-classes :definition)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Some theorems

(defthm r32-low-from-four-r08-low
  (implies (and (n32p addr)
                (n32p (+ 3 addr))
                (memoryp mem)
                (equal (r08-low      addr  mem) byte0)
                (equal (r08-low (+ 1 addr) mem) byte1)
                (equal (r08-low (+ 2 addr) mem) byte2)
                (equal (r08-low (+ 3 addr) mem) byte3))
           (equal (r32-low addr mem)
                  (+ (ash byte3 24)
                     (+ (ash byte2 16)
                        (+ (ash byte1 8)
                           byte0))))))

(in-theory (disable r32-low-from-four-r08-low))

;;; Note that I do not have any rules about reads/writes or
;;; writes/writes that intersect but do not overlap completely.  What
;;; should I do about these?  Perhaps this is an argument for some
;;; kind of read-bytes and write-bytes that also specify how many
;;; bytes to read or write.

(defthm |(n08p (r08-low addr mem))|
  (implies (memoryp mem)
	   (n08p (r08-low addr mem)))
  :rule-classes ((:rewrite)
                 (:type-prescription
                  :corollary
                  (implies (memoryp mem)
                           (and (integerp (r08-low addr mem))
                                (<= 0 (r08-low addr mem)))))))

 (defthm |(n32p (r32-low addr mem))|
   (implies (memoryp mem)
            (n32p (r32-low addr mem)))
   :rule-classes ((:rewrite)
                  (:type-prescription
                   :corollary
                   (implies (memoryp mem)
                            (and (integerp (r32-low addr mem))
                                 (<= 0 (r32-low addr mem))))))
   :hints (("Goal" :in-theory (e/d ()
                                   (ash)
                                   ))))

(defthm |(memoryp (w08-low addr val mem))|
  (implies (and (n32p addr)
                (n08p val)
                (memoryp mem))
           (memoryp (w08-low addr val mem))))

(defthm |(memoryp (w32-low addr val mem))|
  (implies (and (n32p addr)
                (n32p val)
                (memoryp mem))
           (memoryp (w32-low addr val mem)))
   :hints (("Goal" :in-theory (e/d ()
                                   (ash)
                                   ))))

(defthm |(r08-low addr (w08-low addr val mem))|
  (equal (r08-low addr (w08-low addr val mem))
         val))

(defthm |(r08-low addr1 (w08-low addr2 val mem))|
  (implies (disjointp (list (list addr1)
                            (list addr2)))
           (equal (r08-low addr1 (w08-low addr2 val mem))
                  (r08-low addr1 mem)))
  :hints (("Goal" :in-theory (enable |(not (equal x y)) --- disjointp|))))

(defthm |(r08-low addr1 (w32-low addr2 val mem))|
  (implies (and (n32p addr1)
                (n32p addr2)
                (n32p (+ 3 addr2))
                (disjointp (list (list addr1)
                                 (range addr2 0 4))))
           (equal (r08-low addr1 (w32-low addr2 val mem))
                  (r08-low addr1 mem)))
  :hints (("Goal" :in-theory (enable |(not (equal x y)) --- disjointp|))))

(defthm |(w08-low addr val1 (w08-low addr val2 mem))|
  (equal (w08-low addr val1 (w08-low addr val2 mem))
         (w08-low addr val1 mem)))

(defthm |(w08-low addr1 val1 (w08-low addr2 val2 mem))|
  (implies (and (integerp addr1)
                (integerp addr2)
                (disjointp (list (list addr1)
                                 (list addr2))))
           (equal (w08-low addr1 val1 (w08-low addr2 val2 mem))
                  (w08-low addr2 val2 (w08-low addr1 val1 mem))))
  :hints (("Goal" :in-theory (enable |(not (equal x y)) --- disjointp|)))
  :rule-classes ((:rewrite :loop-stopper ((addr1 addr2)))))

(defthm |(r32-low addr1 (w08-low addr2 val mem))|
  (implies (and (n32p addr1)
                (n32p (+ 3 addr1))
                (n32p addr2)
                (disjointp (list (range addr1 0 4)
                                 (list addr2))))
           (equal (r32-low addr1 (w08-low addr2 val mem))
                  (r32-low addr1 mem)))
  :hints (("Goal" :in-theory (enable |(not (equal x y)) --- disjointp|))))

(encapsulate
 ()

 (local
  (defthm crock-2
    (implies (n32p x)
             (n08p (floor x 16777216)))))

 (local
  (defthm crock-3
    (implies (n32p val)
             (EQUAL (+ (N08 VAL)
                       (* 16777216 (FLOOR VAL 16777216))
                       (* 256 (N08 (FLOOR VAL 256)))
                       (* 65536 (N08 (FLOOR VAL 65536))))
                    VAL))
    :hints (("Goal" :in-theory (enable n08)))))

 (defthm |(r32-low addr (w32-low addr val mem))|
   (implies (and (n32p addr)
                 (n32p (+ 3 addr))
                 (n32p val))
            (equal (r32-low addr (w32-low addr val mem))
                   val))
  :hints (("Goal" :in-theory (enable |(not (equal x y)) --- disjointp|))))
 )

(defthm |(r32-low addr1 (w32-low addr2 val mem))|
  (implies (and (n32p addr1)
                (n32p (+ 3 addr1))
                (n32p addr2)
                (n32p (+ 3 addr2))
                (disjointp (list (range addr1 0 4)
                                 (range addr2 0 4))))
           (equal (r32-low addr1 (w32-low addr2 val mem))
                  (r32-low addr1 mem)))
  :hints (("Goal" :in-theory (enable |(not (equal x y)) --- disjointp|))))

;;; We push w32's inside w08's
;;; I think this is the proper way if we ever worry about overlapping
;;; reads and writes.

(defthm |(w32-low addr1 val1 (w08-low addr2 val2 mem))|
  (implies (and (n32p addr1)
                (n32p (+ 3 addr1))
                (n32p addr2)
                (disjointp (list (range addr1 0 4)
                                 (list addr2))))
           (equal (w32-low addr1 val1 (w08-low addr2 val2 mem))
                  (w08-low addr2 val2 (w32-low addr1 val1 mem))))
  :hints (("Goal" :in-theory (enable |(not (equal x y)) --- disjointp|))))

(defthm |(w32-low addr val1 (w32-low addr val2 mem))|
  (implies (and (n32p addr)
                (n32p (+ 3 addr)))
           (equal (w32-low addr val1 (w32-low addr val2 mem))
                  (w32-low addr val1 mem))))

(defthm |(w32-low addr1 val1 (w32-low addr2 val2 mem))|
  (implies (and (n32p addr1)
                (n32p (+ 3 addr1))
                (n32p addr2)
                (n32p (+ 3 addr2))
                (disjointp (list (range addr1 0 4)
                                 (range addr2 0 4))))
           (equal (w32-low addr1 val1 (w32-low addr2 val2 mem))
                  (w32-low addr2 val2 (w32-low addr1 val1 mem))))
  :rule-classes ((:rewrite :loop-stopper ((addr1 addr2))))
  :hints (("Goal" :in-theory (enable |(not (equal x y)) --- disjointp|))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable r08-low
                    w08-low
                    r32-low
                    w32-low
                    r32-low-alt-def
                    w32-low-alt-def))
