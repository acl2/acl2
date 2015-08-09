
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; memory.lisp
;;;
;;; Uses memory-acl2 (potentially, memory-raw) to set up a model of
;;; the X86's virtual address 32-bit memory system.  Addresses are
;;; (assumed to be) 32-bit, values are (assumed to be) 32-bit.
;;;
;;; From work by Warren Hunt and/or Alan Dunn.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;; uncomment and comment to get Alan's fast and raw memory
;;;(include-book "memory-low" :ttags (memory))
(include-book "memory-low")
(include-book "paging")

(include-book "../Utilities/bytes-and-words")
(include-book "../Utilities/records")
(include-book "std/util/bstar" :dir :system)

(local
 (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; reading and writing

(defun r08 (v-addr st)
  (declare (xargs :guard (and (integerp v-addr)
                              (integerp (g :cr0 st))
                              (integerp (g :cr3 st))
                              (memoryp (g :mem st)))))
  (let ((p-addr (va-to-pa v-addr st)))
    (if (equal p-addr :PAGE-FAULT)
        0
      (r08-low p-addr (g :mem st)))))

(defun r32 (v-addr st)
  (declare (xargs :guard (and (n32p v-addr)
                              (integerp (g :cr0 st))
                              (integerp (g :cr3 st))
                              (memoryp (g :mem st)))
                  :guard-hints (("Goal" :in-theory (enable safe-address-p)))))
  (let ((p-addr (va-to-pa v-addr st)))
    (if (equal p-addr :PAGE-FAULT)
        0
      (r32-low p-addr (g :mem st)))))

(defun w08 (v-addr val st)
  (declare (xargs :guard (and (n32p v-addr)
                              (integerp val)
                              (integerp (g :cr0 st))
                              (integerp (g :cr3 st))
                              (memoryp (g :mem st)))
                  :guard-hints (("Goal" :in-theory (enable safe-address-p)))))
  (let ((p-addr (va-to-pa v-addr st)))
    (if (equal p-addr :PAGE-FAULT)
        st
      (let ((mem (w08-low p-addr val (g :mem st))))
        (s :mem mem st)))))

(defun w32 (v-addr val st)
  (declare (xargs :guard (and (n32p v-addr)
                              (integerp val)
                              (integerp (g :cr0 st))
                              (integerp (g :cr3 st))
                              (memoryp (g :mem st)))
                  :guard-hints (("Goal" :in-theory (enable safe-address-p)))))
  (let ((p-addr (va-to-pa v-addr st)))
    (if (equal p-addr :PAGE-FAULT)
        st
      (let ((mem (w32-low p-addr val (g :mem st))))
        (s :mem mem st)))))

(defun good-08-address-p (addr st)
  (let ((p-addr (va-to-pa addr st)))
    (and (n32p addr)
         (n32p p-addr))))

(defun good-32-address-p (addr st)
  (let ((p-addr (va-to-pa addr st)))
    (and (n32p addr)
         (n32p p-addr)
         (n32p (+ 3 p-addr)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm r32-from-four-r08
  (implies (and (good-32-address-p addr s)
                ;; remove this hyp when va-to-pa takes account of
                ;; reads crossing page boundaries.
                (not (paging-p s))
                (memoryp (g :mem s))
                (equal (r08      addr  s) byte0)
                (equal (r08 (+ 1 addr) s) byte1)
                (equal (r08 (+ 2 addr) s) byte2)
                (equal (r08 (+ 3 addr) s) byte3))
           (equal (r32 addr s)
                  (+ (ash byte3 24)
                     (+ (ash byte2 16)
                        (+ (ash byte1 8)
                           byte0)))))
  :hints (("Goal" :use ((:instance r32-low-from-four-r08-low
                                   (mem (g :mem s)))))))

(in-theory (disable r32-from-four-r08))

;;; what theorems do we want when paging?

(defthm |(good-08-address-p addr st)|
  (implies (and (not (paging-p st))
                (n32p addr))
           (good-08-address-p addr st)))

(defthm |(good-32-address-p addr st)|
  (implies (and (not (paging-p st))
                (n32p addr)
                (n32p (+ 3 addr)))
           (good-32-address-p addr st)))

(defthm |(g field (w08 addr val st))|
  (implies (not (equal field :mem))
           (equal (g field (w08 addr val st))
                  (g field st))))

(defthm |(g field (w32 addr val st))|
  (implies (not (equal field :mem))
           (equal (g field (w32 addr val st))
                  (g field st)))
  :hints (("goal" :in-theory (e/d ()
                                  (ash
                                   floor
                                   lognot)))))

(defthm |(r08 addr (s field val st))|
  (implies (and (not (equal field :CR0))
                (not (equal field :CR3))
                (not (equal field :mem)))
           (equal (r08 addr (s field val st))
                  (r08 addr st)))
  :hints (("goal" :in-theory (enable va-to-pa
                                     get-pa))))

(defthm |(r32 addr (s field val st))|
  (implies (and (not (equal field :CR0))
                (not (equal field :CR3))
                (not (equal field :mem)))
           (equal (r32 addr (s field val st))
                  (r32 addr st)))
  :hints (("goal" :in-theory (enable va-to-pa
                                     get-pa))))

;;; which is the right direction?

(defthm |(w08 addr val1 (s field val2 st))|
  (implies (and (not (equal field :CR0))
                (not (equal field :CR3))
                (not (equal field :mem)))
           (equal (w08 addr val1 (s field val2 st))
                  (s field val2 (w08 addr val1 st))))
  :hints (("goal" :in-theory (enable va-to-pa
                                     get-pa))))

(defthm |(w32 addr val1 (s field val2 st))|
  (implies (and (not (equal field :CR0))
                (not (equal field :CR3))
                (not (equal field :mem)))
           (equal (w32 addr val1 (s field val2 st))
                  (s field val2 (w32 addr val1 st))))
  :hints (("goal" :in-theory (e/d (va-to-pa
                                     get-pa)
                                  (ash
                                   lognot)))))

;;; types and predicates

(defthm |(paging-p (w08 addr val st))|
  (equal (paging-p (w08 addr val st))
         (paging-p st)))

(defthm |(paging-p (w32 addr val st))|
  (equal (paging-p (w32 addr val st))
         (paging-p st))
  :hints (("Goal" :in-theory (disable ash
                                      lognot))))


 (defthm |(n08p (r08 addr st))|
   (implies (memoryp (g :mem st))
            (n08p (r08 addr st)))
   :hints (("Goal" :in-theory (disable |(mod (floor x y) z)|)))
   :rule-classes ((:rewrite)
                  ;; Will this ever get used?  Can we relieve the hyp?
                  (:type-prescription
                   :corollary
                   (implies (memoryp (g :mem st))
                            (and (integerp (r08 addr st))
                                 (<= 0 (r08 addr st))))
                   :hints (("Goal" :in-theory (disable r08))))
                  (:linear
                   :corollary
                   (implies (memoryp (g :mem st))
                            (and (<= 0 (r08 addr st))
                                 (<= (r08 addr st) (+ -1 (expt 2 8)))))
                   :hints (("Goal" :in-theory (disable r08))))))

 (defthm |(n32p (r32 addr (g :mem st)))|
   (implies (memoryp (g :mem st))
            (n32p (r32 addr st)))
   :hints (("Goal" :in-theory (disable |(mod (floor x y) z)|)))
   :rule-classes ((:rewrite)
                  ;; Will this ever get used?  Can we relieve the hyp?
                  (:type-prescription
                   :corollary
                   (implies (memoryp (g :mem st))
                            (and (integerp (r32 addr st))
                                 (<= 0 (r32 addr st))))
                   :hints (("Goal" :in-theory (disable r32))))
                  (:linear
                   :corollary
                   (implies (memoryp (g :mem st))
                            (and (<= 0 (r32 addr st))
                                 (<= (r32 addr st) (+ -1 (expt 2 32)))))
                   :hints (("Goal" :in-theory (disable r32))))))

(defthm |(memoryp (g :mem (w08 addr val st)))|
  (implies (and (n32p addr)
                (n08p val)
                (memoryp (g :mem st)))
           (memoryp (g :mem (w08 addr val st))))
  :hints (("Goal" :in-theory (enable safe-address-p))))

(defthm |(memoryp (g :mem (w32 addr val st)))|
  (implies (and (n32p addr)
                (n32p val)
                (memoryp (g :mem st)))
           (memoryp (g :mem (w32 addr val st))))
  :hints (("Goal" :in-theory (enable safe-address-p))))

(defthm |(r08 addr (w08 addr val st)) --- paging|
  (implies (and (good-08-address-p addr st)
                (disjointp (list (list (va-to-pa addr st))
                                 (page-table-ranges st)))
                (n32p (g :CR3 st))
                (memoryp (g :mem st)))
           (equal (r08 addr (w08 addr val st))
                  val))
  :hints (("Goal" :in-theory (enable safe-address-p))))

(defthm |(r08 addr (w08 addr val st)) --- not paging|
  (implies (and (good-08-address-p addr st)
                (not (paging-p st))
                (memoryp (g :mem st)))
           (equal (r08 addr (w08 addr val st))
                  val))
  :hints (("Goal" :in-theory (enable safe-address-p))))

(defthm |(r08 addr1 (w08 addr2 val st)) --- paging|
  (implies (and (good-08-address-p addr1 st)
                (good-08-address-p addr2 st)
                (disjointp (list (list (va-to-pa addr1 st))
                                 (list (va-to-pa addr2 st))
                                 (page-table-ranges st)))
                (n32p (g :CR3 st))
                (memoryp (g :mem st)))
           (equal (r08 addr1 (w08 addr2 val st))
                  (r08 addr1 st))))

(defthm |(r08 addr1 (w08 addr2 val st)) --- not paging|
  (implies (and (good-08-address-p addr1 st)
                (good-08-address-p addr2 st)
                (disjointp (list (list addr1)
                                 (list addr2)))
                (not (paging-p st))
                (memoryp (g :mem st)))
           (equal (r08 addr1 (w08 addr2 val st))
                  (r08 addr1 st))))

(defthm |(w08 addr val1 (w08 addr val2 st)) --- paging|
  (implies (and (good-08-address-p addr st)
                (disjointp (list (list (va-to-pa addr st))
                                 (page-table-ranges st)))
                (n32p (g :CR3 st))
                (memoryp (g :mem st)))
           (equal (w08 addr val1 (w08 addr val2 st))
                  (w08 addr val1 st))))

(defthm |(w08 addr val1 (w08 addr val2 st)) --- not paging|
  (implies (and (good-08-address-p addr st)
                (not (paging-p st))
                (memoryp (g :mem st)))
           (equal (w08 addr val1 (w08 addr val2 st))
                  (w08 addr val1 st))))

(defthm |(w08 addr1 val1 (w08 addr2 val2 st)) --- paging|
  (implies (and (good-08-address-p addr1 st)
                (good-08-address-p addr2 st)
                (disjointp (list (list (va-to-pa addr1 st))
                                 (list (va-to-pa addr2 st))
                                 (page-table-ranges st)))
                (n32p (g :CR3 st))
                (memoryp (g :mem st)))
           (equal (w08 addr1 val1 (w08 addr2 val2 st))
                  (w08 addr2 val2 (w08 addr1 val1 st))))
  :rule-classes ((:rewrite :loop-stopper ((addr1 addr2)))))

(defthm |(w08 addr1 val1 (w08 addr2 val2 st)) --- not paging|
  (implies (and (good-08-address-p addr1 st)
                (good-08-address-p addr2 st)
                (disjointp (list (list (va-to-pa addr1 st))
                                 (list (va-to-pa addr2 st))))
                (not (paging-p st))
                (memoryp (g :mem st)))
           (equal (w08 addr1 val1 (w08 addr2 val2 st))
                  (w08 addr2 val2 (w08 addr1 val1 st))))
  :rule-classes ((:rewrite :loop-stopper ((addr1 addr2)))))

(defthm |(r08 addr1 (w32 addr2 val st)) --- paging|
  (implies (and (good-08-address-p addr1 st)
                (good-32-address-p addr2 st)
                (disjointp (list (list (va-to-pa addr1 st))
                                 (range (va-to-pa addr2 st) 0 4)
                                 (page-table-ranges st)))
                (n32p (g :CR3 st))
                (memoryp (g :mem st)))
           (equal (r08 addr1 (w32 addr2 val st))
                  (r08 addr1 st))))

(defthm |(r08 addr1 (w32 addr2 val st)) --- not paging|
  (implies (and (good-08-address-p addr1 st)
                (good-32-address-p addr2 st)
                (disjointp (list (list addr1)
                                 (range addr2 0 4)))
                (not (paging-p st))
                (memoryp (g :mem st)))
           (equal (r08 addr1 (w32 addr2 val st))
                  (r08 addr1 st))))

(defthm |(r32 addr (w32 addr val st)) --- paging|
  (implies (and (good-32-address-p addr st)
                (n32p val)
                (disjointp (list (range (va-to-pa addr st) 0 4)
                                 (page-table-ranges st)))
                (n32p (g :CR3 st))
                (memoryp (g :mem st)))
           (equal (r32 addr (w32 addr val st))
                  val))
  :hints (("Goal" :in-theory (enable safe-address-p))))

(defthm |(r32 addr (w32 addr val st)) --- not paging|
  (implies (and (good-32-address-p addr st)
                (n32p val)
                (not (paging-p st))
                (memoryp (g :mem st)))
           (equal (r32 addr (w32 addr val st))
                  val))
  :hints (("Goal" :in-theory (enable safe-address-p))))

(defthm |(r32 addr1 (w32 addr2 val st)) --- paging|
  (implies (and (good-32-address-p addr1 st)
                (good-32-address-p addr2 st)
                (disjointp (list (range (va-to-pa addr1 st) 0 4)
                                 (range (va-to-pa addr2 st) 0 4)
                                 (page-table-ranges st)))
                (n32p (g :CR3 st))
                (memoryp (g :mem st)))
           (equal (r32 addr1 (w32 addr2 val st))
                  (r32 addr1 st))))

(defthm |(r32 addr1 (w32 addr2 val st)) --- not paging|
  (implies (and (good-32-address-p addr1 st)
                (good-32-address-p addr2 st)
                (disjointp (list (range (va-to-pa addr1 st) 0 4)
                                 (range (va-to-pa addr2 st) 0 4)))
                (not (paging-p st))
                (memoryp (g :mem st)))
           (equal (r32 addr1 (w32 addr2 val st))
                  (r32 addr1 st))))

(defthm |(w32 addr val1 (w32 addr val2 st)) --- paging|
  (implies (and (good-32-address-p addr st)
                (disjointp (list (range (va-to-pa addr st) 0 4)
                                 (page-table-ranges st)))
                (n32p (g :CR3 st))
                (memoryp (g :mem st)))
           (equal (w32 addr val1 (w32 addr val2 st))
                  (w32 addr val1 st))))

(defthm |(w32 addr val1 (w32 addr val2 st)) --- not paging|
  (implies (and (good-32-address-p addr st)
                (not (paging-p st))
                (memoryp (g :mem st)))
           (equal (w32 addr val1 (w32 addr val2 st))
                  (w32 addr val1 st))))

(defthm |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|
  (implies (and (good-32-address-p addr1 st)
                (good-32-address-p addr2 st)
                (disjointp (list (range (va-to-pa addr1 st) 0 4)
                                 (range (va-to-pa addr2 st) 0 4)
                                 (page-table-ranges st)))
                (n32p (g :CR3 st))
                (memoryp (g :mem st)))
           (equal (w32 addr1 val1 (w32 addr2 val2 st))
                  (w32 addr2 val2 (w32 addr1 val1 st))))
  :rule-classes ((:rewrite :loop-stopper ((addr1 addr2)))))

(defthm |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|
  (implies (and (good-32-address-p addr1 st)
                (good-32-address-p addr2 st)
                (disjointp (list (range addr1 0 4)
                                 (range addr2 0 4)))
                (not (paging-p st))
                (memoryp (g :mem st)))
           (equal (w32 addr1 val1 (w32 addr2 val2 st))
                  (w32 addr2 val2 (w32 addr1 val1 st))))
  :rule-classes ((:rewrite :loop-stopper ((addr1 addr2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable r08
                    r32
                    w08
                    w32

                    good-08-address-p
                    good-32-address-p))
