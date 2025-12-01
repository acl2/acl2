;; x86-state-concrete.lisp

(in-package "ACL2")

(include-book "constants")

(defconst *x86-32-model*
  `(

;;; This constant will be used to construct the stobj, and so follows a very
;;; similar format.  We do it this way so that we can also crawl over the
;;; constant to help define useful lemmata and such automatically.

;;; Important note: Keep the three memory-related fields --- mem-table,
;;; mem-array, and mem-array-next-addr --- at the end of this constant.

    (rgf$c :type (array (unsigned-byte 32)
                        (*m86-32-reg-names-len*))
           :initially 0
           :resizable nil)

    ;; The program counter.
    (eip$c :type (unsigned-byte 32)
           :initially 0)

    ;; The eflags register
    (flg$c :type (unsigned-byte 32)
           :initially 0)

    ;; The segment registers
    (seg$c :type (array (unsigned-byte 16)
                        (*m86-32-segment-reg-names-len*))
           :initially 0
           :resizable nil)

    ;; The System Table Registers (GDTR and IDTR) -- these registers
    ;; point to bounded tables of (up to 8192) segment descriptors.
    (str$c :type (array (unsigned-byte 48)
                        (*m86-32-gdtr-idtr-names-len*))
           :initially 0
           :resizable nil)

    ;; These 16-bit values are Segment Selectors (Task Register and
    ;; LDTR):  Index(12),TI(1),RPL(2).  The Index references a segment
    ;; descriptor in the Global Descriptor Table (GDT).
    (ssr$c :type (array (unsigned-byte 16)
                        (*m86-32-ldtr-tr-names-len*))
           :initially 0
           :resizable nil)

    ;; The control registers
    (ctr$c  :type (array (unsigned-byte 32)
                         (*m86-32-control-reg-names-len*))
            :initially 0
            :resizable nil)

    ;; The debug registers
    (dbg$c :type (array (unsigned-byte 32)
                        (*m86-32-debug-reg-names-len*))
           :initially 0
           :resizable nil)

    ;; Additional registers to be defined here.

    ;; FPU 16-bit status registers

    ;; FPU 48-bit last instruction registers

    ;; FPU 80-bit data registers

    ;; XMM 16-bit status

    ;; XMM 128-bit data registers

    ;; This information is loaded from memory when a segment register
    ;; is loaded.  For each segment register, there is a
    ;; corresponding "seg-base", "seg-limit", and "seg-access"
    ;; register; this memory-resident information is automatically
    ;; used when protection is enabled.
    (seg-base$c   :type (array (unsigned-byte 32)
                               (*m86-32-segment-reg-names-len*))
                  :initially 0 :resizable nil)
    (seg-limit$c  :type (array (unsigned-byte 20)
                               (*m86-32-segment-reg-names-len*))
                  :initially 0 :resizable nil)
    (seg-access$c :type (array (unsigned-byte 12)
                               (*m86-32-segment-reg-names-len*))
                  :initially 0 :resizable nil)

    ;; Here we have some additional state -- normally stored in the
    ;; X86 memory, but we make a local copy for performance reasons.
    ;; The X86 processor does something similar by reading such data
    ;; and then loading it into internal X86 processor registers.

    ;; The state of the ACL2 model.  This flag is not part of the
    ;; processor; it is used to signal problems with model state,
    ;; such as the processor is halted.  While this flag is NIL, the
    ;; processor model is OK; otherwise, the flag indicates (part of)
    ;; the problem.
    (ms$c :type t :initially nil)

    ;; The model memory is intended to represent a 2^32 byte physical
    ;; memory.  Starting with the PAE extension, X86 processors can
    ;; address more than 2^32 bytes, but we aren't modeling that
    ;; here.  We maintain the byte-level semantics.

    ;; We define a paging-like mechanism to model the complete x86
    ;; address space.  The memory is laid out in a flat array, to be
    ;; viewed as back-to-back 16MB "pseudo-pages".  The address of a
    ;; byte is split into two pieces: a pseudo-page address and an
    ;; offset within a page.  The mem-table data structure holds the
    ;; pseudo-page addresses, which are 24-bit wide indices of the
    ;; pseudo-pages.  The offset is also an 8-bit wide address, which
    ;; when added to (pseudo-page address << 24), gives the "real"
    ;; address (32-bit wide) of a byte in mem-array.
    ;; mem-array-next-addr keeps track of the index of the
    ;; pseudo-page to be allocated next.

    ;;  Here is an example of how this works.  Suppose we have:

    ;;   mem-table[#x7654321] = 0_[24-zeros]
    ;;   mem-table[#x36789ab] = 1_[24-zeros]
    ;;   mem-table[#x2111111] = 2_[24-zeros]

    ;; All additional values in mem-table are the initial value of 1,
    ;; which means "page is not present".

    ;; Then mem-array starts as follows.

    ;;   2^24 bytes corresponding to byte addresses with top 24 bits =
    ;;   #x7654321
    ;;   2^24 bytes corresponding to byte addresses with top 24 bits =
    ;;   #x36789ab
    ;;   2^24 bytes corresponding to byte addresses with top 24 bits =
    ;;   #x2111111

    ;; Since the size of the entire memory is 2^32 bytes and each
    ;; pseudo-page is 2^24 bytes, we need only 2^8 pseudo-pages to
    ;; represent the entire memory.

    (mem-table :type (array (unsigned-byte 32)
                            (*mem-table-size*))
               :initially 1
               :resizable nil)

    (mem-array :type (array (unsigned-byte 8)
                            (*initial-mem-array-length*))
               :initially 0
               :resizable t)

    (mem-array-next-addr :type (integer 0 4294967296)
                         :initially 0)

    ))

; ======================================================================

;;; Creating the stobj

;; The functions that follow are rather brittle, in that it assumes that the
;; elements of the x86-model are defined in a rigid manner.

(defun create-x86-32-stobj-renaming-fn-1 (x86-32-model-field)
  ;; Renaming the field updaters
  (let ((name (car x86-32-model-field))
        (type (caddr x86-32-model-field)))
    (cond ((and (consp type)
                (equal (car type) 'array))
           (let ((namei (mk-name name "I")))
             `(,(mk-name "UPDATE-" namei) ,(mk-name "!" namei))))
          (t
           `(,(mk-name "UPDATE-" name) ,(mk-name "!" name))))))

(defun create-x86-32-stobj-renaming-fn-2 (x86-32-model-field)
  ;; Renaming the field recognizers

; The field recognizers each take an ordinary object as input.  Thus, we can
; use the same field recognizer for a field of the concrete stobj, the :logic
; ("$a") function for the abstract stobj, and the abstract stobj itself.  (Note
; that this trick won't work for field accessors and updaters, because the
; signatures are different for all three of the corresponding functions as
; above: concrete stobjs, ordinary object, and abstract stobj, respectively.)

  (let ((name (car x86-32-model-field)))
    (cond ((member name '(MEM-TABLE MEM-ARRAY MEM-ARRAY-NEXT-ADDR))
           ;; No renaming needed really...
           `(,(mk-name name "P") ,(mk-name name "P")))
          (t
           (let ((end (search "$C" (symbol-name name))))
             `(,(mk-name name "P")
               ,(mk-name (subseq (symbol-name name) 0 end) "P")))))))

(defun create-x86-32-stobj-renaming-fn (x86-32-model)
  (cond ((endp x86-32-model)
         '())
        (t
         `(,(create-x86-32-stobj-renaming-fn-1 (car x86-32-model))
           ,(create-x86-32-stobj-renaming-fn-2 (car x86-32-model))
           ,@(create-x86-32-stobj-renaming-fn (cdr x86-32-model))))))

(defun create-x86-32-stobj-1 (x86-32-model)
  `(DEFSTOBJ X86-32$C
     ,@x86-32-model
     :INLINE T
     :RENAMING ((x86-32$cp x86-32$cp-pre)
                ,@(create-x86-32-stobj-renaming-fn x86-32-model))))

(defmacro create-x86-32-stobj ()
  (create-x86-32-stobj-1 *x86-32-model*))

(create-x86-32-stobj)

; ======================================================================

;; We now build the infrastructure to define x86-32$cp.

;; x86-32$cp

(defun good-mem-table-entriesp (i table-bound array-next-addr x86-32$c)
  (declare (type (unsigned-byte 8) i table-bound)
           (xargs :stobjs x86-32$c
                  :guard (and (natp array-next-addr)
                              (<= i table-bound))
                  :measure (nfix (- table-bound i))))
  (cond ((mbt (and (natp i) (natp table-bound) (<= i table-bound)))
         (let ((addr (mem-tablei i x86-32$c)))
           (and (or (eql addr 1)
                    (and (natp addr)
                         (equal (logand 16777215
                                        addr) 0)
                         (< (+ 16777215 addr)


; We could use addr instead of (+ mask addr) just above, since presumably
; array-next-addr is always a multiple of 2^*2^x-byte-pseudo-page*.  Of course,
; some proofs would likely change.
                            array-next-addr)))
                (or (eql i table-bound)
                    (good-mem-table-entriesp (1+ i) table-bound array-next-addr
                                             x86-32$c)))))
        (t nil)))

(defun good-mem-table-entriesp-logic (i table-bound array-next-addr mem-table)
  (declare (xargs :measure (nfix (- table-bound i))))
  (cond ((mbt (and (natp i) (natp table-bound) (<= i table-bound)))
         (let ((addr (nth i mem-table)))
           (and (or (eql addr 1)
                    (and (natp addr)
                         (equal (logand 16777215
                                        addr)
                                0)
                         (< (+ 16777215 addr)
                            array-next-addr)))
                (or (eql i table-bound)
                    (good-mem-table-entriesp-logic
                     (1+ i) table-bound array-next-addr mem-table)))))
        (t nil)))

(defun-nx nth-nx (n x)
  (nth n x))

(defthm good-mem-table-entriesp-is-good-mem-table-entriesp-logic
  (equal (good-mem-table-entriesp i table-bound array-next-addr x86-32$c)
         (good-mem-table-entriesp-logic i table-bound array-next-addr
                                        (nth *mem-tablei* x86-32$c))))

(in-theory (disable good-mem-table-entriesp-logic))

(defun merge-<-into-> (lst1 lst2 acc)

; Merge upward-sorted lists lst1 and lst2 into downward-sorted list acc, to
; produce a downward-sorted list.

  (declare (xargs :guard (and (rational-listp lst1)
                              (rational-listp lst2))
                  :measure (+ (len lst1) (len lst2))))
  (cond ((endp lst1) (revappend lst2 acc))
        ((endp lst2) (revappend lst1 acc))
        ((< (car lst1) (car lst2))
         (merge-<-into-> (cdr lst1) lst2 (cons (car lst1) acc)))
        (t
         (merge-<-into-> lst1 (cdr lst2) (cons (car lst2) acc)))))

(defun merge->-into-< (lst1 lst2 acc)

; Merge downward-sorted lists lst1 and lst2 into upward-sorted list acc, to
; produce an upward-sorted list.

  (declare (xargs :guard (and (rational-listp lst1)
                              (rational-listp lst2))
                  :measure (+ (len lst1) (len lst2))))
  (cond ((endp lst1) (revappend lst2 acc))
        ((endp lst2) (revappend lst1 acc))
        ((> (car lst1) (car lst2))
         (merge->-into-< (cdr lst1) lst2 (cons (car lst1) acc)))
        (t
         (merge->-into-< lst1 (cdr lst2) (cons (car lst2) acc)))))

(defun good-mem-table-entriesp-weak (i table-bound x86-32$c)

; For guard of mem-table-entries.

  (declare (type (unsigned-byte 8)
                 i table-bound)
           (xargs :stobjs x86-32$c
                  :guard (<= i table-bound)
                  :measure (nfix (- table-bound i))))
  (cond ((mbt (and (natp i) (natp table-bound) (<= i table-bound)))
         (and (natp (mem-tablei i x86-32$c))
              (or (eql i table-bound)
                  (good-mem-table-entriesp-weak (1+ i) table-bound x86-32$c))))
        (t nil)))


(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

  (defun mem-table-entries (lower upper x86-32$c parity)
   (declare (type (unsigned-byte 8) lower upper)
            (xargs :stobjs x86-32$c
                   :guard
                   (and (<= lower upper)
                        (booleanp parity)
                        (good-mem-table-entriesp-weak lower upper x86-32$c))
                   :verify-guards nil
                   :measure (nfix (- upper lower))))
   (cond ((eql lower upper)
          (let ((addr (mem-tablei lower x86-32$c)))
            (cond ((eql addr 1) nil)
                  (t (list addr)))))
         ((eql (1+ lower) upper)
          (let ((addr-lower (mem-tablei lower x86-32$c))
                (addr-upper (mem-tablei upper x86-32$c)))
            (cond ((eql addr-lower 1)
                   (cond ((eql addr-upper 1) nil)
                         (t (list addr-upper))))
                  ((eql addr-upper 1)
                   (list addr-lower))
                  ((equal parity (< addr-lower addr-upper))
                   (list addr-lower addr-upper))
                  (t
                   (list addr-upper addr-lower)))))
         ((mbt (and (natp lower) (natp upper) (< (1+ lower) upper)))
          (let ((mid (ash (+ lower upper) -1)))
            (cond (parity
                   (merge->-into-<
                    (mem-table-entries lower mid x86-32$c nil)
                    (mem-table-entries (1+ mid) upper x86-32$c nil)
                    nil))
                  (t
                   (merge-<-into->
                    (mem-table-entries lower mid x86-32$c t)
                    (mem-table-entries (1+ mid) upper x86-32$c t)
                    nil)))))
         (t 'impossible)))
) ;; End of encapsulate


(defthm rational-listp-revappend
  (implies (rational-listp x)
           (equal (rational-listp (revappend x y))
                  (rational-listp y))))

(defthm rational-listp-merge->-into-<
  (implies (and (rational-listp x)
                (rational-listp y)
                (rational-listp z))
           (rational-listp (merge->-into-< x y z))))

(defthm rational-listp-merge-<-into->
  (implies (and (rational-listp x)
                (rational-listp y)
                (rational-listp z))
           (rational-listp (merge-<-into-> x y z))))

(encapsulate
 ()

 (local (defthm good-mem-table-entriesp-weak-preserved-lemma
          (implies (and (good-mem-table-entriesp-weak lower upper1 x86-32$c)
                        (natp upper2)
                        (<= lower upper2)
                        (<= upper2 upper1))
                   (good-mem-table-entriesp-weak lower upper2 x86-32$c))
          :hints (("Goal" :in-theory (disable (force))))))

 (defthm good-mem-table-entriesp-weak-preserved
   (implies (and (good-mem-table-entriesp-weak lower1 upper1 x86-32$c)
                 (natp lower2)
                 (natp upper2)
                 (<= lower1 lower2)
                 (<= lower2 upper2)
                 (<= upper2 upper1))
            (good-mem-table-entriesp-weak lower2 upper2 x86-32$c))
   :hints (("Goal" :in-theory (disable (force)))))
) ;; End of encapsulate

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm ash-minus-1-inequality-1
   (implies (and (natp lower)
                 (natp upper)
                 (< (1+ lower) upper))
            (< lower
               (ash (+ lower upper) -1)))
   :rule-classes :linear)

 (defthm ash-minus-1-inequality-2
   (implies (and (natp lower)
                 (natp upper)
                 (< (1+ lower) upper))
            (<= (+ 1 (ash (+ lower upper) -1))
                upper))
   :rule-classes :linear)
) ;; End of encapsulate

(defthm rational-listp-mem-table-entries
  (implies (good-mem-table-entriesp-weak lower upper x86-32$c)
           (rational-listp (mem-table-entries lower upper x86-32$c parity)))
  :hints (("Goal"
           :induct (mem-table-entries lower upper x86-32$c parity)
           :in-theory (disable (force)))))

(verify-guards mem-table-entries)

(defun no-duplicatesp-sorted (lst)
  (declare (xargs :guard (eqlable-listp lst)))
  (cond ((or (endp lst)
             (endp (cdr lst)))
         t)
        ((eql (car lst) (cadr lst))
         nil)
        (t (no-duplicatesp-sorted (cdr lst)))))

(local (defthm rational-listp-implies-eqlable-listp
         (implies (rational-listp x)
                  (eqlable-listp x))))

(defun good-mem-table-no-dupsp (lower upper x86-32$c)
  (declare (type (unsigned-byte 8) lower upper)
           (xargs :stobjs x86-32$c
                  :guard
                  (and (<= lower upper)
                       (good-mem-table-entriesp-weak lower upper x86-32$c))))
  (no-duplicatesp-sorted (mem-table-entries lower upper x86-32$c t)))


(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defun mem-table-entries-logic (lower upper mem-table parity)
; The result is increasing if parity is true, increasing if parity is false.
   (declare (xargs :measure (nfix (- upper lower))))
   (cond ((eql lower upper)
          (let ((addr (nth lower mem-table)))
            (cond ((eql addr 1) nil)
                  (t (list addr)))))
         ((eql (1+ lower) upper)
          (let ((addr-lower (nth lower mem-table))
                (addr-upper (nth upper mem-table)))
            (cond ((eql addr-lower 1)
                   (cond ((eql addr-upper 1) nil)
                         (t (list addr-upper))))
                  ((eql addr-upper 1)
                   (list addr-lower))
                  ((equal parity (< addr-lower addr-upper))
                   (list addr-lower addr-upper))
                  (t
                   (list addr-upper addr-lower)))))
         ((mbt (and (natp lower) (natp upper) (< (1+ lower) upper)))
          (let ((mid (ash (+ lower upper) -1)))
            (cond (parity
                   (merge->-into-<
                    (mem-table-entries-logic lower mid mem-table nil)
                    (mem-table-entries-logic (1+ mid) upper mem-table nil)
                    nil))
                  (t
                   (merge-<-into->
                    (mem-table-entries-logic lower mid mem-table t)
                    (mem-table-entries-logic (1+ mid) upper mem-table t)
                    nil)))))
         (t 'impossible)))
) ;; End of encapsulate

(defun good-mem-table-no-dupsp-logic (lower upper mem-table)
  (no-duplicatesp-sorted (mem-table-entries-logic lower upper mem-table t)))

(defthm mem-table-entries-is-mem-table-entries-logic
  (equal (mem-table-entries lower upper x86-32$c parity)
         (mem-table-entries-logic lower upper
                                  (nth *mem-tablei* x86-32$c)
                                  parity)))

(defthm good-mem-table-no-dupsp-is-good-mem-table-no-dupsp-logic
  (equal (good-mem-table-no-dupsp lower upper x86-32$c)
         (good-mem-table-no-dupsp-logic lower upper
                                        (nth *mem-tablei* x86-32$c))))

(in-theory (disable good-mem-table-no-dupsp-logic
                    good-mem-table-no-dupsp))

; Before defining good-memp, towards defining x86-32$cp, we define a function
; that will let us reason about the mem-array-next-addr field, showing (e.g.,
; for guard verification) that it's not too large.

(defun expected-mem-array-next-addr (i table-len x86-32$c)
  (declare (type (integer 0 256)
                 i table-len)
           (xargs :stobjs x86-32$c
                  :guard (<= i table-len)
                  :measure (nfix (- table-len i))))
  (cond ((or (not (natp i))
             (not (natp table-len))
             (>= i table-len))
         0)
        (t (let ((addr (mem-tablei i x86-32$c)))
             (cond ((eql addr 1)
                    (expected-mem-array-next-addr (1+ i) table-len x86-32$c))
                   (t (+ *pseudo-page-size-in-bytes*
                         (expected-mem-array-next-addr (1+ i)
                                                       table-len
                                                       x86-32$c))))))))

(defthm expected-mem-array-in-parts
  (implies (and (natp i)
                (natp j)
                (natp k)
                (<= i j)
                (<= j k))
           (equal (+ (expected-mem-array-next-addr i j x86-32$c)
                     (expected-mem-array-next-addr j k x86-32$c))
                  (expected-mem-array-next-addr i k x86-32$c)))
  :rule-classes nil)

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm expected-mem-array-bound-general
   (implies (<= i table-len)
            (<= (expected-mem-array-next-addr i table-len x86-32$c)
                (* *pseudo-page-size-in-bytes* (- table-len i))))

; Need linear rule here, rather than :rule-classes nil, for later lemma
; expected-mem-array-next-addr-bound-general.

   :rule-classes :linear)
) ;; End of encapsulate

(defthm expected-mem-array-bound
  (implies (<= i table-len)
           (<= (expected-mem-array-next-addr 0
                                             (mem-table-length x86-32$c)
                                             x86-32$c)
               (* *pseudo-page-size-in-bytes* (mem-table-length x86-32$c))))
  :hints (("Goal" :use ((:instance expected-mem-array-bound-general
                                   (i 0)
                                   (table-len (mem-table-length x86-32$c))))))
  :rule-classes :linear)

(defthm expected-mem-array-next-addr-only-depends-on-mem-table-lemma
  (implies (equal (nth *mem-tablei* x86-32$c-alt)
                  (nth *mem-tablei* x86-32$c))
           (equal (expected-mem-array-next-addr i j x86-32$c-alt)
                  (expected-mem-array-next-addr i j x86-32$c)))
  :rule-classes nil)

(defthm expected-mem-array-next-addr-only-depends-on-mem-table
  (implies (and (equal (expected-mem-array-next-addr 0 *mem-table-size* x86-32$c)
                       x) ; free var
                (syntaxp (equal x86-32$c 'x86-32$c))
                (equal (nth *mem-tablei* x86-32$c-alt)
                       (nth *mem-tablei* x86-32$c)))
           (equal (expected-mem-array-next-addr 0 *mem-table-size* x86-32$c-alt)
                  x))
  :hints (("Goal"
           :use
           ((:instance
             expected-mem-array-next-addr-only-depends-on-mem-table-lemma
             (i 0) (j *mem-table-size*))))))

(in-theory (disable expected-mem-array-next-addr))

(defthm good-mem-table-entriesp-logic-forward-to-good-mem-table-entriesp-weak
  (implies (good-mem-table-entriesp-logic lower upper
                                          array-next-addr
                                          (nth *mem-tablei* x86-32$c))
           (good-mem-table-entriesp-weak lower upper x86-32$c))
  :hints (("Goal" :in-theory (e/d (good-mem-table-entriesp-logic
                                   good-mem-table-entriesp-weak)
                                  ((force)))))
  :rule-classes :forward-chaining)

(defun good-mem-arrayp-1 (index len x86-32$c)
  (declare (xargs :stobjs x86-32$c
                  :guard (and (natp index)
                              (natp len)
                              (<= index len)
                              (<= len (mem-array-length x86-32$c)))
                  :measure (nfix (- len index))))
  (cond ((mbe :logic (not (and (natp index)
                               (natp len)
                               (< index len)))
              :exec (eql index len))
         t)
        (t (and (eql (mem-arrayi index x86-32$c) 0)
                (good-mem-arrayp-1 (1+ index) len x86-32$c)))))

(defun good-mem-arrayp-1-logic (index len mem-array)
  (declare (xargs :measure (nfix (- len index))))
  (cond ((not (and (natp index)
                   (natp len)
                   (< index len)))
         t)
        (t (and (eql (nth index mem-array) 0)
                (good-mem-arrayp-1-logic (1+ index) len mem-array)))))

(defthm good-mem-arrayp-1-is-good-mem-arrayp-1-logic
  (equal (good-mem-arrayp-1 index len x86-32$c)
         (good-mem-arrayp-1-logic index len (nth *mem-arrayi* x86-32$c))))

(defun good-mem-arrayp (x86-32$c)
  (declare (xargs :stobjs x86-32$c
                  :guard (<= (mem-array-next-addr x86-32$c)
                             (mem-array-length x86-32$c))))
  (mbe :logic
       (good-mem-arrayp-1-logic (mem-array-next-addr x86-32$c)
                                (mem-array-length x86-32$c)
                                (nth-nx *mem-arrayi* x86-32$c))
       :exec
       (good-mem-arrayp-1 (mem-array-next-addr x86-32$c)
                          (mem-array-length x86-32$c)
                          x86-32$c)))

; MEM-TABLE read lemmas

(defthm mem-tablep-forward
   (implies (mem-tablep x)
           (nat-listp x))
  :rule-classes :forward-chaining)

(defmacro mem-table-indexp (x)
  `(and (natp ,x)
        (< ,x *mem-table-size*)))

(defthm natp-mem-tablep-when-valid-mem-table-index
  (implies (forced-and (x86-32$cp-pre x86-32$c)
                       (mem-table-indexp i))
           (and (integerp (mem-tablei i x86-32$c))
                (<= 0 (mem-tablei i x86-32$c))))
  :rule-classes (:rewrite :type-prescription))

(defthm natp-mem-tablep-when-valid-mem-table-index-nth-version
  (implies (forced-and (x86-32$cp-pre x86-32$c)
                       (mem-table-indexp i))
           (and (integerp (nth i (nth *mem-tablei* x86-32$c)))
                (<= 0 (nth i (nth *mem-tablei* x86-32$c)))))
  :rule-classes (:rewrite :type-prescription))

(encapsulate
 ()

 (local (defthm nth-of-mem-table-<=-*mem-size-in-bytes*
          (implies (and (mem-tablep x)
                        (integerp i)
                        (<= 0 i)
                        (< i (len x)))
                   (< (nth i x) *mem-size-in-bytes*))
          :rule-classes :linear
          :hints (("Goal" :in-theory (e/d (nth) ())))))

 (defthm mem-tablei-less-than-*mem-size-in-bytes*
   (implies (forced-and (x86-32$cp-pre x86-32$c)
                        (mem-table-indexp i))
            (< (mem-tablei i x86-32$c) *mem-size-in-bytes*))
   :rule-classes :linear)

 (defthm mem-tablei-less-than-*mem-size-in-bytes*-nth-version
   (implies (forced-and (x86-32$cp-pre x86-32$c)
                        (mem-table-indexp i))
            (< (nth i (nth *mem-tablei* x86-32$c))
               *mem-size-in-bytes*))
   :rule-classes :linear))

(defun good-memp (x86-32$c)
  (declare (xargs :stobjs x86-32$c))
  (let ((table-bound (1- (mem-table-length x86-32$c)))
        (array-length (mem-array-length x86-32$c))
        (array-next-addr (mem-array-next-addr x86-32$c)))
    (and (<= array-next-addr array-length)
         (<= *initial-mem-array-length* array-length)
         (eql (logand 16777215 array-length) 0)
         ; integral number of pseudo pages
         (equal array-next-addr
                (expected-mem-array-next-addr 0
                                              (mem-table-length x86-32$c)
                                              x86-32$c))
         (<= array-next-addr array-length)
         (mbe :logic
              (good-mem-table-entriesp-logic 0 table-bound array-next-addr
                                             (nth-nx *mem-tablei* x86-32$c))
              :exec
              (good-mem-table-entriesp 0 table-bound array-next-addr
                                       x86-32$c))
         (mbe :logic
              (good-mem-table-no-dupsp-logic 0 table-bound
                                             (nth-nx *mem-tablei* x86-32$c))
              :exec
              (good-mem-table-no-dupsp 0 table-bound x86-32$c))
         (good-mem-arrayp x86-32$c))))

(defun x86-32$cp (x86-32$c)
  (declare (xargs :stobjs x86-32$c))
  (and (x86-32$cp-pre x86-32$c)
       (good-memp x86-32$c)))

; ======================================================================

;; The following are the "basic" theorems we need about the fields of the
;; concrete stobj.  We need a little more than the rest for the memory fields
;; since they are "special".

(LOCAL (IN-THEORY (E/D NIL (NTH UPDATE-NTH))))

;; We define two kinds of rules about each field in the stobj now: some forward
;; chaining rules, and some rules that say something about the recognizers.
;; These theorems help us in defining the :logic recognizers of the fields of
;; the abstract stobj.

(defun x86-32-concrete-stobj-array-thms-1 (x86-32-model-field)

  ;; This function is rather brittle, in that it assumes that the elements of
  ;; the x86-32-model are defined in a rigid manner.

  (let* ((name (car x86-32-model-field))
         (type (caddr x86-32-model-field))
         (size (cadr (cadr type))))
    (cond ((equal (car (cadr type)) 'unsigned-byte)
           (let* ((end (search "$C" (symbol-name name)))
                  (predicate (mk-name (subseq (symbol-name name) 0 end)
                                      "P")))
             `( ;; readers
               (DEFTHM ,(mk-name predicate "-FORWARD")
                 (IMPLIES (,predicate X)
                          (NAT-LISTP X))
                 :RULE-CLASSES :FORWARD-CHAINING)
               ;; writers
               (DEFTHM ,(mk-name predicate "-UPDATE-NTH")
                 (IMPLIES (FORCED-AND (,predicate X)
                                      (INTEGERP I)
                                      (<= 0 I)
                                      (< I (LEN X))
                                      (INTEGERP V)
                                      (<= 0 V)
                                      (< V ,(expt 2 size)))
                          (,predicate (UPDATE-NTH I V X)))
                 :HINTS (("Goal" :IN-THEORY (E/D (UPDATE-NTH) ()))))
               )))
          (t
           ;; This branch pertains to all arrays of type signed-byte.
           ;;      (equal (car (cadr type)) 'signed-byte)
           (let* ((end (search "$C" (symbol-name name)))
                  (predicate (mk-name (subseq (symbol-name name) 0 end)
                                      "P")))
             `( ;; readers
               (DEFTHM ,(mk-name predicate "-FORWARD")
                 (IMPLIES (,predicate X)
                          (INTEGER-LISTP X))
                 :RULE-CLASSES :FORWARD-CHAINING)
               ;; writers
               (DEFTHM ,(mk-name predicate "-UPDATE-NTH")
                 (IMPLIES (FORCED-AND (,predicate X)
                                      (INTEGERP I)
                                      (<= 0 I)
                                      (< I (LEN X))
                                      (INTEGERP V)
                                      (<= ,(- (expt 2 size)) V)
                                      (< V ,(expt 2 size)))
                          (,predicate (UPDATE-NTH I V X)))
                 :HINTS (("Goal" :IN-THEORY (E/D (UPDATE-NTH) ()))))
               )))
          )))

(defun x86-32-concrete-stobj-array-thms (x86-32-model)
  (cond ((endp x86-32-model)
         '())
        (t
         (if (and (consp (caddr (car x86-32-model)))
                  (equal (caaddr (car x86-32-model)) 'array))
             (append (x86-32-concrete-stobj-array-thms-1 (car x86-32-model))
                     (x86-32-concrete-stobj-array-thms (cdr x86-32-model)))
           (x86-32-concrete-stobj-array-thms (cdr x86-32-model))))))

(defmacro x86-32-concrete-stobj-array-theorems ()
  (cons 'progn
        (x86-32-concrete-stobj-array-thms *x86-32-model*)))

(x86-32-concrete-stobj-array-theorems)

;; Additional theorems about mem-array:

(defthm natp-mem-arrayi
  (implies (forced-and (x86-32$cp x86-32$c)
                       (integerp i)
                       (<= 0 i)
                       (< i (mem-array-length x86-32$c)))
           (and (integerp (mem-arrayi i x86-32$c))
                (<= 0 (mem-arrayi i x86-32$c))))
  :rule-classes :type-prescription)

(encapsulate
 ()

(defthm nth-of-mem-arrayi-less-than-expt-2-8
  (implies (and (mem-arrayp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (< (nth i x) 256))
  :hints (("goal" :in-theory (e/d (nth) nil)))
  :rule-classes :linear)

(defthm mem-arrayi-less-than-expt-2-8
  (implies (forced-and (x86-32$cp x86-32$c)
                       (integerp i)
                       (<= 0 i)
                       (< i (mem-array-length x86-32$c)))
           (< (mem-arrayi i x86-32$c) 256))
  :rule-classes :linear)
) ;; End of encapsulate

; ======================================================================

;;; Disabling the concrete stobj functions --- recognizers, accessors, and
;;; updaters:

(defun disable-stobj-fns-fn-1 (x86-32-model)
  (cond ((endp x86-32-model)
         '())
        (t
         (let ((name (car (car x86-32-model)))
               (type (caddr (car x86-32-model))))
           (cond ((and (consp type)
                       (equal (car type) 'array))
                  (let* ((namei     (mk-name name "I"))
                         (getter    namei)
                         (setter    (mk-name "!" namei))
                         (recognizer (mk-name
                                      (subseq (symbol-name name)
                                              0 (search "$C"
                                                        (symbol-name name)))
                                      "P")))
                    (append `(,getter
                              ,setter
                              ,recognizer
                              )
                            (disable-stobj-fns-fn-1 (cdr x86-32-model)))))
                 (t
                  (let ((getter  name)
                        (setter  (mk-name "!" name))
                        (recognizer (mk-name
                                     (subseq (symbol-name name)
                                             0 (search "$C" (symbol-name name)))
                                     "P")))
                    (append `(,getter ,setter ,recognizer)
                            (disable-stobj-fns-fn-1 (cdr x86-32-model))))))))))

(defmacro disable-stobj-fns-fn (x86-32-model)
  `(IN-THEORY
    (DISABLE ,@(disable-stobj-fns-fn-1 x86-32-model))))

(make-event
 `(disable-stobj-fns-fn ,*x86-32-model*))

(defthm x86-32$cp-forward-to-x86-32$cp-pre
  (implies (x86-32$cp x86-32$c)
           (x86-32$cp-pre x86-32$c))
  :rule-classes :forward-chaining)

(defthm x86-32$cp-forward-to-good-memp
  (implies (x86-32$cp x86-32$c)
           (good-memp x86-32$c))
  :rule-classes :forward-chaining)

(in-theory (disable x86-32$cp-pre
                    x86-32$cp))

; ======================================================================