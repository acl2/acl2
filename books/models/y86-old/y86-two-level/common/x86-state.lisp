; x86-state.lisp                               Warren A. Hunt, Jr.

; We model the X86 state with two arrays: one array of 32-bit values
; for the registers and array of 8-bit values for the memory.  There
; are a large number of registers, as this data structure holds all of
; the supervisor data as well.

(in-package "ACL2")

(include-book "constants")
(include-book "std/lists/list-defuns" :dir :system)

; Increase memory for X86 memory.
;; (include-book "centaur/misc/memory-mgmt-logic" :dir :system)
;; (value-triple (set-max-mem (* 6 (expt 2 30))))

; Here we include the GL book to help verify various arithmetic facts.
(local (include-book "centaur/gl/gl" :dir :system))

(defun gl-int (start by count)
  (declare (xargs :guard (and (natp start)
                              (natp by)
                              (natp count))))
  (if (zp count)
      nil
    (cons start
          (gl-int (+ by start) by (1- count)))))

; ======================================================================

;; Defining the x86-32 state:

(defconst *x86-32-model*
  `(

; Notice that the array fields use UNSIGNED-BYTE types rather than
; types (SATISFIES N32P) and (SATISFIES N08P).  The reason is that we
; want to help the host Lisp system allocate these arrays using
; minimal real (physical) memory.

    (rgf :type (array (unsigned-byte 32)
                      (*m86-32-reg-names-len*))
         :initially 0
         :resizable nil)

    ;; The program counter.
    (eip :type (unsigned-byte 32)
         :initially 0)

    ;; The eflags register
    (flg :type (unsigned-byte 32)
         :initially 0)

    ;; The segment registers
    (seg :type (array (unsigned-byte 16)
                      (*m86-32-segment-reg-names-len*))
         :initially 0
         :resizable nil)

    ;; The System Table Registers (GDTR and IDTR) -- these registers
    ;; point to bounded tables of (up to 8192) segment descriptors.
    (str :type (array (unsigned-byte 48)
                      (*m86-32-gdtr-idtr-names-len*))
         :initially 0
         :resizable nil)

    ;; These 16-bit values are Segment Selectors (Task Register and
    ;; LDTR):  Index(12),TI(1),RPL(2).  The Index references a segment
    ;; descriptor in the Global Descriptor Table (GDT).
    (ssr :type (array (unsigned-byte 16)
                      (*m86-32-ldtr-tr-names-len*))
         :initially 0
         :resizable nil)

    ;; The control registers
    (ctr  :type (array (unsigned-byte 32)
                       (*m86-32-control-reg-names-len*))
          :initially 0
          :resizable nil)

    ;; The debug registers
    (dbg :type (array (unsigned-byte 32)
                      (*m86-32-debug-reg-names-len*))
         :initially 0
         :resizable nil)

    ;; Additional registers to be defined here.

    ;; FPU 16-bit status registers

    ;; FPU 48-bit last instruction registers

    ;; FPU 80-bit data registers

    ;; XMM 16-bit status

    ;; XMM 128-bit data registers

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

    ;; This information is loaded from memory when a segment register
    ;; is loaded.  For each segment register, there is a
    ;; corresponding "seg-base", "seg-limit", and "seg-access"
    ;; register; this memory-resident information is automatically
    ;; used when protection is enabled.
    (seg-base   :type (array (unsigned-byte 32)
                             (*m86-32-segment-reg-names-len*))
                :initially 0 :resizable nil)
    (seg-limit  :type (array (unsigned-byte 20)
                             (*m86-32-segment-reg-names-len*))
                :initially 0 :resizable nil)
    (seg-access :type (array (unsigned-byte 12)
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
    (ms :type t :initially nil)

    ))

;;; Creating the stobj

(defun create-x86-32-stobj-renaming-fn-1 (x86-32-model-field)
  ;; this function is rather brittle, in that it assumes that the
  ;; elements of the x86-model are defined in a rigid manner.
  (let ((name (car x86-32-model-field))
        (type (caddr x86-32-model-field)))
    (cond ((and (consp type)
                (equal (car type) 'array))
           (let ((namei (mk-name name "I")))
             `(,(mk-name "UPDATE-" namei) ,(mk-name "!" namei))))
          (t
           `(,(mk-name "UPDATE-" name) ,(mk-name "!" name))))))

(defun create-x86-32-stobj-renaming-fn (x86-32-model)
  (cond ((endp x86-32-model)
         '())
        (t
         `(,(create-x86-32-stobj-renaming-fn-1 (car x86-32-model))
           ,@(create-x86-32-stobj-renaming-fn (cdr x86-32-model))))))

(defun create-x86-32-stobj-1 (x86-32-model)
  `(DEFSTOBJ X86-32
     ,@x86-32-model
     :INLINE T
     :RENAMING ((x86-32p x86-32p-pre)
                ,@(create-x86-32-stobj-renaming-fn x86-32-model))))

(defmacro create-x86-32-stobj ()
  (create-x86-32-stobj-1 *x86-32-model*))

(create-x86-32-stobj)

; ======================================================================

;; We now build the infrastructure to define x86-32p.

;; x86-32p

(defun good-mem-table-entriesp (i table-bound array-next-addr x86-32)
  (declare (type (unsigned-byte 8) i table-bound)
           (xargs :stobjs x86-32
                  :guard (and (natp array-next-addr)
                              (<= i table-bound))
                  :measure (nfix (- table-bound i))))
  (cond ((mbt (and (natp i) (natp table-bound) (<= i table-bound)))
         (let ((addr (mem-tablei i x86-32)))
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
                                             x86-32)))))
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
  (equal (good-mem-table-entriesp i table-bound array-next-addr x86-32)
         (good-mem-table-entriesp-logic i table-bound array-next-addr
                                        (nth *mem-tablei* x86-32))))

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

(defun good-mem-table-entriesp-weak (i table-bound x86-32)

; For guard of mem-table-entries.

  (declare (type (unsigned-byte 8)
                 i table-bound)
           (xargs :stobjs x86-32
                  :guard (<= i table-bound)
                  :measure (nfix (- table-bound i))))
  (cond ((mbt (and (natp i) (natp table-bound) (<= i table-bound)))
         (and (natp (mem-tablei i x86-32))
              (or (eql i table-bound)
                  (good-mem-table-entriesp-weak (1+ i) table-bound x86-32))))
        (t nil)))

; Required on 7/28/2013, perhaps due to a change in or under
; centaur/books/gl/gl.lisp:
(local (in-theory (enable nfix)))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

  (defun mem-table-entries (lower upper x86-32 parity)
   (declare (type (unsigned-byte 8) lower upper)
            (xargs :stobjs x86-32
                   :guard
                   (and (<= lower upper)
                        (booleanp parity)
                        (good-mem-table-entriesp-weak lower upper x86-32))
                   :verify-guards nil
                   :measure (nfix (- upper lower))))
   (cond ((eql lower upper)
          (let ((addr (mem-tablei lower x86-32)))
            (cond ((eql addr 1) nil)
                  (t (list addr)))))
         ((eql (1+ lower) upper)
          (let ((addr-lower (mem-tablei lower x86-32))
                (addr-upper (mem-tablei upper x86-32)))
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
                    (mem-table-entries lower mid x86-32 nil)
                    (mem-table-entries (1+ mid) upper x86-32 nil)
                    nil))
                  (t
                   (merge-<-into->
                    (mem-table-entries lower mid x86-32 t)
                    (mem-table-entries (1+ mid) upper x86-32 t)
                    nil)))))
         (t 'impossible)))
) ;; End of encapsulate


(defthm rational-listp-append
  (equal (rational-listp (append x y))
         (and (rational-listp (list-fix x))
              (rational-listp y)))
  :hints(("Goal" :induct (len x))))

(defthm rational-listp-rev
  (equal (rational-listp (rev x))
         (rational-listp (list-fix x)))
  :hints(("Goal" :induct (len x))))

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
          (implies (and (good-mem-table-entriesp-weak lower upper1 x86-32)
                        (natp upper2)
                        (<= lower upper2)
                        (<= upper2 upper1))
                   (good-mem-table-entriesp-weak lower upper2 x86-32))
          :hints (("Goal" :in-theory (disable (force))))))

 (defthm good-mem-table-entriesp-weak-preserved
   (implies (and (good-mem-table-entriesp-weak lower1 upper1 x86-32)
                 (natp lower2)
                 (natp upper2)
                 (<= lower1 lower2)
                 (<= lower2 upper2)
                 (<= upper2 upper1))
            (good-mem-table-entriesp-weak lower2 upper2 x86-32))
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
  (implies (good-mem-table-entriesp-weak lower upper x86-32)
           (rational-listp (mem-table-entries lower upper x86-32 parity)))
  :hints (("Goal"
           :induct (mem-table-entries lower upper x86-32 parity)
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

(defun good-mem-table-no-dupsp (lower upper x86-32)
  (declare (type (unsigned-byte 8) lower upper)
           (xargs :stobjs x86-32
                  :guard
                  (and (<= lower upper)
                       (good-mem-table-entriesp-weak lower upper x86-32))))
  (no-duplicatesp-sorted (mem-table-entries lower upper x86-32 t)))


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
  (equal (mem-table-entries lower upper x86-32 parity)
         (mem-table-entries-logic lower upper
                                  (nth *mem-tablei* x86-32)
                                  parity)))

(defthm good-mem-table-no-dupsp-is-good-mem-table-no-dupsp-logic
  (equal (good-mem-table-no-dupsp lower upper x86-32)
         (good-mem-table-no-dupsp-logic lower upper
                                        (nth *mem-tablei* x86-32))))

(in-theory (disable good-mem-table-no-dupsp-logic
                    good-mem-table-no-dupsp))

; Before defining good-memp, towards defining x86-32p, we define a function
; that will let us reason about the mem-array-next-addr field, showing (e.g.,
; for guard verification) that it's not too large.

(defun expected-mem-array-next-addr (i table-len x86-32)
  (declare (type (integer 0 256)
                 i table-len)
           (xargs :stobjs x86-32
                  :guard (<= i table-len)
                  :measure (nfix (- table-len i))))
  (cond ((or (not (natp i))
             (not (natp table-len))
             (>= i table-len))
         0)
        (t (let ((addr (mem-tablei i x86-32)))
             (cond ((eql addr 1)
                    (expected-mem-array-next-addr (1+ i) table-len x86-32))
                   (t (+ *pseudo-page-size-in-bytes*
                         (expected-mem-array-next-addr (1+ i)
                                                       table-len
                                                       x86-32))))))))


(defthm expected-mem-array-in-parts
  (implies (and (natp i)
                (natp j)
                (natp k)
                (<= i j)
                (<= j k))
           (equal (+ (expected-mem-array-next-addr i j x86-32)
                     (expected-mem-array-next-addr j k x86-32))
                  (expected-mem-array-next-addr i k x86-32)))
  :rule-classes nil)

; Note to myself from Matt: Could be local if chk-embedded-event-form doesn't
; look at first argument of record-expansion.
; Actually no longer needed, for now at least:
; (include-book "make-event/proof-by-arith" :dir :system)

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm expected-mem-array-bound-general
   (implies (<= i table-len)
            (<= (expected-mem-array-next-addr i table-len x86-32)
                (* *pseudo-page-size-in-bytes* (- table-len i))))

; Need linear rule here, rather than :rule-classes nil, for later lemma
; expected-mem-array-next-addr-bound-general.

   :rule-classes :linear)
) ;; End of encapsulate

(defthm expected-mem-array-bound
  (implies (<= i table-len)
           (<= (expected-mem-array-next-addr 0
                                             (mem-table-length x86-32)
                                             x86-32)
               (* *pseudo-page-size-in-bytes* (mem-table-length x86-32))))
  :hints (("Goal" :use ((:instance expected-mem-array-bound-general
                                   (i 0)
                                   (table-len (mem-table-length x86-32))))))
  :rule-classes :linear)

(defthm expected-mem-array-next-addr-only-depends-on-mem-table-lemma
  (implies (equal (nth *mem-tablei* x86-32-alt)
                  (nth *mem-tablei* x86-32))
           (equal (expected-mem-array-next-addr i j x86-32-alt)
                  (expected-mem-array-next-addr i j x86-32)))
  :rule-classes nil)

(defthm expected-mem-array-next-addr-only-depends-on-mem-table
  (implies (and (equal (expected-mem-array-next-addr 0 *mem-table-size* x86-32)
                       x) ; free var
                (syntaxp (equal x86-32 'x86-32))
                (equal (nth *mem-tablei* x86-32-alt)
                       (nth *mem-tablei* x86-32)))
           (equal (expected-mem-array-next-addr 0 *mem-table-size* x86-32-alt)
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
                                          (nth *mem-tablei* x86-32))
           (good-mem-table-entriesp-weak lower upper x86-32))
  :hints (("Goal" :in-theory (e/d (good-mem-table-entriesp-logic
                                   good-mem-table-entriesp-weak)
                                  ((force)))))
  :rule-classes :forward-chaining)

(defun good-mem-arrayp-1 (index len x86-32)
  (declare (xargs :stobjs x86-32
                  :guard (and (natp index)
                              (natp len)
                              (<= index len)
                              (<= len (mem-array-length x86-32)))
                  :measure (nfix (- len index))))
  (cond ((mbe :logic (not (and (natp index)
                               (natp len)
                               (< index len)))
              :exec (eql index len))
         t)
        (t (and (eql (mem-arrayi index x86-32) 0)
                (good-mem-arrayp-1 (1+ index) len x86-32)))))

(defun good-mem-arrayp-1-logic (index len mem-array)
  (declare (xargs :measure (nfix (- len index))))
  (cond ((not (and (natp index)
                   (natp len)
                   (< index len)))
         t)
        (t (and (eql (nth index mem-array) 0)
                (good-mem-arrayp-1-logic (1+ index) len mem-array)))))

(defthm good-mem-arrayp-1-is-good-mem-arrayp-1-logic
  (equal (good-mem-arrayp-1 index len x86-32)
         (good-mem-arrayp-1-logic index len (nth *mem-arrayi* x86-32))))

(defun good-mem-arrayp (x86-32)
  (declare (xargs :stobjs x86-32
                  :guard (<= (mem-array-next-addr x86-32)
                             (mem-array-length x86-32))))
  (mbe :logic
       (good-mem-arrayp-1-logic (mem-array-next-addr x86-32)
                                (mem-array-length x86-32)
                                (nth-nx *mem-arrayi* x86-32))
       :exec
       (good-mem-arrayp-1 (mem-array-next-addr x86-32)
                          (mem-array-length x86-32)
                          x86-32)))

; MEM-TABLE read lemmas

(defthm mem-tablep-forward
   (implies (mem-tablep x)
           (nat-listp x))
  :rule-classes :forward-chaining)

(defmacro mem-table-indexp (x)
  `(and (natp ,x)
        (< ,x *mem-table-size*)))

(defthm natp-mem-tablep-when-valid-mem-table-index
  (implies (forced-and (x86-32p-pre x86-32)
                       (mem-table-indexp i))
           (and (integerp (mem-tablei i x86-32))
                (<= 0 (mem-tablei i x86-32))))
  :rule-classes (:rewrite :type-prescription))

(defthm natp-mem-tablep-when-valid-mem-table-index-nth-version
  (implies (forced-and (x86-32p-pre x86-32)
                       (mem-table-indexp i))
           (and (integerp (nth i (nth *mem-tablei* x86-32)))
                (<= 0 (nth i (nth *mem-tablei* x86-32)))))
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
   (implies (forced-and (x86-32p-pre x86-32)
                        (mem-table-indexp i))
            (< (mem-tablei i x86-32) *mem-size-in-bytes*))
   :rule-classes :linear)

 (defthm mem-tablei-less-than-*mem-size-in-bytes*-nth-version
   (implies (forced-and (x86-32p-pre x86-32)
                        (mem-table-indexp i))
            (< (nth i (nth *mem-tablei* x86-32))
               *mem-size-in-bytes*))
   :rule-classes :linear))

(defun good-memp (x86-32)
  (declare (xargs :stobjs x86-32))
  (let ((table-bound (1- (mem-table-length x86-32)))
        (array-length (mem-array-length x86-32))
        (array-next-addr (mem-array-next-addr x86-32)))
    (and (<= array-next-addr array-length)
         (<= *initial-mem-array-length* array-length)
         (eql (logand 16777215 array-length) 0)
         ; integral number of pseudo pages
         (equal array-next-addr
                (expected-mem-array-next-addr 0
                                              (mem-table-length x86-32)
                                              x86-32))
         (<= array-next-addr array-length)
         (mbe :logic
              (good-mem-table-entriesp-logic 0 table-bound array-next-addr
                                             (nth-nx *mem-tablei* x86-32))
              :exec
              (good-mem-table-entriesp 0 table-bound array-next-addr
                                       x86-32))
         (mbe :logic
              (good-mem-table-no-dupsp-logic 0 table-bound
                                             (nth-nx *mem-tablei* x86-32))
              :exec
              (good-mem-table-no-dupsp 0 table-bound x86-32))
         (good-mem-arrayp x86-32))))

(defun x86-32p (x86-32)
  (declare (xargs :stobjs x86-32))
  (and (x86-32p-pre x86-32)
       (good-memp x86-32)))

; ======================================================================

;;; Generate the basic lemmatta we want about the accessors/updaters
;;; of the x86-32 model.

(defun read-over-write-thms-array (this-name x86-32-model)
  (cond ((endp x86-32-model)
         '())
        ((equal (car (car x86-32-model))
                this-name)
         (read-over-write-thms-array this-name (cdr x86-32-model)))
        (t
         (let* ((x86-32-model-field (car x86-32-model))
                (that-name (car x86-32-model-field))
                (that-type (caddr x86-32-model-field)))
           (cond ((and (consp that-type)
                       (equal (car that-type) 'array))
                  (let ((this-getter (mk-name this-name "I"))
                        (that-setter (mk-name "!" that-name "I")))
                    (cons `(DEFTHM ,(mk-name this-getter "-" that-setter)
                             (EQUAL (,this-getter I2 (,that-setter I1 VAL X86-32))
                                    (,this-getter I2 X86-32)))
                          (read-over-write-thms-array this-name (cdr x86-32-model)))))
                 (t
                  (let ((this-getter (mk-name this-name "I"))
                        (that-setter (mk-name "!" that-name)))
                    (cons `(DEFTHM ,(mk-name this-getter "-" that-setter)
                             (EQUAL (,this-getter I (,that-setter VAL X86-32))
                                    (,this-getter I X86-32)))
                          (read-over-write-thms-array this-name (cdr x86-32-model))))))))))

(defun write-over-write-thms-array-1 (this-name x86-32-model)
  (cond ((endp x86-32-model)
         '())
        (t
         (let* ((x86-32-model-field (car x86-32-model))
                (that-name (car x86-32-model-field))
                (that-type (caddr x86-32-model-field)))
           (cond ((and (consp that-type)
                       (equal (car that-type) 'array))
                  (let ((this-setter (mk-name "!" this-name "I"))
                        (that-setter (mk-name "!" that-name "I")))
                    (cons `(DEFTHM ,(mk-name this-setter "-" that-setter)
                             (EQUAL (,this-setter I2 VAL2 (,that-setter I1 VAL1 X86-32))
                                    (,that-setter I1 VAL1 (,this-setter I2 VAL2 X86-32))))
                          (write-over-write-thms-array-1 this-name (cdr x86-32-model)))))
                 (t
                  (let ((this-setter (mk-name "!" this-name "I"))
                        (that-setter (mk-name "!" that-name)))
                    (cons `(DEFTHM ,(mk-name this-setter "-" that-setter)
                             (EQUAL (,this-setter I VAL2 (,that-setter VAL1 X86-32))
                                    (,that-setter VAL1 (,this-setter I VAL2 X86-32))))
                          (write-over-write-thms-array-1 this-name (cdr x86-32-model))))))))))

(defun write-over-write-thms-array (this-name x86-32-model)
  (cond ((endp x86-32-model)
         '())
        ((equal (car (car x86-32-model))
                this-name)
         ;; We wish to nest field updates in the same order (inside to
         ;; outside) as they are given in the x86-32 model.  So we
         ;; generate the write over write commutativity lemmatta only
         ;; for fields that come after this one in the model.
         (write-over-write-thms-array-1 this-name (cdr x86-32-model)))
        (t
         (write-over-write-thms-array this-name (cdr x86-32-model)))))

(defun read-over-write-thms-simple (this-name x86-32-model)
  (cond ((endp x86-32-model)
         '())
        ((equal (car (car x86-32-model))
                this-name)
         (read-over-write-thms-simple this-name (cdr x86-32-model)))
        (t
         (let* ((x86-32-model-field (car x86-32-model))
                (that-name (car x86-32-model-field))
                (that-type (caddr x86-32-model-field)))
           (cond ((and (consp that-type)
                       (equal (car that-type) 'array))
                  (let ((this-getter (mk-name this-name))
                        (that-setter (mk-name "!" that-name "I")))
                    (cons `(DEFTHM ,(mk-name this-getter "-" that-setter)
                             (EQUAL (,this-getter (,that-setter I VAL X86-32))
                                    (,this-getter X86-32)))
                          (read-over-write-thms-simple this-name (cdr x86-32-model)))))
                 (t
                  (let ((this-getter (mk-name this-name))
                        (that-setter (mk-name "!" that-name)))
                    (cons `(DEFTHM ,(mk-name this-getter "-" that-setter)
                             (EQUAL (,this-getter (,that-setter VAL X86-32))
                                    (,this-getter X86-32)))
                          (read-over-write-thms-simple this-name (cdr x86-32-model))))))))))

(defun write-over-write-thms-simple-1 (this-name x86-32-model)
  (cond ((endp x86-32-model)
         '())
        (t
         (let* ((x86-32-model-field (car x86-32-model))
                (that-name (car x86-32-model-field))
                (that-type (caddr x86-32-model-field)))
           (cond ((and (consp that-type)
                       (equal (car that-type) 'array))
                  (let ((this-setter (mk-name "!" this-name))
                        (that-setter (mk-name "!" that-name "I")))
                    (cons `(DEFTHM ,(mk-name this-setter "-" that-setter)
                             (EQUAL (,this-setter VAL2 (,that-setter I VAL1 X86-32))
                                    (,that-setter I VAL1 (,this-setter VAL2 X86-32))))
                          (write-over-write-thms-simple-1 this-name (cdr x86-32-model)))))
                 (t
                  (let ((this-setter (mk-name "!" this-name))
                        (that-setter (mk-name "!" that-name)))
                    (cons `(DEFTHM ,(mk-name this-setter "-" that-setter)
                             (EQUAL (,this-setter VAL2 (,that-setter VAL1 X86-32))
                                    (,that-setter VAL1 (,this-setter VAL2 X86-32))))
                          (write-over-write-thms-simple-1 this-name (cdr x86-32-model))))))))))

(defun write-over-write-thms-simple (this-name x86-32-model)
  (cond ((endp x86-32-model)
         '())
        ((equal (car (car x86-32-model))
                this-name)
         ;; We wish to nest field updates in the same order (inside to
         ;; outside) as they are given in the x86-32 model.  So we
         ;; generate the write over write commutativity lemmatta only
         ;; for fields that come after this one in the model.  (These
         ;; rules commute "this" inside "that")
         (write-over-write-thms-simple-1 this-name (cdr x86-32-model)))
        (t
         (write-over-write-thms-simple this-name (cdr x86-32-model)))))

(defun x86-32-stobj-field-thms-fn-1 (x86-32-model-field x86-32-model)
  ;; this function is rather brittle, in that it assumes that the
  ;; elements of the x86-32-model are defined in a rigid manner.
  (let ((name (car x86-32-model-field))
        (type (caddr x86-32-model-field)))
    (cond ((and (consp type)
                (equal (car type) 'array)
                (consp (cadr type))
                (equal (car (cadr type)) 'unsigned-byte))
           (let* ((predicate (mk-name name "P"))
                  (namei     (mk-name name "I"))
                  (getter    namei)
                  (setter    (mk-name "!" namei))

                  (size      (cadr (cadr  type)))
                  (length    (if (equal (car (cddr (cddr (cddr x86-32-model-field))))
                                        'T)
                                 ;; resizable array
                                 `(,(mk-name name "-LENGTH") X86-32)
                               (car  (caddr type)))))
             `(;; readers
               (LOCAL
                (DEFTHM ,(mk-name predicate "-FORWARD")
                  (IMPLIES (,predicate X)
                           (NAT-LISTP X))
                  :RULE-CLASSES :FORWARD-CHAINING))
               (DEFTHM ,(mk-name "NATP-" getter)
                 (IMPLIES (FORCED-AND (X86-32P X86-32)
                                      (INTEGERP I)
                                      (<= 0 I)
                                      (< I ,length))
                          (AND (INTEGERP (,getter I X86-32))
                               (<= 0 (,getter I X86-32))))
                 :RULE-CLASSES :TYPE-PRESCRIPTION)
               (ENCAPSULATE
                ()
                ;; I used to have this local, but some of the proofs
                ;; about functions such as memi needed them.
                (DEFTHM ,(mk-name "NTH-OF-" getter "-LESS-THAN-EXPT-2-" size)
                  (IMPLIES (AND (,predicate X)
                                (INTEGERP I)
                                (<= 0 I)
                                (< I (LEN X)))
                           (< (NTH I X) ,(expt 2 size)))
                  :HINTS (("Goal" :IN-THEORY (E/D (NTH) ())))
                  :RULE-CLASSES :LINEAR)
                (DEFTHM ,(mk-name getter "-LESS-THAN-EXPT-2-" size)
                  (IMPLIES (FORCED-AND (X86-32P X86-32)
                                       (INTEGERP I)
                                       (<= 0 I)
                                       (< I ,length))
                           (< (,getter I X86-32) ,(expt 2 size)))
                  :RULE-CLASSES :LINEAR)
                )
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
               ;; read over write and such --- this field
               (DEFTHM ,(mk-name getter "-" setter)
                 (IMPLIES (FORCED-AND ;; (X86-32P X86-32)
                                      (INTEGERP I1)
                                      (<= 0 I1)
                                      ;;(< I1 ,length)
                                      (INTEGERP I2)
                                      (<= 0 I2)
                                      ;;(< I2 ,length)
                                      )
                          (EQUAL (,getter I2 (,setter I1 V X86-32))
                                 (IF (EQUAL I1 I2)
                                     V
                                     (,getter I2 X86-32)))))
               (DEFTHM ,(mk-name setter "-" setter "-SAME")
                 (IMPLIES (FORCED-AND ;; (X86-32P X86-32)
                                      ;;(INTEGERP I)
                                      ;;(<= 0 I)
                                      ;;(< I ,length)
                                      )
                          (EQUAL (,setter I V2 (,setter I V1 X86-32))
                                 (,setter I V2 X86-32))))
               (DEFTHM ,(mk-name setter "-" setter "-DIFFERENT")
                 ;; do we wnat to specify the loop-stopper?
                 (IMPLIES (AND (NOT (EQUAL I1 I2))
                               (FORCED-AND ;; (X86-32P X86-32)
                                           (INTEGERP I1)
                                           (<= 0 I1)
                                           ;;(< I1 ,length)
                                           (INTEGERP I2)
                                           (<= 0 I2)
                                           ;;(< I2 ,length)
                                           ))
                          (EQUAL (,setter I2 V2 (,setter I1 V1 X86-32))
                                 (,setter I1 V1 (,setter I2 V2 X86-32)))))
               (DEFTHM ,(mk-name setter "-" getter)
                 (IMPLIES (FORCED-AND (X86-32P X86-32)
                                      (INTEGERP I)
                                      (<= 0 I)
                                      (< I ,length))
                          (EQUAL (,setter I (,getter I X86-32) X86-32)
                                 X86-32)))
                 ;; TO-DO@Shilpi: Why did I need to add the following hint?
                 ;;:hints (("Goal" :in-theory (enable nth update-nth))))
               ;; read over write and such --- other field
               ,@(read-over-write-thms-array name x86-32-model)
               ,@(write-over-write-thms-array name x86-32-model)
               )))
          ((and (consp type)
                (equal (car type) 'array)
                (consp (cadr type))
                (equal (car (cadr type)) 'signed-byte))
           (let* ((predicate (mk-name name "P"))
                  (namei     (mk-name name "I"))
                  (getter    namei)
                  (setter    (mk-name "!" namei))

                  (size      (1- (cadr (cadr  type))))
                  (length    (if (equal (car (cddr (cddr (cddr x86-32-model-field))))
                                        'T)
                                 ;; resizable array
                                 `(,(mk-name name "-LENGTH") X86-32)
                               (car  (caddr type)))))
             `(;; readers
               (LOCAL
                (DEFTHM ,(mk-name predicate "-FORWARD")
                  (IMPLIES (,predicate X)
                           (INTEGER-LISTP X))
                  :RULE-CLASSES :FORWARD-CHAINING))
               (DEFTHM ,(mk-name "INTEGERP-" getter)
                 (IMPLIES (FORCED-AND (X86-32P X86-32)
                                      (INTEGERP I)
                                      (<= 0 I)
                                      (< I ,length))
                          (INTEGERP (,getter I X86-32)))
                 :RULE-CLASSES :TYPE-PRESCRIPTION)
               (ENCAPSULATE
                ()
                ;; I used to have this local, but some of the proofs
                ;; about functions such as memi needed them.
                (DEFTHM ,(mk-name "NTH-OF-" getter "-LESS-THAN-EXPT-2-" size)
                  (IMPLIES (AND (,predicate X)
                                (INTEGERP I)
                                (<= 0 I)
                                (< I (LEN X)))
                           (< (NTH I X) ,(expt 2 size)))
                  :HINTS (("Goal" :IN-THEORY (E/D (NTH) ())))
                  :RULE-CLASSES :LINEAR)
                (DEFTHM ,(mk-name "NTH-OF-" getter "-GE-NEG-EXPT-2-" size)
                  (IMPLIES (AND (,predicate X)
                                (INTEGERP I)
                                (<= 0 I)
                                (< I (LEN X)))
                           (<= ,(- (expt 2 size)) (NTH I X)))
                  :HINTS (("Goal" :IN-THEORY (E/D (NTH) ())))
                  :RULE-CLASSES :LINEAR)
                (DEFTHM ,(mk-name getter "-LESS-THAN-EXPT-2-" size)
                  (IMPLIES (FORCED-AND (X86-32P X86-32)
                                       (INTEGERP I)
                                       (<= 0 I)
                                       (< I ,length))
                           (< (,getter I X86-32) ,(expt 2 size)))
                  :RULE-CLASSES :LINEAR)
                (DEFTHM ,(mk-name getter "-GE-NEG-EXPT-2-" size)
                  (IMPLIES (FORCED-AND (X86-32P X86-32)
                                       (INTEGERP I)
                                       (<= 0 I)
                                       (< I ,length))
                           (<= ,(- (expt 2 size)) (,getter I X86-32)))
                  :RULE-CLASSES :LINEAR)
                )
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
               ;; read over write and such --- this field
               (DEFTHM ,(mk-name getter "-" setter)
                 (IMPLIES (FORCED-AND ;; (X86-32P X86-32)
                                      (INTEGERP I1)
                                      (<= 0 I1)
                                      ;;(< I1 ,length)
                                      (INTEGERP I2)
                                      (<= 0 I2)
                                      ;;(< I2 ,length)
                                      )
                          (EQUAL (,getter I2 (,setter I1 V X86-32))
                                 (IF (EQUAL I1 I2)
                                     V
                                     (,getter I2 X86-32)))))
               (DEFTHM ,(mk-name setter "-" setter "-SAME")
                 (IMPLIES (FORCED-AND ;; (X86-32P X86-32)
                                      ;;(INTEGERP I)
                                      ;;(<= 0 I)
                                      ;;(< I ,length)
                                      )
                          (EQUAL (,setter I V2 (,setter I V1 X86-32))
                                 (,setter I V2 X86-32))))
               (DEFTHM ,(mk-name setter "-" setter "-DIFFERENT")
                 ;; do we want to specify the loop-stopper?
                 (IMPLIES (AND (NOT (EQUAL I1 I2))
                               (FORCED-AND ;; (X86-32P X86-32)
                                           (INTEGERP I1)
                                           (<= 0 I1)
                                           ;;(< I1 ,length)
                                           (INTEGERP I2)
                                           (<= 0 I2)
                                           ;;(< I2 ,length)
                                           ))
                          (EQUAL (,setter I2 V2 (,setter I1 V1 X86-32))
                                 (,setter I1 V1 (,setter I2 V2 X86-32)))))
               (DEFTHM ,(mk-name setter "-" getter)
                 (IMPLIES (FORCED-AND (X86-32P X86-32)
                                      (INTEGERP I)
                                      (<= 0 I)
                                      (< I ,length))
                          (EQUAL (,setter I (,getter I X86-32) X86-32)
                                 X86-32)))
                 ;; TO-DO@Shilpi: Why did I need to add the following hint?
                 ;;:hints (("Goal" :in-theory (enable nth update-nth))))
               ;; read over write and such --- other field
               ,@(read-over-write-thms-array name x86-32-model)
               ,@(write-over-write-thms-array name x86-32-model)
               )))
          ((and (consp type)
                (equal (car type) 'unsigned-byte))
           (let* ((getter  name)
                  (setter  (mk-name "!" name))

                  (size    (cadr type)))
             `(;; readers
               (DEFTHM ,(mk-name "NATP-" name)
                 (IMPLIES (FORCE (X86-32P X86-32))
                          (AND (INTEGERP (,getter X86-32))
                               (<= 0 (,getter X86-32))))
                 :RULE-CLASSES :TYPE-PRESCRIPTION)
               (DEFTHM ,(mk-name name "-LESS-THAN-EXPT-2-" size)
                 (IMPLIES (FORCE (X86-32P X86-32))
                          (< (,getter X86-32) ,(expt 2 size)))
                 :RULE-CLASSES :LINEAR)
               ;; writers
               ;; read over write and such --- this field
               (DEFTHM ,(mk-name getter "-" setter)
                 (EQUAL (,getter (,setter V X86-32))
                        V))
               (DEFTHM ,(mk-name setter "-" setter)
                 (EQUAL (,setter V2 (,setter V1 X86-32))
                        (,setter V2 X86-32)))
               (DEFTHM ,(mk-name setter "-" getter)
                 (IMPLIES (FORCE (X86-32P X86-32))
                          (EQUAL (,setter (,getter X86-32) X86-32)
                                 X86-32)))
                 ;; TO-DO@Shilpi: Why did I need to add the following hint?
                 ;;:hints (("Goal" :in-theory (enable nth update-nth))))
               ;; read over write and such --- other field
               ,@(read-over-write-thms-simple name x86-32-model)
               ,@(write-over-write-thms-simple name x86-32-model)
               )))
          ((and (consp type)
                (equal (car type) 'signed-byte))
           (let* ((getter  name)
                  (setter  (mk-name "!" name))

                  (size    (1- (cadr type))))
             `( ;; readers
               (DEFTHM ,(mk-name "INTEGERP-" name)
                 (IMPLIES (FORCE (X86-32P X86-32))
                          (INTEGERP (,getter X86-32)))
                 :RULE-CLASSES :TYPE-PRESCRIPTION)
               (DEFTHM ,(mk-name name "-LESS-THAN-EXPT-2-" size)
                 (IMPLIES (FORCE (X86-32P X86-32))
                          (< (,getter X86-32) ,(expt 2 size)))
                 :RULE-CLASSES :LINEAR)
               (DEFTHM ,(mk-name name "-GE-NEGATIVE-EXPT-2-" size)
                 (IMPLIES (FORCE (X86-32P X86-32))
                          (<= ,(- (expt 2 size)) (,getter X86-32)))
                 :RULE-CLASSES :LINEAR)
               ;; writers
               ;; read over write and such --- this field
               (DEFTHM ,(mk-name getter "-" setter)
                 (EQUAL (,getter (,setter V X86-32))
                        V))
               (DEFTHM ,(mk-name setter "-" setter)
                 (EQUAL (,setter V2 (,setter V1 X86-32))
                        (,setter V2 X86-32)))
               (DEFTHM ,(mk-name setter "-" getter)
                 (IMPLIES (FORCE (X86-32P X86-32))
                          (EQUAL (,setter (,getter X86-32) X86-32)
                                 X86-32)))
                 ;; TO-DO@Shilpi: Why did I need to add the following hint?
                 ;;:hints (("Goal" :in-theory (enable nth update-nth))))
               ;; read over write and such --- other field
               ,@(read-over-write-thms-simple name x86-32-model)
               ,@(write-over-write-thms-simple name x86-32-model)
               )))
          ((and (consp type)
                (equal (car type) 'integer))
           (let* ((getter  name)
                  (setter  (mk-name "!" name))

                  (size    (caddr type)))
             `(;; readers
               (DEFTHM ,(mk-name "NATP-" name)
                 (IMPLIES (FORCE (X86-32P X86-32))
                          (AND (INTEGERP (,getter X86-32))
                               (<= 0 (,getter X86-32))))
                 :RULE-CLASSES :TYPE-PRESCRIPTION)
               (DEFTHM ,(mk-name name "-LESS-THAN-" size)
                 (IMPLIES (FORCE (X86-32P X86-32))
                          (<= (,getter X86-32) ,size))
                 :RULE-CLASSES :LINEAR)
               ;; writers
               ;; read over write and such --- this field
               (DEFTHM ,(mk-name getter "-" setter)
                 (EQUAL (,getter (,setter V X86-32))
                        V))
               (DEFTHM ,(mk-name setter "-" setter)
                 (EQUAL (,setter V2 (,setter V1 X86-32))
                        (,setter V2 X86-32)))
               (DEFTHM ,(mk-name setter "-" getter)
                 (IMPLIES (FORCE (X86-32P X86-32))
                          (EQUAL (,setter (,getter X86-32) X86-32)
                                 X86-32)))
                 ;; TO-DO@Shilpi: Why did I need to add the following hint?
                 ;;:hints (("Goal" :in-theory (enable nth update-nth))))
               ;; read over write and such --- other field
               ,@(read-over-write-thms-simple name x86-32-model)
               ,@(write-over-write-thms-simple name x86-32-model)
               )))
          (t
           ;; type is presumably 'T
           (let* ((getter name)
                  (setter (mk-name "!" name)))
             `(;; readers
               ;; none
               ;; writers
               ;; read over write and such --- this field
               (DEFTHM ,(mk-name getter "-" setter)
                 (EQUAL (,getter (,setter V X86-32))
                        V))
               (DEFTHM ,(mk-name setter "-" setter)
                 (EQUAL (,setter V2 (,setter V1 X86-32))
                        (,setter V2 X86-32)))
               (DEFTHM ,(mk-name setter "-" getter)
                 (IMPLIES (FORCE (X86-32P X86-32))
                          (EQUAL (,setter (,getter X86-32) X86-32)
                                 X86-32)))
                 ;; TO-DO@Shilpi: Why did I need to add the following hint?
                 ;;:hints (("Goal" :in-theory (enable nth update-nth))))
               ;; read over write and such --- other field
               ,@(read-over-write-thms-simple name x86-32-model)
               ,@(write-over-write-thms-simple name x86-32-model)
               ))))))

(defun x86-32-stobj-x86-32p-setter-thms-fn-1 (x86-32-model-field)
  ;; this function is rather brittle, in that it assumes that the
  ;; elements of the x86-32-model are defined in a rigid manner.
  (let ((name (car x86-32-model-field))
        (type (caddr x86-32-model-field)))
    (cond ((and (consp type)
                (equal (car type) 'array)
                (consp (cadr type))
                (equal (car (cadr type)) 'unsigned-byte))
           (let* ((namei     (mk-name name "I"))
                  (setter    (mk-name "!" namei))
                  (size      (cadr (cadr  type)))
                  (length    (if (equal (car (cddr (cddr (cddr x86-32-model-field))))
                                        'T)
                                 ;; resizable array
                                 `(,(mk-name name "-LENGTH") X86-32)
                               (car  (caddr type)))))
             `((DEFTHM ,(mk-name "X86-32P-" setter)
                 (IMPLIES (FORCED-AND (X86-32P X86-32)
                                      (INTEGERP I)
                                      (<= 0 I)
                                      (< I ,length)
                                      (INTEGERP V)
                                      (<= 0 V)
                                      (< V ,(expt 2 size)))
                          ,(if (or (equal name 'mem-table)
                                   (equal name 'mem-array))
                               ;; Because of the good-memp predicate,
                               ;; we must handle these two
                               ;; seperately.  In fact, these fields
                               ;; will only be modified by !memi, and
                               ;; it is that which we will prove
                               ;; maintains the x86-32p predicate.
                               `(X86-32P-PRE (,setter I V X86-32))
                             `(X86-32P (,setter I V X86-32)))))
               )))
          ((and (consp type)
                (equal (car type) 'array)
                (consp (cadr type))
                (equal (car (cadr type)) 'signed-byte))
           (let* ((namei     (mk-name name "I"))
                  (setter    (mk-name "!" namei))
                  (size      (1- (cadr (cadr  type))))
                  (length    (if (equal (car (cddr (cddr (cddr x86-32-model-field))))
                                        'T)
                                 ;; resizable array
                                 `(,(mk-name name "-LENGTH") X86-32)
                               (car  (caddr type)))))
             `((DEFTHM ,(mk-name "X86-32P-" setter)
                 (IMPLIES (FORCED-AND (X86-32P X86-32)
                                      (INTEGERP I)
                                      (<= 0 I)
                                      (< I ,length)
                                      (INTEGERP V)
                                      (<= ,(- (expt 2 size)) V)
                                      (< V ,(expt 2 size)))
                          ,(if (or (equal name 'mem-table)
                                   (equal name 'mem-array))
                               ;; Because of the good-memp predicate,
                               ;; we must handle these two
                               ;; seperately.  In fact, these fields
                               ;; will only be modified by !memi, and
                               ;; it is that which we will prove
                               ;; maintains the x86-32p predicate.
                               `(X86-32P-PRE (,setter I V X86-32))
                             `(X86-32P (,setter I V X86-32)))))
               )))
          ((and (consp type)
                (equal (car type) 'unsigned-byte))
           (let* ((setter  (mk-name "!" name))
                  (size    (cadr type)))
             `((DEFTHM ,(mk-name "X86-32P-" setter)
                 (IMPLIES (FORCED-AND (X86-32P X86-32)
                                      ;; can we replace these with
                                      ;; nXYp?  do we want to?
                                      (INTEGERP V)
                                      (<= 0 V)
                                      (< V ,(expt 2 size)))
                          ,(if (equal name 'mem-array-next-addr)
                               ;; Because of the good-memp predicate,
                               ;; we must handle this one seperately.
                               ;; In fact, this field will only be
                               ;; modified by !memi, and it is that
                               ;; which we will prove maintains the
                               ;; x86-32p predicate.
                               `(X86-32P-PRE (,setter V X86-32))
                             `(X86-32P (,setter V X86-32)))))
               )))
          ((and (consp type)
                (equal (car type) 'signed-byte))
           (let* ((setter  (mk-name "!" name))
                  (size    (1- (cadr type))))
             `((DEFTHM ,(mk-name "X86-32P-" setter)
                 (IMPLIES (FORCED-AND (X86-32P X86-32)
                                      ;; can we replace these with
                                      ;; iXYp?  do we want to?
                                      (INTEGERP V)
                                      (<= ,(- (expt 2 size)) V)
                                      (< V ,(expt 2 size)))
                          ,(if (equal name 'mem-array-next-addr)
                               ;; Because of the good-memp predicate,
                               ;; we must handle this one seperately.
                               ;; In fact, this field will only be
                               ;; modified by !memi, and it is that
                               ;; which we will prove maintains the
                               ;; x86-32p predicate.
                               `(X86-32P-PRE (,setter V X86-32))
                             `(X86-32P (,setter V X86-32)))))
               )))
          ((and (consp type)
                (equal (car type) 'integer))
           (let* ((setter  (mk-name "!" name))
                  (size    (caddr type)))
             `((DEFTHM ,(mk-name "X86-32P-" setter)
                 (IMPLIES (FORCED-AND (X86-32P X86-32)
                                      ;; can we replace these with
                                      ;; nXYp?  do we want to?
                                      (INTEGERP V)
                                      (<= 0 V)
                                      (<= V ,size))
                          ,(if (equal name 'mem-array-next-addr)
                               ;; Because of the good-memp predicate,
                               ;; we must handle this one seperately.
                               ;; In fact, this field will only be
                               ;; modified by !memi, and it is that
                               ;; which we will prove maintains the
                               ;; x86-32p predicate.
                               `(X86-32P-PRE (,setter V X86-32))
                             `(X86-32P (,setter V X86-32)))))
               )))
          (t
           ;; type is presumably 'T
           (let* ((setter (mk-name "!" name)))
             `((DEFTHM ,(mk-name "X86-32P-" setter)
                 (IMPLIES (FORCE (X86-32P X86-32))
                          (X86-32P (,setter V X86-32))))
               ))))))

(defun x86-32-stobj-x86-32p-setter-thms-fn (x86-32-model)
  (cond ((endp x86-32-model)
         '())
        (t
         `(,@(x86-32-stobj-x86-32p-setter-thms-fn-1 (car x86-32-model))
           ,@(x86-32-stobj-x86-32p-setter-thms-fn (cdr x86-32-model))))))

(defun x86-32-stobj-field-thms-fn (x86-32-model full-x86-32-model)
  ;; we use two copies of the x86-32-model, one to step through here, and
  ;; one to step through in x86-32-stobj-field-thms-fn-1 so that we can
  ;; generate the read-over-write lematta for different fields.
 (cond ((endp x86-32-model)
         '())
        (t
         `(,@(x86-32-stobj-field-thms-fn-1 (car x86-32-model) full-x86-32-model)
           ,@(x86-32-stobj-field-thms-fn (cdr x86-32-model) full-x86-32-model)))))

; Lemmas to help with proofs about STOBJs that hold x86-32 state.  Our
; goal is to prove a nice set of forward-chaining lemmas, as our
; predicates seem nicely set up for that.

(defmacro x86-32-stobj-field-thms (x86-32-model)
  `(ENCAPSULATE
    ()

    (LOCAL
     (DEFTHM NAT-LISTP-THM
       (IMPLIES (AND (NAT-LISTP X)
                     (INTEGERP I)
                     (<= 0 I)
                     (< I (LEN X)))
                (AND (INTEGERP (NTH I X))
                     (<= 0 (NTH I X))))))

    (LOCAL
     (DEFTHM UPDATE-NTH-THM-1
       (EQUAL (UPDATE-NTH I V2 (UPDATE-NTH I V1 X))
              (UPDATE-NTH I V2 X))))

    (LOCAL
     (DEFTHM UPDATE-NTH-THM-2
       (IMPLIES (AND (INTEGERP I1)
                     (<= 0 I1)
                     (INTEGERP I2)
                     (<= 0 I2)
                     (NOT (EQUAL I1 I2)))
                (EQUAL (UPDATE-NTH I2 V2 (UPDATE-NTH I1 V1 X))
                       (UPDATE-NTH I1 V1 (UPDATE-NTH I2 V2 X))))))

    ;; TO-DO@Shilpi
    ;; RBK
    ;; Why don't we have a loop-stopper in the update-nth-thm-2 theorem?

    (LOCAL
     (DEFTHM UPDATE-NTH-THM-3
       (IMPLIES (AND (INTEGERP N)
                     (<= 0 N)
                     (< N (LEN X86-32))
                     (INTEGERP I)
                     (<= 0 I)
                     (< I (LEN (NTH N X86-32))))
                (EQUAL (UPDATE-NTH N
                                   (UPDATE-NTH I (NTH I (NTH N X86-32))
                                               (NTH N X86-32))
                                   X86-32)
                       X86-32))))

    (LOCAL
     (DEFTHM UPDATE-NTH-THM-4
       (IMPLIES (AND (INTEGERP I)
                     (<= 0 I)
                     (< I (LEN X86-32)))
                (EQUAL (UPDATE-NTH I (NTH I X86-32) X86-32)
                       X86-32))))

    (LOCAL
     (IN-THEORY (E/D ()
                     (NTH UPDATE-NTH))))

    ,@(x86-32-stobj-field-thms-fn x86-32-model x86-32-model)
    ,@(x86-32-stobj-x86-32p-setter-thms-fn x86-32-model)))

;; TO-DO@Shilpi: Where was length disabled?  Should it have been
;; disabled locally there?
(in-theory (enable length))

(make-event
 `(x86-32-stobj-field-thms ,*x86-32-model*))

; ======================================================================

;;; Disabling the stobj functions:

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
                         ;;(length    (mk-name name "-LENGTH"))
                         )
                    (append `(,getter
                              ,setter
                              ;;,length
                              )
                            (disable-stobj-fns-fn-1 (cdr x86-32-model)))))
                 (t
                  (let ((getter  name)
                        (setter  (mk-name "!" name)))
                    (append `(,getter ,setter)
                            (disable-stobj-fns-fn-1 (cdr x86-32-model))))))))))

(defmacro disable-stobj-fns-fn (x86-32-model)
  `(IN-THEORY
    (DISABLE ,@(disable-stobj-fns-fn-1 x86-32-model))))

(make-event
 `(disable-stobj-fns-fn ,*x86-32-model*))

(defthm x86-32p-forward-to-x86-32p-pre
  (implies (x86-32p x86-32)
           (x86-32p-pre x86-32))
  :rule-classes :forward-chaining)

(defthm x86-32p-forward-to-good-memp
  (implies (x86-32p x86-32)
           (good-memp x86-32))
  :rule-classes :forward-chaining)

(in-theory (disable x86-32p-pre
                    x86-32p))

; ======================================================================

;; (i-am-here)

;; ; Read memory byte and memory double-word functions

;; (encapsulate
;;  ()

;;  (local
;;   (def-gl-thm ash-logand-addr-3-is-integerp-less-or-equal-24
;;     :hyp (n32p addr)
;;     :concl (<= (ash (logand addr 3) 3) 24)
;;     :g-bindings
;;      `((addr (:g-number ,(gl-int  0 1 33))))))

;;  (local
;;   (def-gl-thm ash-memi-ash-logand-addr
;;     :hyp (and (n32p mem-value)
;;               (n32p addr))
;;     :concl (< (ash mem-value (- (ash (logand addr 3) 3)))
;;               4294967296)
;;     :rule-classes :linear
;;     :g-bindings
;;     `((addr      (:g-number ,(gl-int  0 1 33)))
;;       (mem-value (:g-number ,(gl-int 33 1 33))))))

;;  (defun rm08 (addr x86-32)
;;    (declare (xargs :guard (n32p addr)
;;                    :stobjs (x86-32)))
;;    (declare (type (unsigned-byte 32) addr))
;;    (let* ((byte-num     (n02 addr))
;;           (dword-addr   (ash addr -2))
;;           (dword        (memi dword-addr x86-32))
;;           (shift-amount (ash byte-num 3))
;;           ;; Next form causes (callq (@ .SPBUILTIN-ASH)).
;;           (shifted-word (ash dword (- shift-amount))))
;;      (declare (type (unsigned-byte  2) byte-num)
;;               (type (unsigned-byte 30) dword-addr)
;;               (type (unsigned-byte 32) dword shifted-word)
;;               (type (integer 0     24) shift-amount))
;;      (n08 shifted-word)))

;;  (defun rm16 (addr x86-32)
;;    (declare (xargs :guard (n32p addr)
;;                    :stobjs (x86-32)))
;;    (declare (type (unsigned-byte 32) addr))
;;    (let* ((byte-num   (n02 addr))
;;           (dword-addr (ash addr -2))
;;           (dword      (memi dword-addr x86-32)))
;;      (declare (type (unsigned-byte  2) byte-num)
;;               (type (unsigned-byte 30) dword-addr)
;;               (type (unsigned-byte 32) dword))
;;      (if (= byte-num 3)
;;        ;; Memory "wrap"
;;          (let* ((byte0 (rm08       addr    x86-32))
;;                 (byte1 (rm08 (n32+ addr 1) x86-32)))
;;            (declare (type (unsigned-byte 8) byte0 byte1))
;;            (logior (ash byte1 8) byte0))
;;        (logand (ash dword (- (ash byte-num 3)))
;;                #xffff))))

;;  (local (defthm integerp-+
;;           (implies (and (integerp x)
;;                         (integerp y))
;;                    (integerp (+ x y)))))

;;  (local (defthm integerp-expt
;;           (implies (natp x)
;;                    (integerp (expt 2 x)))))

;;  (defun rm32 (addr x86-32)
;;    (declare (xargs :guard (n32p addr)
;;                    :stobjs (x86-32)))
;;    (declare (type (unsigned-byte 32) addr))
;;    (let* ((byte-num   (n02 addr))
;;           (dword-addr (ash addr -2))
;;           (dword      (memi dword-addr x86-32)))
;;      (declare (type (unsigned-byte  2) byte-num)
;;               (type (unsigned-byte 30) dword-addr)
;;               (type (unsigned-byte 32) dword))
;;      (if (= byte-num 0)
;;          dword

;; ; Here is a picture in the case that byte-num is 3 (each "x" digit is hex):

;; ;     dword-addr+1  dword-addr  ...... 0
;; ;           |        |
;; ; [next-dword] [dword]
;; ;    xxxxxxxx xxxxxxxx  [from old mem]
;; ;                   <>  shift0 [ 8 in this example]
;; ;               <-  ->  shift1 [24 in this example]
;; ;             xx        lo
;; ;      xxxxxx           hi

;;        (let* ((shift0 (ash (- 4 byte-num) 3))
;;               (shift1 (ash byte-num 3))
;;               (lo (ash dword (- shift1)))
;;               (dword-addr+1 (n30+ dword-addr 1))
;;               (next-dword (memi dword-addr+1 x86-32))
;;               (hi (logand next-dword (- (ash 1 shift1)
;;                                         1))))
;;          (declare (type (unsigned-byte 32) lo hi))
;;          (logior lo (ash hi shift0)))))))

;; (defthm natp-rm08
;;   (implies (and (force (x86-32p x86-32))
;;                 (force (n32p addr)))
;;            (and (integerp (rm08 addr x86-32))
;;                 (<= 0 (rm08 addr x86-32))))
;;   :rule-classes :type-prescription)

;; (defthm rm08-less-than-expt-2-32
;;   (implies (and (x86-32p x86-32)
;;                 (n32p addr))
;;            (< (rm08 addr x86-32) 256))
;;   :rule-classes :linear)

;; (in-theory (disable rm08))

;; (encapsulate
;;  ()
;;  (local
;;   (def-gl-thm logior-ash-bytes-<=-0
;;     :hyp (and (n08p byte0)
;;               (n08p byte1))
;;     :concl
;;     (<= 0 (logior (ash byte1 8) byte0))
;;     :g-bindings
;;     `((byte0 (:g-number ,(gl-int  0 1 9)))
;;       (byte1 (:g-number ,(gl-int  9 1 9))))))

;;  (local
;;   (def-gl-thm logior-ash-bytes-<-4294967296
;;     :hyp (and (n08p byte0)
;;               (n08p byte1))
;;     :concl
;;     (< (logior (ash byte1 8) byte0)
;;        65536)
;;     :g-bindings
;;     `((byte0 (:g-number ,(gl-int  0 1 9)))
;;       (byte1 (:g-number ,(gl-int  9 1 9))))))

;;  (defthm integerp-rm16
;;    (implies (and (force (x86-32p x86-32))
;;                  (force (n32p addr)))
;;             (and (integerp (rm16 addr x86-32))
;;                  (<= 0 (rm16 addr x86-32))))
;;    :rule-classes :type-prescription)

;;  (defthm rm16-less-than-expt-2-16
;;    (implies (and (x86-32p x86-32)
;;                  (n32p addr))
;;             (< (rm16 addr x86-32) 65536))
;;    :rule-classes :linear))

;; (in-theory (disable rm16))

;; (defthm integerp-rm32
;;   (implies (and (force (x86-32p x86-32))
;;                 (force (n32p addr)))
;;            (and (integerp (rm32 addr x86-32))
;;                 (<= 0 (rm32 addr x86-32))))
;;   :rule-classes :type-prescription)

;; (encapsulate
;;  ()

;;  (local
;;   (def-gl-thm hack
;;     :hyp (and (n32p dword1)
;;               (n32p dword2)
;;               (integerp addr)
;;               (<= 0 addr)
;;               (< addr 4294967296)
;;               (not (equal (logand addr 3) 0)))
;;     :concl (< (logior (ash dword1
;;                            (- (ash (logand addr 3) 3)))
;;                       (ash (logand dword2
;;                                    (+ -1 (ash 1 (ash (logand addr 3) 3))))
;;                            (ash (+ 4 (- (logand addr 3))) 3)))
;;               4294967296)
;;     :g-bindings
;;     `((addr (:g-number ,(gl-int 0 1 33)))
;;       (dword1 (:g-number ,(gl-int 33 1 33)))
;;       (dword2 (:g-number ,(gl-int 66 1 33))))))

;;  (defthm rm32-less-than-expt-2-32
;;    (implies (and (x86-32p x86-32)
;;                  (n32p addr))
;;             (< (rm32 addr x86-32) 4294967296))
;;    :rule-classes :linear))

;; (in-theory (disable rm32))

;; ; Write memory byte, memory double-word functions

;; (encapsulate
;;  ()

;;  (local
;;   (def-gl-thm ash-logand-addr-3-is-integerp-less-than-or-equal-24
;;     :hyp (n32p addr)
;;     :concl (<= (ash (logand addr 3) 3) 24)
;;     :g-bindings
;;     `((addr (:g-number ,(gl-int  0 1 33))))))

;;  (local
;;   (def-gl-thm ash-n08p-ash-logand-addr-3-3
;;     :hyp (and (n32p addr)
;;               (n08p byte))
;;     :concl (< (ash byte (ash (logand addr 3) 3))
;;                4294967296)
;;     :g-bindings
;;     `((addr (:g-number ,(gl-int  0 1 33)))
;;       (byte (:g-number ,(gl-int 33 1 9))))))

;;  (local
;;   (def-gl-thm word-to-write-equality
;;     :hyp (and (n08p byte)
;;               (n32p val)
;;               (n32p addr))
;;     :concl
;;     (equal (logand (logior (logand (lognot (ash 255 (ash (logand addr 3) 3))) val)
;;                            (ash byte (ash (logand addr 3) 3)))
;;                    4294967295)
;;            (logior (logand (lognot (ash 255 (ash (logand addr 3) 3)))
;;                            val)
;;                    (ash byte (ash (logand addr 3) 3))))
;;     :g-bindings
;;     `((addr (:g-number ,(gl-int  0 1 33)))
;;       (byte (:g-number ,(gl-int 33 1 9)))
;;       (val  (:g-number ,(gl-int 42 1 33))))))

;;  (local
;;   (def-gl-thm natp-word-to-write
;;     :hyp (and (n08p byte)
;;               (n32p value)
;;               (n32p addr))
;;     :concl
;;     (<= 0 (logior (logand (lognot (ash 255 (ash (logand addr 3) 3))) value)
;;                   (ash byte (ash (logand addr 3) 3))))
;;     :rule-classes :linear
;;     :g-bindings
;;     `((addr  (:g-number ,(gl-int  0 1 33)))
;;       (byte  (:g-number ,(gl-int 33 1 9)))
;;       (value (:g-number ,(gl-int 42 1 33))))))

;;  (local
;;   (def-gl-thm word-to-write-equality-less-than-2^32
;;     :hyp (and (n08p byte)
;;               (n32p val)
;;               (n32p addr))
;;     :concl
;;     (< (logior (logand (lognot (ash 255 (ash (logand addr 3) 3))) val)
;;                (ash byte (ash (logand addr 3) 3)))
;;        4294967296)
;;     :rule-classes :linear
;;     :g-bindings
;;     `((addr (:g-number ,(gl-int  0 1 33)))
;;       (byte (:g-number ,(gl-int 33 1 9)))
;;       (val  (:g-number ,(gl-int 42 1 33))))))

;;  (local
;;   (def-gl-thm another-logand-fact
;;     :hyp (and (n32p word)
;;               (n08p byte)
;;               (n32p addr))
;;     :concl
;;     (<= 0 (logior (logand (+ -1 (- (ash 255 (ash (logand addr 3) 3)))) word)
;;                   (ash byte (ash (logand addr 3) 3))))
;;     :g-bindings
;;     `((addr (:g-number ,(gl-int  0 1 33)))
;;       (byte (:g-number ,(gl-int 33 1 9)))
;;       (word (:g-number ,(gl-int 42 1 33))))))

;;  (defun wm08 (addr byte x86-32)
;;    (declare (xargs :guard (and (n32p addr)
;;                                (n08p byte))
;;                    :stobjs (x86-32)
;;                    :guard-hints
;;                    (("Goal" :in-theory (e/d () (lognot))))))
;;    (declare (type (unsigned-byte 32) addr))
;;    (let* ((byte-num       (n02 addr))
;;           (dword-addr     (ash addr -2))
;;           (dword          (memi dword-addr x86-32))
;;           (mask           #xFF)
;;           (shift-amount   (ash byte-num 3))
;;           (byte-mask      (ash mask shift-amount))
;;           (dword-masked   (logand (lognot byte-mask) dword))
;;           (byte-to-write  (ash byte shift-amount))
;;           (dword-to-write (logior dword-masked byte-to-write)))
;;      (declare (type (unsigned-byte  2) byte-num)
;;               (type (integer 0     24) shift-amount)
;;               (type (unsigned-byte 30) dword-addr)
;;               (type (unsigned-byte 32)
;;                     byte-mask dword dword-masked byte-to-write dword-to-write))
;;      (!memi dword-addr dword-to-write x86-32)))

;;  (defthm x86-32p-wm08
;;    (implies (and (x86-32p x86-32)
;;                  (n32p addr)
;;                  (n08p byte))
;;             (x86-32p (wm08 addr byte x86-32)))))

;; (in-theory (disable wm08))

;; (encapsulate
;;  ()

;;  (local
;;   (def-gl-thm hack1
;;     :hyp (and (n32p addr)
;;               (not (equal (logand addr 3) 3)))
;;     :concl (<= (ash (logand addr 3) 3) 16)
;;     :g-bindings
;;     `((addr (:g-number ,(gl-int  0 1 33))))
;;     :rule-classes :linear))

;;  (local
;;   (def-gl-thm hack2
;;     :hyp (and (n16p word)
;;               (natp shift)
;;               (<= shift 16))
;;     :concl (< (ash word shift) 4294967296)
;;     :g-bindings
;;     `((word  (:g-number ,(gl-int 0 1 17)))
;;       (shift (:g-number ,(gl-int 17 1 6))))
;;     :rule-classes :linear))

;;  (local
;;   (def-gl-thm logior-ash-bytes-<-4294967296
;;     :hyp (and (n08p byte0)
;;               (n08p byte1)
;;               (n08p byte2)
;;               (n08p byte3))
;;     :concl
;;     (< (logior (ash byte3 24) (ash byte2 16) (ash byte1 8) byte0)
;;        4294967296)
;;     :g-bindings
;;     `((byte0 (:g-number ,(gl-int  0 1 9)))
;;       (byte1 (:g-number ,(gl-int  9 1 9)))
;;       (byte2 (:g-number ,(gl-int 18 1 9)))
;;       (byte3 (:g-number ,(gl-int 27 1 9))))))

;;  (defun wm16 (addr word x86-32)
;;    (declare (xargs :guard (and (n32p addr)
;;                                (n16p word))
;;                    :stobjs (x86-32)
;;                    :guard-hints
;;                    (("Goal" :in-theory (e/d () (lognot))))))
;;    (declare (type (unsigned-byte 32) addr))
;;    (let* ((byte-num      (n02 addr))
;;           (dword-addr    (ash addr -2)))
;;      (declare (type (unsigned-byte  2) byte-num)
;;               (type (unsigned-byte 30) dword-addr))
;;      (if (= byte-num 3) ; memory wrap
;;          (b* ((x86-32 (wm08       addr    (n08      word     ) x86-32))
;;               (x86-32 (wm08 (n32+ addr 1) (n08 (ash word  -8)) x86-32)))
;;              x86-32)
;;        (let* ((dword          (memi dword-addr x86-32))
;;               (mask           #xFFFF)
;;               (shift-amount   (ash byte-num 3))
;;               (byte-mask      (ash mask shift-amount))
;;               (dword-masked   (logand (lognot byte-mask) dword))
;;               (word-to-write  (ash word shift-amount))
;;               (dword-to-write (logior dword-masked word-to-write)))
;;          (declare (type (integer 0 16) shift-amount)
;;                   (type (unsigned-byte 32)
;;                         byte-mask dword dword-masked word-to-write
;;                         dword-to-write))
;;          (!memi dword-addr dword-to-write x86-32)))))

;;  (defthm x86-32p-wm16
;;    (implies (and (x86-32p x86-32)
;;                  (n32p addr)
;;                  (n16p word))
;;             (x86-32p (wm16 addr word x86-32)))))

;; (in-theory (disable wm16))

;; ; The next two hack lemmas are needed not only to admit wm32 (below), but also
;; ; to prove x86-32p-wm32 (below).

;; (local
;;  (def-gl-thm hack1
;;    :hyp (and (n32p dword)
;;              (n32p addr))
;;    :concl
;;    (< (ash (logand dword
;;                    (+ -1
;;                       (ash 1 (ash (+ 4 (- (logand addr 3))) 3))))
;;            (ash (logand addr 3) 3))
;;       4294967296)
;;    :g-bindings
;;    `((dword (:g-number ,(gl-int  0 1 33)))
;;      (addr  (:g-number ,(gl-int 34 1 33))))))

;; (local
;;  (def-gl-thm hack2
;;    :hyp (and (n32p dword)
;;              (n32p addr))
;;    :concl
;;    (< (ash dword
;;            (- (ash (+ 4 (- (logand addr 3))) 3)))
;;       4294967296)
;;    :g-bindings
;;    `((dword (:g-number ,(gl-int  0 1 33)))
;;      (addr  (:g-number ,(gl-int 34 1 33))))))

;; (defun wm32 (addr dword x86-32)
;;   (declare (xargs :guard (and (n32p addr)
;;                               (n32p dword))
;;                   :stobjs (x86-32)))
;;   (declare (type (unsigned-byte 32) addr))
;;   (let* ((byte-num   (n02 addr))
;;          (dword-addr (ash addr -2)))
;;     (declare (type (integer 0 3) byte-num)
;;              (type (unsigned-byte 30) dword-addr))
;;     (if (= byte-num 0)
;;         (!memi dword-addr dword x86-32)

;; ; We write two dwords to memory: a lower dword obtained by replacing the upper
;; ; bits of the original lower dword, and similarly, an upper dword obtained by
;; ; replacing the lower bits of the original upper dword.

;; ; Here is a picture in the case that byte-num is 3 (each "x" digit is hex):

;; ;  dword-addr+1  dword-addr  ...... 0
;; ;        |        |
;; ; xxxxxxxx xxxxxxxx  [from old mem]
;; ;   xxxxxx xx        dword
;; ;                <>  shift0 [ 8 in this example]
;; ;                ff  mask0
;; ;            <-  ->  shift1 [24 in this example]
;; ;            ffffff  mask1

;;       (let* ((dword0-old   (memi dword-addr x86-32))
;;              (shift0       (ash (- 4 byte-num) 3))
;;              (mask0        (- (ash 1 shift0) 1))
;;              (shift1       (ash byte-num 3))
;;              (mask1        (- (ash 1 shift1) 1))
;;              (dword0-lo    (logand dword0-old mask1))
;;              (dword0-hi    (ash (logand dword mask0) shift1))
;;              (dword0-new   (logior dword0-lo dword0-hi))
;;              (x86-32       (!memi dword-addr dword0-new x86-32))
;;              (dword-addr+1 (n30+ dword-addr 1))
;;              (dword1-old   (memi dword-addr+1 x86-32))
;;              (dword1-lo    (ash dword (- shift0)))
;;              (dword1-hi    (logand dword1-old (ash mask0 shift1)))
;;              (dword1-new   (logior dword1-lo dword1-hi))
;;              (x86-32       (!memi dword-addr+1 dword1-new x86-32)))
;;         x86-32))))

;; (defthm x86-32p-wm32
;;   (implies (and (x86-32p x86-32)
;;                 (n32p addr)
;;                 (n32p dword))
;;            (x86-32p (wm32 addr dword x86-32))))

;; (in-theory (disable wm32))
