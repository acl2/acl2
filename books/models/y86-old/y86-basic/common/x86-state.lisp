
; x86-state.lisp                               Warren A. Hunt, Jr.

; We model the X86 state with two arrays: one array of 32-bit values
; for the registers and array of 8-bit values for the memory.  There
; are a large number of registers, as this data structure holds all of
; the supervisor data as well.

; Added by Matt K., 9/16/2020:
; In GCL, the use of GCL_MEM_MULTIPLE can cause this to fail with a call of
; make-array on behalf of the defstobj event below: "The storage for
; RELOCATABLE-BLOCKS is exhausted. 23545 pages allocated."  (Specifically, this
; has happened at UT CS when GCL_MEM_MULTIPLE was set to 0.25, where there was
; success on a single-threaded certification without that setting.)  Since
; available memory is an issue when using GCL_MEM_MULTIPLE as recommended, we
; remove this book for GCL in order to avoid surprising certification failures.
; The following line accomplishes that task:
; cert_param: (non-gcl)

(in-package "ACL2")

(include-book "constants")

; Increase memory for X86 memory.
(include-book "centaur/misc/memory-mgmt-logic" :dir :system)
(value-triple (set-max-mem (* 6 (expt 2 30))))

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


(defstobj x86-32

; Notice that the array fields use UNSIGNED-BYTE types rather than
; types (SATISFIES N32P) and (SATISFIES N08P).  The reason is that we
; want to help the host Lisp system allocate these arrays using
; minimal real (physical) memory.

  ;; The model register file has a simple structure; it just an array
  ;; of 32-bit words.
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
  ;; address more than 2^32 bytes, but we aren't modeling that as yet.
  ;; We choose (for performance reasons) to model the 2^32 byte memory
  ;; as 2^30 double-word (4-byte) memory.  We maintain the byte-level
  ;; semantics.
  (mem :type (array (unsigned-byte 32)
                    (*mem-size-in-dwords*))
       :initially 0
       :resizable nil)

  ;; This information is loaded from memory when a segment register is loaded.
  ;; For each segment register, there is a corresponding "seg-base", "seg-limit",
  ;; and "seg-access" register; this memory-resident information is automatically
  ;; used when protection is enabled.
  (seg-base   :type (array (unsigned-byte 32) (*m86-32-segment-reg-names-len*))
              :initially 0 :resizable nil)
  (seg-limit  :type (array (unsigned-byte 20) (*m86-32-segment-reg-names-len*))
              :initially 0 :resizable nil)
  (seg-access :type (array (unsigned-byte 12) (*m86-32-segment-reg-names-len*))
              :initially 0 :resizable nil)

  ;; Here we have some additional state -- normally stored in the
  ;; X86 memory, but we make a local copy for performance reasons.
  ;; The X86 processor does something similar by reading such data
  ;; and then loading it into internal X86 processor registers.

  ;; The state of the ACL2 model.  This flag is not part of the X86
  ;; processor; it is used to signal problems with model state, such
  ;; as the processor is halted.  While this flag is NIL, the processor
  ;; model is OK; otherwise, the flag indicates (part of) the problem.
  (ms :type t :initially nil)
  :inline t
  :renaming
  ((update-rgfi !rgfi)
   (update-eip !eip)
   (update-flg !flg)
   (update-segi !segi)
   (update-stri !stri)
   (update-ssri !ssri)
   (update-ctri !ctri)
   (update-dbgi !dbgi)
   (update-memi !memi)
   (update-seg-basei !seg-basei)
   (update-seg-limiti !seg-limiti)
   (update-seg-accessi !seg-accessi)
   (update-ms !ms)))

; Event to observe all events introduced by DEFSTOBJ.

(defun get-stobj-raw-defs (form state)
  (declare (xargs :mode :program :stobjs (state)))
  (let* ((name (cadr form))
         (args (cddr form))
         (wrld (w state))
         (template (defstobj-template name args wrld)))
    (defstobj-raw-defs name template nil wrld)))

; Lemmas to help with proofs about STOBJs that hold X86 state.  Our
; goal is to prove a nice set of forward-chaining lemmas, as our
; predicates seem nicely set up for that.

(in-theory (disable nth))  ; Because NTH used to select object from
                           ; the x86-32 state.

; Lemmas below are in the same order as the fields declare in the
; X86-32 STOBJ above.

; We first deal with the STOBJ read lemmas

; RGF read lemmas

(defthm natp-nth-of-rgf
  (implies (and (rgfp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (and (integerp (nth i x))
                (<= 0 (nth i x))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm nth-of-rgf-<=4294967296
  (implies (and (rgfp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (< (nth i x) 4294967296))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm natp-rgfi
  (implies (and (force (x86-32p x86-32))
                (force (n03p i)))
           (and (integerp (rgfi i x86-32))
                (<= 0 (rgfi i x86-32))))
  :rule-classes :type-prescription)

(defthm rgfi-less-than-expt-2-32
  (implies (and (x86-32p x86-32)
                (n03p i))
           (< (rgfi i x86-32) 4294967296))
  :rule-classes :linear)


; EIP read lemmas

(defthm natp-eip
  (implies (force (x86-32p x86-32))
           (and (integerp (eip x86-32))
                (<= 0 (eip x86-32))))
  :rule-classes :type-prescription)

(defthm eip-less-than-expt-2-32
  (implies (x86-32p x86-32)
           (< (eip x86-32) 4294967296))
  :rule-classes :linear)


; FLG read lemmas

(defthm natp-flg
  (implies (force (x86-32p x86-32))
           (and (integerp (flg x86-32))
                (<= 0 (flg x86-32))))
  :rule-classes :type-prescription)

(defthm flg-less-than-expt-2-32
  (implies (x86-32p x86-32)
           (< (flg x86-32) 4294967296))
  :rule-classes :linear)


; SEG read lemmas

(defthm natp-nth-of-seg
  (implies (and (segp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (and (integerp (nth i x))
                (<= 0 (nth i x))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm nth-of-seg-<=65536
  (implies (and (segp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (< (nth i x) 65536))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm natp-segi
  (implies (and (force (x86-32p x86-32))
                (force (n01p i)))
           (and (integerp (segi i x86-32))
                (<= 0 (segi i x86-32))))
  :rule-classes :type-prescription)

(defthm segi-less-than-expt-2-16
  (implies (and (x86-32p x86-32)
                (n01p i))
           (< (segi i x86-32) 65536))
  :rule-classes :linear)


; STR read lemmas

(defthm natp-nth-of-str
  (implies (and (strp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (and (integerp (nth i x))
                (<= 0 (nth i x))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm nth-of-str-<=281474976710656
  (implies (and (strp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (< (nth i x) 281474976710656))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm natp-stri
  (implies (and (force (x86-32p x86-32))
                (force (n01p i)))
           (and (integerp (stri i x86-32))
                (<= 0 (stri i x86-32))))
  :rule-classes :type-prescription)

(defthm stri-less-than-expt-2-48
  (implies (and (x86-32p x86-32)
                (n01p i))
           (< (stri i x86-32) 281474976710656))
  :rule-classes :linear)


; SSR read lemmas

(defthm natp-nth-of-ssr
  (implies (and (ssrp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (and (integerp (nth i x))
                (<= 0 (nth i x))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm nth-of-ssr-<=65536
  (implies (and (ssrp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (< (nth i x) 65536))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm natp-ssri
  (implies (and (force (x86-32p x86-32))
                (force (n01p i)))
           (and (integerp (ssri i x86-32))
                (<= 0 (ssri i x86-32))))
  :rule-classes :type-prescription)

(defthm ssri-less-than-expt-2-16
  (implies (and (x86-32p x86-32)
                (n01p i))
           (< (ssri i x86-32) 65536))
  :rule-classes :linear)


; CTR read lemmas

(defthm natp-nth-of-ctr
  (implies (and (ctrp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (and (integerp (nth i x))
                (<= 0 (nth i x))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm nth-of-ctr-<=4294967296
  (implies (and (ctrp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (< (nth i x) 4294967296))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm natp-ctri
  (implies (and (force (x86-32p x86-32))
                (force (natp i))
                (force (< i 6)))
           (and (integerp (ctri i x86-32))
                (<= 0 (ctri i x86-32))))
  :rule-classes :type-prescription)

(defthm ctri-less-than-expt-2-32
  (implies (and (x86-32p x86-32)
                (natp i)
                (< i 6))
           (< (ctri i x86-32) 4294967296))
  :rule-classes :linear)


; MEM read lemmas

(defthm natp-nth-of-mem
  (implies (and (memp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (and (integerp (nth i x))
                (<= 0 (nth i x))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (nth)))))

(defthm nth-of-mem-<=-4294967296
  (implies (and (memp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (< (nth i x) 4294967296))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm natp-memi-when-n30p-addr
  (implies (and (force (x86-32p x86-32))
                (force (n30p addr)))
           (and (integerp (memi addr x86-32))
                (<= 0 (memi addr x86-32))))
  :rule-classes (:rewrite :type-prescription))

(defthm memi-less-than-expt-2-32
  (implies (and (x86-32p x86-32)
                (force (n30p addr)))
           (< (memi addr x86-32) 4294967296))
  :rule-classes :linear)

(encapsulate
 ()

 (local
  (def-gl-thm n32p-ash--2-is-n30p-lemma
    :hyp (n32p x)
    :concl (n30p (ash x -2))
    :g-bindings
    `((x (:g-number ,(gl-int  0  1  33))))))

 (defthm n32p-ash--2-is-n30p
   (implies (n32p x)
            (n30p (ash x -2)))
   :hints (("Goal" :by n32p-ash--2-is-n30p-lemma))
   :rule-classes ((:type-prescription
                   :corollary (implies (n32p x)
                                       (natp (ash x -2))))
                  (:linear
                   :corollary (implies (n32p x)
                                       (< (ash x -2) 1073741824))))))

; SEG-BASE read lemmas

(defthm natp-nth-of-seg-base
  (implies (and (seg-basep x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (and (integerp (nth i x))
                (<= 0 (nth i x))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm nth-of-seg-base-<=4294967296
  (implies (and (seg-basep x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (< (nth i x) 4294967296))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm natp-seg-basei
  (implies (and (force (x86-32p x86-32))
                (force (natp i))
                (force (< i 6)))
           (and (integerp (seg-basei i x86-32))
                (<= 0 (seg-basei i x86-32))))
  :rule-classes :type-prescription)

(defthm seg-basei-less-than-expt-2-32
  (implies (and (x86-32p x86-32)
                (natp i)
                (< i 6))
           (< (seg-basei i x86-32) 4294967296))
  :rule-classes :linear)


; SEG-LIMIT read lemmas

(defthm natp-nth-of-seg-limit
  (implies (and (seg-limitp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (and (integerp (nth i x))
                (<= 0 (nth i x))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm nth-of-seg-limit-<=1048576
  (implies (and (seg-limitp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (< (nth i x) 1048576))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm natp-seg-limiti
  (implies (and (force (x86-32p x86-32))
                (force (natp i))
                (force (< i 6)))
           (and (integerp (seg-limiti i x86-32))
                (<= 0 (seg-limiti i x86-32))))
  :rule-classes :type-prescription)

(defthm seg-limiti-less-than-expt-2-32
  (implies (and (x86-32p x86-32)
                (natp i)
                (< i 6))
           (< (seg-limiti i x86-32) 1048576))
  :rule-classes :linear)


; SEG-ACCESS read lemmas

(defthm natp-nth-of-seg-access
  (implies (and (seg-accessp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (and (integerp (nth i x))
                (<= 0 (nth i x))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm nth-of-seg-access-<=4096
  (implies (and (seg-accessp x)
                (integerp i)
                (<= 0 i)
                (< i (len x)))
           (< (nth i x) 4096))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (nth) ()))))

(defthm natp-seg-accessi
  (implies (and (force (x86-32p x86-32))
                (force (natp i))
                (force (< i 6)))
           (and (integerp (seg-accessi i x86-32))
                (<= 0 (seg-accessi i x86-32))))
  :rule-classes :type-prescription)

(defthm seg-accessi-less-than-expt-2-32
  (implies (and (x86-32p x86-32)
                (natp i)
                (< i 6))
           (< (seg-accessi i x86-32) 4096))
  :rule-classes :linear)



; We wonder if the two lemmas about !xxx would be better as
; :FORWARD-CHAINING rules (or, as both :REWRITE and :FORWARD-CHAINING
; rules), using *MEM-SIZE-IN-BYTES* and *REG-SIZE-IN-DWRDS* in the
; hypotheses instead of LEN.

(defthm length-is-len-when-not-stringp
  (implies (not (stringp x))
           (equal (length x)
                  (len x)))
  :hints (("Goal" :in-theory (e/d (length) ()))))


; RGF update lemmas

(defthm rgfp-update-nth
  (implies (and (rgfp x)
                (integerp i)
                (<= 0 i)
                (< i (len x))
                (n32p v))
           (rgfp (update-nth i v x))))

(defthm x86-32p-!rgfi-n03p
  (implies (and (x86-32p x86-32)
                (n03p i)
                (n32p v))
           (x86-32p (!rgfi i v x86-32))))


; EIP update lemma

(defthm x86-32p-!eip
  (implies (and (x86-32p x86-32)
                (n32p v))
           (x86-32p (!eip v x86-32))))


; EFLAGS update lemma

(defthm x86-32p-!flg
  (implies (and (x86-32p x86-32)
                (n32p v))
           (x86-32p (!flg v x86-32))))


; SEG update lemmas

(defthm segp-update-nth
  (implies (and (segp x)
                (integerp i)
                (<= 0 i)
                (< i (len x))
                (n16p v))
           (segp (update-nth i v x))))

(defthm x86-32p-!segi
  (implies (and (x86-32p x86-32)
                (integerp i)
                (n01p i)
                (n16p v))
           (x86-32p (!segi i v x86-32))))


; STR update lemmas

(defthm strp-update-nth
  (implies (and (strp x)
                (integerp i)
                (<= 0 i)
                (< i (len x))
                (n48p v))
           (strp (update-nth i v x))))

(defthm x86-32p-!stri
  (implies (and (x86-32p x86-32)
                (integerp i)
                (n01p i)
                (n48p v))
           (x86-32p (!stri i v x86-32))))


; SSR update lemmas

(defthm ssrp-update-nth
  (implies (and (ssrp x)
                (integerp i)
                (<= 0 i)
                (< i (len x))
                (n16p v))
           (ssrp (update-nth i v x))))

(defthm x86-32p-!ssri
  (implies (and (x86-32p x86-32)
                (n01p i)
                (n16p v))
           (x86-32p (!ssri i v x86-32))))


; CTR update lemmas

(defthm ctrp-update-nth
  (implies (and (ctrp x)
                (integerp i)
                (<= 0 i)
                (< i (len x))
                (n32p v))
           (ctrp (update-nth i v x))))

(defthm x86-32p-!ctri
  (implies (and (x86-32p x86-32)
                (integerp i)
                (<= 0 i)
                (< i 6)
                (n32p v))
           (x86-32p (!ctri i v x86-32))))


; Memory update lemmas

(defthm memp-update-nth
  (implies (and (memp x)
                (integerp i)
                (<= 0 i)
                (< i (len x))
                (n32p v))
           (memp (update-nth i v x))))

(defthm x86-32p-!memi-n30p
  (implies (and (force (x86-32p x86-32))
                (force (n30p i))
                (force (n32p v)))
           (x86-32p (!memi i v x86-32))))

; SEG-BASE register update lemmas

(defthm seg-basep-update-nth
  (implies (and (seg-basep x)
                (integerp i)
                (<= 0 i)
                (< i (len x))
                (n32p v))
           (seg-basep (update-nth i v x))))




; SEG-LIMIT register update lemmas

(defthm seg-limitp-update-nth
  (implies (and (seg-limitp x)
                (integerp i)
                (<= 0 i)
                (< i (len x))
                (n20p v))
           (seg-limitp (update-nth i v x))))

(defthm x86-32p-!seg-limiti
  (implies (and (x86-32p x86-32)
                (integerp i)
                (<= 0 i)
                (< i 6)
                (n20p v))
           (x86-32p (!seg-limiti i v x86-32))))


; SEG-ACCESS register update lemmas

(defthm seg-accessp-update-nth
  (implies (and (seg-accessp x)
                (integerp i)
                (<= 0 i)
                (< i (len x))
                (n12p v))
           (seg-accessp (update-nth i v x))))

(defthm x86-32p-!seg-accessi
  (implies (and (x86-32p x86-32)
                (integerp i)
                (<= 0 i)
                (< i 6)
                (n12p v))
           (x86-32p (!seg-accessi i v x86-32))))


; Should we have this next group of lemmas?  Probably not, but the
; first, for instance, one allows later lemma X86-32P-WMB-NO-WRAP (see
; below) to be proven.

(defthm len-x86-32-rgf
  (implies (x86-32p x86-32)
           (equal (len (nth *rgfi* x86-32))
                  *m86-32-reg-names-len*)))

(defthm len-x86-32-seg
  (implies (x86-32p x86-32)
           (equal (len (nth *segi* x86-32))
                  *m86-32-segment-reg-names-len*)))

(defthm len-x86-32-str
  (implies (x86-32p x86-32)
           (equal (len (nth *stri* x86-32))
                  *m86-32-gdtr-idtr-names-len*)))

(defthm len-x86-32-ssr
  (implies (x86-32p x86-32)
           (equal (len (nth *ssri* x86-32))
                  *m86-32-ldtr-tr-names-len*)))

(defthm len-x86-32-ctr
  (implies (x86-32p x86-32)
           (equal (len (nth *ctri* x86-32))
                  *m86-32-control-reg-names-len*)))

(defthm len-x86-32-dbg
  (implies (x86-32p x86-32)
           (equal (len (nth *dbgi* x86-32))
                  *m86-32-debug-reg-names-len*)))

(defthm len-x86-32-mem
  (implies (x86-32p x86-32)
           (equal (len (nth *memi* x86-32))
                  *mem-size-in-dwords*)))

(defthm len-x86-32-seg-base
  (implies (x86-32p x86-32)
           (equal (len (nth *seg-basei* x86-32))
                  *m86-32-segment-reg-names-len*)))

(defthm len-x86-32-seg-limit
  (implies (x86-32p x86-32)
           (equal (len (nth *seg-limiti* x86-32))
                  *m86-32-segment-reg-names-len*)))

(defthm len-x86-32-seg-access
  (implies (x86-32p x86-32)
           (equal (len (nth *seg-accessi* x86-32))
                  *m86-32-segment-reg-names-len*)))


(defthm x86-32p-properties
  (implies (x86-32p x86-32)
           (and (true-listp x86-32)
                (equal (len x86-32) 13)

                (rgfp (nth 0 x86-32))
                (equal (len (nth 0 x86-32))
                       *m86-32-reg-names-len*)

                (eipp (nth 1 x86-32))
                (flgp (nth 2 x86-32))

                (segp (nth 3 x86-32))
                (equal (len (nth 3 x86-32))
                       *m86-32-segment-reg-names-len*)

                (strp (nth 4 x86-32))
                (equal (len (nth 4 x86-32))
                       *m86-32-gdtr-idtr-names-len*)

                (ssrp (nth 5 x86-32))
                (equal (len (nth 5 x86-32))
                       *m86-32-ldtr-tr-names-len*)

                (ctrp (nth 6 x86-32))
                (equal (len (nth 6 x86-32))
                       *m86-32-control-reg-names-len*)

                (dbgp (nth 7 x86-32))
                (equal (len (nth 7 x86-32))
                       *m86-32-debug-reg-names-len*)

                (memp (nth 8 x86-32))
                (equal (len (nth 8 x86-32))
                       *mem-size-in-dwords*)

                (seg-basep (nth 9 x86-32))
                (equal (len (nth 9 x86-32))
                       *m86-32-segment-reg-names-len*)

                (seg-limitp (nth 10 x86-32))
                (equal (len (nth 11 x86-32))
                       *m86-32-segment-reg-names-len*)

                (seg-accessp (nth 11 x86-32))
                (equal (len (nth 11 x86-32))
                       *m86-32-segment-reg-names-len*)
                ))
  :hints (("Goal" :in-theory (enable x86-32p
                                     rgfp eipp flgp segp strp ssrp ctrp dbgp memp
                                     seg-basep seg-limitp seg-accessp)))
  :rule-classes :forward-chaining)

; Additional lemmas to help with later guard proofs.

; Hopefully, we have proven all the facts we need about the X86
; machine state.

(in-theory (disable x86-32p
                    rgfp        rgfi        !rgfi
                    eipp        eip         !eip
                    flgp        flg         !flg
                    strp        stri        !stri
                    ssrp        ssri        !ssri
                    ctrp        ctri        !ctri
                    dbgp        dbgi        !dbgi
                    memp        memi        !memi
                    seg-basep   seg-basei   !seg-basei
                    seg-limitp  seg-limiti  !seg-limiti
                    seg-accessp seg-accessi !seg-accessi
                    ))


; Read memory byte and memory double-word functions

(encapsulate
 ()

 (local
  (def-gl-thm ash-logand-addr-3-is-integerp-less-or-equal-24
    :hyp (n32p addr)
    :concl (<= (ash (logand addr 3) 3) 24)
    :g-bindings
     `((addr (:g-number ,(gl-int  0 1 33))))))

 (local
  (def-gl-thm ash-memi-ash-logand-addr
    :hyp (and (n32p mem-value)
              (n32p addr))
    :concl (< (ash mem-value (- (ash (logand addr 3) 3)))
              4294967296)
    :rule-classes :linear
    :g-bindings
    `((addr      (:g-number ,(gl-int  0 1 33)))
      (mem-value (:g-number ,(gl-int 33 1 33))))))

 (defun rm08 (addr x86-32)
   (declare (xargs :guard (n32p addr)
                   :stobjs (x86-32)))
   (declare (type (unsigned-byte 32) addr))
   (let* ((byte-num     (n02 addr))
          (dword-addr   (ash addr -2))
          (dword        (memi dword-addr x86-32))
          (shift-amount (ash byte-num 3))
          ;; Next form causes (callq (@ .SPBUILTIN-ASH)).
          (shifted-word (ash dword (- shift-amount))))
     (declare (type (unsigned-byte  2) byte-num)
              (type (unsigned-byte 30) dword-addr)
              (type (unsigned-byte 32) dword shifted-word)
              (type (integer 0     24) shift-amount))
     (n08 shifted-word)))

 (defun rm16 (addr x86-32)
   (declare (xargs :guard (n32p addr)
                   :stobjs (x86-32)))
   (declare (type (unsigned-byte 32) addr))
   (let* ((byte-num   (n02 addr))
          (dword-addr (ash addr -2))
          (dword      (memi dword-addr x86-32)))
     (declare (type (unsigned-byte  2) byte-num)
              (type (unsigned-byte 30) dword-addr)
              (type (unsigned-byte 32) dword))
     (if (= byte-num 3)
       ;; Memory "wrap"
         (let* ((byte0 (rm08       addr    x86-32))
                (byte1 (rm08 (n32+ addr 1) x86-32)))
           (declare (type (unsigned-byte 8) byte0 byte1))
           (logior (ash byte1 8) byte0))
       (logand (ash dword (- (ash byte-num 3)))
               #xffff))))

 (local (defthm integerp-+
          (implies (and (integerp x)
                        (integerp y))
                   (integerp (+ x y)))))

 (local (defthm integerp-expt
          (implies (natp x)
                   (integerp (expt 2 x)))))

 (defun rm32 (addr x86-32)
   (declare (xargs :guard (n32p addr)
                   :stobjs (x86-32)))
   (declare (type (unsigned-byte 32) addr))
   (let* ((byte-num   (n02 addr))
          (dword-addr (ash addr -2))
          (dword      (memi dword-addr x86-32)))
     (declare (type (unsigned-byte  2) byte-num)
              (type (unsigned-byte 30) dword-addr)
              (type (unsigned-byte 32) dword))
     (if (= byte-num 0)
         dword

; Here is a picture in the case that byte-num is 3 (each "x" digit is hex):

;     dword-addr+1  dword-addr  ...... 0
;           |        |
; [next-dword] [dword]
;    xxxxxxxx xxxxxxxx  [from old mem]
;                   <>  shift0 [ 8 in this example]
;               <-  ->  shift1 [24 in this example]
;             xx        lo
;      xxxxxx           hi

       (let* ((shift0 (ash (- 4 byte-num) 3))
              (shift1 (ash byte-num 3))
              (lo (ash dword (- shift1)))
              (dword-addr+1 (n30+ dword-addr 1))
              (next-dword (memi dword-addr+1 x86-32))
              (hi (logand next-dword (- (ash 1 shift1)
                                        1))))
         (declare (type (unsigned-byte 32) lo hi))
         (logior lo (ash hi shift0)))))))

(defthm natp-rm08
  (implies (and (force (x86-32p x86-32))
                (force (n32p addr)))
           (and (integerp (rm08 addr x86-32))
                (<= 0 (rm08 addr x86-32))))
  :rule-classes :type-prescription)

(defthm rm08-less-than-expt-2-32
  (implies (and (x86-32p x86-32)
                (n32p addr))
           (< (rm08 addr x86-32) 256))
  :rule-classes :linear)

(in-theory (disable rm08))

(encapsulate
 ()
 (local
  (def-gl-thm logior-ash-bytes-<=-0
    :hyp (and (n08p byte0)
              (n08p byte1))
    :concl
    (<= 0 (logior (ash byte1 8) byte0))
    :g-bindings
    `((byte0 (:g-number ,(gl-int  0 1 9)))
      (byte1 (:g-number ,(gl-int  9 1 9))))))

 (local
  (def-gl-thm logior-ash-bytes-<-4294967296
    :hyp (and (n08p byte0)
              (n08p byte1))
    :concl
    (< (logior (ash byte1 8) byte0)
       65536)
    :g-bindings
    `((byte0 (:g-number ,(gl-int  0 1 9)))
      (byte1 (:g-number ,(gl-int  9 1 9))))))

 (defthm integerp-rm16
   (implies (and (force (x86-32p x86-32))
                 (force (n32p addr)))
            (and (integerp (rm16 addr x86-32))
                 (<= 0 (rm16 addr x86-32))))
   :rule-classes :type-prescription)

 (defthm rm16-less-than-expt-2-16
   (implies (and (x86-32p x86-32)
                 (n32p addr))
            (< (rm16 addr x86-32) 65536))
   :rule-classes :linear))

(in-theory (disable rm16))

(defthm integerp-rm32
  (implies (and (force (x86-32p x86-32))
                (force (n32p addr)))
           (and (integerp (rm32 addr x86-32))
                (<= 0 (rm32 addr x86-32))))
  :rule-classes :type-prescription)

(encapsulate
 ()

 (local
  (def-gl-thm hack
    :hyp (and (n32p dword1)
              (n32p dword2)
              (integerp addr)
              (<= 0 addr)
              (< addr 4294967296)
              (not (equal (logand addr 3) 0)))
    :concl (< (logior (ash dword1
                           (- (ash (logand addr 3) 3)))
                      (ash (logand dword2
                                   (+ -1 (ash 1 (ash (logand addr 3) 3))))
                           (ash (+ 4 (- (logand addr 3))) 3)))
              4294967296)
    :g-bindings
    `((addr (:g-number ,(gl-int 0 1 33)))
      (dword1 (:g-number ,(gl-int 33 1 33)))
      (dword2 (:g-number ,(gl-int 66 1 33))))))

 (defthm rm32-less-than-expt-2-32
   (implies (and (x86-32p x86-32)
                 (n32p addr))
            (< (rm32 addr x86-32) 4294967296))
   :rule-classes :linear))

(in-theory (disable rm32))

; Write memory byte, memory double-word functions

(encapsulate
 ()

 (local
  (def-gl-thm ash-logand-addr-3-is-integerp-less-than-or-equal-24
    :hyp (n32p addr)
    :concl (<= (ash (logand addr 3) 3) 24)
    :g-bindings
    `((addr (:g-number ,(gl-int  0 1 33))))))

 (local
  (def-gl-thm ash-n08p-ash-logand-addr-3-3
    :hyp (and (n32p addr)
              (n08p byte))
    :concl (< (ash byte (ash (logand addr 3) 3))
               4294967296)
    :g-bindings
    `((addr (:g-number ,(gl-int  0 1 33)))
      (byte (:g-number ,(gl-int 33 1 9))))))

 (local
  (def-gl-thm word-to-write-equality
    :hyp (and (n08p byte)
              (n32p val)
              (n32p addr))
    :concl
    (equal (logand (logior (logand (lognot (ash 255 (ash (logand addr 3) 3))) val)
                           (ash byte (ash (logand addr 3) 3)))
                   4294967295)
           (logior (logand (lognot (ash 255 (ash (logand addr 3) 3)))
                           val)
                   (ash byte (ash (logand addr 3) 3))))
    :g-bindings
    `((addr (:g-number ,(gl-int  0 1 33)))
      (byte (:g-number ,(gl-int 33 1 9)))
      (val  (:g-number ,(gl-int 42 1 33))))))

 (local
  (def-gl-thm natp-word-to-write
    :hyp (and (n08p byte)
              (n32p value)
              (n32p addr))
    :concl
    (<= 0 (logior (logand (lognot (ash 255 (ash (logand addr 3) 3))) value)
                  (ash byte (ash (logand addr 3) 3))))
    :rule-classes :linear
    :g-bindings
    `((addr  (:g-number ,(gl-int  0 1 33)))
      (byte  (:g-number ,(gl-int 33 1 9)))
      (value (:g-number ,(gl-int 42 1 33))))))

 (local
  (def-gl-thm word-to-write-equality-less-than-2^32
    :hyp (and (n08p byte)
              (n32p val)
              (n32p addr))
    :concl
    (< (logior (logand (lognot (ash 255 (ash (logand addr 3) 3))) val)
               (ash byte (ash (logand addr 3) 3)))
       4294967296)
    :rule-classes :linear
    :g-bindings
    `((addr (:g-number ,(gl-int  0 1 33)))
      (byte (:g-number ,(gl-int 33 1 9)))
      (val  (:g-number ,(gl-int 42 1 33))))))

 (local
  (def-gl-thm another-logand-fact
    :hyp (and (n32p word)
              (n08p byte)
              (n32p addr))
    :concl
    (<= 0 (logior (logand (+ -1 (- (ash 255 (ash (logand addr 3) 3)))) word)
                  (ash byte (ash (logand addr 3) 3))))
    :g-bindings
    `((addr (:g-number ,(gl-int  0 1 33)))
      (byte (:g-number ,(gl-int 33 1 9)))
      (word (:g-number ,(gl-int 42 1 33))))))

 (defun wm08 (addr byte x86-32)
   (declare (xargs :guard (and (n32p addr)
                               (n08p byte))
                   :stobjs (x86-32)
                   :guard-hints
                   (("Goal" :in-theory (e/d () (lognot))))))
   (declare (type (unsigned-byte 32) addr))
   (let* ((byte-num       (n02 addr))
          (dword-addr     (ash addr -2))
          (dword          (memi dword-addr x86-32))
          (mask           #xFF)
          (shift-amount   (ash byte-num 3))
          (byte-mask      (ash mask shift-amount))
          (dword-masked   (logand (lognot byte-mask) dword))
          (byte-to-write  (ash byte shift-amount))
          (dword-to-write (logior dword-masked byte-to-write)))
     (declare (type (unsigned-byte  2) byte-num)
              (type (integer 0     24) shift-amount)
              (type (unsigned-byte 30) dword-addr)
              (type (unsigned-byte 32)
                    byte-mask dword dword-masked byte-to-write dword-to-write))
     (!memi dword-addr dword-to-write x86-32)))

 (defthm x86-32p-wm08
   (implies (and (x86-32p x86-32)
                 (n32p addr)
                 (n08p byte))
            (x86-32p (wm08 addr byte x86-32)))))

(in-theory (disable wm08))

(encapsulate
 ()

 (local
  (def-gl-thm hack1
    :hyp (and (n32p addr)
              (not (equal (logand addr 3) 3)))
    :concl (<= (ash (logand addr 3) 3) 16)
    :g-bindings
    `((addr (:g-number ,(gl-int  0 1 33))))
    :rule-classes :linear))

 (local
  (def-gl-thm hack2
    :hyp (and (n16p word)
              (natp shift)
              (<= shift 16))
    :concl (< (ash word shift) 4294967296)
    :g-bindings
    `((word  (:g-number ,(gl-int 0 1 17)))
      (shift (:g-number ,(gl-int 17 1 6))))
    :rule-classes :linear))

 (local
  (def-gl-thm logior-ash-bytes-<-4294967296
    :hyp (and (n08p byte0)
              (n08p byte1)
              (n08p byte2)
              (n08p byte3))
    :concl
    (< (logior (ash byte3 24) (ash byte2 16) (ash byte1 8) byte0)
       4294967296)
    :g-bindings
    `((byte0 (:g-number ,(gl-int  0 1 9)))
      (byte1 (:g-number ,(gl-int  9 1 9)))
      (byte2 (:g-number ,(gl-int 18 1 9)))
      (byte3 (:g-number ,(gl-int 27 1 9))))))

 (defun wm16 (addr word x86-32)
   (declare (xargs :guard (and (n32p addr)
                               (n16p word))
                   :stobjs (x86-32)
                   :guard-hints
                   (("Goal" :in-theory (e/d () (lognot))))))
   (declare (type (unsigned-byte 32) addr))
   (let* ((byte-num      (n02 addr))
          (dword-addr    (ash addr -2)))
     (declare (type (unsigned-byte  2) byte-num)
              (type (unsigned-byte 30) dword-addr))
     (if (= byte-num 3) ; memory wrap
         (b* ((x86-32 (wm08       addr    (n08      word     ) x86-32))
              (x86-32 (wm08 (n32+ addr 1) (n08 (ash word  -8)) x86-32)))
             x86-32)
       (let* ((dword          (memi dword-addr x86-32))
              (mask           #xFFFF)
              (shift-amount   (ash byte-num 3))
              (byte-mask      (ash mask shift-amount))
              (dword-masked   (logand (lognot byte-mask) dword))
              (word-to-write  (ash word shift-amount))
              (dword-to-write (logior dword-masked word-to-write)))
         (declare (type (integer 0 16) shift-amount)
                  (type (unsigned-byte 32)
                        byte-mask dword dword-masked word-to-write
                        dword-to-write))
         (!memi dword-addr dword-to-write x86-32)))))

 (defthm x86-32p-wm16
   (implies (and (x86-32p x86-32)
                 (n32p addr)
                 (n16p word))
            (x86-32p (wm16 addr word x86-32)))))

(in-theory (disable wm16))

; The next two hack lemmas are needed not only to admit wm32 (below), but also
; to prove x86-32p-wm32 (below).

(local
 (def-gl-thm hack1
   :hyp (and (n32p dword)
             (n32p addr))
   :concl
   (< (ash (logand dword
                   (+ -1
                      (ash 1 (ash (+ 4 (- (logand addr 3))) 3))))
           (ash (logand addr 3) 3))
      4294967296)
   :g-bindings
   `((dword (:g-number ,(gl-int  0 1 33)))
     (addr  (:g-number ,(gl-int 34 1 33))))))

(local
 (def-gl-thm hack2
   :hyp (and (n32p dword)
             (n32p addr))
   :concl
   (< (ash dword
           (- (ash (+ 4 (- (logand addr 3))) 3)))
      4294967296)
   :g-bindings
   `((dword (:g-number ,(gl-int  0 1 33)))
     (addr  (:g-number ,(gl-int 34 1 33))))))

(defun wm32 (addr dword x86-32)
  (declare (xargs :guard (and (n32p addr)
                              (n32p dword))
                  :stobjs (x86-32)))
  (declare (type (unsigned-byte 32) addr))
  (let* ((byte-num   (n02 addr))
         (dword-addr (ash addr -2)))
    (declare (type (integer 0 3) byte-num)
             (type (unsigned-byte 30) dword-addr))
    (if (= byte-num 0)
        (!memi dword-addr dword x86-32)

; We write two dwords to memory: a lower dword obtained by replacing the upper
; bits of the original lower dword, and similarly, an upper dword obtained by
; replacing the lower bits of the original upper dword.

; Here is a picture in the case that byte-num is 3 (each "x" digit is hex):

;  dword-addr+1  dword-addr  ...... 0
;        |        |
; xxxxxxxx xxxxxxxx  [from old mem]
;   xxxxxx xx        dword
;                <>  shift0 [ 8 in this example]
;                ff  mask0
;            <-  ->  shift1 [24 in this example]
;            ffffff  mask1

      (let* ((dword0-old   (memi dword-addr x86-32))
             (shift0       (ash (- 4 byte-num) 3))
             (mask0        (- (ash 1 shift0) 1))
             (shift1       (ash byte-num 3))
             (mask1        (- (ash 1 shift1) 1))
             (dword0-lo    (logand dword0-old mask1))
             (dword0-hi    (ash (logand dword mask0) shift1))
             (dword0-new   (logior dword0-lo dword0-hi))
             (x86-32       (!memi dword-addr dword0-new x86-32))
             (dword-addr+1 (n30+ dword-addr 1))
             (dword1-old   (memi dword-addr+1 x86-32))
             (dword1-lo    (ash dword (- shift0)))
             (dword1-hi    (logand dword1-old (ash mask0 shift1)))
             (dword1-new   (logior dword1-lo dword1-hi))
             (x86-32       (!memi dword-addr+1 dword1-new x86-32)))
        x86-32))))

(defthm x86-32p-wm32
  (implies (and (x86-32p x86-32)
                (n32p addr)
                (n32p dword))
           (x86-32p (wm32 addr dword x86-32))))

(in-theory (disable wm32))
