;; AUTHORS:
;; Shilpi Goel <shigoel@cs.utexas.edu>
;; Matt Kaufmann <kaufmann@cs.utexas.edu>
;; Warren A. Hunt, Jr. <hunt@cs.utexas.edu>
;; Robert Krug <rkrug@cs.utexas.edu>

(in-package "X86ISA")

(include-book "constants" :dir :utils)
(include-book "centaur/fty/top" :dir :system)

; cert_param: (non-lispworks)
; cert_param: (hons-only)

;; Matt Kaufmann discovered that LispWorks complained about making an
;; array whose length is more than twice the legal limit.  Here's the
;; exact error (from an email Matt sent to Shilpi):

;;   HARD ACL2 ERROR in ACL2::MAKE-ARRAY$:  The dimensions of an array must
;;   obey restrictions of the underlying Common Lisp:  each must be a non-
;;   negative integer less than the value of array-dimension-limit (here,
;;   536870911) and their product must be less than the value of array-
;;   total-size-limit (here, 536870911).  The call
;;   '(ACL2::MAKE-ARRAY$ 1342177280
;;                       :ELEMENT-TYPE '(UNSIGNED-BYTE 8)
;;                       :INITIAL-ELEMENT '0),
;;   which has dimensions 1342177280, is thus illegal.

;; Since other Lisps do not complain about the large array length, we
;; choose not to support LispWorks at this point.

;; ======================================================================

(defsection machine
  :parents (x86isa)
  :short "Core elements of the x86 ISA, like the @('x86') state,
   decoder function, etc., and proofs about the x86 ISA
   specification.")

(defsection concrete-state
  :parents (machine)
  :short "Concrete stobj @(see defstobj) defining the state of an
  @('x86') processor")

;; ======================================================================
;; Environment Field Recognizer
;; ======================================================================

(defsection environment-field

  :parents (concrete-state)

  :short "An environment field that includes a simple model of the
  file system and an oracle"

  :long "<p>The environment allows reasoning about non-deterministic
  events and computations in the ISA, like the @('RDRAND') instruction
  and in the user-level mode, the @('SYSCALL') instruction.</p>"

  (define rip-ret-alistp (lst)
    :short "Recognizer for the @('oracle') sub-field of the environment
    field @('env')"
    :long "<p>A valid @('rip-ret-alistp') associates canonical linear
    addresses, i.e., 48-bit integers in our specification, to a list
    of arbitrary values.  For example, <tt>'((1 . ((-1 . 12) 5000)) (2
    . (0)))</tt> means that if the oracle in the environment field is
    consulted at address <tt>1</tt>, <tt>'(-1 . 12)</tt> will be
    popped out.  If the oracle is consulted again at the address
    <tt>1</tt>, then <tt>5000</tt> will be popped out.</p>"
    :parents (environment-field)
    (if (atom lst)
        (equal lst nil)
      (and (consp (car lst))
           (i48p (caar lst))
           (true-listp (cdar lst))
           (rip-ret-alistp (cdr lst))))
    ///

    (defthm rip-ret-alistp-fwd-chaining-alistp
      (implies (rip-ret-alistp x)
               (alistp x))
      :rule-classes :forward-chaining))

  (define env-alistp (env)
    :short "Recognizer of the environment field @('env')"
    :long "<p>As of now, @('env-alistp') consists of three sub-fields,
    all of which are basically alists --- file descriptors, file
    contents, and an oracle field.</p>"
    :parents (environment-field)
    (or (equal env nil)
        (and (alistp env)
             (equal (len env) 3)
             (consp (assoc :FILE-DESCRIPTORS env))
             (alistp (cdr (assoc :FILE-DESCRIPTORS env)))
             (consp (assoc :FILE-CONTENTS env))
             (alistp (cdr (assoc :FILE-CONTENTS env)))
             (consp (assoc :ORACLE env))
             (rip-ret-alistp (cdr (assoc :ORACLE env)))))

    ///

    (defthm env-alistp-fwd-chaining-alistp
      (implies (env-alistp x)
               (alistp x))
      :rule-classes :forward-chaining)

    (defthml nth-and-assoc-equal-check
      (implies (and (alistp x)
                    (not (equal (car (nth 0 x)) :oracle))
                    (equal (car (nth 1 x)) :oracle))
               (equal (nth 1 x)
                      (assoc-equal :oracle x))))

    (defthm env-alistp-fwd-chaining-rip-ret-alistp
      (implies (env-alistp x)
               (rip-ret-alistp (cdr (assoc-equal :oracle x))))
      :rule-classes :forward-chaining)

    (defthm env-alistp-fwd-chaining-alistp-file-descriptors
      (implies (env-alistp x)
               (alistp (cdr (assoc-equal :file-descriptors x))))
      :rule-classes :forward-chaining)

    (defthm env-alistp-fwd-chaining-alistp-file-contents
      (implies (env-alistp x)
               (alistp (cdr (assoc-equal :file-contents x))))
      :rule-classes :forward-chaining)))

;; ======================================================================
;; Admitting the concrete x86 stobj (x86$c)
;; ======================================================================

(defsection x86-concrete-stobj

  :parents (concrete-state)

  :short "The concrete stobj representing the ('x86') state"

  :long "<p>The constant @('*x86$c-model*') will be used to construct
    the stobj, and so follows a very similar format to the stobj
    format.  We do it this way so that we can also crawl over the
    constant to help define useful lemmata and such automatically.</p>

    @(def *x86$c-model*)"

  (defconst *x86$c-model*


    `(
      ;; The general-purpose registers are just an array of signed
      ;; 64-bit integers.  Note that we choose to define the GPRs as
      ;; signed integers for the sake of efficiency.  E.g., -1 in
      ;; unsigned format would occupy 64 bits, a bignum.  But in the
      ;; signed format, it would be a fixum.
      (rgf$c :type (array (signed-byte 64)
                          (#.*64-bit-general-purpose-registers-len*))
             :initially 0
             :resizable nil)

      ;; We choose the RIP to be a 48-bit signed integer.  RIP can
      ;; contain only canonical addresses, which range from 0 to
      ;; 2^47-1 and 2^64-2^47 to 2^64-1, inclusive, for the 64-bit
      ;; mode.  So, in our model, 0 to 2^47-1 represents the lower
      ;; range of canonical addresses and -2^47 to -1 represents the
      ;; upper range of canonical addresses.
      (rip$c :type (signed-byte 48)
             :initially 0)

      ;; Rflags: We define the rflags register as a 32-bit field, even
      ;; though in the 64-bit mode, rflags is a 64-bit register.  This
      ;; is good to do, because it avoids bignum creation.  Also, as
      ;; of 2014, Intel says that the top 32 bits of rflags are
      ;; reserved, so we aren't messing anything up.
      (rflags$c :type (unsigned-byte 32)
                ;; Bit 1 is always 1.
                :initially 2)

      ;; User Segment Registers
      ;; Visible portion:
      ;; 16-bit selector INDEX(13)::TI(1)::RPL(2)
      ;; Invisible portion:
      ;; 16-bit Attributes
      ;; 32-bit Limit
      ;; 64-bit Base Address
      (seg-visible$c :type (array (unsigned-byte 16)
                                  (#.*segment-register-names-len*))
                     :initially 0
                     :resizable nil)
      (seg-hidden$c :type (array (unsigned-byte 112)
                                 (#.*segment-register-names-len*))
                    :initially 0
                    :resizable nil)

      ;; System Table Registers (GDTR and IDTR) -- these registers
      ;; point to bounded tables of (up to 8192) segment descriptors.
      ;; In 64-bit mode, the system table registers are extended from
      ;; 48 to 80 bits.
      (str$c :type (array (unsigned-byte 80)
                          (#.*gdtr-idtr-names-len*))
             :initially 0
             :resizable nil)

      ;; System Segment Registers (Task Register and LDTR)
      ;; Visible portion:
      ;; 16-bit selector INDEX(13)::TI(1)::RPL(2)
      ;; Invisible portion:
      ;; 16-bit Attributes
      ;; 32-bit Limit
      ;; 64-bit Base Address
      (ssr-visible$c :type (array (unsigned-byte 16)
                                  (#.*ldtr-tr-names-len*))
                     :initially 0
                     :resizable nil)
      (ssr-hidden$c :type (array (unsigned-byte 112)
                                 (#.*ldtr-tr-names-len*))
                    :initially 0
                    :resizable nil)

      ;; Control registers
      ;; [Shilpi]:
      ;; Note that CR0 is still a 32-bit register in 64-bit mode.  All
      ;; other control registers are 64-bit wide.  Also, CR4 has all
      ;; but the low 21 bits reserved.  It'd be nice to define these
      ;; registers separately so that bignum creation can be avoided
      ;; during slicing operations involving these registers.
      (ctr$c  :type (array (unsigned-byte 64)
                           (#.*control-register-names-len*))
              :initially 0
              :resizable nil)

      ;; Debug registers
      (dbg$c :type (array (unsigned-byte 64)
                          (#.*debug-register-names-len*))
             :initially 0
             :resizable nil)

      ;; Floating-point registers:

      ;; FPU 80-bit data registers
      ;; The MMX registers (MM0 through MM7) are aliased to the low
      ;; 64-bits of the FPU data registers.
      (fp-data$c :type (array (unsigned-byte 80)
                              (#.*fp-data-register-names-len*))
                 :initially 0
                 :resizable nil)

      ;; FPU 16-bit control register
      (fp-ctrl$c :type (unsigned-byte 16)
                 :initially 0)

      ;; FPU 16-bit status register
      (fp-status$c :type (unsigned-byte 16)
                   :initially 0)

      ;; FPU 16-bit tag register
      (fp-tag$c :type (unsigned-byte 16)
                :initially 0)

      ;; FPU 48-bit last instruction pointer
      (fp-last-inst$c :type (unsigned-byte 48)
                      :initially 0)

      ;; FPU 48-bit last data (operand) pointer
      (fp-last-data$c :type (unsigned-byte 48)
                      :initially 0)

      ;; FPU 11-bit opcode
      (fp-opcode$c :type (unsigned-byte 11)
                   :initially 0)

      ;; XMM 128-bit data registers
      (xmm$c :type (array (unsigned-byte 128)
                          (#.*xmm-register-names-len*))
             :initially 0
             :resizable nil)

      ;; MXCSR
      ;; Top 16 bits are reserved.
      (mxcsr$c :type (unsigned-byte 32)
               ;; Bits 7 through 12 are the individual masks for the
               ;; SIMD floating point exceptions.  These are set upon
               ;; a power-up or reset.
               :initially 8064)

      ;; Model-specific registers
      (msr$c :type (array (unsigned-byte 64)
                          (#.*model-specific-register-names-len*))
             :initially 0
             :resizable nil)

      ;; Model state, used to indicate I/O or errors that our model
      ;; does not handle yet.  Basically, we use the model state to
      ;; assert partial correctness.  If the model state is nil till
      ;; the end of execution, we expect the results to be correct.
      ;; Otherwise, all bets are off.
      (ms$c :type t :initially nil)

      ;; We need some way to pass exceptions and such around.  So we
      ;; stuff them into the fault slot, to be processed by the step
      ;; function.
      (fault$c :type t :initially nil)

      ;; Environment for the programs running on our x86 model:
      (env$c :type (satisfies env-alistp) :initially nil)

      ;; Field that seeds unknown values that characterize commonly
      ;; occurring undefined behavior:
      (undef$c :type t :initially 0)

      ;; The following field acts as a switch.  When its value is t,
      ;; support for paging is absent, and it is present otherwise.
      ;; This field is an artifact of our model, and does not exist on
      ;; the real x86 processors.
      (app-view$c :type (satisfies booleanp) :initially t)

      ;; The following field also acts as a switch. When its value is
      ;; t, then accessed and dirty bits in the paging structures are
      ;; set during those data structure traversals, as
      ;; expected. Otherwise, these bits are not set. This switch is
      ;; meaningful only in when the model is in sys-view.
      (marking-view$c :type (satisfies booleanp) :initially t)

      ;; The os-info$c is meaningful only in the application-level view.
      (os-info$c               :type (satisfies keywordp) :initially :linux)

      ;; For our ACL2 model, we define a paging-like mechanism to
      ;; model the complete x86 52-bit address space.  The memory is
      ;; laid out in a flat array, to be viewed as back-to-back
      ;; "pseudo-pages" each of size 2^27 bytes (128MB).  The address
      ;; of a byte is split into two pieces: a 25-bit pseudo-page
      ;; address and a 27-bit offset within a page.  The mem-table
      ;; data structure is of size *mem-table-size* = 2^25 -- thus,
      ;; indices are 25 bits -- and it maps these indices to 25-bit
      ;; pseudo-page addresses.  However, the mem-table values are
      ;; actually 26-bit values: the least significant bit is
      ;; initially 1, but is 0 when the entry is valid, in which case
      ;; the most significant 25 bits represent a pseudo-page address.
      ;; The offset of a byte address is a 27-bit wide address, which
      ;; when added to (pseudo-page address << 27), gives the "real"
      ;; address of a byte stored in mem-array.  Mem-array-next-addr
      ;; keeps track of the 25-bit index of the pseudo-page to be
      ;; allocated next.

      ;; Here is an example of how this works.  Suppose we have the
      ;; following, where again, the least significant bit of 0
      ;; indicates a valid entry, and where {i, 1'bx} denotes
      ;; concatenation of the bit-vector i with the single bit x.

      ;;   mem-table[#x0654321] = {0, 1'b0}
      ;;   mem-table[#x16789ab] = {1, 1'b0}
      ;;   mem-table[#x0111111] = {2, 1'b0}

      ;; All additional values in mem-table are the initial value of
      ;; 1, which means "page is not present".

      ;; Then mem-array starts as follows.

      ;;  2^27 bytes corresponding to byte addresses with top 25 bits = #x0654321
      ;;  2^27 bytes corresponding to byte addresses with top 25 bits = #x16789ab
      ;;  2^27 bytes corresponding to byte addresses with top 25 bits = #x0111111

      (mem-table :type (array (unsigned-byte #.*mem-table-size-bits+1*)
                              ;; *mem-table-size-bits* of pseudo-page
                              ;; address, followed by 1 extra bit
                              ;; (LSB) to indicate the
                              ;; absence/presence of pseudo-pages
                              (#.*mem-table-size*))
                 :initially 1
                 :resizable nil)

      (mem-array :type (array (unsigned-byte 8)
                              (#.*initial-mem-array-length*))
                 :initially 0
                 :resizable t)

      (mem-array-next-addr :type (integer 0 #.*mem-table-size*)
                           :initially 0)))

  ;; Creating the stobj

  (defun create-stobj-renaming-fn-1 (x86-model-field)
    ;; Renaming the field updaters
    (let ((name (car x86-model-field))
          (type (caddr x86-model-field)))
      (cond ((and (consp type)
                  (equal (car type) 'array))
             (let ((namei (mk-name name "I")))
               `(,(mk-name "UPDATE-" namei) ,(mk-name "!" namei))))
            (t
             `(,(mk-name "UPDATE-" name) ,(mk-name "!" name))))))

  (defun create-stobj-renaming-fn (x86-model)
    (cond ((endp x86-model)
           '())
          (t
           `(,(create-stobj-renaming-fn-1 (car x86-model))
             ,@(create-stobj-renaming-fn (cdr x86-model))))))

  (defun create-x86-stobj-1 (x86$c-model)
    `(DEFSTOBJ X86$C
       ,@x86$c-model
       :INLINE t
       :RENAMING ((x86$cp x86$cp-pre)
                  ,@(create-stobj-renaming-fn x86$c-model))
       :NON-MEMOIZABLE T))

  (defmacro create-x86-stobj ()
    (create-x86-stobj-1 *x86$c-model*))

  (create-x86-stobj))

;; ======================================================================
;; Strong recognizer for the concrete x86 state (x86$cp)
;; ======================================================================

(defsection x86-concrete-stobj-recognizer

  :parents (concrete-state)

  :short "Definition of @('x86$cp'), the real concrete @('x86') state
  recognizer"

  :long "<p>We have renamed the recognizer that comes with the
  @('defstobj') event to @('x86$cp-pre'). The function @('x86$cp-pre')
  only states that the individual fields of the @('x86') state are
  well-formed in some sense --- it doesn't say anything about the
  relationships between those fields.  The recognizer @('x86$cp') is a
  conjunction of @('x86$cp-pre') and a predicate called
  @('good-memp'), which, at a high-level, says that the three memory
  fields in the concrete stobj together give us a large
  byte-addressable memory.</p>"


  (define good-mem-table-entriesp
    ((i               (unsigned-byte-p #.*mem-table-size-bits* i))
     (table-bound     (unsigned-byte-p #.*mem-table-size-bits* table-bound))
     (array-next-addr natp)
     x86$c)
    :guard (<= i table-bound)
    :measure (nfix (- table-bound i))
    :enabled t
    :parents (x86-concrete-stobj-recognizer)
    (cond ((mbt (and (natp i) (natp table-bound) (<= i table-bound)))
           (let ((addr (mem-tablei i x86$c)))
             (and (or (eql addr 1)
                      (and (natp addr)
                           (equal (logand #x1 addr) 0)
                           (< (ash addr -1)
                              array-next-addr)))
                  (or (eql i table-bound)
                      (good-mem-table-entriesp (1+ i) table-bound array-next-addr
                                               x86$c)))))
          (t nil)))

  (defun good-mem-table-entriesp-logic (i table-bound array-next-addr mem-table)
    (declare (xargs :measure (nfix (- table-bound i))))
    (cond ((mbt (and (natp i) (natp table-bound) (<= i table-bound)))
           (let ((addr (nth i mem-table)))
             (and (or (eql addr 1)
                      (and (natp addr)
                           (equal (logand #x1 addr) 0)
                           (< (ash addr -1)
                              array-next-addr)))
                  (or (eql i table-bound)
                      (good-mem-table-entriesp-logic
                       (1+ i) table-bound array-next-addr mem-table)))))
          (t nil)))

  (defun-nx nth-nx (n x)
    (nth n x))

  (defthm good-mem-table-entriesp-is-good-mem-table-entriesp-logic
    (equal (good-mem-table-entriesp i table-bound array-next-addr x86$c)
           (good-mem-table-entriesp-logic i table-bound array-next-addr
                                          (nth *mem-tablei* x86$c))))

  (in-theory (disable good-mem-table-entriesp-logic))

  (defun good-mem-table-entriesp-weak (i table-bound x86$c)
    ;; For guard of mem-table-entries.
    (declare (type (unsigned-byte #.*mem-table-size-bits*)
                   i table-bound)
             (xargs :stobjs x86$c
                    :guard (<= i table-bound)
                    :measure (nfix (- table-bound i))))
    (cond ((mbt (and (natp i) (natp table-bound) (<= i table-bound)))
           (and (natp (mem-tablei i x86$c))
                (or (eql i table-bound)
                    (good-mem-table-entriesp-weak (1+ i) table-bound x86$c))))
          (t nil)))

  (defthml rational-listp-revappend
    (implies (rational-listp x)
             (equal (rational-listp (revappend x y))
                    (rational-listp y))))

  (define merge-<-into->
    ((lst1 rational-listp)
     (lst2 rational-listp)
     acc)
    :enabled t
    :measure (+ (len lst1) (len lst2))
    :short "Merge upward-sorted lists lst1 and lst2 into
    downward-sorted list acc."
    :parents (x86-concrete-stobj-recognizer)
    (cond ((endp lst1) (revappend lst2 acc))
          ((endp lst2) (revappend lst1 acc))
          ((< (car lst1) (car lst2))
           (merge-<-into-> (cdr lst1) lst2 (cons (car lst1) acc)))
          (t
           (merge-<-into-> lst1 (cdr lst2) (cons (car lst2) acc))))
    ///
    (defthm rational-listp-merge-<-into->
      (implies (and (rational-listp x)
                    (rational-listp y)
                    (rational-listp z))
               (rational-listp (merge-<-into-> x y z)))))

  (define merge->-into-<
    ((lst1 rational-listp)
     (lst2 rational-listp)
     acc)
    :enabled t
    :measure (+ (len lst1) (len lst2))
    :short "Merge downward-sorted lists lst1 and lst2 into upward-sorted
    list acc."
    :parents (x86-concrete-stobj-recognizer)
    (cond ((endp lst1) (revappend lst2 acc))
          ((endp lst2) (revappend lst1 acc))
          ((> (car lst1) (car lst2))
           (merge->-into-< (cdr lst1) lst2 (cons (car lst1) acc)))
          (t
           (merge->-into-< lst1 (cdr lst2) (cons (car lst2) acc))))
    ///
    (defthm rational-listp-merge->-into-<
      (implies (and (rational-listp x)
                    (rational-listp y)
                    (rational-listp z))
               (rational-listp (merge->-into-< x y z)))))


  (encapsulate
    ()

    (local
     (encapsulate
       ()

       (local (include-book "arithmetic-5/top" :dir :system))

       (defthm mem-table-entries-measure-helper-1
         (implies (and (not (equal lower upper))
                       (not (equal (+ 1 lower) upper))
                       (natp lower)
                       (natp upper)
                       (< (+ 1 lower) upper)
                       (<= lower (floor (+ lower upper) 2)))
                  (< (floor (+ lower upper) 2) upper)))

       (defthm mem-table-entries-measure-helper-2
         (implies (and (not (equal lower upper))
                       (not (equal (+ 1 lower) upper))
                       (natp lower)
                       (natp upper)
                       (< (+ 1 lower) upper)
                       (< (floor (+ lower upper) 2) upper))
                  (< (+ -1 (- (floor (+ lower upper) 2)))
                     (- lower))))
       ))

    (local (include-book "arithmetic/top-with-meta" :dir :system))
    (local (include-book "centaur/bitops/ihs-extensions" :dir :system))

    (local (in-theory (e/d (logtail) ())))

    (defun mem-table-entries (lower upper x86$c parity)
      (declare (type (unsigned-byte #.*mem-table-size-bits*) lower upper)
               (xargs :stobjs x86$c
                      :guard (and (<= lower upper)
                                  (booleanp parity)
                                  (good-mem-table-entriesp-weak lower upper x86$c))
                      :verify-guards nil
                      :measure (nfix (- upper lower))))
      (cond ((eql lower upper)
             (let ((addr (mem-tablei lower x86$c)))
               (cond ((eql addr 1) nil)
                     (t (list (ash addr -1))))))
            ((eql (1+ lower) upper)
             (let ((addr-lower (mem-tablei lower x86$c))
                   (addr-upper (mem-tablei upper x86$c)))
               (cond ((eql addr-lower 1)
                      (cond ((eql addr-upper 1) nil)
                            (t (list (ash addr-upper -1)))))
                     ((eql addr-upper 1)
                      (list (ash addr-lower -1)))
                     ((equal parity (< addr-lower addr-upper))
                      (list (ash addr-lower -1) (ash addr-upper -1)))
                     (t
                      (list (ash addr-upper -1) (ash addr-lower -1))))))
            ((mbt (and (natp lower) (natp upper) (< (1+ lower) upper)))
             (let ((mid (ash (+ lower upper) -1)))
               (cond (parity
                      (merge->-into-<
                       (mem-table-entries lower mid x86$c nil)
                       (mem-table-entries (1+ mid) upper x86$c nil)
                       nil))
                     (t
                      (merge-<-into->
                       (mem-table-entries lower mid x86$c t)
                       (mem-table-entries (1+ mid) upper x86$c t)
                       nil)))))
            (t 'impossible)))

    )

  (defthml good-mem-table-entriesp-weak-preserved-lemma
    (implies (and (good-mem-table-entriesp-weak lower upper1 x86$c)
                  (natp upper2)
                  (<= lower upper2)
                  (<= upper2 upper1))
             (good-mem-table-entriesp-weak lower upper2 x86$c)))

  (defthm good-mem-table-entriesp-weak-preserved
    (implies (and (good-mem-table-entriesp-weak lower1 upper1 x86$c)
                  (natp lower2)
                  (natp upper2)
                  (<= lower1 lower2)
                  (<= lower2 upper2)
                  (<= upper2 upper1))
             (good-mem-table-entriesp-weak lower2 upper2 x86$c)))

  (local
   (encapsulate
     ()
     (local (include-book "arithmetic-5/top" :dir :system))

     ;; Some arithmetic theorems for the guard proof of
     ;; mem-table-entries.
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

     (defthm floor-1/2-inequalities
       (implies (and (natp lower)
                     (natp upper)
                     (< lower 33554432)
                     (< upper 33554432)
                     (< (+ 1 lower) upper))
                (and (< (floor (+ (* 1/2 lower) (* 1/2 upper)) 1) 33554432)
                     (<= 0 (floor (+ (* 1/2 lower) (* 1/2 upper)) 1))
                     (<= (+ 1 (floor (+ (* 1/2 lower) (* 1/2 upper)) 1)) upper)
                     (<= lower (floor (+ (* 1/2 lower) (* 1/2 upper)) 1))))
       :rule-classes :linear)
     ))

  (defthm rational-listp-mem-table-entries
    (implies (good-mem-table-entriesp-weak lower upper x86$c)
             (rational-listp (mem-table-entries lower upper x86$c parity)))
    :hints (("Goal"
             :induct (mem-table-entries lower upper x86$c parity))))

  (verify-guards mem-table-entries)

  (defun no-duplicatesp-sorted (lst)
    (declare (xargs :guard (eqlable-listp lst)))
    (cond ((or (endp lst)
               (endp (cdr lst)))
           t)
          ((eql (car lst) (cadr lst))
           nil)
          (t (no-duplicatesp-sorted (cdr lst)))))

  (defthml rational-listp-implies-eqlable-listp
    (implies (rational-listp x)
             (eqlable-listp x))
    :rule-classes (:rewrite :type-prescription))

  (defun good-mem-table-no-dupsp (lower upper x86$c)
    (declare (type (unsigned-byte #.*mem-table-size-bits*)
                   lower upper)
             (xargs :stobjs x86$c
                    :guard
                    (and (<= lower upper)
                         (good-mem-table-entriesp-weak lower upper x86$c))))
    (no-duplicatesp-sorted (mem-table-entries lower upper x86$c t)))


  (defun mem-table-entries-logic (lower upper mem-table parity)
    ;; The result is increasing if parity is true, increasing if parity is false.
    (declare (xargs :measure (nfix (- upper lower))))
    (cond ((eql lower upper)
           (let ((addr (nth lower mem-table)))
             (cond ((eql addr 1) nil)
                   (t (list (ash addr -1))))))
          ((eql (1+ lower) upper)
           (let ((addr-lower (nth lower mem-table))
                 (addr-upper (nth upper mem-table)))
             (cond ((eql addr-lower 1)
                    (cond ((eql addr-upper 1) nil)
                          (t (list (ash addr-upper -1)))))
                   ((eql addr-upper 1)
                    (list (ash addr-lower -1)))
                   ((equal parity (< addr-lower addr-upper))
                    (list (ash addr-lower -1)
                          (ash addr-upper -1)))
                   (t
                    (list (ash addr-upper -1)
                          (ash addr-lower -1))))))
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

  (defun good-mem-table-no-dupsp-logic (lower upper mem-table)
    (no-duplicatesp-sorted (mem-table-entries-logic lower upper mem-table t)))

  (defthm mem-table-entries-is-mem-table-entries-logic
    (equal (mem-table-entries lower upper x86$c parity)
           (mem-table-entries-logic lower upper
                                    (nth *mem-tablei* x86$c)
                                    parity)))

  (defthm good-mem-table-no-dupsp-is-good-mem-table-no-dupsp-logic
    (equal (good-mem-table-no-dupsp lower upper x86$c)
           (good-mem-table-no-dupsp-logic lower upper
                                          (nth *mem-tablei* x86$c))))

  (in-theory (disable good-mem-table-no-dupsp-logic
                      good-mem-table-no-dupsp))

  ;; Before defining good-memp, towards defining x86$cp, we define a
  ;; function that will let us reason about the mem-array-next-addr
  ;; field, showing (e.g., for guard verification) that it's not too
  ;; large.

  (defun expected-mem-array-next-addr (i table-len x86$c)
    (declare (type (integer 0 #.*mem-table-size*)
                   ;; Note that 0 and *mem-table-size* form a closed interval,
                   ;; unlike that formed by (unsigned-byte 25).
                   i table-len)
             (xargs :stobjs x86$c
                    :guard (<= i table-len)
                    :measure (nfix (- table-len i))))
    (cond ((or (not (natp i))
               (not (natp table-len))
               (>= i table-len))
           0)
          (t (let ((addr (mem-tablei i x86$c)))
               (cond ((eql addr 1)
                      (expected-mem-array-next-addr (1+ i) table-len x86$c))
                     (t (+ 1 (expected-mem-array-next-addr (1+ i)
                                                           table-len
                                                           x86$c))))))))

  (defthm expected-mem-array-in-parts
    (implies (and (natp i)
                  (natp j)
                  (natp k)
                  (<= i j)
                  (<= j k))
             (equal (+ (expected-mem-array-next-addr i j x86$c)
                       (expected-mem-array-next-addr j k x86$c))
                    (expected-mem-array-next-addr i k x86$c)))
    :rule-classes nil)

  (defthm expected-mem-array-bound-general
    (implies (<= i table-len)
             (<= (expected-mem-array-next-addr i table-len x86$c)
                 (- table-len i)))
    :rule-classes :linear)

  (defthm expected-mem-array-bound
    (<= (expected-mem-array-next-addr 0
                                      (mem-table-length x86$c)
                                      x86$c)
        (mem-table-length x86$c))
    :hints (("Goal" :use ((:instance expected-mem-array-bound-general
                                     (i 0)
                                     (table-len (mem-table-length x86$c))))))
    :rule-classes :linear)

  (defthm expected-mem-array-next-addr-only-depends-on-mem-table-lemma
    (implies (equal (nth *mem-tablei* x86$c-alt)
                    (nth *mem-tablei* x86$c))
             (equal (expected-mem-array-next-addr i j x86$c-alt)
                    (expected-mem-array-next-addr i j x86$c)))
    :rule-classes nil)

  (defthm expected-mem-array-next-addr-only-depends-on-mem-table
    (implies (and (equal (expected-mem-array-next-addr 0 *mem-table-size* x86$c)
                         x) ;; free var
                  (syntaxp (equal x86$c 'x86$c))
                  (equal (nth *mem-tablei* x86$c-alt)
                         (nth *mem-tablei* x86$c)))
             (equal (expected-mem-array-next-addr 0 *mem-table-size* x86$c-alt)
                    x))
    :hints (("Goal"
             :use
             ((:instance
               expected-mem-array-next-addr-only-depends-on-mem-table-lemma
               (i 0) (j *mem-table-size*))))))

  (defthmd expected-mem-array-next-addr-only-depends-on-mem-table-no-syntaxp
    (implies (and (equal (expected-mem-array-next-addr 0 *mem-table-size* x86$c)
                         x) ;; free var
                  (equal (nth *mem-tablei* x86$c-alt)
                         (nth *mem-tablei* x86$c)))
             (equal (expected-mem-array-next-addr 0 *mem-table-size* x86$c-alt)
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
                                            (nth *mem-tablei* x86$c))
             (good-mem-table-entriesp-weak lower upper x86$c))
    :hints (("Goal" :in-theory (e/d (good-mem-table-entriesp-logic
                                     good-mem-table-entriesp-weak)
                                    ((force)))))
    :rule-classes :forward-chaining)

  (defun good-mem-arrayp-1 (index len x86$c)
    (declare (xargs :stobjs x86$c
                    :guard (and (natp index)
                                (natp len)
                                (<= index len)
                                (<= len (mem-array-length x86$c)))
                    :measure (nfix (- len index))))
    (cond ((mbe :logic (not (and (natp index)
                                 (natp len)
                                 (< index len)))
                :exec (eql index len))
           t)
          (t (and (eql (mem-arrayi index x86$c) 0)
                  (good-mem-arrayp-1 (1+ index) len x86$c)))))

  (defun good-mem-arrayp-1-logic (index len mem-array)
    (declare (xargs :measure (nfix (- len index))))
    (cond ((not (and (natp index)
                     (natp len)
                     (< index len)))
           t)
          (t (and (eql (nth index mem-array) 0)
                  (good-mem-arrayp-1-logic (1+ index) len mem-array)))))

  (defthm good-mem-arrayp-1-is-good-mem-arrayp-1-logic
    (equal (good-mem-arrayp-1 index len x86$c)
           (good-mem-arrayp-1-logic index len (nth *mem-arrayi* x86$c))))

  (defun good-mem-arrayp (x86$c)
    (declare (xargs :stobjs x86$c
                    :guard (<= (ash (mem-array-next-addr x86$c) #.*2^x-byte-pseudo-page*)
                               (mem-array-length x86$c))
                    :guard-hints (("Goal" :in-theory (enable ash floor)))))
    (mbe :logic
         (good-mem-arrayp-1-logic (ash (mem-array-next-addr x86$c)
                                       #.*2^x-byte-pseudo-page*)
                                  (mem-array-length x86$c)
                                  (nth-nx *mem-arrayi* x86$c))
         :exec
         (good-mem-arrayp-1 (ash (mem-array-next-addr x86$c)
                                 #.*2^x-byte-pseudo-page*)
                            (mem-array-length x86$c)
                            x86$c)))

  ;; mem-table lemmas

  (defthm mem-tablep-forward
    (implies (mem-tablep x)
             (nat-listp x))
    :rule-classes :forward-chaining)

  (defmacro mem-table-indexp (x)
    `(and (natp ,x)
          (< ,x *mem-table-size*)))

  (defthm nth-of-nat-listp-within-bounds
    (implies (and (nat-listp x)
                  (natp i)
                  (< i (len x)))
             (natp (nth i x)))
    :rule-classes :type-prescription)


  (defthm natp-mem-tablep-when-valid-mem-table-index
    (implies (forced-and (x86$cp-pre x86$c)
                         (mem-table-indexp i))
             (and (integerp (mem-tablei i x86$c))
                  (<= 0 (mem-tablei i x86$c))))
    :rule-classes (:rewrite :type-prescription))

  (defthm natp-mem-tablep-when-valid-mem-table-index-nth-version
    (implies (forced-and (x86$cp-pre x86$c)
                         (mem-table-indexp i))
             (and (integerp (nth i (nth *mem-tablei* x86$c)))
                  (<= 0 (nth i (nth *mem-tablei* x86$c)))))
    :rule-classes (:rewrite :type-prescription))

  (defthml nth-of-mem-table-<=-*2^mem-table-size-bits+1*
    (implies (and (mem-tablep x)
                  (integerp i)
                  (<= 0 i)
                  (< i (len x)))
             (< (nth i x) #.*2^mem-table-size-bits+1*))
    :rule-classes :linear
    :hints (("Goal" :in-theory (e/d (nth) ()))))

  (defthm mem-tablei-less-than-*2^mem-table-size-bits+1*
    (implies (forced-and (x86$cp-pre x86$c)
                         (mem-table-indexp i))
             (< (mem-tablei i x86$c) #.*2^mem-table-size-bits+1*))
    :rule-classes :linear)

  (defthm mem-tablei-less-than-*2^mem-table-size-bits+1*-nth-version
    (implies (forced-and (x86$cp-pre x86$c)
                         (mem-table-indexp i))
             (< (nth i (nth *mem-tablei* x86$c))
                #.*2^mem-table-size-bits+1*))
    :rule-classes :linear)

  (define good-memp (x86$c)
    :short "@('good-memp') says that the concrete state of the
    @('x86') ISA has a well-formed byte-addressable memory."
    :parents (x86-concrete-stobj-recognizer)
    (let ((table-bound (1- (mem-table-length x86$c)))
          (array-length (mem-array-length x86$c))
          (array-next-addr (mem-array-next-addr x86$c)))
      (and (<= (ash array-next-addr #.*2^x-byte-pseudo-page*) array-length)
           (<= *initial-mem-array-length* array-length)
           (eql (logand #.*pseudo-page-size-in-bytes-1* array-length) 0)
           ;; integral number of pseudo pages
           (equal array-next-addr
                  (expected-mem-array-next-addr 0
                                                (mem-table-length x86$c)
                                                x86$c))
           (mbe :logic
                (good-mem-table-entriesp-logic 0 table-bound array-next-addr
                                               (nth-nx *mem-tablei* x86$c))
                :exec
                (good-mem-table-entriesp 0 table-bound array-next-addr
                                         x86$c))
           (mbe :logic
                (good-mem-table-no-dupsp-logic 0 table-bound
                                               (nth-nx *mem-tablei* x86$c))
                :exec
                (good-mem-table-no-dupsp 0 table-bound x86$c))
           (good-mem-arrayp x86$c))))

  (define x86$cp (x86$c)
    :parents (x86-concrete-stobj-recognizer)
    :enabled t
    :short "The <i>real</i> recognizer of a well-formed concrete
    @('x86') state"
    (and (x86$cp-pre x86$c)
         (good-memp x86$c))))

;; ======================================================================
;; Type-like theorems about concrete stobj accessors/updaters and
;; recognizers
;; ======================================================================

(defsection theorems-about-concrete-accessors-updaters-and-recognizers

  :parents (concrete-state)

  :short "Some basic theorems about the type of the fields of the
  concrete @('x86') state and about the updater functions of these
  fields."

  :long "<p> We define two kinds of rules about each field in the
  stobj now: some forward chaining rules that state that a field is,
  for example, a @('nat-listp'), and some rules that say that the
  updaters preserve the respective field recognizer under certain
  hypotheses.  These theorems are useful later in defining the :logic
  recognizers of the fields of the abstract stobj for the @('x86')
  state.</p>"

  (local (in-theory (e/d () (nth update-nth))))

  (defun x86-concrete-stobj-array-thms-1 (x86$c-model-field)

    ;; This function assumes that x86-model-field is defined using the
    ;; same syntax as that for a field in a defstobj definition.

    (let* ((name (car x86$c-model-field))
           (type (caddr x86$c-model-field))
           (size (cadr (cadr type))))
      (cond ((equal (car (cadr type)) 'unsigned-byte)
             (let* ((predicate (mk-name (symbol-name name) "P")))
               `( ;; readers
                 (DEFRULE ,(mk-name predicate "-FORWARD")
                   :parents (theorems-about-concrete-accessors-updaters-and-recognizers)
                   (IMPLIES (,predicate X)
                            (NAT-LISTP X))
                   :RULE-CLASSES :FORWARD-CHAINING)
                 ;; writers
                 (DEFRULE ,(mk-name predicate "-UPDATE-NTH")
                   :parents (theorems-about-concrete-accessors-updaters-and-recognizers)
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
             (let* ((predicate (mk-name (symbol-name name) "P")))
               `( ;; readers
                 (DEFRULE ,(mk-name predicate "-FORWARD")
                   :parents (theorems-about-concrete-accessors-updaters-and-recognizers)
                   (IMPLIES (,predicate X)
                            (INTEGER-LISTP X))
                   :RULE-CLASSES :FORWARD-CHAINING)
                 ;; writers
                 (DEFRULE ,(mk-name predicate "-UPDATE-NTH")
                   :parents (theorems-about-concrete-accessors-updaters-and-recognizers)
                   (IMPLIES (FORCED-AND (,predicate X)
                                        (INTEGERP I)
                                        (<= 0 I)
                                        (< I (LEN X))
                                        (INTEGERP V)
                                        (<= ,(- (expt 2 (1- size))) V)
                                        (< V ,(expt 2 (1- size))))
                            (,predicate (UPDATE-NTH I V X)))
                   :HINTS (("Goal" :IN-THEORY (E/D (UPDATE-NTH) ()))))
                 )))
            )))

  (defun x86-concrete-stobj-array-thms (x86$c-model)
    (cond ((endp x86$c-model)
           '())
          (t
           (if (and (consp (caddr (car x86$c-model)))
                    (equal (caaddr (car x86$c-model)) 'array))
               (append (x86-concrete-stobj-array-thms-1 (car x86$c-model))
                       (x86-concrete-stobj-array-thms (cdr x86$c-model)))
             (x86-concrete-stobj-array-thms (cdr x86$c-model))))))

  (defmacro x86-concrete-stobj-array-theorems ()
    (cons 'progn
          (x86-concrete-stobj-array-thms *x86$c-model*)))

  (x86-concrete-stobj-array-theorems)

  ;; Additional theorems about mem-array:

  (defthml nth-of-mem-arrayp
    (implies (and (mem-arrayp x)
                  (integerp i)
                  (<= 0 i)
                  (< i (len x)))
             (< (nth i x) 256))
    :hints (("Goal" :in-theory (e/d (nth) nil)))
    :rule-classes :linear)

  (defthm-usb n08p-mem-arrayi
    :hyp (forced-and (x86$cp x86$c)
                     (integerp i)
                     (<= 0 i)
                     (< i (len (nth *mem-arrayi* x86$c))))
    :bound 8
    :concl (nth i (nth *mem-arrayi* x86$c))
    :gen-type t
    :gen-linear t)

  (defthm x86$cp-forward-to-x86$cp-pre
    (implies (x86$cp x86$c)
             (x86$cp-pre x86$c))
    :rule-classes :forward-chaining)

  (defthm x86$cp-forward-to-good-memp
    (implies (x86$cp x86$c)
             (good-memp x86$c))
    :rule-classes :forward-chaining))

;; ======================================================================

(defsection concrete-stobj-ruleset

  :parents (concrete-state)

  :short "A ruleset containing definitions pertaining to @('x86$c')"

  :long "<p>The accessors, updaters, and recognizers of @('x86$c'),
  the concrete x86 state, are added to a ruleset called
  @('concrete-stobj-fns-theory'). This ruleset is disabled.</p>"

  (defun disable-stobj-fns-fn (x86$c-model)
    (cond ((endp x86$c-model)
           '())
          (t
           (let ((name (car (car x86$c-model)))
                 (type (caddr (car x86$c-model))))
             (cond ((and (consp type)
                         (equal (car type) 'array))
                    (let* ((namei     (mk-name name "I"))
                           (getter    namei)
                           (setter    (mk-name "!" namei))
                           (recognizer (mk-name (symbol-name name) "P")))
                      (append `(,getter
                                ,setter
                                ,recognizer
                                )
                              (disable-stobj-fns-fn (cdr x86$c-model)))))
                   (t
                    (let ((getter  name)
                          (setter  (mk-name "!" name))
                          (recognizer (mk-name (symbol-name name) "P")))
                      (append `(,getter ,setter ,recognizer)
                              (disable-stobj-fns-fn (cdr x86$c-model))))))))))

  (defmacro create-concrete-stobj-fns-ruleset (x86$c-model)
    `(DEF-RULESET concrete-stobj-fns-ruleset
       (quote ,(disable-stobj-fns-fn x86$c-model))))

  (make-event
   `(create-concrete-stobj-fns-ruleset ,*x86$c-model*))

  (in-theory (disable* concrete-stobj-fns-ruleset x86$cp-pre x86$cp)))

; =============================================================================
