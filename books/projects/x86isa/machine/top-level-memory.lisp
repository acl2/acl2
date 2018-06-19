;; Author: Alessandro Coglio <coglio@kestrel.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "segmentation")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

(defsection top-level-memory
  :parents (machine)
  :short "Top-level Memory Accessor and Updater Functions"
  )

(local (xdoc::set-default-parents top-level-memory))

;; ======================================================================

;; Factored out by Alessandro Coglio <coglio@kestrel.edu>
;; Alignment check originally contributed by Dmitry Nadezhin
(define address-aligned-p
  ((addr :type (signed-byte #.*max-linear-address-size*))
   (operand-size :type (member 1 2 4 6 8 10 16))
   (memory-ptr? booleanp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check the alignment of a linear address."
  :long
  "<p>
   Besides the address to check for alignment,
   this function takes as argument the operand size
   (from which the alignment to check is determined)
   and a flag indicating whether the address to check for alignment
   contains a memory operand of the form m16:16, m16:32, or m16:64
   (see Intel manual, Mar'17, Volume 2, Section 3.1.1.3).
   </p>
   <p>
   Words, doublewords, quadwords, and double quadwords
   must be aligned at boundaries of 2, 4, 8, or 16 bytes.
   Memory pointers of the form m16:xx must be aligned so that
   their xx portion is aligned as a word, doubleword, or quadword;
   this automatically guarantees that their m16 portion is aligned as a word.
   See Intel manual, Mar'17, Volume 1, Section 4.1.1.
   See AMD manual, Dec'17, Volume 2, Table 8-7
   (note that the table does not mention explicitly
   memory pointers of the form m16:64).
   </p>
   <p>
   If the operand size is 6, the operand must be an m16:32 pointer.
   If the operand size is 10, the operand must an m16:64 pointer.
   If the operand size is 4, it may be either an m16:16 pointer or not;
   in this case, the @('memory-ptr?') argument is used to
   determined whether the address should be aligned
   at a word or doubleword boundary.
   If the operand size is 1, 2, 8, or 16,
   it cannot be a memory pointer of the form m16:xx.
   </p>"
  (b* ((addr (the (signed-byte #.*max-linear-address-size*) addr))
       (operand-size (the (integer 0 16) operand-size)))
    (case operand-size
      ;; Every byte access is always aligned.
      (1 t)
      (6 (equal (logand addr #b11) 0))   ; m16:32
      (10 (equal (logand addr #b111) 0)) ; m16:64
      (otherwise
       (if (and memory-ptr?
                (eql operand-size 4))
           (equal (logand addr #b1) 0) ; m16:16
         (equal (logand addr
                        (the (integer 0 15) (- operand-size 1)))
                0)))))
  :inline t
  ///

  (defthm memory-byte-accesses-are-always-aligned
    (equal (address-aligned-p eff-addr 1 mem-ptr?) t))

  (defthm address-aligned-p-mem-ptr-input-irrelevant-for-all-but-bytes=4
    (implies (and (syntaxp (not (equal mem-ptr? ''nil)))
                  (not (equal nbytes 4)))
             (equal (address-aligned-p eff-addr nbytes mem-ptr?)
                    (address-aligned-p eff-addr nbytes nil)))))

;; ======================================================================

; read and write bytes:

(define rme08 ((eff-addr i64p)
               (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
               (r-x :type (member :r :x))
               x86)
  :returns (mv flg
               (byte (unsigned-byte-p 8 byte) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Read an unsigned (8-bit) byte from memory via an effective address."
  :long
  "<p>The effective address is translated to a linear address and then
   @('rml08') is called.  If the resulting linear address is not
   canonical, an error occurs.</p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86)))
    (rml08 lin-addr r-x x86))
  :inline t
  ///

  (defthm-usb n08p-of-mv-nth-1-rme08
    :hyp (x86p x86)
    :bound 8
    :concl (mv-nth 1 (rme08 eff-addr seg-reg r-x x86))
    :gen-linear t
    :gen-type t)

  (defrule rme08-value-when-error
    (implies (mv-nth 0 (rme08 eff-addr seg-reg r-x x86))
             (equal (mv-nth 1 (rme08 eff-addr seg-reg r-x x86)) 0))
    :enable (rml08 rvm08))

  (defrule rme08-does-not-affect-state-in-app-view
    (implies (app-view x86)
             (equal (mv-nth 2 (rme08 eff-addr seg-reg r-x x86)) x86))
    :enable rml08)

  (defrule mv-nth-2-rme08-in-system-level-non-marking-view
    (implies (and (not (app-view x86))
                  (not (marking-view x86))
                  (x86p x86)
                  (not (mv-nth 0 (rme08 eff-addr seg-reg r-x x86))))
             (equal (mv-nth 2 (rme08 eff-addr seg-reg r-x x86))
                    x86)))

  (defrule xr-rme08-state-app-view
    (implies (app-view x86)
             (equal (xr fld index (mv-nth 2 (rme08 addr seg-reg r-x x86)))
                    (xr fld index x86)))
    :enable rml08)

  (defrule xr-rme08-state-sys-view
    (implies (and (not (app-view x86))
                  (not (equal fld :mem))
                  (not (equal fld :fault)))
             (equal (xr fld index (mv-nth 2 (rme08 addr seg-reg r-x x86)))
                    (xr fld index x86))))

  (defrule rme08-xw-app-view
    (implies
     (and (app-view x86)
          (not (equal fld :mem))
          (not (equal fld :app-view))
          (not (equal fld :seg-hidden))
          (not (equal fld :msr)))
     (and (equal (mv-nth 0 (rme08 addr seg-reg r-x (xw fld index value x86)))
                 (mv-nth 0 (rme08 addr seg-reg r-x x86)))
          (equal (mv-nth 1 (rme08 addr seg-reg r-x (xw fld index value x86)))
                 (mv-nth 1 (rme08 addr seg-reg r-x x86)))
          ;; No need for the conclusion about the state because
          ;; "rme08-does-not-affect-state-in-app-view".
          ))
    )

  (defrule rme08-xw-sys-view
    (implies
     (and (not (app-view x86))
          (not (equal fld :fault))
          (not (equal fld :seg-visible))
          (not (equal fld :seg-hidden))
          (not (equal fld :mem))
          (not (equal fld :ctr))
          (not (equal fld :msr))
          (not (equal fld :rflags))
          (not (equal fld :app-view))
          (not (equal fld :marking-view)))
     (and (equal (mv-nth 0 (rme08 addr seg-reg r-x (xw fld index value x86)))
                 (mv-nth 0 (rme08 addr seg-reg r-x x86)))
          (equal (mv-nth 1 (rme08 addr seg-reg r-x (xw fld index value x86)))
                 (mv-nth 1 (rme08 addr seg-reg r-x x86)))
          (equal (mv-nth 2 (rme08 addr seg-reg r-x (xw fld index value x86)))
                 (xw fld index value (mv-nth 2 (rme08 addr seg-reg r-x x86)))))))

  (defrule rme08-xw-sys-view-rflags-not-ac
    (implies
     (and (not (app-view x86))
          (equal (rflags-slice :ac value)
                 (rflags-slice :ac (rflags x86))))
     (and (equal (mv-nth 0 (rme08 addr seg-reg r-x (xw :rflags 0 value x86)))
                 (mv-nth 0 (rme08 addr seg-reg r-x x86)))
          (equal (mv-nth 1 (rme08 addr seg-reg r-x (xw :rflags 0 value x86)))
                 (mv-nth 1 (rme08 addr seg-reg r-x x86)))
          (equal (mv-nth 2 (rme08 addr seg-reg r-x (xw :rflags 0 value x86)))
                 (xw :rflags 0 value (mv-nth 2 (rme08 addr seg-reg r-x x86)))))))

  (defrule rme08-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (rme08 eff-addr seg-reg r-x x86)
                    (rml08 eff-addr r-x x86)))))

(define rime08
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   x86)
  :returns (mv flg
               (byte (signed-byte-p 8 byte) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Read a signed (8-bit) byte from memory via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('riml08') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86)))
    (riml08 lin-addr r-x x86))
  :inline t
  ///

  (defthm-sb i08p-of-mv-nth-1-rime08
    :hyp (x86p x86)
    :bound 8
    :concl (mv-nth 1 (rime08 eff-addr seg-reg r-x x86))
    :gen-linear t
    :gen-type t)

  (defrule rime08-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (rime08 eff-addr seg-reg r-x x86)
                    (riml08 eff-addr r-x x86)))))

(define wme08
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (unsigned-byte 8))
   x86)
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Write an unsigned (8-bit) byte to memory via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('wml08') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86)))
    (wml08 lin-addr val x86))
  :inline t
  ///

  (defrule wme08-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (wme08 eff-addr seg-reg val x86)
                    (wml08 eff-addr val x86)))))

(define wime08
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (signed-byte 8))
   x86)
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Write a signed (8-bit) byte to memory via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('wiml08') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86)))
    (wiml08 lin-addr val x86))
  :inline t
  ///

  (defrule wime08-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (wime08 eff-addr seg-reg val x86)
                    (wiml08 eff-addr val x86)))))

;; ======================================================================

; read and write words:

(define rme16
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   (check-alignment? booleanp)
   x86)
  :returns (mv flg
               (word (unsigned-byte-p 16 word) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Read an unsigned (16-bit) word from memory via an effective address."
  :long
  "<p>The effective address is translated to a linear address and
   then @('rml16') is called.  If the resulting linear address is not
   canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.</p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr 2 nil)))
        (mv (list :unaligned-linear-address lin-addr) 0 x86)))
    (rml16 lin-addr r-x x86))
  :inline t
  ///

  (defthm-usb n16p-of-mv-nth-1-rme16
    :hyp (x86p x86)
    :bound 16
    :concl (mv-nth 1 (rme16 eff-addr seg-reg r-x check-alignment? x86))
    :gen-linear t
    :gen-type t)

  (defrule rme16-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr 2 nil)))
             (equal (rme16 eff-addr seg-reg r-x check-alignment? x86)
                    (rml16 eff-addr r-x x86)))))

(define rime16
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   (check-alignment? booleanp)
   x86)
  :returns (mv flg
               (byte (signed-byte-p 16 byte) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Read a signed (16-bit) word from memory via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('riml16') is called.  If the resulting linear address is not
   canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.</p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr 2 nil)))
        (mv (list :unaligned-linear-address lin-addr) 0 x86)))
    (riml16 lin-addr r-x x86))
  :inline t
  ///

  (defthm-sb i16p-of-mv-nth-1-rime16
    :hyp (x86p x86)
    :bound 16
    :concl (mv-nth 1 (rime16 eff-addr seg-reg r-x check-alignment? x86))
    :gen-linear t
    :gen-type t)

  (defrule rime16-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr 2 nil)))
             (equal (rime16 eff-addr seg-reg r-x check-alignment? x86)
                    (riml16 eff-addr r-x x86)))))

(define wme16
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (unsigned-byte 16))
   (check-alignment? booleanp)
   x86)
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Write an unsigned (16-bit) word to memory via an effective address."
  :long
  "<p>The effective address is translated to a linear address and then
   @('wml16') is called.  If the resulting linear address is not
   canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.</p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr 2 nil)))
        (mv (list :unaligned-linear-address lin-addr) x86)))
    (wml16 lin-addr val x86))
  :inline t
  ///

  (defrule wme16-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr 2 nil)))
             (equal (wme16 eff-addr seg-reg val check-alignment? x86)
                    (wml16 eff-addr val x86)))))

(define wime16
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (signed-byte 16))
   (check-alignment? booleanp)
   x86)
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Write a signed (16-bit) word to memory via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('wiml16') is called.  If the resulting linear address is not
   canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.  </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr 2 nil)))
        (mv (list :unaligned-linear-address lin-addr) x86)))
    (wiml16 lin-addr val x86))
  :inline t
  ///

  (defrule wime16-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr 2 nil)))
             (equal (wime16 eff-addr seg-reg val check-alignment? x86)
                    (wiml16 eff-addr val x86)))))

;; ======================================================================

; read and write long words:

(define rme32
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   (check-alignment? booleanp)
   x86
   &key
   ;; Note that the default value of mem-ptr? is nil. Provide t input
   ;; to mem-ptr? only when dealing with a m16:16 pointer.
   ((mem-ptr? booleanp) 'nil))
  :returns (mv flg
               (word (unsigned-byte-p 32 word) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Read an unsigned (32-bit) long word from memory
          via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('rml32') is called.  If the resulting linear address is not
   canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.  </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr 4 mem-ptr?)))
        (mv (list :unaligned-linear-address lin-addr) 0 x86)))
    (rml32 lin-addr r-x x86))
  :inline t
  ///

  (defthm-usb n32p-of-mv-nth-1-rme32
    :hyp (x86p x86)
    :bound 32
    :concl (mv-nth 1 (rme32 eff-addr seg-reg r-x check-alignment? x86 :mem-ptr? mem-ptr?))
    :gen-linear t
    :gen-type t)

  (defrule rme32-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr 4 mem-ptr?)))
             (equal (rme32 eff-addr seg-reg r-x check-alignment? x86 :mem-ptr? mem-ptr?)
                    (rml32 eff-addr r-x x86)))))

(define rime32
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   (check-alignment? booleanp)
   x86
   &key
   ;; Note that the default value of mem-ptr? is nil. Provide t input
   ;; to mem-ptr? only when dealing with a m16:16 pointer.
   ((mem-ptr? booleanp) 'nil))
  :returns (mv flg
               (byte (signed-byte-p 32 byte) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Read a signed (32-bit) long word from memory
          via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('riml32') is called.  If the resulting linear address is not
   canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.</p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr 4 mem-ptr?)))
        (mv (list :unaligned-linear-address lin-addr) 0 x86)))
    (riml32 lin-addr r-x x86))
  :inline t
  ///

  (defthm-sb i32p-of-mv-nth-1-rime32
    :hyp (x86p x86)
    :bound 32
    :concl (mv-nth 1 (rime32 eff-addr seg-reg r-x check-alignment? x86 :mem-ptr? mem-ptr?))
    :gen-linear t
    :gen-type t)

  (defrule rime32-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr 4 mem-ptr?)))
             (equal (rime32 eff-addr seg-reg r-x check-alignment? x86 :mem-ptr? mem-ptr?)
                    (riml32 eff-addr r-x x86)))))

(define wme32
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (unsigned-byte 32))
   (check-alignment? booleanp)
   x86
   &key
   ;; Note that the default value of mem-ptr? is nil. Provide t input
   ;; to mem-ptr? only when dealing with a m16:16 pointer.
   ((mem-ptr? booleanp) 'nil))
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Write an unsigned (32-bit) long word to memory
          via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('wml32') is called.  If the resulting linear address is not
   canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.  </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr 4 mem-ptr?)))
        (mv (list :unaligned-linear-address lin-addr) x86)))
    (wml32 lin-addr val x86))
  :inline t
  ///

  (defrule wme32-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr 4 mem-ptr?)))
             (equal (wme32 eff-addr seg-reg val check-alignment? x86 :mem-ptr? mem-ptr?)
                    (wml32 eff-addr val x86)))))

(define wime32
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (signed-byte 32))
   (check-alignment? booleanp)
   x86
   &key
   ;; Note that the default value of mem-ptr? is nil. Provide t input
   ;; to mem-ptr? only when dealing with a m16:16 pointer.
   ((mem-ptr? booleanp) 'nil))
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Write a signed (32-bit) long word to memory
          via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('wiml32') is called.  If the resulting linear address is not
   canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.  </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr 4 mem-ptr?)))
        (mv (list :unaligned-linear-address lin-addr) x86)))
    (wiml32 lin-addr val x86))
  :inline t
  ///

  (defrule wime32-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr 4 mem-ptr?)))
             (equal (wime32 eff-addr seg-reg val check-alignment? x86 :mem-ptr? mem-ptr?)
                    (wiml32 eff-addr val x86)))))

;; ======================================================================

; read and write 48-bit values:

(define rme48
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   (check-alignment? booleanp)
   x86)
  :returns (mv flg
               (word (unsigned-byte-p 48 word) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Read an unsigned 48-bit value (typically a m16:32 pointer)
  from memory via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('rml48') is called.  If the resulting linear address is not
   canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.  </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr 6 t)))
        (mv (list :unaligned-linear-address lin-addr) 0 x86)))
    (rml48 lin-addr r-x x86))
  :inline t
  ///

  (defthm-usb n48p-of-mv-nth-1-rme48
    :hyp (x86p x86)
    :bound 48
    :concl (mv-nth 1 (rme48 eff-addr seg-reg r-x check-alignment? x86))
    :gen-linear t
    :gen-type t)

  (defrule rme48-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr 6 t)))
             (equal (rme48 eff-addr seg-reg r-x check-alignment? x86)
                    (rml48 eff-addr r-x x86)))))

(define wme48
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (unsigned-byte 48))
   (check-alignment? booleanp)
   x86)
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Write an unsigned 48-bit value (typically a m16:32 pointer)
  to memory via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('wml48') is called.  If the resulting linear address is not
   canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.  </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr 6 t)))
        (mv (list :unaligned-linear-address lin-addr) x86)))
    (wml48 lin-addr val x86))
  :inline t
  ///

  (defrule wme48-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr 6 t)))
             (equal (wme48 eff-addr seg-reg val check-alignment? x86)
                    (wml48 eff-addr val x86)))))

;; ======================================================================

; read and write quad words:

(define rme64
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   (check-alignment? booleanp)
   x86)
  :returns (mv flg
               (word (unsigned-byte-p 64 word) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Read an unsigned (64-bit) quad word from memory
          via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('rml64') is called.  If the resulting linear address is not
   canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.</p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr 8 nil)))
        (mv (list :unaligned-linear-address lin-addr) 0 x86)))
    (rml64 lin-addr r-x x86))
  :inline t
  ///

  (defthm-usb n64p-of-mv-nth-1-rme64
    :hyp (x86p x86)
    :bound 64
    :concl (mv-nth 1 (rme64 eff-addr seg-reg r-x check-alignment? x86))
    :gen-linear t
    :gen-type t)

  (defrule rme64-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr 8 nil)))
             (equal (rme64 eff-addr seg-reg r-x check-alignment? x86)
                    (rml64 eff-addr r-x x86)))))

(define rime64
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   (check-alignment? booleanp)
   x86)
  :returns (mv flg
               (byte (signed-byte-p 64 byte) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Read a signed (64-bit) quad word from memory
          via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('riml64') is called.  If the resulting linear address is not
   canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.  </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr 8 nil)))
        (mv (list :unaligned-linear-address lin-addr) 0 x86)))
    (riml64 lin-addr r-x x86))
  :inline t
  ///

  (defthm-sb i64p-of-mv-nth-1-rime64
    :hyp (x86p x86)
    :bound 64
    :concl (mv-nth 1 (rime64 eff-addr seg-reg r-x check-alignment? x86))
    :gen-linear t
    :gen-type t)

  (defrule rime64-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr 8 nil)))
             (equal (rime64 eff-addr seg-reg r-x check-alignment? x86)
                    (riml64 eff-addr r-x x86)))))

(define wme64
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (unsigned-byte 64))
   (check-alignment? booleanp)
   x86)
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Write an unsigned (64-bit) quad word to memory
          via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('wml64') is called.  If the resulting linear address is not
   canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.</p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr 8 nil)))
        (mv (list :unaligned-linear-address lin-addr) x86)))
    (wml64 lin-addr val x86))
  :inline t
  ///

  (defrule wme64-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr 8 nil)))
             (equal (wme64 eff-addr seg-reg val check-alignment? x86)
                    (wml64 eff-addr val x86)))))

(define wime64
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (signed-byte 64))
   (check-alignment? booleanp)
   x86)
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Write a signed (64-bit) quad word to memory
          via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('wiml64') is called.  If the resulting linear address is not
   canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.  </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr 8 nil)))
        (mv (list :unaligned-linear-address lin-addr) x86)))
    (wiml64 lin-addr val x86))
  :inline t
  ///

  (defrule wime64-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr 8 nil)))
             (equal (wime64 eff-addr seg-reg val check-alignment? x86)
                    (wiml64 eff-addr val x86)))))

;; ======================================================================

; read and write 80-bit values:

(define rme80
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   (check-alignment? booleanp)
   x86)
  :returns (mv flg
               (word (unsigned-byte-p 80 word) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Read an unsigned 80-bit value (typically a m16:64 pointer)
  from memory via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('rml80') is called.  If the resulting linear address is not
   canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.  </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr 10 t)))
        (mv (list :unaligned-linear-address lin-addr) 0 x86)))
    (rml80 lin-addr r-x x86))
  :inline t
  ///

  (defthm-usb n80p-of-mv-nth-1-rme80
    :hyp (x86p x86)
    :bound 80
    :concl (mv-nth 1 (rme80 eff-addr seg-reg r-x check-alignment? x86))
    :gen-linear t
    :gen-type t)

  (defrule rme80-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr 10 t)))
             (equal (rme80 eff-addr seg-reg r-x check-alignment? x86)
                    (rml80 eff-addr r-x x86)))))

(define wme80
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (unsigned-byte 80))
   (check-alignment? booleanp)
   x86)
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Write an unsigned 80-bit value (typically a m16:64 pointer)
  to memory via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('wml80') is called.  If the resulting linear address is not
   canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.  </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr 10 t)))
        (mv (list :unaligned-linear-address lin-addr) x86)))
    (wml80 lin-addr val x86))
  :inline t
  ///

  (defrule wme80-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr 10 t)))
             (equal (wme80 eff-addr seg-reg val check-alignment? x86)
                    (wml80 eff-addr val x86)))))

;; ======================================================================

; read and write 128-bit values:

(define rme128
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   (check-alignment? booleanp)
   x86)
  :returns (mv flg
               (word (unsigned-byte-p 128 word) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Read an unsigned 128-bit value from memory via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('rml128') is called.  If the resulting linear address is not
   canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs. </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr 16 t)))
        ;; Note: a #GP exception should be thrown here instead of an
        ;; #AC fault.  See Intel Manuals, Volume 3, Section 6.15,
        ;; Exception and Interrupt Reference, Interrupt 17 Alignment
        ;; Check Exception (#AC).
        (mv (list :unaligned-linear-address lin-addr) 0 x86)))
    (rml128 lin-addr r-x x86))
  :inline t
  ///

  (defthm-usb n128p-of-mv-nth-1-rme128
    :hyp (x86p x86)
    :bound 128
    :concl (mv-nth 1 (rme128 eff-addr seg-reg r-x check-alignment? x86))
    :gen-linear t
    :gen-type t)

  (defrule rme128-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr 16 t)))
             (equal (rme128 eff-addr seg-reg r-x check-alignment? x86)
                    (rml128 eff-addr r-x x86)))))

(define wme128
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (unsigned-byte 128))
   (check-alignment? booleanp)
   x86)
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Write an unsigned 128-bit value to memory via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('wml128') is called.  If the resulting linear address is not
   canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.  </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr 16 t)))
        ;; Note: a #GP exception should be thrown here instead of an
        ;; #AC fault.  See Intel Manuals, Volume 3, Section 6.15,
        ;; Exception and Interrupt Reference, Interrupt 17 Alignment
        ;; Check Exception (#AC).
        (mv (list :unaligned-linear-address lin-addr) x86)))
    (wml128 lin-addr val x86))
  :inline t
  ///

  (defrule wme128-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr 16 t)))
             (equal (wme128 eff-addr seg-reg val check-alignment? x86)
                    (wml128 eff-addr val x86)))))

;; ======================================================================

; read and write values of specified number of bytes:

(define rme-size
  ((nbytes :type (member 1 2 4 6 8 10 16))
   (eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   (check-alignment? booleanp)
   x86
   &key
   ;; Default value for mem-ptr? is nil --- note that this input is
   ;; relevant only for nbytes = 4.
   ((mem-ptr? booleanp) 'nil))
  :returns (mv flg
               (value natp :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Read an unsigned value with the specified number of bytes
          from memory via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('rml-size') is called.  If the resulting linear address is
   not canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs. </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr nbytes mem-ptr?)))
        (mv (list :unaligned-linear-address lin-addr) 0 x86)))
    (rml-size nbytes lin-addr r-x x86))
  :inline t
  ///

  (defrule rme-size-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr nbytes mem-ptr?)))
             (equal (rme-size nbytes eff-addr seg-reg r-x check-alignment? x86
                              :mem-ptr? mem-ptr?)
                    (rml-size nbytes eff-addr r-x x86))))

  (defruled rme-size-of-1-to-rme08
    (equal (rme-size 1 eff-addr seg-reg r-x check-alignment? x86 :mem-ptr? mem-ptr?)
           (rme08 eff-addr seg-reg r-x x86))
    :enable (rme-size rme08))

  (defruled rme-size-of-2-to-rme16
    (equal (rme-size 2 eff-addr seg-reg r-x check-alignment? x86 :mem-ptr? mem-ptr?)
           (rme16 eff-addr seg-reg r-x check-alignment? x86))
    :enable (rme-size rme16))

  (defruled rme-size-of-4-to-rme32
    (equal (rme-size 4 eff-addr seg-reg r-x check-alignment? x86 :mem-ptr? mem-ptr?)
           (rme32 eff-addr seg-reg r-x check-alignment? x86 :mem-ptr? mem-ptr?))
    :enable (rme-size rme32))

  (defruled rme-size-of-6-to-rme48
    (equal (rme-size 6 eff-addr seg-reg r-x check-alignment? x86 :mem-ptr? mem-ptr?)
           (rme48 eff-addr seg-reg r-x check-alignment? x86))
    :enable (rme-size rme48))

  (defruled rme-size-of-8-to-rme64
    (equal (rme-size 8 eff-addr seg-reg r-x check-alignment? x86 :mem-ptr? mem-ptr?)
           (rme64 eff-addr seg-reg r-x check-alignment? x86))
    :enable (rme-size rme64))

  (defruled rme-size-of-10-to-rme64
    (equal (rme-size 10 eff-addr seg-reg r-x check-alignment? x86 :mem-ptr? mem-ptr?)
           (rme80 eff-addr seg-reg r-x check-alignment? x86))
    :enable (rme-size rme80))

  (defruled rme-size-of-16-to-rme128
    (equal (rme-size 16 eff-addr seg-reg r-x check-alignment? x86 :mem-ptr? mem-ptr?)
           (rme128 eff-addr seg-reg r-x check-alignment? x86))
    :enable (rme-size rme128)))

(define rime-size
  ((nbytes :type (member 1 2 4 8))
   (eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   (check-alignment? booleanp)
   x86
   &key
   ;; Default value for mem-ptr? is nil --- note that this input is
   ;; relevant only for nbytes = 4.
   ((mem-ptr? booleanp) 'nil))
  :returns (mv flg
               (value integerp :hyp (and (x86p x86) (integerp nbytes)))
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Read a signed value with the specified number of bytes
          from memory via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('riml-size') is called.  If the resulting linear address is
   not canonical or if it is mis-aligned and @('check-alignment?')  is
   @('t'), an error occurs.  </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr nbytes mem-ptr?)))
        (mv (list :unaligned-linear-address lin-addr) 0 x86)))
    (riml-size nbytes lin-addr r-x x86))
  :inline t
  ///

  (defrule rime-size-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr nbytes mem-ptr?)))
             (equal (rime-size
                     nbytes eff-addr seg-reg r-x check-alignment? x86 :mem-ptr? mem-ptr?)
                    (riml-size nbytes eff-addr r-x x86))))

  (defruled rime-size-of-1-to-rime08
    (equal (rime-size 1 eff-addr seg-reg r-x check-alignment? x86 :mem-ptr? mem-ptr?)
           (rime08 eff-addr seg-reg r-x x86))
    :enable (rime-size rime08))

  (defruled rime-size-of-2-to-rime16
    (equal (rime-size 2 eff-addr seg-reg r-x check-alignment? x86 :mem-ptr? mem-ptr?)
           (rime16 eff-addr seg-reg r-x check-alignment? x86))
    :enable (rime-size rime16))

  (defruled rime-size-of-4-to-rime32
    (equal (rime-size 4 eff-addr seg-reg r-x check-alignment? x86 :mem-ptr? mem-ptr?)
           (rime32 eff-addr seg-reg r-x check-alignment? x86 :mem-ptr? mem-ptr?))
    :enable (rime-size rime32))

  (defruled rime-size-of-8-to-rime64
    (equal (rime-size 8 eff-addr seg-reg r-x check-alignment? x86 :mem-ptr? mem-ptr?)
           (rime64 eff-addr seg-reg r-x check-alignment? x86))
    :enable (rime-size rime64)))

(define wme-size
  ((nbytes :type (member 1 2 4 6 8 10 16))
   (eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (integer 0 *))
   (check-alignment? booleanp)
   x86
   &key
   ;; Default value for mem-ptr? is nil --- note that this input is
   ;; relevant only for nbytes = 4.
   ((mem-ptr? booleanp) 'nil))
  :guard (case nbytes
           (1  (n08p val))
           (2  (n16p val))
           (4  (n32p val))
           (6  (n48p val))
           (8  (n64p val))
           (10 (n80p val))
           (16 (n128p val)))
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Write an unsigned value with the specified number of bytes
          to memory via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('wml-size') is called.  If the resulting linear address is
   not canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.  </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr nbytes mem-ptr?)))
        (mv (list :unaligned-linear-address lin-addr) x86)))
    (wml-size nbytes lin-addr val x86))
  :inline t
  ///

  (defrule wme-size-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr nbytes mem-ptr?)))
             (equal (wme-size
                     nbytes eff-addr seg-reg val check-alignment? x86 :mem-ptr? mem-ptr?)
                    (wml-size nbytes eff-addr val x86)))))

(define wime-size
  ((nbytes :type (member 1 2 4 8))
   (eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type integer)
   (check-alignment? booleanp)
   x86
   &key
   ;; Default value for mem-ptr? is nil --- note that this input is
   ;; relevant only for nbytes = 4.
   ((mem-ptr? booleanp) 'nil))
  :guard (case nbytes
           (1  (i08p val))
           (2  (i16p val))
           (4  (i32p val))
           (8  (i64p val)))
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (top-level-memory)
  :short "Write a signed value with the specified number of bytes
          to memory via an effective address."
  :long
  "<p> The effective address is translated to a linear address and
   then @('wiml-size') is called.  If the resulting linear address is
   not canonical or if it is mis-aligned and @('check-alignment?') is
   @('t'), an error occurs.  </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86))
       ((unless (or (not check-alignment?)
                    (address-aligned-p lin-addr nbytes mem-ptr?)))
        (mv (list :unaligned-linear-address lin-addr) x86)))
    (wiml-size nbytes lin-addr val x86))
  :inline t
  ///

  (defrule wime-size-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr)
                  (or (not check-alignment?)
                      (address-aligned-p eff-addr nbytes mem-ptr?)))
             (equal (wime-size
                     nbytes eff-addr seg-reg val check-alignment? x86 :mem-ptr? mem-ptr?)
                    (wiml-size nbytes eff-addr val x86)))))

;; ======================================================================
