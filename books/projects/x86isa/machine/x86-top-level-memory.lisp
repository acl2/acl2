;; Author: Alessandro Coglio <coglio@kestrel.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "x86-segmentation")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

(defsection x86-top-level-memory
  :parents (machine)
  :short "Top-level Memory Accessor and Updater Functions"
  )

(local (xdoc::set-default-parents x86-top-level-memory))

;; ======================================================================

; read and write bytes:

(define rme08
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   x86)
  :returns (mv flg
               (byte (unsigned-byte-p 8 byte) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Read an unsigned (8-bit) byte from memory via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('rml08') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
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

  (defrule rme08-does-not-affect-state-in-programmer-level-mode
    (implies (programmer-level-mode x86)
             (equal (mv-nth 2 (rme08 eff-addr seg-reg r-x x86)) x86))
    :enable rml08)

  (defrule mv-nth-2-rme08-in-system-level-non-marking-mode
    (implies (and (not (programmer-level-mode x86))
                  (not (page-structure-marking-mode x86))
                  (x86p x86)
                  (not (mv-nth 0 (rme08 eff-addr seg-reg r-x x86))))
             (equal (mv-nth 2 (rme08 eff-addr seg-reg r-x x86))
                    x86)))

  (defrule xr-rme08-state-programmer-level-mode
    (implies (programmer-level-mode x86)
             (equal (xr fld index (mv-nth 2 (rme08 addr seg-reg r-x x86)))
                    (xr fld index x86)))
    :enable rml08)

  (defrule xr-rme08-state-system-level-mode
    (implies (and (not (programmer-level-mode x86))
                  (not (equal fld :mem))
                  (not (equal fld :fault)))
             (equal (xr fld index (mv-nth 2 (rme08 addr seg-reg r-x x86)))
                    (xr fld index x86))))

  (defrule rme08-xw-programmer-level-mode
    (implies
     (and (programmer-level-mode x86)
          (not (equal fld :mem))
          (not (equal fld :programmer-level-mode))
          (not (equal fld :seg-hidden))
          (not (equal fld :msr)))
     (and (equal (mv-nth 0 (rme08 addr seg-reg r-x (xw fld index value x86)))
                 (mv-nth 0 (rme08 addr seg-reg r-x x86)))
          (equal (mv-nth 1 (rme08 addr seg-reg r-x (xw fld index value x86)))
                 (mv-nth 1 (rme08 addr seg-reg r-x x86)))
          ;; No need for the conclusion about the state because
          ;; "rme08-does-not-affect-state-in-programmer-level-mode".
          ))
    )

  (defrule rme08-xw-system-level-mode
    (implies
     (and (not (programmer-level-mode x86))
          (not (equal fld :fault))
          (not (equal fld :seg-visible))
          (not (equal fld :seg-hidden))
          (not (equal fld :mem))
          (not (equal fld :ctr))
          (not (equal fld :msr))
          (not (equal fld :rflags))
          (not (equal fld :programmer-level-mode))
          (not (equal fld :page-structure-marking-mode)))
     (and (equal (mv-nth 0 (rme08 addr seg-reg r-x (xw fld index value x86)))
                 (mv-nth 0 (rme08 addr seg-reg r-x x86)))
          (equal (mv-nth 1 (rme08 addr seg-reg r-x (xw fld index value x86)))
                 (mv-nth 1 (rme08 addr seg-reg r-x x86)))
          (equal (mv-nth 2 (rme08 addr seg-reg r-x (xw fld index value x86)))
                 (xw fld index value (mv-nth 2 (rme08 addr seg-reg r-x x86)))))))

  (defrule rme08-xw-system-level-mode-rflags-not-ac
    (implies
     (and (not (programmer-level-mode x86))
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
  :parents (x86-top-level-memory)
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
  :parents (x86-top-level-memory)
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
  :parents (x86-top-level-memory)
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
   x86)
  :returns (mv flg
               (word (unsigned-byte-p 16 word) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Read an unsigned (16-bit) word from memory via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('rml16') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86)))
    (rml16 lin-addr r-x x86))
  :inline t
  ///

  (defthm-usb n16p-of-mv-nth-1-rme16
    :hyp (x86p x86)
    :bound 16
    :concl (mv-nth 1 (rme16 eff-addr seg-reg r-x x86))
    :gen-linear t
    :gen-type t)

  (defrule rme16-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (rme16 eff-addr seg-reg r-x x86)
                    (rml16 eff-addr r-x x86)))))

(define rime16
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   x86)
  :returns (mv flg
               (byte (signed-byte-p 16 byte) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Read a signed (16-bit) word from memory via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('riml16') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86)))
    (riml16 lin-addr r-x x86))
  :inline t
  ///

  (defthm-sb i16p-of-mv-nth-1-rime16
    :hyp (x86p x86)
    :bound 16
    :concl (mv-nth 1 (rime16 eff-addr seg-reg r-x x86))
    :gen-linear t
    :gen-type t)

  (defrule rime16-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (rime16 eff-addr seg-reg r-x x86)
                    (riml16 eff-addr r-x x86)))))

(define wme16
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (unsigned-byte 16))
   x86)
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Write an unsigned (16-bit) word to memory via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('wml16') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86)))
    (wml16 lin-addr val x86))
  :inline t
  ///

  (defrule wme16-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (wme16 eff-addr seg-reg val x86)
                    (wml16 eff-addr val x86)))))

(define wime16
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (signed-byte 16))
   x86)
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Write a signed (16-bit) word to memory via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('wiml16') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86)))
    (wiml16 lin-addr val x86))
  :inline t
  ///

  (defrule wime16-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (wime16 eff-addr seg-reg val x86)
                    (wiml16 eff-addr val x86)))))

;; ======================================================================

; read and write long words:

(define rme32
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   x86)
  :returns (mv flg
               (word (unsigned-byte-p 32 word) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Read an unsigned (32-bit) long word from memory
          via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('rml32') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86)))
    (rml32 lin-addr r-x x86))
  :inline t
  ///

  (defthm-usb n32p-of-mv-nth-1-rme32
    :hyp (x86p x86)
    :bound 32
    :concl (mv-nth 1 (rme32 eff-addr seg-reg r-x x86))
    :gen-linear t
    :gen-type t)

  (defrule rme32-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (rme32 eff-addr seg-reg r-x x86)
                    (rml32 eff-addr r-x x86)))))

(define rime32
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   x86)
  :returns (mv flg
               (byte (signed-byte-p 32 byte) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Read a signed (32-bit) long word from memory
          via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('riml32') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86)))
    (riml32 lin-addr r-x x86))
  :inline t
  ///

  (defthm-sb i32p-of-mv-nth-1-rime32
    :hyp (x86p x86)
    :bound 32
    :concl (mv-nth 1 (rime32 eff-addr seg-reg r-x x86))
    :gen-linear t
    :gen-type t)

  (defrule rime32-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (rime32 eff-addr seg-reg r-x x86)
                    (riml32 eff-addr r-x x86)))))

(define wme32
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (unsigned-byte 32))
   x86)
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Write an unsigned (32-bit) long word to memory
          via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('wml32') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86)))
    (wml32 lin-addr val x86))
  :inline t
  ///

  (defrule wme32-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (wme32 eff-addr seg-reg val x86)
                    (wml32 eff-addr val x86)))))

(define wime32
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (signed-byte 32))
   x86)
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Write a signed (32-bit) long word to memory
          via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('wiml32') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86)))
    (wiml32 lin-addr val x86))
  :inline t
  ///

  (defrule wime32-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (wime32 eff-addr seg-reg val x86)
                    (wiml32 eff-addr val x86)))))

;; ======================================================================

; read and write 48-bit values:

(define rme48
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   x86)
  :returns (mv flg
               (word (unsigned-byte-p 48 word) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Read an unsigned 48-bit value from memory via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('rml48') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86)))
    (rml48 lin-addr r-x x86))
  :inline t
  ///

  (defthm-usb n48p-of-mv-nth-1-rme48
    :hyp (x86p x86)
    :bound 48
    :concl (mv-nth 1 (rme48 eff-addr seg-reg r-x x86))
    :gen-linear t
    :gen-type t)

  (defrule rme48-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (rme48 eff-addr seg-reg r-x x86)
                    (rml48 eff-addr r-x x86)))))

(define wme48
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (unsigned-byte 48))
   x86)
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Write an unsigned 48-bit value to memory via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('wml48') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86)))
    (wml48 lin-addr val x86))
  :inline t
  ///

  (defrule wme48-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (wme48 eff-addr seg-reg val x86)
                    (wml48 eff-addr val x86)))))

;; ======================================================================

; read and write quad words:

(define rme64
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   x86)
  :returns (mv flg
               (word (unsigned-byte-p 64 word) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Read an unsigned (64-bit) quad word from memory
          via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('rml64') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86)))
    (rml64 lin-addr r-x x86))
  :inline t
  ///

  (defthm-usb n64p-of-mv-nth-1-rme64
    :hyp (x86p x86)
    :bound 64
    :concl (mv-nth 1 (rme64 eff-addr seg-reg r-x x86))
    :gen-linear t
    :gen-type t)

  (defrule rme64-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (rme64 eff-addr seg-reg r-x x86)
                    (rml64 eff-addr r-x x86)))))

(define rime64
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   x86)
  :returns (mv flg
               (byte (signed-byte-p 64 byte) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Read a signed (64-bit) quad word from memory
          via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('riml64') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86)))
    (riml64 lin-addr r-x x86))
  :inline t
  ///

  (defthm-sb i64p-of-mv-nth-1-rime64
    :hyp (x86p x86)
    :bound 64
    :concl (mv-nth 1 (rime64 eff-addr seg-reg r-x x86))
    :gen-linear t
    :gen-type t)

  (defrule rime64-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (rime64 eff-addr seg-reg r-x x86)
                    (riml64 eff-addr r-x x86)))))

(define wme64
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (unsigned-byte 64))
   x86)
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Write an unsigned (64-bit) quad word to memory
          via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('wml64') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86)))
    (wml64 lin-addr val x86))
  :inline t
  ///

  (defrule wme64-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (wme64 eff-addr seg-reg val x86)
                    (wml64 eff-addr val x86)))))

(define wime64
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (signed-byte 64))
   x86)
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Write a signed (64-bit) quad word to memory
          via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('wiml64') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86)))
    (wiml64 lin-addr val x86))
  :inline t
  ///

  (defrule wime64-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (wime64 eff-addr seg-reg val x86)
                    (wiml64 eff-addr val x86)))))

;; ======================================================================

; read and write 80-bit values:

(define rme80
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   x86)
  :returns (mv flg
               (word (unsigned-byte-p 80 word) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Read an unsigned 80-bit value from memory via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('rml80') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86)))
    (rml80 lin-addr r-x x86))
  :inline t
  ///

  (defthm-usb n80p-of-mv-nth-1-rme80
    :hyp (x86p x86)
    :bound 80
    :concl (mv-nth 1 (rme80 eff-addr seg-reg r-x x86))
    :gen-linear t
    :gen-type t)

  (defrule rme80-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (rme80 eff-addr seg-reg r-x x86)
                    (rml80 eff-addr r-x x86)))))

(define wme80
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (unsigned-byte 80))
   x86)
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Write an unsigned 80-bit value to memory via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('wml80') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86)))
    (wml80 lin-addr val x86))
  :inline t
  ///

  (defrule wme80-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (wme80 eff-addr seg-reg val x86)
                    (wml80 eff-addr val x86)))))

;; ======================================================================

; read and write 128-bit values:

(define rme128
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   x86)
  :returns (mv flg
               (word (unsigned-byte-p 128 word) :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Read an unsigned 128-bit value from memory via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('rml128') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86)))
    (rml128 lin-addr r-x x86))
  :inline t
  ///

  (defthm-usb n128p-of-mv-nth-1-rme128
    :hyp (x86p x86)
    :bound 128
    :concl (mv-nth 1 (rme128 eff-addr seg-reg r-x x86))
    :gen-linear t
    :gen-type t)

  (defrule rme128-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (rme128 eff-addr seg-reg r-x x86)
                    (rml128 eff-addr r-x x86)))))

(define wme128
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (unsigned-byte 128))
   x86)
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Write an unsigned 128-bit value to memory via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('wml128') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86)))
    (wml128 lin-addr val x86))
  :inline t
  ///

  (defrule wme128-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (wme128 eff-addr seg-reg val x86)
                    (wml128 eff-addr val x86)))))

;; ======================================================================

; read and write values of specified number of bytes:

(define rme-size
  ((nbytes :type (member 1 2 4 6 8 10 16))
   (eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   x86)
  :returns (mv flg
               (value natp :hyp (x86p x86))
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Read an unsigned value with the specified number of bytes
          from memory via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('rml-size') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86)))
    (rml-size nbytes lin-addr r-x x86))
  :inline t
  ///

  (defrule rme-size-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (rme-size nbytes eff-addr seg-reg r-x x86)
                    (rml-size nbytes eff-addr r-x x86)))))

(define rime-size
  ((nbytes :type (member 1 2 4 8))
   (eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   x86)
  :returns (mv flg
               (value integerp :hyp (and (x86p x86) (integerp nbytes)))
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Read a signed value with the specified number of bytes
          from memory via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('riml-size') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) 0 x86)))
    (riml-size nbytes lin-addr r-x x86))
  :inline t
  ///

  (defrule rime-size-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (rime-size nbytes eff-addr seg-reg r-x x86)
                    (riml-size nbytes eff-addr r-x x86)))))

(define wme-size
  ((nbytes :type (member 1 2 4 6 8 10 16))
   (eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (integer 0 *))
   x86)
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
  :parents (x86-top-level-memory)
  :short "Write an unsigned value with the specified number of bytes
          to memory via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('wml-size') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86)))
    (wml-size nbytes lin-addr val x86))
  :inline t
  ///

  (defrule wme-size-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (wme-size nbytes eff-addr seg-reg val x86)
                    (wml-size nbytes eff-addr val x86)))))

(define wime-size
  ((nbytes :type (member 1 2 4 8))
   (eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type integer)
   x86)
  :guard (case nbytes
           (1  (i08p val))
           (2  (i16p val))
           (4  (i32p val))
           (8  (i64p val)))
  :returns (mv flg
               (x86-new x86p :hyp (x86p x86)))
  :parents (x86-top-level-memory)
  :short "Write a signed value with the specified number of bytes
          to memory via an effective address."
  :long
  "<p>
   The effective address is translated to a linear address
   and then @('wiml-size') is called.
   If the resulting linear address is not canonical,
   an error occurs.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86))
       ((unless (canonical-address-p lin-addr))
        (mv (list :non-canonical-address lin-addr) x86)))
    (wiml-size nbytes lin-addr val x86))
  :inline t
  ///

  (defrule wime-size-when-64-bit-modep-and-not-fs/gs
    (implies (and (64-bit-modep x86)
                  (not (equal seg-reg *fs*))
                  (not (equal seg-reg *gs*))
                  (canonical-address-p eff-addr))
             (equal (wime-size nbytes eff-addr seg-reg val x86)
                    (wiml-size nbytes eff-addr val x86)))))
