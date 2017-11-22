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

(define rme08
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   x86)
  :returns (mv flg
               (byte (unsigned-byte-p 8 byte) :hyp :guard)
               x86)
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
  :guard-hints (("Goal" :in-theory (enable ea-to-la)))
  :inline t
  ///

  (defthm-usb n08p-of-mv-nth-1-rme08
    :hyp (x86p x86)
    :bound 8
    :concl (mv-nth 1 (rme08 eff-addr seg-reg r-x x86))
    :gen-linear t
    :gen-type t)

  (defrule x86p-rme08
    (implies (x86p x86)
             (x86p (mv-nth 2 (rme08 eff-addr seg-reg r-x x86)))))

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
    :enable (ea-to-la x86-segment-base-and-bounds))

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
               (byte (signed-byte-p 8 byte) :hyp :guard)
               x86)
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
  :guard-hints (("Goal" :in-theory (enable ea-to-la)))
  :inline t)

(define wme08
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (unsigned-byte 8))
   x86)
  :returns (mv flg x86)
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
  :guard-hints (("Goal" :in-theory (enable ea-to-la)))
  :inline t)

(define wime08
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (val :type (signed-byte 8))
   x86)
  :returns (mv flg x86)
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
  :guard-hints (("Goal" :in-theory (enable ea-to-la)))
  :inline t)

;; ======================================================================
