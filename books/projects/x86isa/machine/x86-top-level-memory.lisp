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
   and then @('rm08') is called.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86)))
    (rm08 lin-addr r-x x86))
  :guard-hints (("Goal" :in-theory (enable ea-to-la))))

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
   and then @('rim08') is called.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg 0 x86)))
    (rim08 lin-addr r-x x86))
  :guard-hints (("Goal" :in-theory (enable ea-to-la))))

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
   and then @('wm08') is called.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86)))
    (wm08 lin-addr val x86))
  :guard-hints (("Goal" :in-theory (enable ea-to-la))))

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
   and then @('wim08') is called.
   </p>"
  (b* (((mv flg lin-addr) (ea-to-la eff-addr seg-reg x86))
       ((when flg) (mv flg x86)))
    (wim08 lin-addr val x86))
  :guard-hints (("Goal" :in-theory (enable ea-to-la))))

;; ======================================================================
