;; Author: Alessandro Coglio <coglio@kestrel.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "x86-decoding-and-spec-utils")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

(defxdoc x86-segmentation
  :parents (machine)
  :short "Specification of segmentation."
  :long
  "<p>
   This includes the translation of effective addresses to linear addresses
   and functions to read and write memory via effective addresses.
   </p>
   <p>
   This topic should be merged with the @(tsee ia32e-segmentation) topic.
   </p>")

(define x86-segment-base-and-bounds
  ((seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   x86)
  :returns (mv (base n32p) (lower-bound n33p) (upper-bound n32p))
  :parents (x86-segmentation)
  :short "Return a segment's base linear address, lower bound, and upper bound."
  :long
  "<p>
   The segment is the one in the given segment register.
   </p>
   <p>
   Even though @('*hidden-segment-register-layout*') uses 64 bits
   for the segment base address,
   addresses coming from segment descriptors are always 32 bits:
   see Intel manual, Mar'17, Vol. 3A, Sec. 3.4.5
   and AMD manual, Apr'16, Vol. 2, Sec. 4-7 and 4-8.
   Thus, this function returns an unsigned 32-bit integer as the base result.
   As an optimization, in 64-bit mode,
   since segment bases for CS, DS, SS, and ES are ignored,
   this function just returns 0 as the base result under these conditions.
   </p>
   <p>
   @('*hidden-segment-register-layout*') uses 32 bits
   for the segment limit,
   which is consistent with the 20 bits in segment descriptors
   when the G (granularity) bit is 1:
   see Intel manual, Mar'17, Vol. 3A, Sec. 3.4.5
   and AMD manual, Apr'16, Vol. 2, Sec. 4-7 and 4-8.
   Thus, the limit is an unsigned 32-bit integer.
   </p>
   <p>
   The lower bound is 0 for code segments, i.e. for the CS register.
   For data (including stack) segments,
   i.e. for the SS, DS, ES, FS, and GS registers,
   the lower bound depends on the E bit:
   if E is 0, the lower bound is 0;
   if E is 1, the segment is an expand-down data segment
   and the lower bound is one plus the segment limit.
   See Intel manual, Mar'17, Vol. 3A, Sec. 3.4.5
   and AMD manual, Apr'16, Vol. 2, Sec. 4.7 and 4-8.
   Since the limit is an unsigned 32-bit (see above),
   adding 1 may produce an unsigned 33-bit result.
   Even though this should not actually happen with well-formed segments,
   this function returns an unsigned 33-bit integer as the lower bound result.
   As an optimization, in 64-bit mode,
   since segment limits and bounds are ignored,
   this function returns 0 as the lower bound;
   the caller must ignore this result in 64-bit mode.
   </p>
   <p>
   The upper bound is the segment limit for code segments,
   i.e. for the CS register.
   For data (including stack) segments,
   i.e. for the SS, DS, ES, FS, and GS registers,
   the upper bound depends on the E and D/B bits:
   if E is 0, the upper bound is the segment limit;
   if E is 1, the segment is an expand-down data segment
   and the upper bound is 2^32-1 if D/B is 1, 2^16-1 if D/B is 0.
   See Intel manual, Mar'17, Vol. 3A, Sec. 3.4.5
   and AMD manual, Apr'16, Vol. 2, Sec. 4.7 and 4-8.
   Since  the limit is an unsigned 32-bit (see above),
   this function returns an unsigned 32-bit integer as the upper bound result.
   As an optimization, in 64-bit mode,
   since segment limits and bounds are ignored,
   this function returns 0 as the upper bound;
   the caller must ignore this result in 64-bit mode.
   </p>"
  (if (64-bit-modep x86)
      (if (or (eql seg-reg *fs*)
              (eql seg-reg *gs*))
          (b* ((hidden (xr :seg-hidden seg-reg x86))
               (base (hidden-seg-reg-layout-slice :base-addr hidden)))
            (mv (n32 base) 0 0))
        (mv 0 0 0))
    (b* ((hidden (xr :seg-hidden seg-reg x86))
         (base (hidden-seg-reg-layout-slice :base-addr hidden))
         (limit (hidden-seg-reg-layout-slice :limit hidden))
         (attr (hidden-seg-reg-layout-slice :attr hidden))
         (d/b (data-segment-descriptor-attributes-layout-slice :d/b attr))
         (e (data-segment-descriptor-attributes-layout-slice :e attr))
         (lower (if e (1+ limit) 0))
         (upper (if e (if d/b #xffffffff #xffff) limit)))
      (mv (n32 base) lower upper))))

(define ea-to-la
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   x86)
  :returns (mv flg (lin-addr i48p))
  :parents (x86-segmentation)
  :short "Translate an effective address to a linear address."
  :long
  "<p>
   This translation is illustrated in Intel manual, Mar'17, Vol. 3A, Fig. 3-5,
   as well in AMD mamual, Oct'2013, Vol. 1, Fig. 2-3 and 2-4.
   In addition to the effective address,
   this function takes as input (the index of) a segment register,
   whose corresponding segment selector, with the effective address,
   forms the logical address that is turned into the linear address.
   </p>
   <p>
   This translation is used:
   when fetching instructions,
   in which case the effective address is in RIP, EIP, or IP;
   when accessing the stack implicitly,
   in which case the effective address is in RSP, ESP, or SP;
   and when accessing data explicitly,
   in which case the effective address is calculated by instructions
   via @(tsee x86-effective-addr).
   In the formal model,
   RIP contains a signed 48-bit integer,
   RSP contains a signed 64-bit integer,
   and @(tsee x86-effective-addr) returns a signed 64-bit integer:
   thus, the guard of this function requires @('eff-addr')
   to be a signed 64-bit integer.
   In 64-bit mode, the caller of this function supplies as @('eff-addr')
   the content of RIP,
   the content of RSP,
   or the result of @(tsee x86-effective-address).
   In 32-bit mode, the caller of this function supplies as @('eff-addr')
   the unsigned 32-bit or 16-bit truncation of
   the content of RIP (i.e. EIP or IP),
   the content of RSP (i.e. ESP or SP),
   or the result of @(tsee x86-effective-address);
   the choice between 32-bit and 16-bit is determined by
   default address size and override prefixes.
   </p>
   <p>
   In 32-bit mode, the effective address is checked against
   the lower and upper bounds of the segment.
   In 64-bit mode, this check is skipped.
   </p>
   <p>
   In 32-bit mode,
   the effective address is added to the base address of the segment;
   the result is truncated to 32 bits, in case;
   this truncation should not actually happen with well-formed segments.
   In 64-bit mode,
   the addition of the base address of the segment is performed
   only if the segments are in registers FS and GS;
   the result is truncated to 64 bits, in case;
   this truncation should not actually happen with well-formed segments.
   </p>
   <p>
   If the translation is successful,
   this function returns a signed 48-bit integer
   that represents a canonical linear address.
   In 64-bit mode, the 64-bit linear address that results from the translation
   is checked to be canonical before returning it.
   In 32-bit mode, the 32-bit linear address that results from the translation
   is always canonical.
   If the translation fails,
   including the check that the linear address is canonical,
   a non-@('nil') error flag is returned,
   which provides some information about the failure.
   </p>"
  (if (64-bit-modep x86)
      (if (or (eql seg-reg *fs*)
              (eql seg-reg *gs*))
          (b* (((mv base & &) (x86-segment-base-and-bounds seg-reg x86))
               (lin-addr (i64 (+ base (n64 eff-addr)))))
            (if (canonical-address-p lin-addr)
                (mv nil lin-addr)
              (mv (list :non-canonical-address lin-addr) 0)))
        (mv nil (i48 eff-addr)))
    (b* (((mv base
              lower-bound
              upper-bound) (x86-segment-base-and-bounds seg-reg x86))
         ((unless (and (<= lower-bound eff-addr)
                       (<= eff-addr upper-bound)))
          (mv (list :segment-limit-fail
                    (list seg-reg eff-addr lower-bound upper-bound))
              0))
         (lin-addr (n32 (+ base eff-addr))))
      (mv nil lin-addr)))
  :guard-hints (("Goal" :in-theory (enable x86-segment-base-and-bounds))))

(define rme08
  ((eff-addr i64p)
   (seg-reg (integer-range-p 0 *segment-register-names-len* seg-reg))
   (r-x :type (member :r :x))
   x86)
  :returns (mv flg
               (byte (unsigned-byte-p 8 byte) :hyp :guard)
               x86)
  :parents (x86-segmentation)
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
  :parents (x86-segmentation)
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
  :parents (x86-segmentation)
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
  :parents (x86-segmentation)
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
