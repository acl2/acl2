;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "x86-rflags-spec")
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
; Instruction to cert.pl for dependency tracking.
; (depends-on "x86-register-readers-and-writers-raw.lsp")

;; ======================================================================

(defsection x86-register-readers-and-writers
  :parents (machine)
  :short "Top-level utilities for reading and writing into various
  registers"
  )

;; ======================================================================

;; Some arithmetic theorems that will be used in all books higher up
;; (especially for proving away MBEs):

(encapsulate
 ()

 (local
  (include-book "arithmetic-5/top" :dir :system))

 (defun power-of-2p-measure (x)
   (cond ((or (not (natp x))
              (<= x 1))
          0)
         (t (floor x 1))))

 (defn is-power-of-2p (x)
   (declare (xargs :measure (power-of-2p-measure x)))
   (if (natp x)
       (if (<= x 1)
           t
         (is-power-of-2p (* 1/2 x)))
     nil))

 (local
  (set-default-hints
   '((acl2::nonlinearp-default-hint++ acl2::id acl2::stable-under-simplificationp
                                      acl2::hist nil))))

 (defthm ash-bounds-with-powers-of-two
   ;; A general ash bounds theorem
   (implies (and (integerp i)
                 (<= 0 i)
                 (equal 2-to-x (* 2-to-x-y (expt 2 y)))
                 (< i 2-to-x)
                 (syntaxp (quotep 2-to-x))
                 (is-power-of-2p 2-to-x)
                 (< (expt 2 y) 2-to-x)
                 (syntaxp (quotep y))
                 (syntaxp (quotep 2-to-x-y))
                 (integerp y)
                 (<= 0 y))
            (< (ash i (- y)) 2-to-x-y))
   :rule-classes :rewrite)

 ) ;; End of encapsulate

(local
 (defun my-induct (x y)
   (if (and (natp x)
            (natp y))
       (if (zp x)
           y
         (if (zp y)
             x
           (my-induct (logcdr x) (logcdr y))))
     nil)))

(defthm integer-length-of-logior-of-natp
  (implies (and (natp x)
                (natp y)
                (<= (integer-length x) (integer-length y)))
           (equal (integer-length (logior x y))
                  (integer-length y)))
  :hints (("Goal" :induct (my-induct x y)
           :in-theory (e/d (acl2::integer-length**)
                           (integer-length)))))

(defthm integer-length-and-loghead-when-natp-identity-theorem
  (implies (natp x)
           (equal (loghead (integer-length x) x)
                  x))
  :hints (("Goal" :in-theory (e/d* (acl2::loghead** acl2::integer-length**
                                                    acl2::ihsext-inductions)
                                   ((force))))))

(defthm mod-expt-and-integer-length-identity-theorem
  (implies (natp x)
           (equal (mod x (expt 2 (integer-length x)))
                  x))
  :hints (("Goal" :in-theory (e/d* (acl2::ihsext-arithmetic)
                                   (bitops::ash-1-removal)))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 ;; The following are useful for MBE kind of proofs.  Be careful when
 ;; using them though; sometimes, they might cause loops when enabled
 ;; alongside logand-with-negated-bitmask and
 ;; logand-with-bitmask.

 (defthmd negative-logand-to-positive-logand-with-natp-x
   (implies (and (syntaxp (and (quotep n)
                               (let* ((n-abs (acl2::unquote n)))
                                 (< n-abs 0))))
                 (equal m (integer-length x))
                 (integerp n)
                 (natp x))
            (equal (logand n x)
                   (logand (logand (1- (ash 1 m)) n) x))))

 (defun find-best-fitting-m (n)
   (if (signed-byte-p 8 (acl2::unquote n))
       (list (list (cons 'm ''8))
             (list (cons 'm ''16))
             (list (cons 'm ''32))
             (list (cons 'm ''64)))
     (if (signed-byte-p 16 (acl2::unquote n))
         (list (list (cons 'm ''16))
               (list (cons 'm ''32))
               (list (cons 'm ''64)))
       (if (signed-byte-p 32 (acl2::unquote n))
           (list (list (cons 'm ''32))
                 (list (cons 'm ''64)))
         (list (list (cons 'm ''64)))))))

 (defthm negative-logand-to-positive-logand-with-integerp-x
   (implies (and (syntaxp (and (quotep n)
                               (let* ((n-abs (acl2::unquote n)))
                                 (< n-abs 0))))
                 (bind-free (find-best-fitting-m n) (m))
                 (unsigned-byte-p m x)
                 (integerp n))
            (equal (logand n x)
                   (logand (logand (1- (ash 1 m)) n) x))))

 (defthmd loghead-to-logand
   ;; This rule causes loop when used alongside
   ;; bitops::logand-with-bitmask and bitops::logand-with-negated-bitmask.
   (implies (and (natp n)
                 (syntaxp (quotep n))
                 (integerp x))
            (equal (loghead n x)
                   (logand (1- (expt 2 n)) x)))
   :hints (("Goal" :in-theory (e/d (loghead) ()))))

 (defthm logand-redundant
   (implies (and (unsigned-byte-p n x)
                 (equal width (1- (ash 1 n)))
                 (syntaxp (quotep width)))
            (equal (logand width x)
                   x)))

 )

;; ======================================================================

(defsection GPR-indices

  :parents (x86-register-readers-and-writers)

  :short "Functions that enable the use of extended GPRs using the
  @('rex') byte"

  (local (xdoc::set-default-parents GPR-indices))

  (define reg-indexp
    ((reg)
     (rex-byte :type (unsigned-byte 8)))
    :short "Valid GPR index recognizer"
    :long "<p>General purpose register indices are 3 bits except in
64-bit mode, where they can have 4 bits depending on the @('rex')
prefix.</p>"
    :enabled t
    (if (eql rex-byte 0)
        (n03p reg)
      (n04p reg))

    ///

    (defthm reg-indexp-for-3-bits
      (implies (and (syntaxp (quotep reg))
                    (n03p reg))
               (reg-indexp reg rex)))

    (defthm reg-indexp-logand-7
      (implies (n08p rex-byte)
               (reg-indexp (loghead 3 modr/m) rex-byte))
      :hints (("Goal" :in-theory (enable reg-indexp)))))

  (define reg-index
    ((reg      :type (unsigned-byte 3))
     (rex-byte :type (unsigned-byte 8))
     (index    :type (unsigned-byte 2)))
    :inline t
    (if (logbitp index rex-byte)
        (logior 8 (mbe :logic (n03 reg) :exec reg))
      (mbe :logic (n03 reg) :exec reg))

    ///

    (local (in-theory (e/d (reg-indexp) ())))

    (defthm reg-indexp-reg-index
      (reg-indexp (reg-index reg rex-byte name) rex-byte))

    (defthm-usb n04p-reg-index
      :hyp t
      :bound 4
      :concl (reg-index reg rex-byte name)
      :gen-linear t
      :gen-type t)

    (defthm reg-indexp-forward
      (implies (reg-indexp reg rex-byte)
               (n04p reg))
      :rule-classes :forward-chaining))

  )

;; ======================================================================

;; [Jared] these rules broke something below
(local (in-theory (disable BITOPS::LOGEXT-OF-LOGAND
                           BITOPS::LOGEXT-OF-LOGIOR)))

(defsection GPRs-Reads-and-Writes

  :parents (x86-register-readers-and-writers)

  :short "Functions to read/write 8/16/32/64 bits into the registers"

  :long "<p>@(see rr08), @(see rr16), @(see rr32), and @(see rr64)
will read the contents of the GPRs as natural numbers. Remember that
@('rgfi') will return an @(see i64p) value.</p>

<p>Here is an example:</p>
<br/>
<tt>
\(!rgfi 0 -1 x86\) ;; Write -1 to register 0
</tt>

<p><tt>\(rr64 0 x86\)</tt> returns @('18446744073709551615') and
<tt>(rgfi 0 x86)</tt> returns @('0').  Note that
@('18446744073709551615') is a bignum in CCL. This is precisely the
reason why we declared registers as @('i64p') instead of @('n64p');
@('-1') would be stored as a bignum if the registers were
@('n64p'). </p>

<p>Similarly, @(see wr08), @(see wr16), @(see wr32), and @(see wr64)
are used to write natural numbers into the GPRs.</p>"

  (local (xdoc::set-default-parents GPRs-Reads-and-Writes))

  (define rr08
    ((reg :type (unsigned-byte 4))
     (rex :type (unsigned-byte 8))
     (x86))
    :inline t
    :guard (reg-indexp reg rex)

    (cond ((or (not (eql rex 0))
               (< reg 4))
           (let ((qword (the (signed-byte 64) (rgfi reg x86))))
             (n08 qword)))
          (t ;; no rex and reg is at least 4 -- then read from AH, etc.
           (let ((qword
                  (the (signed-byte 64) (rgfi (the (unsigned-byte 4) (- reg 4)) x86))))
             (mbe :logic (part-select qword :low 8 :width 8)
                  :exec (n08 (ash qword -8))))))

    ///

    (defthm-usb n08p-rr08
      :hyp t
      :bound 8
      :concl (rr08 reg rex x86)
      :gen-linear t
      :gen-type t))

  (define rr16
    ((reg :type (unsigned-byte 4))
     (x86))
    :inline t

    (n16 (the (signed-byte 64) (rgfi reg x86)))

    ///

    (defthm-usb n16p-rr16
      :hyp t
      :bound 16
      :concl (rr16 reg x86)
      :gen-linear t
      :gen-type t))

  (define rr32
    ((reg :type (unsigned-byte 4))
     (x86))
    :inline t

    (n32 (the (signed-byte 64) (rgfi reg x86)))

    ///

    (defthm-usb n32p-rr32
      :hyp t
      :bound 32
      :concl (rr32 reg x86)
      :gen-linear t
      :gen-type t))

  (define rr64
    ((reg :type (unsigned-byte 4))
     (x86))
    :inline t

    (n64 (the (signed-byte 64) (rgfi reg x86)))

    ///

    (defthm-usb n64p-rr64
      :hyp t
      :bound 64
      :concl (rr64 reg x86)
      :gen-linear t
      :gen-type t))

  (define wr08
    ((reg  :type (unsigned-byte 4))
     (rex  :type (unsigned-byte 8))
     (byte :type (unsigned-byte 8))
     (x86))
    :inline t
    :guard (reg-indexp reg rex)
    :guard-hints (("Goal" :in-theory (e/d (
                                           loghead-to-logand
                                           bitops::logsquash)
                                          (bitops::logand-with-negated-bitmask
                                           bitops::logand-with-bitmask
                                           unsigned-byte-p))))

    (cond ((or (not (eql rex 0))
               (< reg 4))
           (let ((qword (the (signed-byte 64) (rgfi reg x86))))
             (!rgfi reg
                    (n64-to-i64
                     (mbe :logic
                          (part-install
                           byte
                           (part-select qword :low 0 :width 64)
                           :low 0 :width 8)
                          :exec
                          (the (unsigned-byte 64)
                            (logior (the (unsigned-byte 64)
                                      (logand #xffffffffffffff00 qword))
                                    byte))))
                    x86)))
          (t ;; no rex and reg is at least 4 -- then write to AH, etc.
           (let* ((index (the (unsigned-byte 4)
                           (- (the (unsigned-byte 4) reg) 4)))
                  (qword (the (signed-byte 64) (rgfi index x86))))
             (!rgfi index
                    (n64-to-i64
                     (mbe :logic
                          (part-install
                           byte
                           (part-select qword :low 0 :width 64)
                           :low 8 :width 8)
                          :exec
                          (the (unsigned-byte 64)
                            (logior (the (unsigned-byte 64)
                                      (logand #xffffffffffff00ff qword))
                                    (the (unsigned-byte 16) (ash byte 8))))))
                    x86))))

    ///

    (defthm x86p-wr08
      (implies (and (x86p x86)
                    (natp reg))
               (x86p (wr08 reg rex byte x86)))))

  (encapsulate
   ()

   (local
    (include-book "arithmetic-5/top" :dir :system))

   (defthm loghead-logtail-logext-for-rr08/wr08
     (implies (integerp x)
              (equal (loghead 8 (logtail 8 (logext 64 x)))
                     (loghead 8 (logtail 8 x))))
     :hints (("Goal" :in-theory
              (e/d (logtail evenp oddp logbitp logext loghead logapp)
                   ())))))

  (defthm rr08-wr08-same
    (implies (n08p byte)
             (equal (rr08 reg rex
                          (wr08 reg rex byte x86))
                    byte))
    :hints (("Goal"
             :in-theory (e/d (n64-to-i64
                              rr08 wr08)
                             (unsigned-byte-p)))))

  (defthm rr08-wr08-different
    (implies (and (n08p byte)
                  (not (equal reg1 reg2)))
             (equal (rr08 reg1 rex1
                          (wr08 reg2 rex2 byte x86))
                    (rr08 reg1 rex1 x86)))
    :hints (("Goal"
             :in-theory (e/d (n64-to-i64 rr08 wr08)
                             ()))))

  (define wr16
    ((reg  :type (unsigned-byte 4))
     (val  :type (unsigned-byte 16))
     (x86))
    :inline t
    :guard-hints (("Goal" :in-theory (e/d (
                                           loghead-to-logand
                                           bitops::logsquash)
                                          (bitops::logand-with-negated-bitmask
                                           bitops::logand-with-bitmask
                                           unsigned-byte-p))))

    (let ((qword (the (signed-byte 64) (rgfi reg x86))))
      (!rgfi reg
             (n64-to-i64
              (mbe :logic
                   (part-install
                    val
                    (part-select qword :low 0 :width 64)
                    :low 0 :width 16)
                   :exec
                   (the (unsigned-byte 64)
                     (logior (the (unsigned-byte 64)
                               (logand qword #xffffffffffff0000))
                             val))))
             x86))

    ///

    (defthm x86p-wr16
      (implies (and (x86p x86)
                    (natp reg))
               (x86p (wr16 reg val x86)))))

  (defthm rr16-wr16-same
    (implies (n16p val)
             (equal (rr16 reg (wr16 reg val x86))
                    val))
    :hints (("Goal"
             :in-theory (e/d (n64-to-i64
                              rr16 wr16)
                             (unsigned-byte-p force (force))))))

  (defthm rr16-wr16-different
    (implies (and (n16p val)
                  (not (equal reg1 reg2)))
             (equal (rr16 reg1 (wr16 reg2 val x86))
                    (rr16 reg1 x86)))
    :hints (("Goal"
             :in-theory (e/d (n64-to-i64 rr16 wr16)
                             (force (force))))))

  (define wr32
    ((reg  :type (unsigned-byte  4))
     (val  :type (unsigned-byte 32))
     (x86))
    :inline t
    :guard-hints (("Goal" :in-theory (e/d (
                                           loghead-to-logand
                                           bitops::logsquash)
                                          (bitops::logand-with-negated-bitmask
                                           bitops::logand-with-bitmask
                                           unsigned-byte-p))))

    :long "<p>Write a dword to a register.  Note Intel Vol. 1 Sec. 3.4.1.1
    p. 3-17, which says the following about 64-bit mode:</p>

    <p><em>32-bit operands generate a 32-bit result, zero-extended to a
    64-bit result in the destination general-purpose
    register.</em></p>

<p>Outside 64-bit mode, the upper 32 bits are undefined, as specified
by the following quote from the same page as above: </p>

<p><em>Because the upper 32 bits of 64-bit general-purpose registers
  are undefined in 32-bit modes, the upper 32 bits of any
  general-purpose register are not preserved when switching from
  64-bit mode to a 32-bit mode (to protected mode or compatibility
  mode). Software must not depend on these bits to maintain a value
  after a 64-bit to 32-bit mode switch.</em></p>"

    (!rgfi reg (mbe :logic (n32 val) :exec val) x86)

    ///

    (defthm x86p-wr32
      (implies (and (x86p x86)
                    (natp reg))
               (x86p (wr32 reg val x86)))))

  (defthm rr32-wr32-same
    (implies (n32p val)
             (equal (rr32 reg (wr32 reg val x86))
                    val))
    :hints (("Goal"
             :in-theory (e/d (n64-to-i64
                              rr32 wr32)
                             (unsigned-byte-p)))))

  (defthm rr32-wr32-different
    (implies (and (n32p val)
                  (not (equal reg1 reg2)))
             (equal (rr32 reg1 (wr32 reg2 val x86))
                    (rr32 reg1 x86)))
    :hints (("Goal"
             :in-theory (e/d (n64-to-i64 rr32 wr32)
                             ()))))

  (define wr64
    ((reg  :type (unsigned-byte  4))
     (val  :type (unsigned-byte 64))
     (x86))
    :inline t
    :guard-hints (("Goal" :in-theory (e/d (
                                           loghead-to-logand
                                           bitops::logsquash)
                                          (bitops::logand-with-negated-bitmask
                                           bitops::logand-with-bitmask
                                           unsigned-byte-p))))
    (!rgfi reg (n64-to-i64 val) x86)

    ///
    (defthm x86p-wr64
      (implies (and (x86p x86)
                    (natp reg))
               (x86p (wr64 reg val x86)))))

  (defthm rr64-wr64-same
    (implies (n64p val)
             (equal (rr64 reg (wr64 reg val x86))
                    val))
    :hints (("Goal"
             :in-theory (e/d (n64-to-i64
                              rr64 wr64)
                             (unsigned-byte-p)))))

  (defthm rr64-wr64-different
    (implies (and (n64p val)
                  (not (equal reg1 reg2)))
             (equal (rr64 reg1 (wr64 reg2 val x86))
                    (rr64 reg1 x86)))
    :hints (("Goal"
             :in-theory (e/d (n64-to-i64 rr64 wr64)
                             ()))))

  (define rgfi-size
    ((nbytes :type (unsigned-byte 4))
     (index  :type (unsigned-byte 4))
     (rex    :type (unsigned-byte 8))
     x86)
    :enabled t
    :guard (and (reg-indexp index rex)
                (member nbytes '(1 2 4 8)))
    :inline t
    :returns (val natp :rule-classes :type-prescription)
    (case nbytes
      (1 (rr08 index rex x86))
      (2 (rr16 index x86))
      (4 (rr32 index x86))
      (8 (rr64 index x86))
      (otherwise
       ;; This function shouldn't really be used in the case when nbytes
       ;; != 1, 2, 4, or 8.  Anyway, the guard says nbytes shouldn't be
       ;; anything else.
       0)))


  (define !rgfi-size
    ((nbytes :type (unsigned-byte 4))
     (index  :type (unsigned-byte 4))
     (val    :type integer)
     (rex    :type (unsigned-byte 8))
     x86)
    :enabled t
    :guard (and (reg-indexp index rex)
                (member nbytes '(1 2 4 8))
                (unsigned-byte-p (ash nbytes 3) val))
    :returns (x86 x86p :hyp (and (x86p x86) (natp index)))
    :inline t
    (case nbytes
      (1 (wr08 index rex val x86))
      (2 (wr16 index val x86))
      (4 (wr32 index val x86))
      (8 (wr64 index val x86))
      (otherwise
       ;; The guard says nbytes shouldn't be anything other than 1, 2,
       ;; 4, or 8.
       x86)))

  )

;; ======================================================================

(defsection XMMs-Reads-and-Writes

  :parents (x86-register-readers-and-writers)

  :short "Functions to read/write 32/64/128 bits into the XMM registers"

  :long "<p>@(see rx32), @(see rx64), and @(see rx128) will read the contents
of the XMMs as natural numbers.</p>

<p>Similarly, @(see wx32), @(see wx64), and @(see wx128)
are used to write natural numbers into the XMMs.</p>"

  (local (xdoc::set-default-parents XMMs-Reads-and-Writes))

  (define rx32
    ((reg :type (unsigned-byte 4))
     (x86))
    :inline t

    (n32 (the (unsigned-byte 128) (xmmi reg x86)))

    ///

    (defthm-usb n32p-rx32
      :hyp t
      :bound 32
      :concl (rx32 reg x86)
      :gen-linear t
      :gen-type t))

  (define rx64
    ((reg :type (unsigned-byte 4))
     (x86))
    :inline t

    (n64 (the (unsigned-byte 128) (xmmi reg x86)))

    ///

    (defthm-usb n64p-rx64
      :hyp t
      :bound 64
      :concl (rx64 reg x86)
      :gen-linear t
      :gen-type t))

  (define rx128
    ((reg :type (unsigned-byte 4))
     (x86))
    :inline t

    (mbe :logic (n128 (xmmi reg x86))
         :exec  (the (unsigned-byte 128) (xmmi reg x86)))

    ///

    (defthm-usb n128p-rx128
      :hyp t
      :bound 128
      :concl (rx128 reg x86)
      :hints (("Goal" :in-theory (disable xmmi-is-n128p)))
      :gen-linear t
      :gen-type t))

  (define wx32
    ((reg  :type (unsigned-byte  4))
     (val  :type (unsigned-byte 32))
     (x86))
    :inline t
    :guard-hints (("Goal" :in-theory (e/d (
                                           loghead-to-logand
                                           bitops::logsquash)
                                          (bitops::logand-with-negated-bitmask
                                           bitops::logand-with-bitmask
                                           unsigned-byte-p))))

    (let ((oword (the (unsigned-byte 128) (xmmi reg x86))))
      (!xmmi reg
             (mbe :logic
                  (part-install val
                                (part-select oword :low 0 :width 128)
                                :low 0 :width 32)
                  :exec
                  (the (unsigned-byte 128)
                       (logior (the (unsigned-byte 128)
                                    (logand oword #xffffffffffffffffffffffff00000000))
                               val)))
             x86))

    ///

    (defthm x86p-wx32
      (implies (and (x86p x86)
                    (natp reg))
               (x86p (wx32 reg val x86)))))

  (defthm rx32-wx32-same
    (implies (n32p val)
             (equal (rx32 reg (wx32 reg val x86))
                    val))
    :hints (("Goal"
             :in-theory (e/d (rx32 wx32
                              )
                             (xmmi-is-n128p
                              unsigned-byte-p)))))

  (defthm rx32-wx32-different
    (implies (not (equal reg1 reg2))
             (equal (rx32 reg1 (wx32 reg2 val x86))
                    (rx32 reg1 x86)))
    :hints (("Goal"
             :in-theory (e/d (rx32 wx32 )
                             (xmmi-is-n128p)))))

  (define wx64
    ((reg  :type (unsigned-byte  4))
     (val  :type (unsigned-byte 64))
     (x86))
    :inline t
    :guard-hints (("Goal" :in-theory (e/d (
                                           loghead-to-logand
                                           bitops::logsquash)
                                          (bitops::logand-with-negated-bitmask
                                           bitops::logand-with-bitmask
                                           unsigned-byte-p))))
    (let ((oword (the (unsigned-byte 128) (xmmi reg x86))))
      (!xmmi reg
             (mbe :logic
                  (part-install
                   val
                   (part-select oword :low 0 :width 128)
                   :low 0 :width 64)
                  :exec
                  (the (unsigned-byte 128)
                       (logior (the (unsigned-byte 128)
                                    (logand oword #xffffffffffffffff0000000000000000))
                               val)))
             x86))

    ///
    (defthm x86p-wx64
      (implies (and (x86p x86)
                    (natp reg))
               (x86p (wx64 reg val x86)))))

  (defthm rx64-wx64-same
    (implies (n64p val)
             (equal (rx64 reg (wx64 reg val x86))
                    val))
    :hints (("Goal"
             :in-theory (e/d (rx64 wx64
                              )
                             (xmmi-is-n128p
                              unsigned-byte-p)))))

  (defthm rx64-wx64-different
    (implies (not (equal reg1 reg2))
             (equal (rx64 reg1 (wx64 reg2 val x86))
                    (rx64 reg1 x86)))
    :hints (("Goal"
             :in-theory (e/d (rx64 wx64 )
                             (xmmi-is-n128p)))))

  (define wx128
    ((reg  :type (unsigned-byte 4))
     (val  :type (unsigned-byte 128))
     (x86))
    :inline t
    :guard-hints (("Goal" :in-theory (e/d (
                                           loghead-to-logand
                                           bitops::logsquash)
                                          (bitops::logand-with-negated-bitmask
                                           bitops::logand-with-bitmask
                                           unsigned-byte-p))))

    (!xmmi reg (mbe :logic (n128 val)
                    :exec  val)
           x86)

    ///

    (defthm x86p-wx128
      (implies (and (x86p x86)
                    (natp reg))
               (x86p (wx128 reg val x86)))))

  (defthm rx128-wx128-same
    (implies (n128p val)
             (equal (rx128 reg (wx128 reg val x86))
                    val))
    :hints (("Goal"
             :in-theory (e/d (rx128 wx128 )
                             (xmmi-is-n128p
                              unsigned-byte-p)))))

  (defthm rx128-wx128-different
    (implies (not (equal reg1 reg2))
             (equal (rx128 reg1 (wx128 reg2 val x86))
                    (rx128 reg1 x86)))
    :hints (("Goal"
             :in-theory (e/d (rx128 wx128 )
                             (xmmi-is-n128p)))))

  (define xmmi-size
    ((nbytes :type (unsigned-byte 5))
     (index  :type (unsigned-byte 4))
     x86)
    :enabled t
    :guard (member nbytes '(4 8 16))
    :inline t
    :returns (val natp :rule-classes :type-prescription)
    (case nbytes
      (4  (rx32  index x86))
      (8  (rx64  index x86))
      (16 (rx128 index x86))
      (otherwise
       ;; This function shouldn't really be used in the case when nbytes
       ;; != 4, 8, or 16.  Anyway, the guard says nbytes shouldn't be
       ;; anything else.
       0)))

  (define !xmmi-size
    ((nbytes :type (unsigned-byte 5))
     (index  :type (unsigned-byte 4))
     (val    :type integer)
     x86)
    :enabled t
    :guard (and (member nbytes '(4 8 16))
                (unsigned-byte-p (ash nbytes 3) val))
    :returns (x86 x86p :hyp (and (x86p x86) (natp index)))
    :inline t
    (case nbytes
      (4  (wx32  index val x86))
      (8  (wx64  index val x86))
      (16 (wx128 index val x86))
      (otherwise
       ;; This function shouldn't really be used in the case when nbytes
       ;; != 4, 8, or 16.  Anyway, the guard says nbytes shouldn't be
       ;; anything else.
       x86)))

  )

;; ======================================================================

(defsection MMX-Registers-Reads-and-Writes

  :parents (x86-register-readers-and-writers)

  :short "Functions to read/write into the MMX registers"

  :long "<p>From Section 12.2, Intel Manual, Volume 3 \(System
  Programming\):</p>

  <p><em>The MMX state consists of eight 64-bit registers \(MM0
through MM7\). These registers are aliased to the low 64-bits \(bits 0
through 63\) of floating-point registers R0 through R7 \(see Figure
12-1\). Note that the MMX registers are mapped to the physical
locations of the floating-point registers \(R0 through R7\), not to
the relative locations of the registers in the floating-point register
stack \(ST0 through ST7\). As a result, the MMX register mapping is
fixed and is not affected by value in the Top Of Stack \(TOS\) field
in the floating-point status word \(bits 11 through 13\).</em></p>

<p>From Section 12.2, Intel Manual, Volume 3 \(System Programming\)</p>:

<p><em>When a value is written into an MMX register using an MMX
instruction, the value also appears in the corresponding
floating-point register in bits 0 through 63. Likewise, when a
floating-point value written into a floating-point register by a x87
FPU, the low 64 bits of that value also appears in a the corresponding
MMX register.</em></p>

<p><em>The execution of MMX instructions have several side effects on
the x87 FPU state contained in the floating-point registers, the x87
FPU tag word, and the x87 FPU status word. These side effects are as
follows:</em></p>

<p><em>* When an MMX instruction writes a value into an MMX register,
at the same time, bits 64 through 79 of the corresponding
floating-point register are set to all 1s.</em></p>

<p><em>* When an MMX instruction \(other than the EMMS instruction\) is
executed, each of the tag fields in the x87 FPU tag word is set to 00B
\(valid\). \(See also Section 12.2.1, Effect of MMX, x87 FPU, FXSAVE,
and FXRSTOR Instructions on the x87 FPU Tag Word.\)</em></p>

<p><em>* When the EMMS instruction is executed, each tag field in the
x87 FPU tag word is set to 11B \(empty)\.</em></p>

<p><em>* Each time an MMX instruction is executed, the TOS value is
set to 000B.  Execution of MMX instructions does not affect the other
bits in the x87 FPU status word \(bits 0 through 10 and bits 14 and
15\) or the contents of the other x87 FPU registers that comprise the
x87 FPU state \(the x87 FPU control word, instruction pointer, data
pointer, or opcode registers\).</em></p>"

  (local (xdoc::set-default-parents MMX-Registers-Reads-and-Writes))

  (define mmx
    ((i :type (integer 0 7))
     (x86))
    :inline t
    (let ((reg80 (the (unsigned-byte 80) (fp-datai i x86))))
      (mbe :logic (part-select reg80 :low 0 :width 64)
           :exec  (logand #.*2^64-1* reg80)))

    ///

    (defthm-usb n64p-mmx
      :hyp t
      :bound 64
      :concl (mmx i x86)
      :gen-type t
      :gen-linear t))

  (define !mmx
    ((i :type (integer      0 7))
     (v :type (unsigned-byte 64))
     (x86))
    :inline t
    :guard-hints (("Goal" :in-theory (e/d ()
                                          (unsigned-byte-p))))

    (let ((val80 (mbe :logic (part-install #xFFFF v :low 64 :high 79)
                      :exec (the (unsigned-byte 80)
                              (logior #uxFFFF_00000000_00000000 v)))))
      (!fp-datai i val80 x86))

    ///

    (defthm x86p-!mmx
      (implies (and (x86p x86)
                    (n64p v)
                    (integerp i))
               (x86p (!mmx i v x86)))
      :hints (("Goal" :in-theory (e/d ()
                                      (force (force)))))))

  (define mmx-instruction-updates (x86)
    :inline t
    :guard-hints (("Goal" :in-theory (e/d ()
                                          ())))
    :short "We set the FPU tag and TOS field to 00B \(valid\) and 000B
 respectively.  This function accounts for the effects of all MMX
 instructions except EMMS."

    (b* ((x86 (!fp-tag 0 x86))
         (fp-status (fp-status x86))
         (x86 (!fp-status (!fp-status-slice :fp-top 0 fp-status) x86)))
        x86)

    ///

    (defthm x86p-mmx-instruction-updates
      (implies (x86p x86)
               (x86p (mmx-instruction-updates x86)))))

  )

;; ======================================================================

(defsection rflags-Reads-and-Writes
  :parents (rflag-specifications x86-register-readers-and-writers)
  :short "Reading from and writing to the @('rflags') register in the @('x86') state"

  :long "<p>We define @(see flgi) to read a flag's value, and @(see
  !flgi) to write a flag's value into the @('rflags') field in the
  @('x86') state.</p>"

  (local (xdoc::set-default-parents rflags-Reads-and-Writes))

  (define flgi
    ((flg :type (integer 0 32))
     x86)
    :guard (member flg *flg-names*)
    :parents (rflags-Reads-and-Writes)

    (b* ((rflags (the (unsigned-byte 32) (rflags x86))))
        (mbe :logic
             (part-select rflags :low flg
                          :width (if (equal flg *iopl*)
                                     2 1))
             :exec
             (the (unsigned-byte 2)
               (logand (if (equal flg #.*iopl*) 3 1)
                       (the (unsigned-byte 32)
                         (ash (the (unsigned-byte 32) rflags)
                              (the (integer -32 0)
                                (- (the (integer 0 32) flg)))))))))


    ///

    (defthm-usb n01p-flgi-except-iopl
      :hyp (and (force (x86p x86))
                (not (equal flg *iopl*)))
      :bound 1
      :concl (flgi flg x86)
      :gen-type t
      :gen-linear t)

    (defthm-usb n02p-flgi-iopl
      :hyp (force (x86p x86))
      :bound 2
      :concl (flgi *iopl* x86)
      :gen-type t
      :gen-linear t)

    (defthm flgi-xw
      (equal (flgi flg (xw field index value x86))
             (if (equal field :rflags)
                 (if (not (equal flg *iopl*))
                     (logbit flg value)
                   (loghead 2 (logtail *iopl* value)))
               (flgi flg x86)))))

  (define !flgi
    ((flg :type (integer 0 32))
     (val :type (unsigned-byte 2))
     x86)
    :parents (rflags-Reads-and-Writes)
    :guard (and (member flg *flg-names*)
                (if (equal flg *iopl*)
                    (unsigned-byte-p 2 val)
                  (unsigned-byte-p 1 val)))
    :guard-hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))

    (b* ((rflags (the (unsigned-byte 32) (rflags x86)))
         (new-rflags
          (mbe
           :logic
           (part-install val rflags :low flg
                         :width (if (equal flg *iopl*)
                                    2 1))
           :exec
           (let* ((mask (the (unsigned-byte 32)
                          (logand #.*2^32-1*
                                  (lognot
                                   (the (unsigned-byte 32)
                                     (ash (if (equal flg #.*iopl*)
                                              3 1)
                                          (the (integer 0 21)
                                            flg))))))))

             (the (unsigned-byte 32)
               (logior
                (the (unsigned-byte 32) (logand rflags mask))
                (the (unsigned-byte 32) (ash val flg))))))))
        (!rflags (mbe :logic (n32 new-rflags)
                      :exec new-rflags)
                 x86))

    ///

    (defthm x86p-!flgi
      (implies (x86p x86)
               (x86p (!flgi flg val x86))))

    (defthm xr-!flgi
      (implies (not (equal field :rflags))
               (equal (xr field index (!flgi flg val x86))
                      (xr field index x86)))
      :hints (("Goal" :in-theory (e/d* () (force (force))))))

    (defthm !flgi-xw
      ;; Keep !flgi inside all other nests of updates.
      (implies (not (equal field :rflags))
               (equal (!flgi flg val (xw field index value x86))
                      (xw field index value (!flgi flg val x86))))
      :hints (("Goal" :in-theory (e/d* (!flgi) (force (force))))))

    (defthm rflags-!flgi
      (implies (and (member flg *flg-names*)
                    (x86p x86))
               (equal (xr :rflags index (!flgi flg val x86))
                      (part-install val
                                    (xr :rflags 0 x86)
                                    :low flg
                                    :width (if (equal flg *iopl*) 2 1))))))

  )

;; ======================================================================
;; Characterizing Undefined Behavior

(defsection characterizing-undefined-behavior

  :parents (machine)

  :short "An @('undef') field in the @('x86') state feeds unknown
  values to processor components that are undefined"

  :long "<p>The @('undef') field is used to feed unknown values to
processor components that are undefined, as per the Intel
specifications.  For example, the @('SF'), @('ZF'), @('AF'), and
@('PF') rflags are undefined after a @('MUL') instruction is
executed.</p>

<p>The principle behind the @('undef') field is quite like that of the
@('oracle') sub-field of the @('env') field \(see @(see
environment-field)\).  We describe our use of the @('undef') field by
comparing it to the @('oracle') sub-field.</p>

<p>For reasoning about programs that involve commonly occurring
\"undefined events\" \(like flag computations\), using the @('oracle')
sub-field can be quite tedious, since it has to be carefully
initialized; i.e., a list of appropriate \(symbolic or concrete\)
values has to be associated with the instruction pointer where any
such undefined event occurs.  Imagine doing that for @('SF'), @('ZF'),
@('AF'), and @('PF') every time a @('MUL') instruction is executed.
The reason why we need this initialization is because the only way to
access the @('oracle') is through the functions @(see pop-x86-oracle)
and @(see env-read); @('pop-x86-oracle') expects the @('oracle') to
contain information in a specific format, and @('env-read') will give
us nothing unless we put something in to begin with.</p>

<p>On the other hand, the @('undef') field doesn't require any such
initialization.  The @('undef') field contains a natural number that
is increased every time an undefined value is pulled for use \(using
the constrained function @('create-undef')\) from a pool of undefined
values; thus, every access of the @('undef') field causes it to
contain a new value which is used to seed a unique undefined
value. See @(see undef-read) for details.</p>

<p>There is a reason why we enforced that tediousness in the case of
the @('oracle') sub-field: it provides a way of tracking any
computation that relies on the @('env') field. Such computations don't
happen often, and when they do, it'd probably be better if we knew
exactly what we are expecting from the environment.  Initializing the
@('oracle') is a way of expressing these expectations. However, in the
case of undefined values, we aren't really expecting anything from the
environment.  All we want is a sort of infinite pool of arbitary
values, seeded from @('undef') in our case, that we don't know
anything about.  As such, we wouldn't be able to prove that a value
obtained from @('undef') is equal \(or not\) to any other value,
either obtained from @('undef') or not.  This is exactly what we need
when reasoning about undefined values --- an undefined value is
different from another undefined value, and also all the known
values.</p>"

  )

(encapsulate
 ( ((create-undef *) => *) )

 (local
  (defun create-undef (x)
    (nfix x)))

 (defthm natp-create-undef
   (natp (create-undef x)))

 )

(define safe-!undef (v x86)
  ;; We will make !undef untouchable (in x86-row-wow-thms.lisp, after
  ;; proving all row/wow thms in terms of !undef; note that
  ;; safe-!undef is enabled and not untouchable) and will use
  ;; safe-!undef instead.  This function is smashed in raw Lisp --- if
  ;; called during evaluation, it causes an error.  It can be safely
  ;; used during proof attempts.
  :inline nil
  :enabled t
  :returns (x86 x86p :hyp :guard)
  :parents (undef-read)
  (!undef v x86))

(define undef-read-logic (x86)
  :enabled t
  :returns (mv (unknown natp :rule-classes :type-prescription)
               (x86     x86p :hyp (x86p x86)))
  :parents (undef-read)

  (b* ((undef-seed (nfix (undef x86)))
       (new-unknown (create-undef undef-seed))
       (x86 (safe-!undef (1+ undef-seed) x86)))
      (mv new-unknown x86)))

(define undef-read (x86)
  ;; TO-DO@Shilpi: I'll need to add more args to this function if I
  ;; need the corresponding raw Lisp function to have more info.
  :inline nil
  :enabled t
  :returns (mv (unknown natp :rule-classes :type-prescription)
               (x86     x86p :hyp (x86p x86)))
  :parents (characterizing-undefined-behavior)

  :short "Get a unique unknown to be used when reasoning about
    undefined values in the processor"
  :long "<p>See @(see characterizing-undefined-behavior) for more
  details.</p>

  <p>The accessor and updater functions of the @('undef') field are
  untouchable so that the only way to create a new seed for unknowns
  is via this function.  These functions have been made untouchable
  after various RoW/WoW lemmas have been proved about them \(see @(see
  x86-RoW-WoW-thms)\).</p>"

  (undef-read-logic x86))

(define undef-flg-logic (x86)
  :enabled t
  :parents (!flgi-undefined)
  (undef-read x86))

(define undef-flg (x86)
  ;; I have smashed this function under the hood.  This is a tad more
  ;; efficient than smashing undef-read because it helps us avoid
  ;; calling n01 while execution.  This saves one call to the builtin
  ;; LOGAND that might create bignums, potentially.
  :inline nil
  :enabled t
  :parents (!flgi-undefined)
  (b* (((mv val x86)
        (undef-flg-logic x86)))
      (mv (n01 val) x86)))

(define !flgi-undefined
  ((flg :type (member #.*cf* #.*pf* #.*af* #.*zf* #.*sf* #.*of*))
   x86)

  :inline t
  :parents (x86-register-readers-and-writers characterizing-undefined-behavior)

  :short "Setting the rflag @('flg') in the x86 state to @('undefined')"

  :long "<p>Rflag @('flg') is set to the value returned by an oracle,
using the @(see undef-read) function.</p>"

  :returns (x86 x86p :hyp :guard)

  (b* (((mv (the (unsigned-byte 1) val) x86)
        (undef-flg x86))
       (x86 (!flgi flg val x86)))
      x86))

;; (define write-user-rflags
;;   ((x86)
;;    &key
;;    (cf (or (not cf) (unsigned-byte-p 1 cf)))
;;    (pf (or (not pf) (unsigned-byte-p 1 pf)))
;;    (af (or (not af) (unsigned-byte-p 1 af)))
;;    (zf (or (not zf) (unsigned-byte-p 1 zf)))
;;    (sf (or (not sf) (unsigned-byte-p 1 sf)))
;;    (of (or (not of) (unsigned-byte-p 1 of))))

;;   :inline t
;;   :parents (x86-register-readers-and-writers)

;;   :short "Writing user rflags \(CF, PF, AF, ZF, SF, and OF\),
;;   including undefined ones, to the x86 state"

;;   :long "<p>We set the undefined flags, which are indicated by
;;   @('mask'), to the value returned by @(see undef-read).</p>"

;;   :guard ()
;;   :guard-hints (("Goal" :in-theory (e/d (!flgi) ())))

;;   :returns (x86 x86p :hyp :guard)

;;   (b* ((x86 (if cf
;;		(!flgi #.*cf* cf x86)
;;            (!flgi-undefined #.*cf* x86)))

;;        (x86 (if pf
;;		(!flgi #.*pf* pf x86)
;;            (!flgi-undefined #.*pf* x86)))

;;        (x86 (if af
;;		(!flgi #.*af* af x86)
;;            (!flgi-undefined #.*af* x86)))

;;        (x86 (if zf
;;		(!flgi #.*zf* zf x86)
;;            (!flgi-undefined #.*zf* x86)))

;;        (x86 (if sf
;;		(!flgi #.*sf* sf x86)
;;            (!flgi-undefined #.*sf* x86)))

;;        (x86 (if of
;;		(!flgi #.*of* of x86)
;;            (!flgi-undefined #.*of* x86))))
;;       x86))

(local (include-book "centaur/gl/gl" :dir :system))

(local
 (def-gl-thm write-user-rflags-guard-helper
   :hyp (and (unsigned-byte-p 32 input-rflags)
             (unsigned-byte-p 32 flgs))
   :concl
   (equal (logior
           (ash (bool->bit (logbitp 11 flgs)) 11)
           (logand
            4294965247
            (logior
             (ash (bool->bit (logbitp 7 flgs)) 7)
             (logand
              4294967167
              (logior
               (ash (bool->bit (logbitp 6 flgs)) 6)
               (logand
                4294967231
                (logior
                 (ash (bool->bit (logbitp 4 flgs)) 4)
                 (logand
                  4294967279
                  (logior
                   (ash (bool->bit (logbitp 2 flgs)) 2)
                   (logand 4294967291
                           (logior (loghead 1 flgs)
                                   (logand 4294967294
                                           input-rflags))))))))))))
          (logior
           (loghead 1 flgs)
           (logand
            4294967294
            (logior
             (ash (bool->bit (logbitp 2 flgs)) 2)
             (logand
              4294967291
              (logior
               (ash (bool->bit (logbitp 4 flgs)) 4)
               (logand
                4294967279
                (logior
                 (ash (bool->bit (logbitp 7 flgs)) 7)
                 (logand 4294967167
                         (logior (ash (bool->bit (logbitp 6 flgs)) 6)
                                 (logand 4294967231
                                         (logior (logand 4294965247 input-rflags)
                                                 (ash (bool->bit (logbitp 11 flgs))
                                                      11)))))))))))))

   :g-bindings
   (gl::auto-bindings
    (:mix (:nat input-rflags 32)
          (:nat flgs         32)))))

(define write-user-rflags
  ((flgs  :type (unsigned-byte 32))
   (mask  :type (unsigned-byte 32))
   x86)

  :inline t
  :parents (x86-register-readers-and-writers)

  :short "Writing user rflags \(CF, PF, AF, ZF, SF, and OF\),
  including undefined ones, to the x86 state"

  :long "<p>We set the undefined flags, which are indicated by
  @('mask'), to the value returned by @(see undef-read).</p>"

  :guard-hints (("Goal" :in-theory (e/d (!flgi) ())))

  :returns (x86 x86p :hyp (and (unsigned-byte-p 32 flgs)
                               (unsigned-byte-p 32 mask)
                               (x86p x86)))

  (if (equal mask 0)

      ;; (!rflags flgs x86)
      (mbe :logic
           (b* ((x86 (!flgi #.*cf* (rflags-slice :cf flgs) x86))
                (x86 (!flgi #.*pf* (rflags-slice :pf flgs) x86))
                (x86 (!flgi #.*af* (rflags-slice :af flgs) x86))
                (x86 (!flgi #.*zf* (rflags-slice :zf flgs) x86))
                (x86 (!flgi #.*sf* (rflags-slice :sf flgs) x86))
                (x86 (!flgi #.*of* (rflags-slice :of flgs) x86)))
               x86)
           :exec
           (!rflags
            (!rflags-slice
             :cf (rflags-slice :cf flgs)
             (!rflags-slice
              :pf (rflags-slice :pf flgs)
              (!rflags-slice
               :af (rflags-slice :af flgs)
               (!rflags-slice
                :sf (rflags-slice :sf flgs)
                (!rflags-slice
                 :zf (rflags-slice :zf flgs)
                 (!rflags-slice
                  :of (rflags-slice :of flgs)
                  (rflags x86)))))))
            x86))

    (b* ((x86 (if (equal (rflags-slice :cf mask) 1)
                  (!flgi-undefined #.*cf* x86)
                (!flgi #.*cf* (rflags-slice :cf flgs) x86)))

         (x86 (if (equal (rflags-slice :pf mask) 1)
                  (!flgi-undefined #.*pf* x86)
                (!flgi #.*pf* (rflags-slice :pf flgs) x86)))

         (x86 (if (equal (rflags-slice :af mask) 1)
                  (!flgi-undefined #.*af* x86)
                (!flgi #.*af* (rflags-slice :af flgs) x86)))

         (x86 (if (equal (rflags-slice :zf mask) 1)
                  (!flgi-undefined #.*zf* x86)
                (!flgi #.*zf* (rflags-slice :zf flgs) x86)))

         (x86 (if (equal (rflags-slice :sf mask) 1)
                  (!flgi-undefined #.*sf* x86)
                (!flgi #.*sf* (rflags-slice :sf flgs) x86)))

         (x86 (if (equal (rflags-slice :of mask) 1)
                  (!flgi-undefined #.*of* x86)
                (!flgi #.*of* (rflags-slice :of flgs) x86))))
        x86)))

(include-book "tools/include-raw" :dir :system)
(defttag :undef-flg)
(include-raw "x86-register-readers-and-writers-raw.lsp")

;; ======================================================================
