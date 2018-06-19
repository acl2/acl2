;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "state-field-thms")

(local (include-book "guard-helpers"))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (in-theory (disable logior-expt-to-plus-quotep)))

;; ===================================================================

(defsection app-view

  :parents (machine)

  :short "Application-level view of the x86 model"

  :long "<p>The x86 model can be used in the application-level view
  when the value of the field @('app-view') is <tt>T</tt>.</p>

<p>Some supervisor-level features are neither used nor required for
the analysis of application software.  In most cases, a application
cares about the correctness of his application program while assuming
that services like paging and I/O operations are provided reliably by
the operating system.  The application-level view of our model attempts
to provide the same environment to a application for reasoning as is
provided by an OS for programming.  In this mode, our memory model
provides the <tt>2^48</tt>-byte linear address space specified for
modern 64-bit Intel machines.</p>

<p>A 64-bit canonical address can be in either of the two
ranges below:</p>

 <tt>0 to 2^47-1</tt> or <tt>2^64-2^47 to 2^64-1</tt>

<p>Note that this address space is 2^48 bytes of memory.  So I can use
the addresses</p>
<tt>0            to     2^47-1</tt>
<p>to map the first range, and the addresses</p>
<tt>-2^47        to         -1</tt>
<p>to map the second range.</p>

<tt>0            to     2^47-1       |     0            to     2^47-1</tt><br/>
<tt>2^64-2^47    to     2^64-1       |    -2^47         to         -1</tt>

<p>The advantage of doing so is that we will avoid bignum creation
during address computations.</p>

<p>We define some linear memory read and write functions, like @(see
rvm08) and @(see wvm08).  These functions are called by the top-level
functions, like @(see rml08) and @(see wml08) when
@('app-view') is true.</p>

<p>The guards of the linear memory functions are stricter than those
of @('memi') and @('!memi'), because the latter allow reading from and
writing to an address anywhere in the range <tt>0 to 2^52-1</tt>, and
@('rvm08') and @('wvm08') allow reads and writes only to the range
<tt>0 to 2^48-1</tt> of physical memory: they take as argument a signed 48-bit
integer that represents a canonical address, they convert it to an unsigned
48-bit integer, and they use that to access the @('mem') field.
Basically, we're overloading the @('mem') field
in @('x86') --- when @('app-view') is set, @('mem')
refers to the linear memory; otherwise, it refers to the physical
memory.</p>" )

(defsection linear-memory-in-app-view

  :parents (app-view)

  :short "Definition of linear memory accessor and udpater functions,
  used when @('app-view') = @('T')"

  :long "<p>Note that the top-level memory accessor function is @(see
  rml08) and updater function is @(see wml08).  Their 16, 32, and 64 bit
  counterparts are also available.  These functions behave differently
  depending upon the value of @('app-view').</p>"

  )

;; ======================================================================

(define canonical-address-p (lin-addr)
  :parents (linear-memory-in-app-view)
  :inline t
  :enabled t
  ;; In 64-bit mode, an address is considered to be in canonical form
  ;; if address bits 63 through to the most-significant implemented
  ;; bit by the microarchitecture are set to either all ones or all
  ;; zeros.
  (mbe :logic (signed-byte-p #.*max-linear-address-size* lin-addr)
       :exec  (and (integerp lin-addr)
                   (<= #.*-2^47* lin-addr)
                   (< lin-addr #.*2^47*)))

  ///

  (defthm canonical-address-p-and-logext-48
    (implies (canonical-address-p a)
             (equal (logext 48 a) a)))

  (defthm canonical-address-p-of-logext-48
    (canonical-address-p (logext 48 a))))

;; ======================================================================

;; Memory Read Functions:

(define rvm08
  ((addr :type (signed-byte #.*max-linear-address-size*))
   (x86))
  :enabled t
  :inline t
  :parents (linear-memory-in-app-view)

  (mbe :logic (if (canonical-address-p addr)
                  (mv nil (memi (n48 addr) x86) x86)
                (mv 'rvm08 0 x86))
       :exec (mv nil (memi (n48 addr) x86) x86))

  ///

  (defthm rvm08-no-error
    (implies (canonical-address-p addr)
             (equal (mv-nth 0 (rvm08 addr x86))
                    nil))
    :hints (("Goal" :in-theory (e/d () (force (force))))))

  (defthm-usb n08p-mv-nth-1-rvm08
    :hyp (x86p x86)
    :bound 8
    :concl (mv-nth 1 (rvm08 addr x86))
    :gen-linear t
    :gen-type t)

  (defthm x86p-mv-nth-2-rvm08-unchanged
    (equal (mv-nth 2 (rvm08 addr x86))
           x86))

  (defthm xr-rvm08
    (equal (xr fld index (mv-nth 2 (rvm08 addr x86)))
           (xr fld index x86)))

  (defthm rvm08-xw-values
    (implies (not (equal fld :mem))
             (and (equal (mv-nth 0 (rvm08 addr (xw fld index value x86)))
                         (mv-nth 0 (rvm08 addr x86)))
                  (equal (mv-nth 1 (rvm08 addr (xw fld index value x86)))
                         (mv-nth 1 (rvm08 addr x86)))))))

(define rvm16
  ((addr :type (signed-byte #.*max-linear-address-size*))
   (x86))
  :enabled t
  :inline t
  :parents (linear-memory-in-app-view)

  (if (mbt (canonical-address-p addr))

      (let* ((1+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (1+ (the (signed-byte #.*max-linear-address-size*)
                             addr)))))

        (if (mbe :logic (canonical-address-p (1+ addr))
                 :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                            1+addr) #.*2^47*))

            (b* (((the (unsigned-byte 8) byte0) (memi (n48 addr) x86))
                 ((the (unsigned-byte 8) byte1) (memi (n48 1+addr) x86)))
              (mv nil
                  (the (unsigned-byte 16)
                    (logior (the (unsigned-byte 16) (ash byte1 8))
                            byte0))
                  x86))

          (mv 'rvm16 0 x86)))

    (mv 'rvm16 0 x86))

  ///

  (defthm rvm16-no-error
    (implies (and (canonical-address-p addr)
                  (canonical-address-p (+ 1 addr)))
             (equal (mv-nth 0 (rvm16 addr x86))
                    nil))
    :hints (("Goal" :in-theory (e/d () (force (force))))))

  (local
   (defthm-usb n16p-mv-nth-1-rvm16-helper
     :hyp (and (unsigned-byte-p 8 byte0)
               (unsigned-byte-p 8 byte1))
     :bound 16
     :concl (logior byte0 (ash byte1 8))))


  (defthm-usb n16p-mv-nth-1-rvm16
    :hyp (x86p x86)
    :bound 16
    :concl (mv-nth 1 (rvm16 addr x86))
    :gen-linear t
    :hints (("Goal" :in-theory (e/d* () (unsigned-byte-p))))
    :gen-type t)

  (defthm x86p-mv-nth-2-rvm16-unchanged
    (equal (mv-nth 2 (rvm16 addr x86))
           x86)
    :hints (("Goal" :in-theory (e/d () (force (force))))))

  (defthm xr-rvm16
    (equal (xr fld index (mv-nth 2 (rvm16 addr x86)))
           (xr fld index x86)))

  (defthm rvm16-xw-values
    (implies (not (equal fld :mem))
             (and (equal (mv-nth 0 (rvm16 addr (xw fld index value x86)))
                         (mv-nth 0 (rvm16 addr x86)))
                  (equal (mv-nth 1 (rvm16 addr (xw fld index value x86)))
                         (mv-nth 1 (rvm16 addr x86)))))))


(define rvm32
  ((addr :type (signed-byte #.*max-linear-address-size*))
   (x86))
  :enabled t
  :inline t
  :parents (linear-memory-in-app-view)

  (if (mbt (canonical-address-p addr))

      (let* ((1+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 1 (the (signed-byte #.*max-linear-address-size*)
                              addr))))
             (2+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 2 (the (signed-byte #.*max-linear-address-size*)
                              addr))))
             (3+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 3 (the (signed-byte #.*max-linear-address-size*)
                              addr)))))

        (if (mbe :logic (canonical-address-p (+ 3 addr))
                 :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                            3+addr) #.*2^47*))

            (b* (((the (unsigned-byte 8) byte0) (memi (n48 addr) x86))
                 ((the (unsigned-byte 8) byte1) (memi (n48 1+addr) x86))
                 ((the (unsigned-byte 16) word0)
                  (logior (the (unsigned-byte 16)
                            (ash byte1 8)) byte0))
                 ((the (unsigned-byte 8) byte2) (memi (n48 2+addr) x86))
                 ((the (unsigned-byte 8) byte3) (memi (n48 3+addr) x86))
                 ((the (unsigned-byte 16) word1)
                  (the (unsigned-byte 16) (logior (the (unsigned-byte 16)
                                                    (ash byte3 8))
                                                  byte2)))
                 ((the (unsigned-byte 32) dword) (logior (the (unsigned-byte 32)
                                                           (ash word1 16))
                                                         word0)))
              (mv nil dword x86))

          (mv 'rvm32 0 x86)))

    (mv 'rvm32 0 x86))

  ///

  (defthm rvm32-no-error
    (implies (and (canonical-address-p addr)
                  (canonical-address-p (+ 3 addr)))
             (equal (mv-nth 0 (rvm32 addr x86))
                    nil))
    :hints (("Goal" :in-theory (e/d () (force (force))))))

  (local
   (defthm-usb n32p-mv-nth-1-rvm32-helper
     :hyp (and (unsigned-byte-p 8 byte0)
               (unsigned-byte-p 8 byte1)
               (unsigned-byte-p 8 byte2)
               (unsigned-byte-p 8 byte3))
     :bound 32
     :concl (logior byte0
                    (ash
                     (logior byte1
                             (ash (logior byte2 (ash byte3 8)) 8))
                     8))))

  (defthm-usb n32p-mv-nth-1-rvm32
    :hyp (x86p x86)
    :bound 32
    :concl (mv-nth 1 (rvm32 addr x86))
    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p force (force)))))
    :gen-linear t
    :gen-type t)

  (defthm x86p-mv-nth-2-rvm32-unchanged
    (equal (mv-nth 2 (rvm32 addr x86))
           x86)
    :hints (("Goal" :in-theory (e/d () (force (force))))))

  (defthm xr-rvm32
    (equal (xr fld index (mv-nth 2 (rvm32 addr x86)))
           (xr fld index x86)))

  (defthm rvm32-xw-values
    (implies (not (equal fld :mem))
             (and (equal (mv-nth 0 (rvm32 addr (xw fld index value x86)))
                         (mv-nth 0 (rvm32 addr x86)))
                  (equal (mv-nth 1 (rvm32 addr (xw fld index value x86)))
                         (mv-nth 1 (rvm32 addr x86)))))))

(define rvm48
  ((addr :type (signed-byte #.*max-linear-address-size*))
   (x86))
  :enabled t
  :guard-hints (("Goal" :in-theory (e/d (rml48-guard-proof-helper) ())))
  :inline t
  :parents (linear-memory-in-app-view)

  (if (mbt (canonical-address-p addr))

      (let* ((2+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 2 (the (signed-byte #.*max-linear-address-size*)
                              addr))))
             (5+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 5 (the (signed-byte #.*max-linear-address-size*)
                              addr)))))

        (if (mbe :logic (canonical-address-p 5+addr)
                 :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                            5+addr) #.*2^47*))

            (b* (((mv flg0 (the (unsigned-byte 16) word0) x86)
                  (rvm16 addr x86))
                 ((mv flg1 (the (unsigned-byte 32) dword1) x86)
                  (rvm32 2+addr x86))
                 ((the (unsigned-byte 48) value)
                  (the (unsigned-byte 48)
                    (logior (the (unsigned-byte 48) (ash dword1 16))
                            word0))))
              (mbe :logic (if (or flg0 flg1)
                              (mv 'rvm48 0 x86)
                            (mv nil value x86))
                   :exec (mv nil value x86)))

          (mv 'rvm48 0 x86)))

    (mv 'rvm48 0 x86))

  ///

  (local (in-theory (e/d () (rvm16 rvm32))))

  (defthm rvm48-no-error
    (implies (and (canonical-address-p addr)
                  (canonical-address-p (+ 5 addr)))
             (equal (mv-nth 0 (rvm48 addr x86))
                    nil))
    :hints (("Goal" :in-theory (e/d () (force (force))))))

  (local
   (defthm-usb n48p-mv-nth-1-rvm48-helper
     :hyp (and (unsigned-byte-p 16 word)
               (unsigned-byte-p 32 dword))
     :bound 48
     :concl (logior word (ash dword 16))))

  (defthm-usb n48p-mv-nth-1-rvm48
    :hyp (x86p x86)
    :bound 48
    :concl (mv-nth 1 (rvm48 addr x86))
    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p force (force)))))
    :gen-linear t
    :gen-type t)

  (defthm x86p-mv-nth-2-rvm48-unchanged
    (equal (mv-nth 2 (rvm48 addr x86)) x86)
    :hints (("Goal" :in-theory (e/d () (force (force))))))

  (defthm xr-rvm48
    (equal (xr fld index (mv-nth 2 (rvm48 addr x86)))
           (xr fld index x86)))

  (defthm rvm48-xw-values
    (implies (not (equal fld :mem))
             (and (equal (mv-nth 0 (rvm48 addr (xw fld index value x86)))
                         (mv-nth 0 (rvm48 addr x86)))
                  (equal (mv-nth 1 (rvm48 addr (xw fld index value x86)))
                         (mv-nth 1 (rvm48 addr x86)))))))

(define rvm64
  ((addr :type (signed-byte #.*max-linear-address-size*))
   (x86))
  :enabled t
  :guard-hints (("Goal" :in-theory (e/d () (rvm32))))
  :inline t
  :parents (linear-memory-in-app-view)

  (if (mbt (canonical-address-p addr))

      (let* ((4+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 4 (the (signed-byte #.*max-linear-address-size*)
                              addr))))
             (7+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 7 (the (signed-byte #.*max-linear-address-size*)
                              addr)))))

        (if (mbe :logic (canonical-address-p 7+addr)
                 :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                            7+addr) #.*2^47*))

            (b* (((mv flg0 (the (unsigned-byte 32) dword0) x86)
                  (rvm32 addr x86))
                 ((mv flg1 (the (unsigned-byte 32) dword1) x86)
                  (rvm32 4+addr x86))
                 ((the (unsigned-byte 64) qword)
                  (the (unsigned-byte 64) (logior
                                           (the (unsigned-byte 64)
                                             (ash dword1 32))
                                           dword0))))
              (mbe :logic (if (or flg0 flg1)
                              (mv 'rvm64 0 x86)
                            (mv nil qword x86))
                   :exec (mv nil qword x86)))

          (mv 'rvm64 0 x86)))

    (mv 'rvm64 0 x86))

  ///

  (local (in-theory (e/d () (rvm32))))

  (defthm rvm64-no-error
    (implies (and (canonical-address-p addr)
                  (canonical-address-p (+ 7 addr)))
             (equal (mv-nth 0 (rvm64 addr x86))
                    nil))
    :hints (("Goal" :in-theory (e/d () (force (force))))))

  (local
   (defthm-usb n64p-mv-nth-1-rvm64-helper
     :hyp (and (unsigned-byte-p 32 dword0)
               (unsigned-byte-p 32 dword1))
     :bound 64
     :concl (logior dword0 (ash dword1 32))))

  (defthm-usb n64p-mv-nth-1-rvm64
    :hyp (x86p x86)
    :bound 64
    :concl (mv-nth 1 (rvm64 addr x86))
    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p force (force)))))
    :gen-linear t
    :gen-type t)

  (defthm x86p-mv-nth-2-rvm64-unchanged
    (equal (mv-nth 2 (rvm64 addr x86))
           x86)
    :hints (("Goal" :in-theory (e/d () (force (force))))))

  (defthm xr-rvm64
    (equal (xr fld index (mv-nth 2 (rvm64 addr x86)))
           (xr fld index x86)))

  (defthm rvm64-xw-values
    (implies (not (equal fld :mem))
             (and (equal (mv-nth 0 (rvm64 addr (xw fld index value x86)))
                         (mv-nth 0 (rvm64 addr x86)))
                  (equal (mv-nth 1 (rvm64 addr (xw fld index value x86)))
                         (mv-nth 1 (rvm64 addr x86)))))))

(define rvm80
  ((addr :type (signed-byte #.*max-linear-address-size*))
   (x86))
  :enabled t
  :guard-hints (("Goal" :in-theory (e/d () (rvm32))))
  :inline t
  :parents (linear-memory-in-app-view)

  (if (mbt (canonical-address-p addr))

      (let* ((2+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 2 (the (signed-byte #.*max-linear-address-size*)
                              addr))))
             (9+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 9 (the (signed-byte #.*max-linear-address-size*)
                              addr)))))

        (if (mbe :logic (canonical-address-p 9+addr)
                 :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                            9+addr) #.*2^47*))

            (b* (((mv flg0 (the (unsigned-byte 16) word0) x86)
                  (rvm16 addr x86))
                 ((mv flg1 (the (unsigned-byte 64) qword1) x86)
                  (rvm64 2+addr x86))
                 ((the (unsigned-byte 80) value)
                  (the (unsigned-byte 80)
                    (logior (the (unsigned-byte 80) (ash qword1 16))
                            word0))))
              (mbe :logic (if (or flg0 flg1)
                              (mv 'rvm80 0 x86)
                            (mv nil value x86))
                   :exec (mv nil value x86)))

          (mv 'rvm80 0 x86)))

    (mv 'rvm80 0 x86))

  ///

  (local (in-theory (e/d () (rvm16 rvm64))))

  (defthm rvm80-no-error
    (implies (and (canonical-address-p addr)
                  (canonical-address-p (+ 9 addr)))
             (equal (mv-nth 0 (rvm80 addr x86))
                    nil))
    :hints (("Goal" :in-theory (e/d () (force (force))))))

  (local
   (defthm-usb n80p-mv-nth-1-rvm80-helper
     :hyp (and (unsigned-byte-p 16 word)
               (unsigned-byte-p 64 qword))
     :bound 80
     :concl (logior word (ash qword 16))))

  (defthm-usb n80p-mv-nth-1-rvm80
    :hyp (x86p x86)
    :bound 80
    :concl (mv-nth 1 (rvm80 addr x86))
    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p force (force)))))
    :gen-linear t
    :gen-type t)

  (defthm x86p-mv-nth-2-rvm80-unchanged
    (equal (mv-nth 2 (rvm80 addr x86)) x86)
    :hints (("Goal" :in-theory (e/d () (force (force))))))

  (defthm xr-rvm80
    (equal (xr fld index (mv-nth 2 (rvm80 addr x86)))
           (xr fld index x86)))

  (defthm rvm80-xw-values
    (implies (not (equal fld :mem))
             (and (equal (mv-nth 0 (rvm80 addr (xw fld index value x86)))
                         (mv-nth 0 (rvm80 addr x86)))
                  (equal (mv-nth 1 (rvm80 addr (xw fld index value x86)))
                         (mv-nth 1 (rvm80 addr x86)))))))

(define rvm128
  ((addr :type (signed-byte #.*max-linear-address-size*))
   (x86))
  :enabled t
  :guard-hints (("Goal" :in-theory (e/d () (rvm64))))
  :inline t
  :parents (linear-memory-in-app-view)

  (if (mbt (canonical-address-p addr))

      (let* ((8+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 8 (the (signed-byte #.*max-linear-address-size*)
                              addr))))
             (15+addr (the (signed-byte #.*max-linear-address-size+1*)
                        (+ 15 (the (signed-byte #.*max-linear-address-size*)
                                addr)))))

        (if (mbe :logic (canonical-address-p 15+addr)
                 :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                            15+addr) #.*2^47*))

            (b* (((mv flg0 (the (unsigned-byte 64) qword0) x86)
                  (rvm64 addr x86))
                 ((mv flg1 (the (unsigned-byte 64) qword1) x86)
                  (rvm64 8+addr x86))
                 ((the (unsigned-byte 128) oword)
                  (the (unsigned-byte 128) (logior
                                            (the (unsigned-byte 128)
                                              (ash qword1 64))
                                            qword0))))
              (mbe :logic (if (or flg0 flg1)
                              (mv 'rvm128 0 x86)
                            (mv nil oword x86))
                   :exec (mv nil oword x86)))

          (mv 'rvm128 0 x86)))

    (mv 'rvm128 0 x86))

  ///

  (local (in-theory (e/d () (rvm64))))

  (defthm rvm128-no-error
    (implies (and (canonical-address-p addr)
                  (canonical-address-p (+ 15 addr)))
             (equal (mv-nth 0 (rvm128 addr x86))
                    nil))
    :hints (("Goal" :in-theory (e/d () (force (force) rvm64)))))

  (local
   (defthm-usb n128p-mv-nth-1-rvm128-helper
     :hyp (and (unsigned-byte-p 64 qword1)
               (unsigned-byte-p 64 qword0))
     :bound 128
     :concl (logior qword1 (ash qword0 64))))

  (defthm-usb n128p-mv-nth-1-rvm128
    :hyp (x86p x86)
    :bound 128
    :concl (mv-nth 1 (rvm128 addr x86))
    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p force (force) rvm64))))
    :gen-linear t
    :gen-type t)

  (defthm x86p-mv-nth-2-rvm128-unchanged
    (equal (mv-nth 2 (rvm128 addr x86))
           x86)
    :hints (("Goal" :in-theory (e/d () (force (force) rvm64)))))

  (defthm xr-rvm128
    (equal (xr fld index (mv-nth 2 (rvm128 addr x86)))
           (xr fld index x86)))

  (defthm rvm128-xw-values
    (implies (not (equal fld :mem))
             (and (equal (mv-nth 0 (rvm128 addr (xw fld index value x86)))
                         (mv-nth 0 (rvm128 addr x86)))
                  (equal (mv-nth 1 (rvm128 addr (xw fld index value x86)))
                         (mv-nth 1 (rvm128 addr x86)))))))

;; ======================================================================

;; Memory Write Functions:

(define wvm08
  ((addr :type (signed-byte #.*max-linear-address-size*))
   (val :type (unsigned-byte   8))
   (x86))
  :enabled t
  :inline t
  :parents (linear-memory-in-app-view)

  (mbe :logic (if (canonical-address-p addr)
                  (let ((x86 (!memi (n48 addr) (n08 val) x86)))
                    (mv nil x86))
                (mv 'wvm08 x86))
       :exec (let ((x86 (!memi (n48 addr) val x86)))
               (mv nil x86)))
  ///

  (defthm wvm08-no-error
    (implies (canonical-address-p addr)
             (equal (mv-nth 0 (wvm08 addr val x86))
                    nil))
    :hints (("Goal" :in-theory (e/d () (force (force))))))

  (defthm x86p-mv-nth-1-wvm08
    (implies (x86p x86)
             (x86p (mv-nth 1 (wvm08 addr val x86))))
    :rule-classes (:rewrite :type-prescription))

  (defthm xr-wmv08-app-view
    (implies (not (equal fld :mem))
             (equal (xr fld index (mv-nth 1 (wvm08 addr val x86)))
                    (xr fld index x86)))
    :hints (("Goal" :in-theory (e/d* (wvm08) ()))))

  (defthm wvm08-xw-app-view
    (implies (not (equal fld :mem))
             (and (equal (mv-nth 0 (wvm08 addr val (xw fld index value x86)))
                         (mv-nth 0 (wvm08 addr val x86)))
                  (equal (mv-nth 1 (wvm08 addr val (xw fld index value x86)))
                         (xw fld index value (mv-nth 1 (wvm08 addr val x86))))))
    :hints (("Goal" :in-theory (e/d* (wvm08 wvm08) ())))))

(define wvm16
  ((addr :type (signed-byte #.*max-linear-address-size*))
   (val :type (unsigned-byte   16))
   (x86))
  :enabled t
  :guard-hints (("Goal" :in-theory (e/d (logtail) ())))
  :inline t
  :parents (linear-memory-in-app-view)

  (if (mbt (canonical-address-p addr))

      (let* ((1+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (1+ (the (signed-byte #.*max-linear-address-size*) addr)))))

        (if (mbe :logic (canonical-address-p 1+addr)
                 :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                            1+addr)
                          #.*2^47*))

            (b* (((the (unsigned-byte 8) byte0)
                  (mbe :logic (n08 val)
                       :exec  (logand #xff val)))
                 ((the (unsigned-byte 8) byte1)
                  (mbe :logic (part-select val :low 8 :width 8)
                       :exec  (logand #xff (ash val -8))))
                 (x86 (!memi (n48 addr) byte0 x86))
                 (x86 (!memi (n48 1+addr) byte1 x86)))
                (mv nil x86))

          (mv 'wvm16 x86)))

    (mv 'wvm16 x86))

  ///

  (defthm wvm16-no-error
    (implies (and (canonical-address-p addr)
                  (canonical-address-p (+ 3 addr)))
             (equal (mv-nth 0 (wvm16 addr val x86))
                    nil))
    :hints (("Goal" :in-theory (e/d () (force (force))))))

  (defthm x86p-mv-nth-1-wvm16
    (implies (x86p x86)
             (x86p (mv-nth 1 (wvm16 addr val x86))))
    :rule-classes (:rewrite :type-prescription))

  (defthm xr-wmv16-app-view
    (implies (not (equal fld :mem))
             (equal (xr fld index (mv-nth 1 (wvm16 addr val x86)))
                    (xr fld index x86)))
    :hints (("Goal" :in-theory (e/d* (wvm16) ()))))

  (defthm wvm16-xw-app-view
    (implies (not (equal fld :mem))
             (and (equal (mv-nth 0 (wvm16 addr val (xw fld index value x86)))
                         (mv-nth 0 (wvm16 addr val x86)))
                  (equal (mv-nth 1 (wvm16 addr val (xw fld index value x86)))
                         (xw fld index value (mv-nth 1 (wvm16 addr val x86))))))
    :hints (("Goal" :in-theory (e/d* (wvm16 wvm16) ())))))

(define wvm32
  ((addr :type (signed-byte #.*max-linear-address-size*))
   (val :type (unsigned-byte   32))
   (x86))
  :enabled t
  :guard-hints (("Goal" :in-theory (e/d (logtail) ())))
  :inline t
  :parents (linear-memory-in-app-view)

  (if (mbt (canonical-address-p addr))

      (let* ((1+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 1 (the (signed-byte #.*max-linear-address-size*) addr))))
             (2+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 2 (the (signed-byte #.*max-linear-address-size*) addr))))
             (3+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 3 (the (signed-byte #.*max-linear-address-size*) addr)))))

        (if (mbe :logic (canonical-address-p 3+addr)
                 :exec (< (the (signed-byte #.*max-linear-address-size+1*) 3+addr) #.*2^47*))

            (b* (((the (unsigned-byte 8) byte0)
                  (mbe :logic (part-select val :low 0 :width 8)
                       :exec  (logand #xff val)))
                 ((the (unsigned-byte 8) byte1)
                  (mbe :logic (part-select val :low 8 :width 8)
                       :exec  (logand #xff (ash val -8))))
                 ((the (unsigned-byte 8) byte2)
                  (mbe :logic (part-select val :low 16 :width 8)
                       :exec  (logand #xff (ash val -16))))
                 ((the (unsigned-byte 8) byte3)
                  (mbe :logic (part-select val :low 24 :width 8)
                       :exec  (logand #xff (ash val -24))))
                 (x86 (!memi (n48 addr)  byte0 x86))
                 (x86 (!memi (n48 1+addr) byte1 x86))
                 (x86 (!memi (n48 2+addr) byte2 x86))
                 (x86 (!memi (n48 3+addr) byte3 x86)))
                (mv nil x86))

          (mv 'wvm32 x86)))

    (mv 'wvm32 x86))

  ///

  (defthm wvm32-no-error
    (implies (and (canonical-address-p addr)
                  (canonical-address-p (+ 3 addr)))
             (equal (mv-nth 0 (wvm32 addr val x86))
                    nil))
    :hints (("Goal" :in-theory (e/d () (force (force))))))

  (defthm x86p-mv-nth-1-wvm32
    (implies (x86p x86)
             (x86p (mv-nth 1 (wvm32 addr val x86))))
    :rule-classes (:rewrite :type-prescription))

  (defthm xr-wmv32-app-view
    (implies (not (equal fld :mem))
             (equal (xr fld index (mv-nth 1 (wvm32 addr val x86)))
                    (xr fld index x86)))
    :hints (("Goal" :in-theory (e/d* (wvm32) ()))))

  (defthm wvm32-xw-app-view
    (implies (not (equal fld :mem))
             (and (equal (mv-nth 0 (wvm32 addr val (xw fld index value x86)))
                         (mv-nth 0 (wvm32 addr val x86)))
                  (equal (mv-nth 1 (wvm32 addr val (xw fld index value x86)))
                         (xw fld index value (mv-nth 1 (wvm32 addr val x86))))))
    :hints (("Goal" :in-theory (e/d* (wvm32 wvm32) ())))))

(define wvm48
  ((addr :type (signed-byte #.*max-linear-address-size*))
   (val :type (unsigned-byte   48))
   (x86))
  :enabled t
  :guard-hints (("Goal" :in-theory (e/d (logtail) ())))
  :inline t
  :parents (linear-memory-in-app-view)

  (if (mbt (canonical-address-p addr))

      (let* ((2+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 2 (the (signed-byte #.*max-linear-address-size*) addr))))
             (5+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 5 (the (signed-byte #.*max-linear-address-size*) addr)))))

        (if (mbe :logic (canonical-address-p 5+addr)
                 :exec (< (the (signed-byte #.*max-linear-address-size+1*) 5+addr) #.*2^47*))

            (b* ((word0 (mbe :logic (part-select val :low 0 :width 16)
                             :exec  (logand #xFFFF val)))
                 (dword1 (mbe :logic (part-select val :low 16 :width 32)
                              :exec  (logand #xFFFFFFFF (ash val -16))))
                 ((mv flg0 x86) (wvm16 addr    word0 x86))
                 ((mv flg1 x86) (wvm32 2+addr dword1 x86)))
              (mbe :logic (if (or flg0 flg1)
                              (mv 'wvm48 x86)
                            (mv nil x86))
                   :exec (mv nil x86)))

          (mv 'wvm48 x86)))

    (mv 'wvm48 x86))

  ///

  (defthm wvm48-no-error
    (implies (and (canonical-address-p addr)
                  (canonical-address-p (+ 5 addr)))
             (equal (mv-nth 0 (wvm48 addr val x86))
                    nil))
    :hints (("Goal" :in-theory (e/d () (force (force))))))

  (defthm x86p-mv-nth-1-wvm48
    (implies (x86p x86)
             (x86p (mv-nth 1 (wvm48 addr val x86))))
    :rule-classes (:type-prescription :rewrite))

  (defthm xr-wmv48-app-view
    (implies (not (equal fld :mem))
             (equal (xr fld index (mv-nth 1 (wvm48 addr val x86)))
                    (xr fld index x86)))
    :hints (("Goal" :in-theory (e/d* (wvm48) ()))))

  (defthm wvm48-xw-app-view
    (implies (not (equal fld :mem))
             (and (equal (mv-nth 0 (wvm48 addr val (xw fld index value x86)))
                         (mv-nth 0 (wvm48 addr val x86)))
                  (equal (mv-nth 1 (wvm48 addr val (xw fld index value x86)))
                         (xw fld index value (mv-nth 1 (wvm48 addr val x86))))))
    :hints (("Goal" :in-theory (e/d* (wvm48 wvm48) ())))))

(define wvm64
  ((addr :type (signed-byte #.*max-linear-address-size*))
   (val :type (unsigned-byte   64))
   (x86))
  :enabled t
  :guard-hints (("Goal" :in-theory (e/d (logtail) ())))
  :inline t
  :parents (linear-memory-in-app-view)

  (if (mbt (canonical-address-p addr))

      (let* ((4+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 4 (the (signed-byte #.*max-linear-address-size*) addr))))
             (7+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 7 (the (signed-byte #.*max-linear-address-size*) addr)))))

        (if (mbe :logic (canonical-address-p 7+addr)
                 :exec (< (the (signed-byte #.*max-linear-address-size+1*) 7+addr) #.*2^47*))

            (b* ((dword0 (mbe :logic (part-select val :low 0 :width 32)
                              :exec  (logand #xFFFFFFFF val)))
                 (dword1 (mbe :logic (part-select val :low 32 :width 32)
                              :exec  (logand #xFFFFFFFF (ash val -32))))
                 ((mv flg0 x86) (wvm32 addr dword0 x86))
                 ((mv flg1 x86) (wvm32 4+addr dword1 x86)))
                (mbe :logic (if (or flg0 flg1)
                                (mv 'wvm64 x86)
                              (mv nil x86))
                     :exec (mv nil x86)))

          (mv 'wvm64 x86)))

    (mv 'wvm64 x86))

  ///

  (defthm wvm64-no-error
    (implies (and (canonical-address-p addr)
                  (canonical-address-p (+ 7 addr)))
             (equal (mv-nth 0 (wvm64 addr val x86))
                    nil))
    :hints (("Goal" :in-theory (e/d () (force (force))))))

  (defthm x86p-mv-nth-1-wvm64
    (implies (x86p x86)
             (x86p (mv-nth 1 (wvm64 addr val x86))))
    :rule-classes (:type-prescription :rewrite))

  (defthm xr-wmv64-app-view
    (implies (not (equal fld :mem))
             (equal (xr fld index (mv-nth 1 (wvm64 addr val x86)))
                    (xr fld index x86)))
    :hints (("Goal" :in-theory (e/d* (wvm64) ()))))

  (defthm wvm64-xw-app-view
    (implies (not (equal fld :mem))
             (and (equal (mv-nth 0 (wvm64 addr val (xw fld index value x86)))
                         (mv-nth 0 (wvm64 addr val x86)))
                  (equal (mv-nth 1 (wvm64 addr val (xw fld index value x86)))
                         (xw fld index value (mv-nth 1 (wvm64 addr val x86))))))
    :hints (("Goal" :in-theory (e/d* (wvm64 wvm64) ())))))

(define wvm80
  ((addr :type (signed-byte #.*max-linear-address-size*))
   (val :type (unsigned-byte   80))
   (x86))
  :enabled t
  :guard-hints (("Goal" :in-theory (e/d (logtail) ())))
  :inline t
  :parents (linear-memory-in-app-view)

  (if (mbt (canonical-address-p addr))

      (let* ((2+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 2 (the (signed-byte #.*max-linear-address-size*) addr))))
             (9+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 9 (the (signed-byte #.*max-linear-address-size*) addr)))))

        (if (mbe :logic (canonical-address-p 9+addr)
                 :exec (< (the (signed-byte #.*max-linear-address-size+1*) 9+addr) #.*2^47*))

            (b* ((word0 (mbe :logic (part-select val :low 0 :width 16)
                             :exec  (logand #xFFFF val)))
                 (qword1 (mbe :logic (part-select val :low 16 :width 64)
                              :exec  (logand #xFFFFFFFFFFFFFFFF (ash val -16))))
                 ((mv flg0 x86) (wvm16 addr    word0 x86))
                 ((mv flg1 x86) (wvm64 2+addr qword1 x86)))
              (mbe :logic (if (or flg0 flg1)
                              (mv 'wvm80 x86)
                            (mv nil x86))
                   :exec (mv nil x86)))

          (mv 'wvm80 x86)))

    (mv 'wvm80 x86))

  ///

  (defthm wvm80-no-error
    (implies (and (canonical-address-p addr)
                  (canonical-address-p (+ 9 addr)))
             (equal (mv-nth 0 (wvm80 addr val x86))
                    nil))
    :hints (("Goal" :in-theory (e/d () (force (force))))))

  (defthm x86p-mv-nth-1-wvm80
    (implies (x86p x86)
             (x86p (mv-nth 1 (wvm80 addr val x86))))
    :rule-classes (:type-prescription :rewrite))

  (defthm xr-wmv80-app-view
    (implies (not (equal fld :mem))
             (equal (xr fld index (mv-nth 1 (wvm80 addr val x86)))
                    (xr fld index x86)))
    :hints (("Goal" :in-theory (e/d* (wvm80) ()))))

  (defthm wvm80-xw-app-view
    (implies (not (equal fld :mem))
             (and (equal (mv-nth 0 (wvm80 addr val (xw fld index value x86)))
                         (mv-nth 0 (wvm80 addr val x86)))
                  (equal (mv-nth 1 (wvm80 addr val (xw fld index value x86)))
                         (xw fld index value (mv-nth 1 (wvm80 addr val x86))))))
    :hints (("Goal" :in-theory (e/d* (wvm80 wvm80) ())))))

(define wvm128
  ((addr :type (signed-byte #.*max-linear-address-size*))
   (val :type (unsigned-byte   128))
   (x86))
  :enabled t
  :guard-hints (("Goal" :in-theory (e/d (logtail) ())))
  :inline t
  :parents (linear-memory-in-app-view)
  :prepwork ((local (in-theory (e/d () (wvm64)))))
  (if (mbt (canonical-address-p addr))

      (let* ((8+addr (the (signed-byte #.*max-linear-address-size+1*)
                       (+ 8 (the (signed-byte #.*max-linear-address-size*) addr))))
             (15+addr (the (signed-byte #.*max-linear-address-size+1*)
                        (+ 15 (the (signed-byte #.*max-linear-address-size*) addr)))))

        (if (mbe :logic (canonical-address-p 15+addr)
                 :exec (< (the (signed-byte #.*max-linear-address-size+1*) 15+addr) #.*2^47*))

            (b* ((qword0 (mbe :logic (part-select val :low 0 :width 64)
                              :exec  (logand #xFFFFFFFFFFFFFFFF val)))
                 (qword1 (mbe :logic (part-select val :low 64 :width 64)
                              :exec  (logand #xFFFFFFFFFFFFFFFF (ash val -64))))
                 ((mv flg0 x86) (wvm64 addr qword0 x86))
                 ((mv flg1 x86) (wvm64 8+addr qword1 x86)))
                (mbe :logic (if (or flg0 flg1)
                                (mv 'wvm128 x86)
                              (mv nil x86))
                     :exec (mv nil x86)))

          (mv 'wvm128 x86)))

    (mv 'wvm128 x86))

  ///

  (defthm wvm128-no-error
    (implies (and (canonical-address-p addr)
                  (canonical-address-p (+ 15 addr)))
             (equal (mv-nth 0 (wvm128 addr val x86))
                    nil))
    :hints (("Goal" :in-theory (e/d () (force (force))))))

  (defthm x86p-mv-nth-1-wvm128
    (implies (x86p x86)
             (x86p (mv-nth 1 (wvm128 addr val x86))))
    :rule-classes (:type-prescription :rewrite))

  (defthm xr-wmv128-app-view
    (implies (not (equal fld :mem))
             (equal (xr fld index (mv-nth 1 (wvm128 addr val x86)))
                    (xr fld index x86)))
    :hints (("Goal" :in-theory (e/d* (wvm128) ()))))

  (defthm wvm128-xw-app-view
    (implies (not (equal fld :mem))
             (and (equal (mv-nth 0 (wvm128 addr val (xw fld index value x86)))
                         (mv-nth 0 (wvm128 addr val x86)))
                  (equal (mv-nth 1 (wvm128 addr val (xw fld index value x86)))
                         (xw fld index value (mv-nth 1 (wvm128 addr val x86))))))
    :hints (("Goal" :in-theory (e/d* (wvm128 wvm128) ())))))

;; ======================================================================

(globally-disable '(rvm08 rvm16 wvm16 rvm32 rvm48 rvm64 rvm80 rvm128
                    wvm08 wvm16 wvm16 wvm32 wvm48 wvm64 wvm80 wvm128))

;; ======================================================================
