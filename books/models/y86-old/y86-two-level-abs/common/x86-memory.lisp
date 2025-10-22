;; x86-memory.lisp                                         Shilpi Goel

(in-package "ACL2")

(include-book "x86-memory-high")

(set-enforce-redundancy t)

;; ======================================================================

;; rm* and wm*:

(defun rm08 (addr x86-32)
  (declare (xargs :stobjs x86-32
                  :guard (and (integerp addr)
                              (<= 0 addr)
                              (< addr *mem-size-in-bytes*))))
  (memi addr x86-32))

(defthm natp-rm08
  (implies (x86-32p x86-32)
           (and (integerp (rm08 addr x86-32))
                (<= 0 (rm08 addr x86-32))))
  :rule-classes :type-prescription)

(defthm rm08-less-than-expt-2-32
  (implies (x86-32p x86-32)
           (< (rm08 addr x86-32) 256))
  :rule-classes :linear)

(in-theory (disable rm08))

(defun rm16 (addr x86-32)
  (declare (xargs :guard (n32p addr)
                  :stobjs x86-32))
  (let* ((byte0 (memi addr x86-32))
         (byte1 (memi (n32+ addr 1) x86-32))
         (word  (logior (ash byte1 8)
                        byte0)))
    word))

(defthm natp-rm16
  (implies (x86-32p x86-32)
           (and (integerp (rm16 addr x86-32))
                (<= 0 (rm16 addr x86-32))))
  :rule-classes :type-prescription)

(defthm rm16-less-than-expt-2-16
  (implies (x86-32p x86-32)
           (< (rm16 addr x86-32) 65536))
  :rule-classes :linear)

(in-theory (disable rm16))

(defun rm32 (addr x86-32)
  (declare (xargs :stobjs x86-32
                  :guard (n32p addr)))
  (let* ((byte0 (memi      addr x86-32))
         (byte1 (memi (n32+ 1 addr) x86-32))
         (word0 (logior (ash byte1 8)
                        byte0))

         (byte2 (memi (n32+ 2 addr) x86-32))
         (byte3 (memi (n32+ 3 addr) x86-32))
         (word1 (logior (ash byte3 8)
                        byte2))

         (dword (logior (ash word1 16)
                        word0)))
    dword))

(defthm natp-rm32
  (implies (x86-32p x86-32)
           (and (integerp (rm32 addr x86-32))
                (<= 0 (rm32 addr x86-32))))
  :rule-classes :type-prescription)

(defthm rm32-less-than-expt-2-32
  (implies (x86-32p x86-32)
           (< (rm32 addr x86-32) 4294967296))
  :rule-classes :linear)

(in-theory (disable rm32))

;; wm*:

(defun wm08 (addr val x86-32)
  (declare (xargs :stobjs x86-32
                  :guard (and (integerp addr)
                              (<= 0 addr)
                              (< addr *mem-size-in-bytes*)
                              (n08p val))))
  (!memi addr (logand 255 val) x86-32))

(defthm x86-32p-wm08
  (implies (and (x86-32p x86-32)
                (n32p addr))
           (x86-32p (wm08 addr byte x86-32))))

(in-theory (disable wm08))

(defun wm16 (addr val x86-32)
  (declare (xargs :stobjs x86-32
                  :guard (and (n32p addr)
                              (n16p val))))
  (let* ((byte0 (logand #xff val))
         (byte1 (logand #xff (ash val -8)))

         (x86-32 (!memi      addr  byte0 x86-32))
         (x86-32 (!memi (n32+ 1 addr) byte1 x86-32)))
    x86-32))

(defthm x86-32p-wm16
  (implies (and (x86-32p x86-32)
                (n32p addr))
           (x86-32p (wm16 addr word x86-32))))

(in-theory (disable wm16))

(defun wm32 (addr val x86-32)
  (declare (xargs :stobjs x86-32
                  :guard (and (n32p addr)
                              (n32p val))))
  (let* ((byte0 (logand #xff val))
         (byte1 (logand #xff (ash val -8)))
         (byte2 (logand #xff (ash val -16)))
         (byte3 (logand #xff (ash val -24)))
         (x86-32 (!memi         addr  byte0 x86-32))
         (x86-32 (!memi (n32+ 1 addr) byte1 x86-32))
         (x86-32 (!memi (n32+ 2 addr) byte2 x86-32))
         (x86-32 (!memi (n32+ 3 addr) byte3 x86-32)))
    x86-32))

(defthm x86-32p-wm32
  (implies (and (x86-32p x86-32)
                (n32p addr))
           (x86-32p (wm32 addr dword x86-32))))

(in-theory (disable wm32))

;; ======================================================================

;; RoW/WoW theorems:

(defthm rm08-wm08
  (implies (n08p v)
           (equal (rm08 i (wm08 j v x86-32))
                  (if (equal i j)
                      v
                    (rm08 i x86-32)))))

(defthm rm16-wm16
  (implies (and (n32p i)
                (n32p j)
                (n16p v))
           (equal (rm16 i (wm16 j v x86-32))
                  (cond ((equal i j)
                         v)
                        ((equal (n32+ 1 j) i)
                         (logior (ash (memi (n32+ i 1) x86-32) 8)
                                 (logand 255 (ash v -8))))
                        ((equal (n32+ 1 i) j)
                         (logior (ash (logand 255 v) 8)
                                 (memi i x86-32)))
                        (t
                         (logior (ash (memi (n32+ i 1) x86-32) 8)
                                 (memi i x86-32)))))))

;; TO-DO@Shilpi:  Have rm32 RoW and other WoW theorems.

;; ======================================================================