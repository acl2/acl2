; RISC-V Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (acoglio on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "library-extensions")
(include-book "bytes")

(include-book "kestrel/fty/ubyte16" :dir :system)
(include-book "kestrel/fty/ubyte32" :dir :system)

(include-book "kestrel/fty/ubyte8-list" :dir :system)
(include-book "kestrel/fty/ubyte64-list" :dir :system)

(include-book "kestrel/fty/deflist-of-len" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable ash ifix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist-of-len xregfile
  :list-type ubyte64-list
  :length 32
  :pred xregfilep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *mem-size*
  100)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(fty::deflist-of-len memory
    :list-type ubyte8-list
    :length ,*mem-size*
    :pred memoryp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod state64i
  ((xregfile xregfile)
   (pc ubyte64)
   (mem memory)
   (error bool))
  :layout :list
  :tag :state64i
  :pred state64ip)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule len-of-state64i->mem
  (equal (len (state64i->mem stat))
         *mem-size*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-xreg-unsigned ((reg ubyte5p) (stat state64ip))
  :returns (val ubyte64p
                :hints (("Goal" :in-theory (enable ubyte5-fix ubyte5p))))
  (nth (ubyte5-fix reg)
       (state64i->xregfile stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-xreg-signed ((reg ubyte5p) (stat state64ip))
  :returns (val sbyte64p)
  (logext 64 (read-xreg-unsigned reg stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-xreg-unsigned32 ((reg ubyte5p) (stat state64ip))
  :returns (val ubyte32p)
  (loghead 32 (read-xreg-unsigned reg stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-xreg-signed32 ((reg ubyte5p) (stat state64ip))
  :returns (val sbyte32p)
  (logext 32 (read-xreg-signed reg stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-xreg ((reg ubyte5p) (val integerp) (stat state64ip))
  :returns (new-stat state64ip)
  (if (ubyte5-equiv reg 0)
      (state64i-fix stat)
    (change-state64i stat :xregfile (update-nth (ubyte5-fix reg)
                                                (loghead 64 val)
                                                (state64i->xregfile stat))))
  :guard-hints (("Goal" :in-theory (enable xregfilep
                                           state64ip
                                           state64i->xregfile
                                           ubyte5p)))
  ///
  (fty::deffixequiv write-xreg
    :hints (("Goal" :in-theory (enable loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-xreg-32 ((reg ubyte5p) (val integerp) (stat state64ip))
  :returns (new-stat state64ip)
  (write-xreg reg (logext 32 val) stat)
  ///
  (fty::deffixequiv write-xreg-32
    :hints (("Goal" :in-theory (enable logext loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-pc ((stat state64ip))
  :returns (pc ubyte64p)
  (state64i->pc stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-pc ((pc integerp) (stat state64ip))
  :returns (new-stat state64ip)
  (change-state64i stat :pc (loghead 64 pc))
  ///
  (fty::deffixequiv write-pc
    :hints (("Goal" :in-theory (enable loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define inc-pc ((stat state64ip))
  :returns (new-stat state64ip)
  (write-pc (+ (read-pc stat) 4) stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-mem-ubyte8 ((addr integerp) (stat state64ip))
  :returns (val ubyte8p)
  (b* ((addr (loghead 64 addr)))
    (if (< addr *mem-size*)
        (nth addr (state64i->mem stat))
      0))
  :prepwork ((local (include-book "ihs/logops-lemmas" :dir :system)))
  ///

  (more-returns
   (val natp
        :rule-classes :type-prescription
        :hints (("Goal"
                 :use ubyte8p-of-read-mem-ubyte8
                 :in-theory (e/d (ubyte8p) (ubyte8p-of-read-mem-ubyte8))))))

  (defret read-mem-ubyte8-upper-bound
    (< val 256)
    :rule-classes :linear
    :hints (("Goal"
             :use ubyte8p-of-read-mem-ubyte8
             :in-theory (e/d (ubyte8p) (ubyte8p-of-read-mem-ubyte8)))))

  (fty::deffixequiv read-mem-ubyte8
    :hints (("Goal" :in-theory (enable loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-mem-ubyte16-lendian ((addr integerp) (stat state64ip))
  :returns (val ubyte16p :hints (("Goal" :in-theory (enable ubyte16p))))
  (b* ((b0 (read-mem-ubyte8 addr stat))
       (b1 (read-mem-ubyte8 (1+ (ifix addr)) stat)))
    (+ b0
       (ash b1 8)))
  :prepwork ((local (include-book "arithmetic-5/top" :dir :system)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-mem-ubyte32-lendian ((addr integerp) (stat state64ip))
  :returns (val ubyte32p :hints (("Goal" :in-theory (enable ubyte32p))))
  (b* ((b0 (read-mem-ubyte8 addr stat))
       (b1 (read-mem-ubyte8 (+ 1 (ifix addr)) stat))
       (b2 (read-mem-ubyte8 (+ 2 (ifix addr)) stat))
       (b3 (read-mem-ubyte8 (+ 3 (ifix addr)) stat)))
    (+ b0
       (ash b1 8)
       (ash b2 16)
       (ash b3 24)))
  :prepwork ((local (include-book "arithmetic-5/top" :dir :system)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-mem-ubyte64-lendian ((addr integerp) (stat state64ip))
  :returns (val ubyte64p :hints (("Goal" :in-theory (enable ubyte64p))))
  (b* ((b0 (read-mem-ubyte8 addr stat))
       (b1 (read-mem-ubyte8 (+ 1 (ifix addr)) stat))
       (b2 (read-mem-ubyte8 (+ 2 (ifix addr)) stat))
       (b3 (read-mem-ubyte8 (+ 3 (ifix addr)) stat))
       (b4 (read-mem-ubyte8 (+ 4 (ifix addr)) stat))
       (b5 (read-mem-ubyte8 (+ 5 (ifix addr)) stat))
       (b6 (read-mem-ubyte8 (+ 6 (ifix addr)) stat))
       (b7 (read-mem-ubyte8 (+ 7 (ifix addr)) stat)))
    (+ b0
       (ash b1 8)
       (ash b2 16)
       (ash b3 24)
       (ash b4 32)
       (ash b5 40)
       (ash b6 48)
       (ash b7 56)))
  :prepwork ((local (include-book "arithmetic-5/top" :dir :system)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-mem-ubyte8 ((addr integerp) (val ubyte8p) (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((addr (loghead 64 addr)))
    (if (< addr *mem-size*)
        (change-state64i stat :mem (update-nth (loghead 64 addr)
                                               (ubyte8-fix val)
                                               (state64i->mem stat)))
      (state64i-fix stat)))
  :guard-hints (("Goal" :in-theory (enable memoryp)))
  :prepwork ((local (include-book "ihs/logops-lemmas" :dir :system)))
  ///
  (fty::deffixequiv write-mem-ubyte8
    :hints (("Goal" :in-theory (enable loghead)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-mem-ubyte16-lendian ((addr integerp)
                                   (val ubyte16p)
                                   (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((val (ubyte16-fix val))
       (b0 (logand val #xff))
       (b1 (ash val -8))
       (stat (write-mem-ubyte8 addr b0 stat))
       (stat (write-mem-ubyte8 (1+ (ifix addr)) b1 stat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable ubyte8p ubyte16p)))
  :prepwork ((local (include-book "ihs/logops-lemmas" :dir :system))
             (local (include-book "arithmetic-5/top" :dir :system)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-mem-ubyte32-lendian ((addr integerp)
                                   (val ubyte32p)
                                   (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((val (ubyte32-fix val))
       (b0 (logand val #xff))
       (b1 (logand (ash val -8) #xff))
       (b2 (logand (ash val -16) #xff))
       (b3 (logand (ash val -24) #xff))
       (stat (write-mem-ubyte8 addr b0 stat))
       (stat (write-mem-ubyte8 (+ 1 (ifix addr)) b1 stat))
       (stat (write-mem-ubyte8 (+ 2 (ifix addr)) b2 stat))
       (stat (write-mem-ubyte8 (+ 3 (ifix addr)) b3 stat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable ubyte8p ubyte32p)))
  :prepwork ((local (include-book "ihs/logops-lemmas" :dir :system))
             (local (include-book "arithmetic-5/top" :dir :system)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-mem-ubyte64-lendian ((addr integerp)
                                   (val ubyte64p)
                                   (stat state64ip))
  :returns (new-stat state64ip)
  (b* ((val (ubyte64-fix val))
       (b0 (logand val #xff))
       (b1 (logand (ash val -8) #xff))
       (b2 (logand (ash val -16) #xff))
       (b3 (logand (ash val -24) #xff))
       (b4 (logand (ash val -32) #xff))
       (b5 (logand (ash val -40) #xff))
       (b6 (logand (ash val -48) #xff))
       (b7 (logand (ash val -56) #xff))
       (stat (write-mem-ubyte8 addr b0 stat))
       (stat (write-mem-ubyte8 (+ 1 (ifix addr)) b1 stat))
       (stat (write-mem-ubyte8 (+ 2 (ifix addr)) b2 stat))
       (stat (write-mem-ubyte8 (+ 3 (ifix addr)) b3 stat))
       (stat (write-mem-ubyte8 (+ 4 (ifix addr)) b4 stat))
       (stat (write-mem-ubyte8 (+ 5 (ifix addr)) b5 stat))
       (stat (write-mem-ubyte8 (+ 6 (ifix addr)) b6 stat))
       (stat (write-mem-ubyte8 (+ 7 (ifix addr)) b7 stat)))
    stat)
  :guard-hints (("Goal" :in-theory (enable ubyte8p ubyte64p)))
  :prepwork ((local (include-book "ihs/logops-lemmas" :dir :system))
             (local (include-book "arithmetic-5/top" :dir :system)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define errorp ((stat state64ip))
  :returns (yes/no booleanp)
  (state64i->error stat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define error ((stat state64ip))
  :returns (new-stat state64ip)
  (change-state64i stat :error t)
  :hooks (:fix))
