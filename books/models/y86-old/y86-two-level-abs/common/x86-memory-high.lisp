;; x86-memory-high.lisp                                      Shilpi Goel

;; This book is very, very sloppily done.  I'll come back to it later and re-do
;; it nicely.

#||

; [Jared and Sol]: fool make_cert_help.pl into allowing more memory for this
; book. We would just include centaur/misc/memory-mgmt, but that has a ttag.

(set-max-mem (* 6 (expt 2 30)))

||#


(in-package "ACL2")

(include-book "x86-state")

;; rm* and wm* functions as well as their RoW and WoW theorems.

;; ======================================================================

;; rm*:

(local (include-book "centaur/gl/gl" :dir :system))

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

(local
  (def-gl-thm rm16-less-than-expt-2-16-helper
    :hyp (and (n08p byte0)
              (n08p byte1))
    :concl (< (logior (ash byte1 8)
                      byte0)
              65536)
    :g-bindings
    `((byte0 (:g-number ,(gl-int 0 1 9)))
      (byte1 (:g-number ,(gl-int 9 1 9))))))

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


(encapsulate ()

(local
 (def-gl-thm natp-rm32-helper
   :hyp (and (n08p byte0)
             (n08p byte1)
             (n08p byte2)
             (n08p byte3))
   :concl (<= 0
              (LOGIOR (ASH (LOGIOR (ASH byte3 8) byte2)
                           16)
                      (ASH byte1 8)
                      byte0))
   :g-bindings
   `((byte0 (:g-number ,(gl-int 0 2 9)))
     (byte1 (:g-number ,(gl-int 9 2 9)))
     (byte2 (:g-number ,(gl-int 18 2 9)))
     (byte3 (:g-number ,(gl-int 27 2 9))))))

(defthm natp-rm32
  (implies (x86-32p x86-32)
           (and (integerp (rm32 addr x86-32))
                (<= 0 (rm32 addr x86-32))))
  :rule-classes :type-prescription)

(local
  (def-gl-thm rm32-less-than-expt-2-32-helper
    :hyp (and (n08p byte0)
              (n08p byte1)
              (n08p byte2)
              (n08p byte3))
    :concl (< (LOGIOR (ASH (LOGIOR (ASH byte3 8)
                                   byte2)
                           16)
                      (ASH byte1 8)
                      byte0)
              4294967296)
    :g-bindings
    `((byte0 (:g-number ,(gl-int 0 2 9)))
      (byte1 (:g-number ,(gl-int 9 2 9)))
      (byte2 (:g-number ,(gl-int 18 2 9)))
      (byte3 (:g-number ,(gl-int 27 2 9))))))

(defthm rm32-less-than-expt-2-32
  (implies (x86-32p x86-32)
           (< (rm32 addr x86-32) 4294967296))
  :rule-classes :linear)
) ;; End of encapsulate

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
         (x86-32 (!memi      addr  byte0 x86-32))
         (x86-32 (!memi (n32+ 1 addr) byte1 x86-32))
         (x86-32 (!memi (n32+ 2 addr) byte2 x86-32))
         (x86-32 (!memi (n32+ 3 addr) byte3 x86-32)))
    x86-32))

(defthm x86-32p-wm32
  (implies (and (x86-32p x86-32)
                (n32p addr))
           (x86-32p (wm32 addr dword x86-32))))

(in-theory (disable wm32))

;; =====================================================================
;; RoW/WoW theorems for rm* and wm* functions:

; ======================================================================
; rm08 and wm08:
; ======================================================================

(local (in-theory (disable logand-ash-thm-1)))

(local
 (def-gl-thm rm08-wm08-helper-lemma
   :hyp (AND (INTEGERP V)
             (<= 0 V)
             (< V 256))
   :concl
   (EQUAL (LOGAND 255 V) V)
   :g-bindings
   `((v (:g-number ,(gl-int 0 1 9))))))

(defthm rm08-wm08
  (implies (n08p v)
           (equal (rm08 i (wm08 j v x86-32))
                  (if (equal i j)
                      v
                    (rm08 i x86-32))))
  :hints (("Goal" :in-theory (enable rm08 wm08))))

(local (in-theory (disable rm08-wm08-helper-lemma)))

; ======================================================================
; rm16 and wm16:
; ======================================================================

(defthmd rm16-as-rm08
  (equal (rm16 addr x86-32)
         (let ((byte0 (rm08 addr x86-32))
               (byte1 (rm08 (n32+ 1 addr) x86-32)))
           (logior (ash byte1 8) byte0)))
  :hints (("Goal" :in-theory (enable rm16 rm08))))

(encapsulate ()

(local
 (include-book "arithmetic-5/top" :dir :system))

(defthmd wm16-as-wm08
  (equal (wm16 addr val x86-32)
         (let* ((x86-32 (wm08 addr (logand 255 val) x86-32))
                (x86-32 (wm08 (n32+ 1 addr)
                              (ash val -8)
                              x86-32)))
           x86-32))
  :hints (("Goal" :in-theory (enable wm16 wm08))))
) ;; End of encapsulate


(encapsulate ()

(local
 (include-book "arithmetic-5/top" :dir :system))

(defthm clock-arith-helper-1
  (implies (and (natp i)
                (n32p n)
                (< 0 n))
           (equal (equal i (n32+ n i))
                  nil)))
) ;; End of encapsulate


(local
 (def-gl-thm rm16-wm16-same-helper
   :hyp
   (and (integerp v)
        (<= 0 v)
        (< v (expt 2 16)))
   :concl
   (EQUAL (LOGIOR (ASH (LOGAND 255 (ASH V -8)) 8)
                  (LOGAND 255 V))
          V)
   :g-bindings
   `((v (:g-number ,(gl-int 0 1 17))))))

(defthm rm16-wm16-same
  (implies (and (natp i)
                (n16p v))
           (equal (rm16 i (wm16 i v x86-32))
                  v))
  :hints (("Goal" :in-theory (enable rm16 wm16))))

(local (in-theory (disable rm16-wm16-same-helper)))

;; For rm16-wm16, consider the following cases when i != j:
;; 1. (n32+ 1 j) = i
;; 2. (n32+ 1 i) = j
;; 3. Otherwise...

(encapsulate ()

(local
 (include-book "arithmetic-5/top" :dir :system))

(defthm clock-arith-helper-2
  (implies (and (natp i)
                (posp n)
                (< n 2147483648)) ;; 2^31
           (equal (equal i (n32+ n (n32+ n i)))
                  nil)))

) ;; End of encapsulate

(local
 (defthm rm16-wm16-different-1
   (implies (and (natp i)
                 (natp j)
                 (n16p v)
                 (equal (n32+ 1 j) i))
            (equal (rm16 i (wm16 j v x86-32))
                   (logior (ash (memi (n32+ i 1) x86-32) 8)
                           (logand 255 (ash v -8)))))
   :hints (("Goal" :in-theory (enable rm16 wm16)))))

(local
 (defthm rm16-wm16-different-2
   (implies (and (natp i)
                 (natp j)
                 (n16p v)
                 (equal (n32+ 1 i) j))
            (equal (rm16 i (wm16 j v x86-32))
                   (logior (ash (logand 255 v) 8)
                           (memi i x86-32))))
   :hints (("Goal" :in-theory (enable rm16 wm16)))))

(encapsulate ()

(local (include-book "arithmetic-5/top" :dir :system))

(defthm clock-arith-helper-3
  (implies (and (n32p i)
                (n32p j)
                (posp n)
                (n32p n))
           (equal (equal (n32+ n i) (n32+ n j))
                  (equal i j))))
) ;; End of encapsulate

(defthm rm16-wm16
  ;; TO-DO@Shilpi: Clean up the ugly hints!

; Note: The rule clock-arith-helper-3 is the reason why we can not replace
; (n32p i) and (n32p j) in the hypothesis of this theorem by (natp i) and (natp
; j).

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
                                 (memi i x86-32))))))
  :hints (("Goal" :in-theory (e/d (rm16 wm16) ()))
          ("Subgoal 6"
           :in-theory (disable clock-arith-helper-1)
           :use ((:instance clock-arith-helper-1 (n 1))))
          ("Subgoal 1"
           :in-theory (disable clock-arith-helper-2)
           :use ((:instance clock-arith-helper-2
                            (n 1))))
          ("Subgoal 2" :use rm16-wm16-same-helper)
          ("Subgoal 3"
           :in-theory (disable clock-arith-helper-1)
           :use ((:instance clock-arith-helper-1 (n 1)))))
  :otf-flg t)

; ======================================================================
; rm32 and wm32:
; ======================================================================

(defthmd rm32-as-rm08
  (equal (rm32 addr x86-32)
         (let* ((byte0 (rm08 addr x86-32))
                (byte1 (rm08 (n32+ 1 addr) x86-32))
                (byte2 (rm08 (n32+ 2 addr) x86-32))
                (byte3 (rm08 (n32+ 3 addr) x86-32)))
           (logior (ash (logior (ash byte3 8) byte2)
                        16)
                   (logior (ash byte1 8) byte0))))
  :hints (("Goal" :in-theory (enable rm32 rm08))))

(encapsulate ()

(local
 (include-book "arithmetic-5++"))

(defthmd wm32-as-wm08
  (equal (wm32 addr val x86-32)
         (let* ((x86-32 (wm08 addr (logand 255 val) x86-32))
                (x86-32 (wm08 (n32+ 1 addr) (logand 255 (ash val -8)) x86-32))
                (x86-32 (wm08 (n32+ 2 addr) (logand 255 (ash val -16)) x86-32))
                (x86-32 (wm08 (n32+ 3 addr) (logand 255 (ash val -24)) x86-32)))
           x86-32))
  :hints (("Goal" :in-theory (enable wm32 wm08))))
) ;; End of encapsulate


(local
 (def-gl-thm rm32-wm32-same-helper-1
   :hyp
   (AND (INTEGERP V)
        (<= 0 V)
        (< V 4294967296))
   :concl
   (EQUAL (LOGIOR (ASH (LOGIOR (ASH (LOGAND 255 (ASH V -24)) 8)
                               (LOGAND 255 (ASH V -16)))
                       16)
                  (ASH (LOGAND 255 (ASH V -8)) 8)
                  (LOGAND 255 V))
          V)

   :g-bindings
   `((v (:g-number ,(gl-int 0 1 33))))))

(defthm rm32-wm32-same-helper-2
  (implies (n32p v)
           (equal (MEMI (LOGAND (+ 3 I) 4294967295)
                        (!MEMI (LOGAND (+ 3 I) 4294967295)
                               (LOGAND 255 (ASH V -24))
                               (!MEMI (LOGAND (+ 2 I) 4294967295)
                                      (LOGAND 255 (ASH V -16))
                                      (!MEMI (LOGAND (+ 1 I) 4294967295)
                                             (LOGAND 255 (ASH V -8))
                                             (!MEMI I (LOGAND 255 V) X86-32)))))
                  (LOGAND 255 (ASH V -24))))
  :hints (("Goal"
           :in-theory (disable clock-arith-helper-1)
           :use ((:instance clock-arith-helper-1 (n 3))))))

(encapsulate ()

(local (include-book "arithmetic-5/top" :dir :system))

(defthm clock-arith-helper-4
  (implies (and (natp i)
                (not (equal m n))
                (posp n)
                (n32p n)
                (posp m)
                (n32p m))
           (equal (equal (n32+ m i) (n32+ n i))
                  nil)))
) ;; End of encapsulate

(defthm rm32-wm32-same-helper-3
  (implies (and (natp i)
                (n32p v))
           (equal (MEMI (LOGAND (+ 2 I) 4294967295)
                        (!MEMI (LOGAND (+ 3 I) 4294967295)
                               (LOGAND 255 (ASH V -24))
                               (!MEMI (LOGAND (+ 2 I) 4294967295)
                                      (LOGAND 255 (ASH V -16))
                                      (!MEMI (LOGAND (+ 1 I) 4294967295)
                                             (LOGAND 255 (ASH V -8))
                                             (!MEMI I (LOGAND 255 V) X86-32)))))
                  (LOGAND 255 (ASH V -16)))))


(defthm rm32-wm32-same-helper-4
  (implies (and (natp i)
                (n32p v))
           (equal (MEMI (LOGAND (+ 1 I) 4294967295)
                        (!MEMI (LOGAND (+ 3 I) 4294967295)
                               (LOGAND 255 (ASH V -24))
                               (!MEMI (LOGAND (+ 2 I) 4294967295)
                                      (LOGAND 255 (ASH V -16))
                                      (!MEMI (LOGAND (+ 1 I) 4294967295)
                                             (LOGAND 255 (ASH V -8))
                                             (!MEMI I (LOGAND 255 V)
                                                    X86-32)))))
                  (LOGAND 255 (ASH V -8)))))

(defthm rm32-wm32-same-helper-5
  (implies (and (natp i)
                (n32p v))
           (equal (MEMI I
                        (!MEMI (LOGAND (+ 3 I) 4294967295)
                               (LOGAND 255 (ASH V -24))
                               (!MEMI (LOGAND (+ 2 I) 4294967295)
                                      (LOGAND 255 (ASH V -16))
                                      (!MEMI (LOGAND (+ 1 I) 4294967295)
                                             (LOGAND 255 (ASH V -8))
                                             (!MEMI I (LOGAND 255 V) X86-32)))))
                  (LOGAND 255 V))))


(defthm rm32-wm32-same
  (implies (and (natp i)
                (n32p v))
           (equal (rm32 i (wm32 i v x86-32))
                  v))
  :hints (("Goal"
           :in-theory (e/d (rm32) (memi-!memi
                                   !memi-!memi-same
                                   !memi-!memi-different))
           :expand (wm32 i v x86-32))))

;; Locally disabling this rule since it is a def-gl-thm, and the GL books have
;; been included locally.
(local (in-theory (disable rm32-wm32-same-helper-1)))

(in-theory (disable
            rm32-wm32-same-helper-2
            rm32-wm32-same-helper-3
            rm32-wm32-same-helper-4
            rm32-wm32-same-helper-5))


;; (i-am-here)

;; For rm32-wm32, consider the following cases when i != j:
;; 1. (n32+ 1 j) = i
;; 2. (n32+ 2 j) = i
;; 3. (n32+ 3 j) = i
;; 4. (n32+ 1 i) = j
;; 5. (n32+ 2 i) = j
;; 6. (n32+ 3 i) = j


;; rm32:
;; (logior (ash (logior (ash byte3 8) byte2)
;;              16)
;;         (logior (ash byte1 8) byte0))


;; (defthm rm32-wm32-different-1-helper-1
;;   (implies (and (natp i)
;;                 (natp j)
;;                 (n32p v))
;;            (equal (MEMI (LOGAND (+ 3 (LOGAND (+ 1 J) 4294967295))
;;                                 4294967295)
;;                         (!MEMI (LOGAND (+ 3 J) 4294967295)
;;                                (LOGAND 255 (ASH V -24))
;;                                (!MEMI (LOGAND (+ 2 J) 4294967295)
;;                                       (LOGAND 255 (ASH V -16))
;;                                       (!MEMI (LOGAND (+ 1 J) 4294967295)
;;                                              (LOGAND 255 (ASH V -8))
;;                                              (!MEMI J (LOGAND 255 V)
;;                                                     X86-32)))))
;;                   (MEMI (LOGAND (+ 3 (LOGAND (+ 1 J) 4294967295))
;;                                 4294967295)
;;                         x86-32))))


;; (defthm rm32-wm32-different-1
;;   (implies (and (natp i)
;;                 (natp j)
;;                 (n32p v)
;;                 (equal (n32+ 1 j) i))
;;            (equal (rm32 i (wm32 j v x86-32))
;;                   (logior (ash (logior (ash (memi (n32+ 3 i) x86-32) 8)
;;                                        (LOGAND 255 (ASH V -24)))
;;                                16)
;;                           (logior (ash (LOGAND 255 (ASH V -16))
;;                                        8)
;;                                   (LOGAND 255 (ASH V -8))))))
;;   :hints (("Goal"
;;            :in-theory (e/d (rm32) (!memi-!memi-different
;;                                    !memi-!memi-same
;;                                    memi-!memi))
;;            :expand (wm32 j v x86-32))))
