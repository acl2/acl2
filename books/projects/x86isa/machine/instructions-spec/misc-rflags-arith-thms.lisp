;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "../x86-decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
;; ======================================================================

;; Guard proof helper theorems:

(local (include-book "centaur/gl/gl" :dir :system))

;; LOGSQUASH definitions directly plopped in from
;; centaur/bitops/ihsext-basics.
(DEFUN BITOPS::LOGSQUASH$INLINE (N I)
  (DECLARE (XARGS :GUARD (AND (NATP N) (INTEGERP I))))
  (LOGAND I (ASH -1 (NFIX N))))

(DEFMACRO BITOPS::LOGSQUASH (N I)
  (LIST 'BITOPS::LOGSQUASH$INLINE N I))

 (local
  (def-gl-thm !rflags-slice-guard-theorem-helper-using-gl-1
    :hyp (and (unsigned-byte-p 32 input-rflags)
              (unsigned-byte-p 1 cf)
              (unsigned-byte-p 1 pf)
              (unsigned-byte-p 1 af)
              (unsigned-byte-p 1 zf)
              (unsigned-byte-p 1 sf)
              (unsigned-byte-p 1 of))
    :concl
    (equal
     (logior
      cf (ash pf 2)
      (logand
       4294967290 (logior
                   (ash af 4)
                   (logand 4294967278
                           (logior (ash zf 6)
                                   (logand
                                    4294967230
                                    (logior (ash sf 7)
                                            (logand 4294967166
                                                    (logior (logand 4294965246
                                                                    (bitops::logsquash 1 input-rflags))
                                                            (ash of 11))))))))))
     (logior
      cf (logand 4294967294 (logior
                             (ash pf 2)
                             (logand
                              4294967291
                              (logior
                               (ash af 4)
                               (logand
                                4294967279
                                (logior (ash zf 6)
                                        (logand
                                         4294967231
                                         (logior (ash sf 7)
                                                 (logand
                                                  4294967167
                                                  (logior (logand 4294965247 input-rflags)
                                                          (ash of
                                                               11)))))))))))))
    :g-bindings
    (gl::auto-bindings
     (:nat input-rflags 32)
     (:nat cf 1)
     (:nat pf 1)
     (:nat af 1)
     (:nat zf 1)
     (:nat sf 1)
     (:nat of 1))))

 (local
  (def-gl-thm !rflags-slice-guard-theorem-helper-using-gl-2
    :hyp (and (unsigned-byte-p 32 input-rflags)
              (unsigned-byte-p 1 pf)
              (unsigned-byte-p 1 zf)
              (unsigned-byte-p 1 sf))
    :concl
    (equal
     (logior
      (ash pf 2)
      (logand
       4294967290
       (logior (ash zf 6)
               (logand 4294967230
                       (logior (logand 4294965118 (bitops::logsquash 1 input-rflags))
                               (ash sf 7))))))
     (logand
      4294967294
      (logior (ash pf 2)
              (logand 4294967291
                      (logior (ash zf 6)
                              (logand 4294967231
                                      (logior (logand 4294965119 input-rflags)
                                              (ash sf 7))))))))
    :g-bindings
    (gl::auto-bindings
     (:nat input-rflags 32)
     (:nat pf 1)
     (:nat zf 1)
     (:nat sf 1))))

 (defthm !rflags-slice-guard-theorem-helper-1
   (implies (and (unsigned-byte-p 32 input-rflags)
                 (unsigned-byte-p 1 cf)
                 (unsigned-byte-p 1 pf)
                 (unsigned-byte-p 1 af)
                 (unsigned-byte-p 1 zf)
                 (unsigned-byte-p 1 sf)
                 (unsigned-byte-p 1 of))
            (equal
             (logior
              cf (ash pf 2)
              (logand
               4294967290 (logior
                           (ash af 4)
                           (logand 4294967278
                                   (logior (ash zf 6)
                                           (logand
                                            4294967230
                                            (logior (ash sf 7)
                                                    (logand 4294967166
                                                            (logior (logand 4294965246
                                                                            (bitops::logsquash 1 input-rflags))
                                                                    (ash of 11))))))))))
             (logior
              cf (logand 4294967294 (logior
                                     (ash pf 2)
                                     (logand
                                      4294967291
                                      (logior
                                       (ash af 4)
                                       (logand
                                        4294967279
                                        (logior (ash zf 6)
                                                (logand
                                                 4294967231
                                                 (logior (ash sf 7)
                                                         (logand
                                                          4294967167
                                                          (logior (logand 4294965247 input-rflags)
                                                                  (ash of 11))))))))))))))
   :hints (("Goal" :use ((:instance
                          !rflags-slice-guard-theorem-helper-using-gl-1)))))


 (defthm !rflags-slice-guard-theorem-helper-2
   (implies (and (unsigned-byte-p 32 input-rflags)
                 (unsigned-byte-p 1 pf)
                 (unsigned-byte-p 1 zf)
                 (unsigned-byte-p 1 sf))
            (equal
             (logior
              (ash pf 2)
              (logand
               4294967290
               (logior (ash zf 6)
                       (logand 4294967230
                               (logior (logand 4294965118 (bitops::logsquash 1 input-rflags))
                                       (ash sf 7))))))
             (logand
              4294967294
              (logior (ash pf 2)
                      (logand 4294967291
                              (logior (ash zf 6)
                                      (logand 4294967231
                                              (logior (logand 4294965119 input-rflags)
                                                      (ash sf 7)))))))))
   :hints (("Goal" :use ((:instance !rflags-slice-guard-theorem-helper-using-gl-2)))))

;; ======================================================================
