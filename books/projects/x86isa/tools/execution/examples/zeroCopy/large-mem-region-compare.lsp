;; Shilpi Goel

(in-package "X86ISA")

(include-book "../../top" :ttags :all)

;; For the guard proof of the new function introduced by
;; (x86-debug). The sys-view/top book disabled
;; unsigned-byte-p, which causes this failure.
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

;; ======================================================================

;; Initialize the system-level mode of operation
;; 1. Set the programmer-level mode to nil
;; 2. Set CR0.PG  = 1
;; 3. Set CR4.PAE = 1
;; 4. Set CR3.PDB = (logtail 12 address-of-pml4-table)
(init-sys-view
 ;; Address of PML4 Table
 0
 x86)

(!marking-view nil x86)

;; The default paging structures occupy 2,101,248 bytes (#x201000) and
;; are located at address 0.

;; A simple sanity check:
(assert-event (equal (app-view x86) nil))

;; Set CPL = 0 (actually, it's 0 by default, which should change, maybe)
(!seg-visiblei *cs* (!seg-sel-layout-slice :rpl 0 (seg-visiblei *cs* x86)) x86)

;; ======================================================================

(define ones-physical-memory
  ((ptr :type (unsigned-byte #.*physical-address-size*))
   (size :type (unsigned-byte #.*physical-address-size*))
   x86)
  :prepwork ((local (in-theory (e/d (unsigned-byte-p) ()))))
  :short "Write size number of ones bytes starting at ptr."
  :measure (acl2-count size)
  :guard (and (natp ptr)
              (natp size)
              (< (+ size ptr) *mem-size-in-bytes*))
  (if (mbt (and (natp ptr)
                (natp size)
                (< (+ size ptr) *mem-size-in-bytes*)))
      (if (zp size)
          x86
        (b* ((x86 (!memi ptr 1 x86)))
          (ones-physical-memory
           (the (unsigned-byte 60) (1+ ptr))
           (the (unsigned-byte 60) (1- size))
           x86)))
    x86))

;; (ones-physical-memory 0 5 x86)
;; (read-bytes-from-memory 0 8 x86 nil)

;; (time$ (ones-physical-memory 0 *2^30* x86))

(define compare-src-to-dst-memory
  ((src :type (signed-byte #.*max-linear-address-size*))
   (dst :type (signed-byte #.*max-linear-address-size*))
   (size :type (unsigned-byte #.*max-linear-address-size*))
   x86)
  :prepwork ((local (in-theory (e/d (unsigned-byte-p
                                     signed-byte-p
                                     canonical-address-p) ()))))
  :short "Compare size number of bytes starting at linear address
  src to those at dst."
  :measure (acl2-count size)
  :guard (and (integerp src)
              (integerp dst)
              (natp size)
              (signed-byte-p *max-linear-address-size* (+ size src))
              (signed-byte-p *max-linear-address-size* (+ size dst)))
  (if (mbt (and (integerp src)
                (integerp dst)
                (natp size)
                (signed-byte-p *max-linear-address-size* (+ size src))
                (signed-byte-p *max-linear-address-size* (+ size dst))))
      (if (zp size)
          (mv :PASSED x86)
        (b* (((mv src-flg src-byte x86) (rm08 src :r x86))
             ((when src-flg) (mv src-flg x86))
             ((mv dst-flg dst-byte x86) (rm08 dst :r x86))
             ((when dst-flg) (mv dst-flg x86))
             (same? (equal src-byte dst-byte)))
          (if same?
              (compare-src-to-dst-memory
               (the (signed-byte 60) (1+ src))
               (the (signed-byte 60) (1+ dst))
               (the (unsigned-byte 60) (1- size))
               x86)
            (mv :FAILED x86))))
    (mv :FAILED x86)))

;; (ones-physical-memory 0  5 x86)
;; (read-bytes-from-memory 0 8 x86 nil)
;; (ones-physical-memory 20 5 x86)
;; (read-bytes-from-memory 20 8 x86 nil)
;; (compare-src-to-dst-memory
;;  ;; PASSED
;;  0
;;  20
;;  5
;;  x86)
;; (compare-src-to-dst-memory
;;  ;; FAILED
;;  4
;;  20
;;  5
;;  x86)

;; (time$
;;  (compare-src-to-dst-memory
;;   ;; Bytes 0-4 = all 1s
;;   ;; Bytes 20-24 = all 1s
;;   (+ 30 0)
;;   (+ 30 *2^30*)
;;   *2^30*
;;   x86))

;; Make sure that the default page tables aren't being over-written.
(time$ (ones-physical-memory #x400000 *2^30* x86))
(time$ (ones-physical-memory (+ #x400000 *2^30*) *2^30* x86))
(time$
 (compare-src-to-dst-memory
  #x400000            ;; src
  (+ #x400000 *2^30*) ;; dst
  *2^30*              ;; size
  x86))

; (ACL2::EV-REC ACL2::*RETURN-LAST-ARG3* . #@39#) took
; 640.99 seconds realtime, 640.50 seconds runtime
; (128 bytes allocated).
;; (:PASSED <x86>)
