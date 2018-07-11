; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "paging" :dir :machine)
(local (include-book "centaur/gl/gl" :dir :system))

;; ======================================================================

(def-gl-export accessed-bit-set-accessed-bit-identity
  :hyp (and (equal (accessed-bit e) 1)
            (unsigned-byte-p 64 e))
  :concl (equal (set-accessed-bit e) e)
  :g-bindings
  (gl::auto-bindings (:nat e 64)))

(def-gl-export dirty-bit-set-dirty-bit-identity
  :hyp (and (equal (dirty-bit e) 1)
            (unsigned-byte-p 64 e))
  :concl (equal (set-dirty-bit e) e)
  :g-bindings
  (gl::auto-bindings (:nat e 64)))

;; ======================================================================

;; For use in marking-view-top.lisp:

(def-gl-export canonical-address-p-of-lin-addr+7
  :hyp (and (canonical-address-p lin-addr)
            (equal (loghead 3 lin-addr) 0))
  :concl (canonical-address-p (+ 7 lin-addr))
  :g-bindings
  (gl::auto-bindings (:nat lin-addr 64)))

;; ======================================================================

;; For use in gather-paging-structures-thms.lisp:

(def-gl-export pml4-table-entry-addr-and-gather-pml4-table-qword-addresses-helper-1
  :hyp (and (unsigned-byte-p 52 x)
            (equal (loghead 12 x) 0))
  :concl (equal (logand 18446744073709547527 x)
                x)
  :g-bindings `((x (:g-number ,(gl-int 0 1 53)))))

(def-gl-export pml4-table-entry-addr-and-gather-pml4-table-qword-addresses-helper-2
  :hyp (and (canonical-address-p lin-addr)
            (unsigned-byte-p 52 x))
  :concl (< (logior (ash (loghead 9 (logtail 39 lin-addr))
                         3)
                    x)
            (+ 4096 x))
  :g-bindings `((lin-addr (:g-number ,(gl-int 0 2 65)))
                (x        (:g-number ,(gl-int 1 2 65)))))

(def-gl-export page-dir-ptr-table-entry-addr-is-in-a-table-pointed-to-by-a-pml4e-helper-1-1
  :hyp (and (unsigned-byte-p 64 x)
            (canonical-address-p l))
  :concl (<=
          (ash (loghead 40 (logtail 12 x)) 12)
          (logior (ash (loghead 9 (logtail 30 l)) 3)
                  (logand 18446744073709547527
                          (ash (loghead 40 (logtail 12 x)) 12))))
  :g-bindings `((x (:g-number ,(gl-int 0 2 65)))
                (l (:g-number ,(gl-int 1 2 65))))
  :rule-classes :linear)

(def-gl-export page-dir-ptr-table-entry-addr-is-in-a-table-pointed-to-by-a-pml4e-helper-2-1
  :hyp (and (unsigned-byte-p 64 x)
            (canonical-address-p l))
  :concl (<
          (logior (ash (loghead 9 (logtail 30 l)) 3)
                  (ash (loghead 40 (logtail 12 x)) 12))
          (+ 4096 (ash (loghead 40 (logtail 12 x)) 12)))
  :g-bindings `((x (:g-number ,(gl-int 0 2 65)))
                (l (:g-number ,(gl-int 1 2 65))))
  :rule-classes :linear)

(def-gl-export page-directory-entry-addr-is-in-a-table-pointed-to-by-a-pdpte-helper-1
  :hyp (and (unsigned-byte-p 64 x)
            (canonical-address-p l))
  :concl (<
          (logior (ash (loghead 9 (logtail 21 l)) 3)
                  (ash (loghead 40 (logtail 12 x)) 12))
          (+ 4096 (ash (loghead 40 (logtail 12 x)) 12)))
  :g-bindings `((x (:g-number ,(gl-int 0 2 65)))
                (l (:g-number ,(gl-int 1 2 65))))
  :rule-classes :linear)

(def-gl-export page-table-entry-addr-is-in-a-table-pointed-to-by-a-pde-helper-1
  :hyp (and (unsigned-byte-p 64 x)
            (canonical-address-p l))
  :concl (<
          (logior (ash (loghead 9 (logtail 12 l)) 3)
                  (ash (loghead 40 (logtail 12 x)) 12))
          (+ 4096 (ash (loghead 40 (logtail 12 x)) 12)))
  :g-bindings `((x (:g-number ,(gl-int 0 2 65)))
                (l (:g-number ,(gl-int 1 2 65))))
  :rule-classes :linear)

;; For use in paging-basics.lisp:

(def-gl-export 4K-aligned-physical-address-helper
  :hyp (and (unsigned-byte-p 52 x)
            (equal (loghead 12 x) 0))
  :concl (equal (logand 18446744073709547520 x)
                x)
  :g-bindings `((x (:g-number ,(gl-int 0 1 53)))))

(def-gl-export nests-of-set-accessed-bit
  :hyp (unsigned-byte-p 64 e)
  :concl (equal (set-accessed-bit (set-accessed-bit e))
                (set-accessed-bit e))
  :g-bindings `((e (:g-number ,(gl-int 0 1 65)))))

(def-gl-export nests-of-set-dirty-bit
  :hyp (unsigned-byte-p 64 e)
  :concl (equal (set-dirty-bit (set-dirty-bit e))
                (set-dirty-bit e))
  :g-bindings `((e (:g-number ,(gl-int 0 1 65)))))

(def-gl-export pull-out-set-dirty-bit
  :hyp (unsigned-byte-p 64 e)
  :concl (equal (set-accessed-bit (set-dirty-bit e))
                (set-dirty-bit (set-accessed-bit e)))
  :g-bindings `((e (:g-number ,(gl-int 0 1 65)))))

;; For use in paging-*-table-lemmas:

(def-gl-export logand-loghead-and-page-dir-ptr-table-base-addr-helper
  :hyp (unsigned-byte-p 64 x)
  :concl (equal (logand 18446744072635809792 (ash (loghead 22 (logtail 30 x)) 30))
                (ash (loghead 22 (logtail 30 x)) 30))
  :g-bindings `((x (:g-number ,(gl-int 0 1 65)))))

(def-gl-export logand-loghead-and-page-directory-base-addr-helper
  :hyp (unsigned-byte-p 64 x)
  :concl (equal (logand 18446744073709547520 (ash (loghead 40 (logtail 12 x)) 12))
                (ash (loghead 40 (logtail 12 x)) 12))
  :g-bindings `((x (:g-number ,(gl-int 0 1 65)))))


;; ======================================================================

(def-gl-export rm-low-64-and-write-to-physical-memory-equal-helper-1
  :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
            (n08p e) (n08p f) (n08p g) (n08p h))
  :concl (equal
          (logior
           a
           (ash
            (logior
             b
             (ash
              (logior
               c
               (ash
                (logior
                 d
                 (ash
                  (logior
                   e
                   (ash (logior f
                                (ash (logior g
                                             (ash h 8))
                                     8))
                        8))
                  8))
                8))
              8))
            8))
          (logior a
                  (ash b 8)
                  (ash (logior c
                               (ash d 8))
                       16)
                  (ash (logior e
                               (ash f 8)
                               (ash (logior g
                                            (ash h 8))
                                    16))
                       32)))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
         (:nat e 8) (:nat f 8) (:nat g 8) (:nat h 8))))

(def-gl-export rm-low-64-and-write-to-physical-memory-equal-helper-2
  :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
            (n08p e) (n08p f) (n08p g) (n08p h))
  :concl (equal
          (logior (ash b 8)
                  (ash (logior (ash d 8)
                               c)
                       16)
                  (ash (logior (ash f 8)
                               (ash (logior (ash h 8)
                                            g)
                                    16)
                               e)
                       32)
                  a)
          (logior
           a
           (ash
            (logior
             b
             (ash
              (logior
               c
               (ash
                (logior
                 d
                 (ash
                  (logior e
                          (ash (logior f
                                       (ash (logior g
                                                    (ash h 8))
                                            8))
                               8))
                  8))
                8))
              8))
            8)))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
         (:nat e 8) (:nat f 8) (:nat g 8) (:nat h 8))))

(in-theory (e/d () (rm-low-64-and-write-to-physical-memory-equal-helper-1
                    rm-low-64-and-write-to-physical-memory-equal-helper-2)))

;; ======================================================================
