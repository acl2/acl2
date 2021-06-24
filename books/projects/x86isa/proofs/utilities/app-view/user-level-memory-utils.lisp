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

(include-book "row-wow-thms" :ttags :all :dir :proof-utils)
(include-book "general-memory-utils" :ttags :all :dir :proof-utils)
(include-book "clause-processors/find-subterms" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

;; ======================================================================
;; ----------------------------------------------------------------------
;; Debugging:
;; ----------------------------------------------------------------------

;; If you think some rules from this book should fire when you are
;; unwinding your (x86-run ... x86) expression, monitoring the
;; following rules (maybe using Jared Davis's why macro) can tell you
;; (maybe) what's going on.

;; (acl2::why x86-run-opener-not-ms-not-zp-n)
;; (acl2::why x86-fetch-decode-execute-opener)
;; (acl2::why get-prefixes-opener-lemma-no-prefix-byte)
;; (acl2::why get-prefixes-opener-lemma-no-legacy-prefix-but-rex-prefix)
;; (acl2::why one-read-with-rb-from-program-at)
;; (acl2::why program-at-wb-disjoint)

;; ======================================================================

(local (in-theory (enable rvm08 wvm08)))

;; Theorems about rvm08 and wvm08:

;; rvm08 and wmw08 RoW:

(defthm |(rvm08 addr2 (wvm08 addr1 val x86)) --- same addr|
  (implies (and (equal addr1 addr2)
                (canonical-address-p addr1))
           (equal (rvm08 addr2 (mv-nth 1 (wvm08 addr1 val x86)))
                  (mv nil (loghead 8 val) (mv-nth 1 (wvm08 addr1 val x86))))))

(defthm |(rvm08 addr2 (wvm08 addr1 val x86)) --- disjoint addr|
  (implies (not (equal addr1 addr2))
           (equal (rvm08 addr2 (mv-nth 1 (wvm08 addr1 val x86)))
                  (mv (mv-nth 0 (rvm08 addr2 x86))
                      (mv-nth 1 (rvm08 addr2 x86))
                      (mv-nth 1 (wvm08 addr1 val x86)))))
  :hints (("Goal" :in-theory (e/d ()
                                  ((force) force)))))

;; wvm08 WoW:

(defthm |(wvm08 addr2 val2 (wvm08 addr1 val1 x86)) --- same addr|
  (implies (equal addr1 addr2)
           (equal (wvm08 addr2 val2 (mv-nth 1 (wvm08 addr1 val1 x86)))
                  (wvm08 addr2 val2 x86))))

(defthm |(wvm08 addr2 val2 (wvm08 addr1 val1 x86)) --- disjoint addr|
  (implies (not (equal addr1 addr2))
           (equal (mv-nth 1 (wvm08 addr2 val2 (mv-nth 1 (wvm08 addr1 val1 x86))))
                  (mv-nth 1 (wvm08 addr1 val1 (mv-nth 1 (wvm08 addr2 val2 x86))))))
  :hints (("Goal" :in-theory (e/d () ())))
  :rule-classes ((:rewrite :loop-stopper ((addr2 addr1)))))

(local (in-theory (disable rvm08 wvm08)))

;; ----------------------------------------------------------------------

;; Lemmas about rb, wb, and other state accessors/updaters:

(defthm rb-write-user-rflags-in-app-view
  (implies (app-view x86)
           (equal (mv-nth 1 (rb n addr r-x (write-user-rflags flags mask x86)))
                  (mv-nth 1 (rb n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d* (write-user-rflags) (rb force (force))))))

(defthm write-user-rflags-and-wb-in-app-view
  (implies (app-view x86)
           (equal (write-user-rflags flags mask (mv-nth 1 (wb n addr w val x86)))
                  (mv-nth 1 (wb n addr w val (write-user-rflags flags mask x86)))))
  :hints (("Goal" :do-not '(preprocess) :do-not-induct t
           :in-theory (e/d* (write-user-rflags)
                            (acl2::loghead-identity
                             wb force (force))))))

(defthm alignment-checking-enabled-p-and-wb-in-app-view
  (implies (app-view x86)
           (equal (alignment-checking-enabled-p (mv-nth 1 (wb n addr w val x86)))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal" :in-theory (e/d* (alignment-checking-enabled-p)
                                   (wb force (force))))))

(defthm write-x86-file-contents-wb
  (implies (app-view x86)
           (equal (write-x86-file-contents i v (mv-nth 1 (wb n addr w val x86)))
                  (mv-nth 1 (wb n addr w val (write-x86-file-contents i v x86)))))
  :hints (("Goal" :in-theory (e/d* (write-x86-file-contents
                                    write-x86-file-contents-logic)
                                   ()))))

(defthm delete-x86-file-contents-wb
  (implies (app-view x86)
           (equal (delete-x86-file-contents i (mv-nth 1 (wb n addr w val x86)))
                  (mv-nth 1 (wb n addr w val (delete-x86-file-contents i x86)))))
  :hints (("Goal" :in-theory (e/d* (delete-x86-file-contents
                                    delete-x86-file-contents-logic)
                                   ()))))

(defthm pop-x86-oracle-wb
  (implies (app-view x86)
           (equal (mv-nth 1 (pop-x86-oracle (mv-nth 1 (wb n addr w val x86))))
                  (mv-nth 1 (wb n addr w val (mv-nth 1 (pop-x86-oracle x86))))))
  :hints (("Goal" :in-theory (e/d* (pop-x86-oracle pop-x86-oracle-logic) (wb)))))

(defthm rb-and-write-x86-file-des
  (implies (app-view x86)
           (equal (mv-nth 1 (rb n addr r-x (write-x86-file-des i val x86)))
                  (mv-nth 1 (rb n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d* (write-x86-file-des write-x86-file-des-logic)
                                   (rb)))))

(defthm rb-and-write-x86-file-contents
  (implies (app-view x86)
           (equal (mv-nth 1 (rb n addr r-x (write-x86-file-contents i val x86)))
                  (mv-nth 1 (rb n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d* (write-x86-file-contents
                                    write-x86-file-contents-logic)
                                   (rb)))))

(defthm rb-and-pop-x86-oracle
  (implies (app-view x86)
           (equal (mv-nth 1 (rb n addr r-x (mv-nth 1 (pop-x86-oracle x86))))
                  (mv-nth 1 (rb n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d* (pop-x86-oracle pop-x86-oracle-logic) (rb)))))

(defthm delete-x86-file-des-wb
  (implies (app-view x86)
           (equal (delete-x86-file-des i (mv-nth 1 (wb n addr w val x86)))
                  (mv-nth 1 (wb n addr w val (delete-x86-file-des i x86)))))
  :hints (("Goal" :in-theory (e/d* (delete-x86-file-des
                                    delete-x86-file-des-logic)
                                   ()))))

;; ======================================================================

;; Some lemmas about the interaction of rb and wb:

;; rb-wb-disjoint --- rb reads bytes not written by wb:

(local
 (defthm rvm08-wb-1-disjoint
   (implies (or (< addr-1 addr-2)
                (<= (+ n addr-2) addr-1))
            (equal (mv-nth 1 (rvm08 addr-1 (mv-nth 1 (wb-1 n addr-2 w val x86))))
                   (mv-nth 1 (rvm08 addr-1 x86))))))

(local
 (defthm rb-1-wb-1-disjoint
   (implies (or (<= (+ n-2 addr-2) addr-1)
                (<= (+ n-1 addr-1) addr-2))
            (and
             (equal (mv-nth 0 (rb-1 n-1 addr-1 r-x
                                    (mv-nth 1 (wb-1 n-2 addr-2 w val x86))))
                    (mv-nth 0 (rb-1 n-1 addr-1 r-x x86)))
             (equal (mv-nth 1 (rb-1 n-1 addr-1 r-x
                                    (mv-nth 1 (wb-1 n-2 addr-2 w val x86))))
                    (mv-nth 1 (rb-1 n-1 addr-1 r-x x86)))))
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (e/d* (push-ash-inside-logior)
                             (rvm08 wvm08))))))

(defthm rb-wb-disjoint
  (implies (and (separate r-x n-1 addr-1 w n-2 addr-2)
                (app-view x86))
           (and
            (equal (mv-nth 0 (rb n-1 addr-1 r-x (mv-nth 1 (wb n-2 addr-2 w val x86))))
                   (mv-nth 0 (rb n-1 addr-1 r-x x86)))
            (equal (mv-nth 1 (rb n-1 addr-1 r-x (mv-nth 1 (wb n-2 addr-2 w val x86))))
                   (mv-nth 1 (rb n-1 addr-1 r-x x86)))))
  :hints (("Goal"
           :use ((:instance rb-1-wb-1-disjoint))
           :in-theory (e/d* (rb wb separate)
                            (rb-1-wb-1-disjoint wb-1 rb-1)))))

;; rb-wb-equal --- rb reads all the bytes written by wb:

(local
 (defthm rb-1-wb-1-equal
   (implies (and (canonical-address-p addr)
                 (canonical-address-p (+ -1 n addr))
                 (posp n))
            (equal (mv-nth 1 (rb-1 n addr r-x (mv-nth 1 (wb-1 n addr w val x86))))
                   (loghead (ash n 3) val)))
   :hints (("Goal" :in-theory (e/d* (push-ash-inside-logior
                                     rb-1-opener-theorem
                                     wb-1-opener-theorem)
                                    (unsigned-byte-p))))))

(defthm rb-wb-equal
  (implies (and (canonical-address-p addr)
                (canonical-address-p (+ -1 n addr))
                (posp n)
                (app-view x86))
           (equal (mv-nth 1 (rb n addr r-x (mv-nth 1 (wb n addr w val x86))))
                  (loghead (ash n 3) val)))
  :hints (("Goal" :in-theory (e/d* (wb) (rb-1 wb-1)))))

;; rb-wb-subset --- rb reads a subset of the bytes written by wb:

(local
 (defthmd rb-1-wb-1-subset-helper-1
   (implies (and (< (+ addr-1 n-1) (+ addr-2 n-2))
                 (<= addr-2 addr-1)
                 (canonical-address-p addr-2)
                 (canonical-address-p (+ -1 n-2 addr-2))
                 (not (zp n-1)))
            (signed-byte-p 48 (+ 1 addr-2)))))

(local
 (defthmd rb-1-wb-1-same-start-address-different-op-sizes
   (implies (and
             (< n-1 n-2)
             (canonical-address-p addr-1)
             (canonical-address-p (+ -1 n-1 addr-1))
             (canonical-address-p (+ -1 n-2 addr-1))
             (unsigned-byte-p (ash n-2 3) val)
             (posp n-1)
             (posp n-2)
             (x86p x86))
            (equal (mv-nth 1 (rb-1 n-1 addr-1 r-x
                                   (mv-nth 1 (wb-1 n-2 addr-1 w val x86))))
                   (loghead (ash n-1 3) val)))
   :hints (("Goal"
            :induct (rb-1 n-1 addr-1 r-x (mv-nth 1 (wb-1 n-2 addr-1 w val x86)))
            :in-theory (e/d* (ifix
                              nfix
                              rb-1-opener-theorem
                              wb-1-opener-theorem
                              rb-1-wb-1-subset-helper-1)
                             (unsigned-byte-p))))))

(defun-nx rb-1-wb-1-induction-scheme (n-1 a-1 n-2 a-2 val x86)
;                      a-2
;   ------------------------------------------------------------------------
; ...   |   |   |   | w | w | w | w |   |   |   |   |   |   |   |   |   |  ...
;   ------------------------------------------------------------------------
;   0                    a-1                                               max
  (cond ((or (zp n-1) (zp n-2) (<= n-2 n-1))
         (mv n-1 a-1 n-2 a-2 val x86))
        ((equal a-1 a-2)
         ;; n-1 and n-2 are irrelevant here.  See
         ;; rb-1-wb-1-same-start-address-different-op-sizes.
         (mv n-1 a-1 n-2 a-2 val x86))
        ((< a-2 a-1)
         ;; Write a byte that won't be read by rb-1.
         (b* (((mv & x86)
               (wvm08 a-2 (loghead 8 val) x86))
              (n-2 (1- n-2))
              (a-2 (1+ a-2))
              (val (logtail 8 val)))
           (rb-1-wb-1-induction-scheme n-1 a-1 n-2 a-2 val x86)))))

(local
 (defthm rb-1-wb-1-subset
   (implies (and
             (< (+ addr-1 n-1) (+ addr-2 n-2))
             (<= addr-2 addr-1)
             (canonical-address-p addr-1)
             (canonical-address-p (+ -1 n-1 addr-1))
             (canonical-address-p addr-2)
             (canonical-address-p (+ -1 n-2 addr-2))
             (unsigned-byte-p (ash n-2 3) val)
             (posp n-1)
             (posp n-2)
             (x86p x86))
            (equal (mv-nth 1 (rb-1 n-1 addr-1 r-x
                                   (mv-nth 1 (wb-1 n-2 addr-2 w val x86))))
                   (part-select val
                                :low (ash (- addr-1 addr-2) 3)
                                :width (ash n-1 3))))
   :hints (("Goal"
            :induct (rb-1-wb-1-induction-scheme n-1 addr-1 n-2 addr-2 val x86)
            :in-theory (e/d* (ifix
                              nfix
                              rb-1-opener-theorem
                              wb-1-opener-theorem
                              rb-1-wb-1-subset-helper-1
                              rb-1-wb-1-same-start-address-different-op-sizes)
                             (unsigned-byte-p
                              signed-byte-p))))))

(defthm rb-wb-subset
  (implies
   (and (app-view x86)
        (< (+ addr-1 n-1) (+ addr-2 n-2))
        (<= addr-2 addr-1)
        (canonical-address-p addr-1)
        (canonical-address-p (+ -1 n-1 addr-1))
        (canonical-address-p addr-2)
        (canonical-address-p (+ -1 n-2 addr-2))
        (unsigned-byte-p (ash n-2 3) val)
        (posp n-1)
        (posp n-2)
        (x86p x86))
   (equal (mv-nth 1 (rb n-1 addr-1 r-x (mv-nth 1 (wb n-2 addr-2 w val x86))))
          (part-select val :low (ash (- addr-1 addr-2) 3) :width (ash n-1 3)))))

;; rb-rb-subset --- rb re-reads bytes previously read by rb:

(local
 (defthmd rb-1-rb-1-subset-helper-1
   (implies (and (posp j)
                 (x86p x86))
            (equal (loghead (ash j 3) (mv-nth 1 (rvm08 addr x86)))
                   (mv-nth 1 (rvm08 addr x86))))
   :hints (("Goal" :in-theory (e/d* () (n08p-mv-nth-1-rvm08 unsigned-byte-p))
            :use ((:instance n08p-mv-nth-1-rvm08))))))

(local
 (encapsulate
   ()
   (local (include-book "arithmetic-3/top" :dir :system))

   (defthmd rb-1-rb-1-subset-helper-2
     (implies (and (natp j)
                   (natp x))
              (equal (ash (loghead (ash j 3) x) 8)
                     (loghead (ash (1+ j) 3) (ash x 8))))
     :hints (("Goal" :in-theory (e/d* (loghead ash) ()))))))

(defthmd rb-1-rb-1-same-start-address-different-op-sizes
  (implies (and (equal (mv-nth 1 (rb i addr r-x-i x86)) val)
                (canonical-address-p (+ -1 i addr))
                (posp j)
                (<= j i)
                (app-view x86)
                (x86p x86))
           (equal (mv-nth 1 (rb j addr r-x-j x86))
                  (loghead (ash j 3) val)))
  :hints (("Goal"
           :in-theory (e/d* (rb-1-rb-1-subset-helper-1
                             rb-1-rb-1-subset-helper-2)
                            (unsigned-byte-p)))))

(defun-nx rb-1-rb-1-induction-scheme (n-1 a-1 n-2 a-2 val x86)
  ;; Similar to rb-1-wb-1-induction-scheme.
;                    a-2
;   ------------------------------------------------------------------------
; ...   |   |   |   | w | w | w | w |   |   |   |   |   |   |   |   |   |  ...
;   ------------------------------------------------------------------------
;   0                    a-1                                               max
  (cond ((or (zp n-1) (zp n-2) (< n-2 n-1) (< a-1 a-2))
         (mv n-1 a-1 n-2 a-2 val x86))
        ((equal a-1 a-2)
         ;; n-1 and n-2 are irrelevant here.  See
         ;; rb-1-rb-1-same-start-address-different-op-sizes.
         (mv n-1 a-1 n-2 a-2 val x86))
        ((< a-2 a-1)
         ;; Byte that won't be read by the most recent rb-1.
         (b* ((n-2 (1- n-2))
              (a-2 (1+ a-2))
              (val (logtail 8 val)))
           (rb-1-rb-1-induction-scheme n-1 a-1 n-2 a-2 val x86)))))

(defthmd rb-rb-subset
  ;; [Shilpi]: Expensive rule. Keep this disabled.
  (implies (and (equal (mv-nth 1 (rb i addr-i r-x-i x86)) val)
                ;; <j,addr-j> is a subset (not strict) of <i,addr-i>.
                ;; This non-strictness is nice because it lets me have
                ;; a better hyp in one-read-with-rb-from-program-at ---
                ;; (< addr (+ (len bytes) prog-addr))
                ;; instead of
                ;; (< (+ 1 addr) (+ (len bytes) prog-addr))
                (<= (+ j addr-j) (+ i addr-i))
                (<= addr-i addr-j)
                (canonical-address-p addr-i)
                (canonical-address-p (+ -1 i addr-i))
                (posp i) (posp j)
                (integerp addr-j)
                (app-view x86)
                (x86p x86))
           (equal (mv-nth 1 (rb j addr-j r-x-j x86))
                  (part-select val :low (ash (- addr-j addr-i) 3) :width (ash j 3))))
  :hints (("Goal"
           :induct (rb-1-rb-1-induction-scheme j addr-j i addr-i val x86)
           :in-theory (e/d* (ifix
                             nfix
                             rb-1-opener-theorem
                             rb-1-rb-1-same-start-address-different-op-sizes
                             rb-1-wb-1-subset-helper-1
                             rb-1-rb-1-subset-helper-1
                             rb-1-rb-1-subset-helper-2)
                            (unsigned-byte-p)))))

;; rb-rb-split-reads --- split an rb read into two constituent reads:

(defthmd rb-rb-split-reads
  (implies (and (canonical-address-p addr)
                (canonical-address-p (+ -1 k j addr))
                (xr :app-view nil x86)
                (natp j)
                (natp k))
           (equal (mv-nth 1 (rb (+ k j) addr r-x x86))
                  ;; What form of RHS do we really want?
                  (logior
                   (mv-nth 1 (rb j addr r-x x86))
                   (ash (mv-nth 1 (rb k (+ j addr) r-x x86)) (ash j 3))))
           ;; (equal (mv-nth 1 (rb (+ k j) addr r-x x86))
           ;;        ;; k is likely to be a constant, which is why we
           ;;        ;; want (ash k 3) below since it'll evaluate to a
           ;;        ;; concrete value.
           ;;        (logior
           ;;         (ash (mv-nth 1 (rb j (+ k addr) r-x x86)) (ash k 3))
           ;;         (mv-nth 1 (rb k addr r-x x86))))
           )
  :hints (("Goal"
           :in-theory (e/d* (push-ash-inside-logior)
                            (unsigned-byte-p                             
                             (:meta acl2::mv-nth-cons-meta))))))

;; ----------------------------------------------------------------------

;; Lemmas about program-at:

(defthm program-at-wb-disjoint
  (implies (and (separate :x (len bytes) prog-addr w n addr)
                (app-view x86))
           (equal (program-at prog-addr bytes (mv-nth 1 (wb n addr w val x86)))
                  (program-at prog-addr bytes x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (program-at) (rb wb)))))

(defthm program-at-write-x86-file-des
  (implies (app-view x86)
           (equal (program-at addr bytes (write-x86-file-des i v x86))
                  (program-at addr bytes x86)))
  :hints (("Goal" :in-theory (e/d (program-at
                                   write-x86-file-des
                                   write-x86-file-des-logic)
                                  (rb)))))

(defthm program-at-delete-x86-file-des
  (implies (app-view x86)
           (equal (program-at addr bytes (delete-x86-file-des i x86))
                  (program-at addr bytes x86)))
  :hints (("Goal" :in-theory (e/d (program-at
                                   delete-x86-file-des
                                   delete-x86-file-des-logic)
                                  (rb)))))

(defthm program-at-write-x86-file-contents
  (implies (app-view x86)
           (equal (program-at addr bytes (write-x86-file-contents i v x86))
                  (program-at addr bytes x86)))
  :hints (("Goal" :in-theory (e/d (program-at
                                   write-x86-file-contents
                                   write-x86-file-contents-logic)
                                  (rb)))))

(defthm program-at-delete-x86-file-contents
  (implies (app-view x86)
           (equal (program-at addr bytes (delete-x86-file-contents i x86))
                  (program-at addr bytes x86)))
  :hints (("Goal" :in-theory (e/d (program-at
                                   delete-x86-file-contents
                                   delete-x86-file-contents-logic)
                                  (rb)))))

(defthm program-at-pop-x86-oracle
  (implies (app-view x86)
           (equal (program-at addr bytes (mv-nth 1 (pop-x86-oracle x86)))
                  (program-at addr bytes x86)))
  :hints (("Goal" :in-theory (e/d (program-at pop-x86-oracle pop-x86-oracle-logic)
                                  (rb)))))

(defthm program-at-write-user-rflags
  (implies (app-view x86)
           (equal (program-at addr bytes (write-user-rflags flags mask x86))
                  (program-at addr bytes x86)))
  :hints (("Goal" :in-theory (e/d (write-user-rflags)
                                  (force (force))))))

;; ======================================================================

;; Lemmas about rb and program-at:

;; The following theorems help in relieving the hypotheses of
;; get-prefixes opener lemmas.

(defthmd rb-1-error-free-implies-canonical-addresses
  (implies (and (not (mv-nth 0 (rb-1 n addr r-x x86)))
                (not (zp n))
                (app-view x86))
           (and (canonical-address-p (+ -1 n addr))
                (canonical-address-p addr))))

(local
 (defthm non-zero-len-of-consp
   ;; Ugh.
   (implies (consp x)
            (equal (equal (len x) 0) nil))))

(defthmd program-at-implies-canonical-addresses-in-app-view
  (implies (and (program-at prog-addr bytes x86)
                (consp bytes)
                (app-view x86))
           (and (canonical-address-p (+ -1 (len bytes) prog-addr))
                (canonical-address-p prog-addr)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rb-1-error-free-implies-canonical-addresses
                            (n (len bytes))
                            (addr prog-addr)
                            (r-x :x)))
           :in-theory (e/d* (program-at) ()))))

(defun find-info-from-program-at-term-in-app-view (ctx mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable ctx state))
  (b* ((call (acl2::find-call-lst 'program-at (acl2::mfc-clause mfc)))
       ((when (not call))
        ;; (cw "~%~p0: program-at term not encountered.~%" ctx)
        nil)
       (prog-addr (cadr call))
       (bytes (caddr call)))
    `((prog-addr . ,prog-addr)
      (bytes . ,bytes))))

(defthm many-reads-with-rb-from-program-at
  (implies
   (and (bind-free (find-info-from-program-at-term-in-app-view
                    'many-reads-with-rb-from-program-at
                    mfc state)
                   (prog-addr bytes))
        (program-at prog-addr bytes x86)
        (<= prog-addr addr)
        (<= (+ n addr) (+ (len bytes) prog-addr))
        (canonical-address-p addr)
        (posp n)
        (byte-listp bytes)
        (app-view x86)
        (x86p x86))
   (equal (mv-nth 1 (rb n addr :x x86))
          ;; During symbolic simulation of a program, we'd know the
          ;; concrete value of "bytes".  Moreover, note that using
          ;; combine-bytes instead of combine-n-bytes would have been
          ;; expensive because the former would combine all program
          ;; bytes whereas the latter only combines n of them.
          (combine-n-bytes (- addr prog-addr) n bytes)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rb-rb-subset
                            (j n) (addr-j addr) (r-x-j :x) (x86 x86)
                            (i (len bytes)) (addr-i prog-addr) (r-x-i :x)
                            (val (combine-n-bytes 0 (len bytes) bytes)))
                 (:instance program-at-implies-canonical-addresses-in-app-view))
           :in-theory (e/d (relating-combine-bytes-and-part-select
                            program-at)
                           (acl2::commutativity-of-logior
                            take nthcdr ;; combine-n-bytes
                            rb rb-1 nth signed-byte-p)))))

(local
 (defthm relating-nth-and-combine-bytes
   (implies (and (byte-listp bytes)
                 (natp i)
                 (< i (len bytes)))
            (equal (nth i bytes)
                   (loghead 8 (logtail (ash i 3) (combine-bytes bytes)))))
   :hints (("Goal" :in-theory (e/d* (nth
                                     logtail-n>=8-of-byte
                                     loghead-n->=8-of-a-byte)
                                    (member-equal))))))

(defthm one-read-with-rb-from-program-at
  ;; Even though we have many-reads-with-rb-from-program-at, I like
  ;; having this lemma around because it has a weaker hyp of
  ;; (< addr (+ (len bytes) prog-addr))
  ;; instead of
  ;; (< (+ 1 addr) (+ (len bytes) prog-addr)).
  (implies (and
            (bind-free (find-info-from-program-at-term-in-app-view
                        'one-read-with-rb-from-program-at
                        mfc state)
                       (prog-addr bytes))
            (program-at prog-addr bytes x86)
            (<= prog-addr addr)
            (< addr (+ (len bytes) prog-addr))
            ;; (< (+ 1 addr) (+ (len bytes) prog-addr))
            (canonical-address-p addr)
            (byte-listp bytes)
            (app-view x86)
            (x86p x86))
           (equal (mv-nth 1 (rb 1 addr :x x86))
                  (nth (nfix (- addr prog-addr)) bytes)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rb-rb-subset
                            (j 1) (addr-j addr) (r-x-j :x) (x86 x86)
                            (i (len bytes)) (addr-i prog-addr) (r-x-i :x)
                            (val (combine-bytes bytes)))
                 (:instance program-at-implies-canonical-addresses-in-app-view))
           :in-theory (e/d (program-at)
                           (take rb rb-1 nth signed-byte-p)))))

;; ======================================================================

(globally-disable '(rb wb
                    canonical-address-p program-at
                    unsigned-byte-p signed-byte-p))

(in-theory (e/d*
            ;; We enable all these functions so that reasoning about
            ;; memory can be done in terms of rb and wb.
            (riml-size
             rml-size
             wiml-size
             wml-size
             rml08 riml08 wml08 wiml08
             rml16 riml16 wml16 wiml16
             rml32 riml32 wml32 wiml32
             rml64 riml64 wml64 wiml64
             ea-to-la
             rme08 rime08 wme08 wime08)
            ;; We disable some expensive and irrelevant lemmas in
            ;; the application-level view.
            (las-to-pas
             xr-fault-wb-in-system-level-marking-view
             xr-fault-wb-in-sys-view)))

;; ======================================================================
