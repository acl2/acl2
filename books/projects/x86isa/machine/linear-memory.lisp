; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; Copyright (C) 2024, Kestrel Technology, LLC

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
; Robert Krug         <rkrug@cs.utexas.edu>
; Contributing Author(s):
; Alessandro Coglio (www.alessandrocoglio.info)

(in-package "X86ISA")
(include-book "paging" :ttags (:undef-flg))
(include-book "centaur/bitops/merge" :dir :system)

;; ======================================================================

(local (include-book "guard-helpers"))
; (local (include-book "centaur/bitops/ihs-extensions" :dir :system)) ;; Redundant
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))

;; ======================================================================

(defsection linear-memory
  :parents (machine)
  :short "Linear Memory Accessor and Updater Functions"
  :long "<p>First, a quick note about virtual, linear, and physical
  addresses:</p>

 <ul>
 <li><i>Linear (or Virtual) Address:</i> In the flat memory model (see
 Intel Vol. 1, Section 3.3.1), memory appears to a program as a single,
 continuous address space, called a linear (or virtual) address
 space. An address for any byte in linear address space is called a
 linear address.  When paging is disabled, then a linear address is the
 same as a physical address.</li>

 <li><i>Physical Address:</i> The memory that the processor addresses
 on its bus is called physical memory. Physical memory is organized as
 a sequence of 8-bit bytes. Each byte is assigned a unique address,
 called a physical address. When employing the processor's memory
 management facilities, programs do not directly address physical
 memory.</li>

</ul>" )

(local (xdoc::set-default-parents linear-memory))

;; ======================================================================

;; Some utilities to generate numerous (but efficient) RoW and WoW
;; kinda theorems:

(defun remove-elements-from-list (elems lst)
  (if (or (endp lst) (endp elems))
      lst
    (if (member (car lst) elems)
        (remove-elements-from-list (remove (car lst) elems) (cdr lst))
      (cons (car lst) (remove-elements-from-list elems (cdr lst))))))

(defun search-and-replace-once (search-term replace-term lst)
  (if (endp lst)
      nil
    (if (equal search-term (car lst))
        (cons replace-term (cdr lst))
      (cons (car lst) (search-and-replace-once search-term replace-term (cdr lst))))))

(defun generate-read-fn-over-xw-thms-1
    (xw-fld read-fn read-fn-formals output-index hyps-term double-rewrite-in-concl?)
  ;; (generate-read-fn-over-xw-thms-1 :RGF 'gather-all-paging-structure-qword-addresses '(x86) -1 t t)
  (b* ((body
        (if (equal output-index -1)
            `(equal
              (,read-fn
               ,@(search-and-replace-once 'x86 `(XW ,xw-fld index val x86) read-fn-formals))
              (,read-fn
               ,@(if double-rewrite-in-concl?
                     (search-and-replace-once 'x86 '(double-rewrite x86) read-fn-formals)
                   read-fn-formals)))
          `(equal
            (mv-nth ,output-index
                    (,read-fn
                     ,@(search-and-replace-once
                        'x86 `(XW ,xw-fld index val x86) read-fn-formals)))
            (mv-nth ,output-index
                    (,read-fn ,@(if double-rewrite-in-concl?
                                    (search-and-replace-once
                                     'x86 '(double-rewrite x86) read-fn-formals)
                                  read-fn-formals)))))))
    `(defthm ,(mk-name (if (equal output-index -1)
                           read-fn
                         (mk-name "MV-NTH-" output-index "-" read-fn))
                       "-XW-" xw-fld)
       ,(if (atom hyps-term)
            body
          `(implies ,hyps-term ,body)))))

(defun generate-read-fn-over-xw-thms-aux
    (xw-flds read-fn read-fn-formals output-index hyps-term double-rewrite-in-concl?)
  (if (endp xw-flds)
      nil
    (cons
     (generate-read-fn-over-xw-thms-1
      (car xw-flds) read-fn read-fn-formals output-index hyps-term double-rewrite-in-concl?)
     (generate-read-fn-over-xw-thms-aux
      (cdr xw-flds) read-fn read-fn-formals output-index hyps-term double-rewrite-in-concl?))))

(define generate-read-fn-over-xw-thms
  (xw-flds read-fn read-fn-formals
           &key
           (output-index '-1)
           (hyps 't)
           (double-rewrite? 'nil)
           (prepwork 'nil))
  :verify-guards nil
  ;; (generate-read-fn-over-xw-thms
  ;;  *x86-field-names-as-keywords*
  ;;  'rvm08
  ;;  (acl2::formals 'rvm08$inline (w state))
  ;;  :prepwork '((local (in-theory (e/d* () (xw))))))
  `(encapsulate ()
     ,@(or prepwork nil)
     ,@(generate-read-fn-over-xw-thms-aux
        xw-flds read-fn read-fn-formals output-index hyps double-rewrite?)))

(defun generate-write-fn-over-xw-thms-1
    (xw-fld write-fn write-fn-formals output-index hyps-term)
  ;; (generate-write-fn-over-xw-thms-1 :RGF 'rvm08 '(addr x86) 2 t)
  (b* ((body
        (if (equal output-index -1)
            `(equal
              (,write-fn
               ,@(search-and-replace-once 'x86 `(XW ,xw-fld index val x86) write-fn-formals))
              (XW ,xw-fld index val ,(cons write-fn write-fn-formals)))
          `(equal
            (mv-nth
             ,output-index
             (,write-fn
              ,@(search-and-replace-once 'x86 `(XW ,xw-fld index val x86) write-fn-formals)))
            (XW ,xw-fld index val (mv-nth ,output-index ,(cons write-fn write-fn-formals)))))))
    `(defthm ,(mk-name (if (equal output-index -1)
                           write-fn
                         (mk-name "MV-NTH-" output-index "-" write-fn))
                       "-XW-" xw-fld)
       ,(if (atom hyps-term)
            body
          `(implies ,hyps-term ,body)))))

(defun generate-write-fn-over-xw-thms-aux
    (xw-flds write-fn write-fn-formals output-index hyps-term)
  (if (endp xw-flds)
      nil
    (cons (generate-write-fn-over-xw-thms-1
           (car xw-flds) write-fn write-fn-formals output-index hyps-term)
          (generate-write-fn-over-xw-thms-aux
           (cdr xw-flds) write-fn write-fn-formals output-index hyps-term))))

(define generate-write-fn-over-xw-thms
  (xw-flds write-fn write-fn-formals
           &key
           (output-index '-1)
           (hyps 't)
           (prepwork 'nil))
  :verify-guards nil
  ;; (generate-write-fn-over-xw-thms
  ;;  *x86-field-names-as-keywords*
  ;;  'wvm08
  ;;  (acl2::formals 'wvm08$inline (w state))
  ;;  :prepwork '((local (in-theory (e/d* () (xw))))))
  `(encapsulate ()
     ,@(or prepwork nil)
     ,@(generate-write-fn-over-xw-thms-aux xw-flds write-fn write-fn-formals output-index hyps)))

(defun generate-xr-over-write-thms-1
    (xr-fld write-fn write-fn-formals output-index hyps-term double-rewrite-in-concl?)
  ;; (generate-xr-over-write-thms-1 :RGF 'rb '(addr r-x x86) 2 t nil)
  (b* ((body
        (if (equal output-index -1)
            `(equal (XR ,xr-fld index ,(cons write-fn write-fn-formals))
                    (XR ,xr-fld index ,(if double-rewrite-in-concl?
                                           `(double-rewrite x86)
                                         `x86)))
          `(equal (XR ,xr-fld index (mv-nth ,output-index ,(cons write-fn write-fn-formals)))
                  (XR ,xr-fld index ,(if double-rewrite-in-concl?
                                         `(double-rewrite x86)
                                       `x86))))))
    `(defthm ,(mk-name "XR-" xr-fld "-"
                       (if (equal output-index -1)
                           write-fn (mk-name "MV-NTH-" output-index "-" write-fn)))
       ,(if (atom hyps-term)
            body
          `(implies ,hyps-term ,body)))))

(defun generate-xr-over-write-thms-aux
    (xr-flds write-fn write-fn-formals output-index hyps-term double-rewrite?)
  (if (endp xr-flds)
      nil
    (cons
     (generate-xr-over-write-thms-1
      (car xr-flds) write-fn write-fn-formals output-index hyps-term double-rewrite?)
     (generate-xr-over-write-thms-aux
      (cdr xr-flds) write-fn write-fn-formals output-index hyps-term double-rewrite?))))

(define generate-xr-over-write-thms
  (xr-flds write-fn write-fn-formals
           &key
           (output-index '-1)
           (hyps 't)
           (double-rewrite? 'nil)
           (prepwork 'nil))
  :verify-guards nil
  ;; (generate-xr-over-write-thms
  ;;  *x86-field-names-as-keywords*
  ;;  'wvm08
  ;;  (acl2::formals 'wvm08$inline (w state))
  ;;  :prepwork '((local (in-theory (e/d* () (xw))))))
  `(encapsulate ()
     ,@(or prepwork nil)
     ,@(generate-xr-over-write-thms-aux
        xr-flds write-fn write-fn-formals output-index hyps double-rewrite?)))

;; ======================================================================

;; Some misc. arithmetic lemmas and macros:

(defthm signed-byte-p-limits-thm
  ;; i is positive, k is positive, k < i
  (implies (and (signed-byte-p n (+ i addr))
                (signed-byte-p n addr)
                (integerp k)
                (<= 0 k)
                (< k i))
           (signed-byte-p n (+ k addr))))

(defthmd push-ash-inside-logior
  (equal (ash (logior x y) n)
         (logior (ash x n) (ash y n)))
  :hints (("Goal" :in-theory (e/d* (ihsext-recursive-redefs
                                    ihsext-inductions)
                                   ()))))

(local (in-theory (e/d () (unsigned-byte-p))))

;; ======================================================================

;; Events related to RB and WB:

(defsection reasoning-about-memory-reads-and-writes
  :parents (linear-memory)
  :short "Definitions of @(see rb) and @(see wb)"

  :long "<p>The functions @('rb') (read bytes) and @('wb') (write
 bytes) are used in reasoning about memory reads and writes. Functions
 like @('rml08'), @('rml16'), @('rml32'), and @('rml64') are reduced to
 @('rb'), and @('wml08'), @('wml16'), @('wml32'), and @('wml64') to
 @('wb') during reasoning.</p>"

  (local (xdoc::set-default-parents reasoning-about-memory-reads-and-writes))

  (define canonical-address-listp (lst)
    :short "Recognizer of a list of canonical addresses"
    :enabled t
    (if (equal lst nil)
        t
      (and (consp lst)
           (canonical-address-p (car lst))
           (canonical-address-listp (cdr lst))))
    ///
    (defthm cdr-canonical-address-listp
      (implies (canonical-address-listp x)
               (canonical-address-listp (cdr x)))))

  (define create-canonical-address-list (count addr)
    :guard (natp count)

    :long "<p>Given a canonical address @('addr'),
  @('create-canonical-address-list') creates a list of canonical
  addresses where the first address is @('addr') and the last address
  is the last canonical address in the range @('addr') to @('addr +
  count').</p>"
    :enabled t

    (if (or (zp count)
            (not (canonical-address-p addr)))
        nil
      (cons addr (create-canonical-address-list (1- count)
                                                (1+ addr))))
    ///

    (defthm true-listp-create-canonical-address-list
      (true-listp (create-canonical-address-list cnt lin-addr))
      :rule-classes (:rewrite :type-prescription))

    (defthm canonical-address-listp-create-canonical-address-list
      (canonical-address-listp
       (create-canonical-address-list count addr))
      :rule-classes (:rewrite :type-prescription))

    (defthm create-canonical-address-list-1
      (implies (canonical-address-p x)
               (equal (create-canonical-address-list 1 x)
                      (list x)))
      :hints (("Goal" :expand (create-canonical-address-list 1 x))))

    (defthm len-of-create-canonical-address-list
      (implies (and (canonical-address-p (+ -1 addr count))
                    (canonical-address-p addr)
                    (natp count))
               (equal (len (create-canonical-address-list count addr))
                      count)))

    (defthm car-create-canonical-address-list
      (implies (and (canonical-address-p addr)
                    (posp count))
               (equal (car (create-canonical-address-list count addr))
                      addr)))

    (defthm cdr-create-canonical-address-list
      (implies (and (canonical-address-p addr)
                    (posp count))
               (equal (cdr (create-canonical-address-list count addr))
                      (create-canonical-address-list (1- count) (1+ addr)))))

    (defthm consp-of-create-canonical-address-list
      (implies (and (canonical-address-p addr)
                    (natp count)
                    (< 0 count))
               (consp (create-canonical-address-list count addr)))
      :hints (("Goal" :in-theory (e/d (canonical-address-p
                                       signed-byte-p)
                                      ()))))

    (defthmd create-canonical-address-list-split
      (implies (and (canonical-address-p addr)
                    (canonical-address-p (+ k addr))
                    (natp j)
                    (natp k))
               (equal (create-canonical-address-list (+ k j) addr)
                      (append (create-canonical-address-list k addr)
                              (create-canonical-address-list j (+ k addr)))))
      :hints (("Goal" :in-theory (e/d* (canonical-address-p signed-byte-p)
                                       ())))))

    (local
     (defthm ash-n-3-minus-8-lemma
       (implies (posp n)
                (equal (+ -8 (ash n 3))
                       (ash (+ -1 n) 3)))
       :hints (("goal" :in-theory (e/d* (bitops::ihsext-inductions
                                         bitops::ihsext-recursive-redefs
                                         ash floor)
                                        ())))))

    (local
     (defthm unsigned-byte-p-of-ash-x-8-lemma
       (implies
        (and (unsigned-byte-p (ash (+ -1 n) 3) x)
             (< 0 n)
             (integerp n))
        (unsigned-byte-p (ash n 3) (ash x 8)))
       :hints (("goal" :in-theory (e/d () (unsigned-byte-p-of-ash))
                :use ((:instance unsigned-byte-p-of-ash
                                 (n (ash n 3))
                                 (x x)
                                 (m 8)))))))

    (local
     (defthm byte-width-unsigned-byte-p-ash-incr
       (implies (and (unsigned-byte-p 8 b)
                     (posp n))
                (unsigned-byte-p (ash n 3) b))
       :hints (("Goal"
                :use ((:instance bitops::unsigned-byte-p-incr
                                 (a 8) (x b) (b (ash n 3))))
                :in-theory (e/d (ash floor)
                                (bitops::unsigned-byte-p-incr))))))

    (local
     (defthm unsigned-byte-p-of-logior-ash-x-8-lemma
       (implies
        (and (unsigned-byte-p (ash (+ -1 n) 3) x)
             (unsigned-byte-p 8 b)
             (< 0 n)
             (integerp n))
        (unsigned-byte-p (ash n 3) (logior b (ash x 8))))
       :hints (("goal" :in-theory (e/d ()
                                       (unsigned-byte-p-of-logior
                                        ash-n-3-minus-8-lemma
                                        byte-width-unsigned-byte-p-ash-incr))
                :use ((:instance byte-width-unsigned-byte-p-ash-incr)
                      (:instance unsigned-byte-p-of-logior
                                 (n (ash n 3))
                                 (i b)
                                 (j (ash x 8))))))))

  (define rb-1 ((n     natp "Number of bytes to be read")
                (addr  integerp "First linear address")
                (r-x  :type (member :r :x) "Type of memory access")
                (x86))
    :verify-guards :after-returns
    :returns
    (mv flg
        (val natp :rule-classes :type-prescription)
        (new-x86 x86p :hyp (x86p x86)))

    :guard (canonical-address-p (+ -1 n addr))
    :enabled t

    (if (zp n)
        (mv nil 0 x86)
      ;; rb-1 is used only in the app-level view so it makes sense to
      ;; use rvm08 here.
      (b* (((unless (canonical-address-p addr))
            (mv 'rb-1 0 x86))
           ((mv flg0 byte0 x86)
            (rvm08 addr x86))
           ((when flg0)
            (mv flg0 0 x86))
           ((mv rest-flg rest-bytes x86)
            (rb-1 (1- n) (1+ addr) r-x x86)))
        (mv rest-flg (logior byte0 (ash rest-bytes 8)) x86)))

    ///

    (defret integerp-of-mv-nth-1-rb-1
      (integerp val)
      :rule-classes :type-prescription)

    (defret rb-1-returns-x86-app-view
      (implies (app-view x86)
               (equal new-x86 x86)))

    (local
     (defthm rb-1-returns-no-error-app-view-helper
       (implies (xr :app-view nil x86)
                (not (mv-nth 0 (rb-1 1 #.*2^47-1* r-x x86))))
       :hints (("Goal" :expand (rb-1 1 #.*2^47-1* r-x x86)))))

    (defthm rb-1-returns-no-error-app-view
      (implies (and (canonical-address-p addr)
                    (canonical-address-p (+ -1 n addr))
                    (app-view x86))
               (equal (mv-nth 0 (rb-1 n addr r-x x86)) nil))
      :hints (("Goal" :in-theory (e/d (rvm08) ()))))

    (defthm-unsigned-byte-p size-of-rb-1
      :hyp (and (equal m (ash n 3)) (natp n))
      :bound m
      :concl (mv-nth 1 (rb-1 n addr r-x x86))
      :hints (("Goal" :in-theory (e/d* (rvm08) (unsigned-byte-p signed-byte-p))))
      :gen-linear t
      :hints-l (("Goal" :in-theory (e/d* () (rb-1))))))

  (define las-to-pas
    ((n         natp "Number of bytes to be read")
     (lin-addr  integerp "First linear address")
     (r-w-x    :type (member :r :w :x) "Type of memory access: read, write, or execute")
     x86)
    :enabled t
    :guard  (not (app-view x86)) ;; Not x86 "flat" mode or ``app(lication) mode''
    :verify-guards nil
    ;; It'd be sweet if las-to-pas returned the following instead of a
    ;; list of physical addresses: <n, phy-addr>, where this region of
    ;; physical memory corresponds to the linear memory region under
    ;; consideration <n, lin-addr>.  However, it's not quite so simple
    ;; because a contiguous linear memory region, like the one denoted
    ;; by <n, lin-addr>, can map to multiple non-contiguous physical
    ;; memory regions.
    :returns (mv flg
                 (p-addrs  true-listp :rule-classes (:rewrite :type-prescription))
                 (x86      x86p :hyp (x86p x86) :hints (("Goal" :in-theory (e/d () (x86p))))))

    (if (zp n)
        (mv nil nil x86)
      (b* (((unless (canonical-address-p lin-addr))
            (mv t nil x86))
           ((mv flg p-addr x86)
            (ia32e-la-to-pa lin-addr r-w-x x86))
           ((when flg) (mv flg nil x86))
           ((mv flgs p-addrs x86)
            (las-to-pas (1- n) (1+ lin-addr) r-w-x x86)))
        (mv flgs (if flgs nil (cons p-addr p-addrs)) x86)))

    ///

    (defthm consp-mv-nth-1-las-to-pas
            (implies (and (not (mv-nth 0 (las-to-pas n lin-addr r-w-x x86)))
                          (not (zp n)))
                     (consp (mv-nth 1 (las-to-pas n lin-addr r-w-x x86))))
            :rule-classes (:rewrite :type-prescription))

    (defthm car-mv-nth-1-las-to-pas
            (implies (and (not (mv-nth 0 (las-to-pas n lin-addr r-w-x x86)))
                          (not (zp n)))
                     (equal (car (mv-nth 1 (las-to-pas n lin-addr r-w-x x86)))
                            (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))))
            :hints (("Goal" :in-theory (e/d* (las-to-pas) ()))))

    (defthm physical-address-listp-mv-nth-1-las-to-pas
            (physical-address-listp (mv-nth 1 (las-to-pas n lin-addr r-w-x x86))))

    (defthm las-to-pas-n=0
            (and (equal (mv-nth 0 (las-to-pas 0 lin-addr r-w-x x86)) nil)
                 (equal (mv-nth 1 (las-to-pas 0 lin-addr r-w-x x86)) nil)
                 (equal (mv-nth 2 (las-to-pas 0 lin-addr r-w-x x86)) x86)))

    (local
      (defthm xr-las-to-pas
              (implies
                (and (not (equal fld :tlb))
                     (not (equal fld :mem))
                     (not (equal fld :fault)))
                (equal (xr fld index (mv-nth 2 (las-to-pas n lin-addr r-w-x x86)))
                       (xr fld index x86)))
              :hints (("Goal" :in-theory (e/d* () (force (force)))))))

    (make-event
      (generate-xr-over-write-thms
        (remove-elements-from-list
          '(:mem :fault :tlb)
          *x86-field-names-as-keywords*)
        'las-to-pas
        (acl2::formals 'las-to-pas (w state))
        :output-index 2))

    ;; The double-rewrites below are crucial to the applicability of the rules
    ;; below (in sys-view mode).
    (defthm xr-rflags-las-to-pas
            (implies (not (mv-nth 0 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
                     (equal (xr :rflags nil (mv-nth 2 (las-to-pas n lin-addr r-w-x x86)))
                            (xr :rflags nil (double-rewrite x86))))
            :hints (("Goal" :in-theory (e/d* () (force (force))))))

    (defthm xr-fault-las-to-pas
            (implies (not (mv-nth 0 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
                     (equal (xr :fault nil (mv-nth 2 (las-to-pas n lin-addr r-w-x x86)))
                            (xr :fault nil (double-rewrite x86))))
            :hints (("Goal" :in-theory (e/d* () (force (force))))))

    (local (in-theory (e/d () (xr-las-to-pas))))

    ;; The following two make-events generate a bunch of rules that
    ;; together say the same thing as las-to-pas-xw-values, but these
    ;; rules are more efficient than las-to-pas-xw-values as they
    ;; match less frequently.
    (make-event
      (generate-read-fn-over-xw-thms
        (remove-elements-from-list
          '(:mem :rflags :fault :ctr :msr :app-view :marking-view :seg-visible :tlb :implicit-supervisor-access)
          *x86-field-names-as-keywords*)
        'las-to-pas
        (acl2::formals 'las-to-pas (w state))
        :output-index 0))

    (make-event
      (generate-read-fn-over-xw-thms
        (remove-elements-from-list
          '(:mem :rflags :fault :ctr :msr :app-view :marking-view :seg-visible :tlb :implicit-supervisor-access)
          *x86-field-names-as-keywords*)
        'las-to-pas
        (acl2::formals 'las-to-pas (w state))
        :output-index 1))

    (defrule 64-bit-modep-of-las-to-pas
             (equal (64-bit-modep (mv-nth 2 (las-to-pas n lin-addr r-w-x x86)))
                    (64-bit-modep x86))
             :hints (("Goal" :in-theory (e/d* (64-bit-modep) (force (force))))))

    (defrule x86-operation-mode-of-las-to-pas
             (equal (x86-operation-mode (mv-nth 2 (las-to-pas n lin-addr r-w-x x86)))
                    (x86-operation-mode x86))
             :hints (("Goal" :in-theory (e/d* (x86-operation-mode)
                                              (las-to-pas)))))

    ;; The following make-event generate a bunch of rules that
    ;; together say the same thing as las-to-pas-xw-state, but these
    ;; rules are more efficient than las-to-pas-xw-state as they match
    ;; less frequently.
    (make-event
      (generate-write-fn-over-xw-thms
        (remove-elements-from-list
          '(:mem :rflags :fault :ctr :msr :app-view :marking-view :seg-visible :tlb :implicit-supervisor-access)
          *x86-field-names-as-keywords*)
        'las-to-pas
        (acl2::formals 'las-to-pas (w state))
        :output-index 2))

    (local
      (defun-nx las-to-pas-xw-rflags-not-ac-hint (lin-addr n r-w-x value x86)
                (declare (xargs :measure (nfix n)))
                (if (zp n)
                  x86
                  (if (not (canonical-address-p lin-addr))
                    x86
                    (if (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86))
                      x86
                      (las-to-pas-xw-rflags-not-ac-hint
                        (+ 1 lin-addr) (+ -1 n) r-w-x value
                        (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86))))))))

    (defthm las-to-pas-xw-rflags-not-ac
            (implies (equal (rflagsBits->ac value)
                            (rflagsBits->ac (rflags (double-rewrite x86))))
                     (and
                       (equal (mv-nth 0 (las-to-pas n lin-addr r-w-x (xw :rflags nil value x86)))
                              (mv-nth 0 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
                       (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x (xw :rflags nil value x86)))
                              (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))))
            :hints (("Goal"
                     :induct (las-to-pas-xw-rflags-not-ac-hint lin-addr n r-w-x value x86)
                     :in-theory (e/d () (force (force))))))

    (defthm las-to-pas-xw-rflags-state-not-ac
            (implies (equal (rflagsBits->ac value)
                            (rflagsBits->ac (rflags x86)))
                     (equal (mv-nth 2 (las-to-pas n lin-addr r-w-x (xw :rflags nil value x86)))
                            (xw :rflags nil value (mv-nth 2 (las-to-pas n lin-addr r-w-x x86)))))
            :hints (("Goal" :in-theory (e/d* () (force (force))))))

    (defthm len-of-mv-nth-1-las-to-pas
            (implies (not (mv-nth 0 (las-to-pas n lin-addr r-w-x x86)))
                     (equal (len (mv-nth 1 (las-to-pas n lin-addr r-w-x x86)))
                            (nfix n))))
    (verify-guards las-to-pas :guard-debug t))

  (define read-from-physical-memory ((p-addrs physical-address-listp)
                                     x86)
    :parents (reasoning-about-memory-reads-and-writes physical-memory)
    :enabled t
    :verify-guards :after-returns
    :returns (value integerp :rule-classes :type-prescription)
    :guard (not (app-view x86))
    (if (endp p-addrs)
      0
      (b* ((addr0 (car p-addrs))
           (byte0 (memi addr0 x86))
           (rest-bytes (read-from-physical-memory (cdr p-addrs) x86)))
          (logior byte0 (ash rest-bytes 8))))

    ///

    (defthm-unsigned-byte-p size-of-read-from-physical-memory
                            :hyp (equal n (ash (len p-addrs) 3))
                            :bound n
                            :concl (read-from-physical-memory p-addrs x86)
                            :hints (("Goal" :in-theory (e/d* () (signed-byte-p))))
                            :gen-type t
                            :gen-linear t)

    (defthm read-from-physical-memory-xw-rflags
            (equal (read-from-physical-memory p-addrs (xw :rflags nil val x86))
                   (read-from-physical-memory p-addrs x86)))

    (defthm read-from-physical-memory-xw-not-mem
            (implies (not (equal fld :mem))
                     (equal (read-from-physical-memory p-addrs (xw fld index val x86))
                            (read-from-physical-memory p-addrs x86)))))

  (define rb ((n natp "Number of bytes to be read")
              (addr integerp "First linear address")
              (r-x :type (member :r :x) "Type of memory access")
              (x86))
    :enabled t
    :verify-guards :after-returns
    :returns (mv flg
                 (val integerp :rule-classes :type-prescription)
                 (new-x86 x86p :hyp (x86p x86) :hints (("Goal" :in-theory (e/d () (x86p))))))

    :guard (canonical-address-p (+ -1 n addr))

    (if (app-view x86)
      (rb-1 n addr r-x x86)
      (b* (((mv flgs p-addrs x86)
            (las-to-pas n addr r-x x86))
           ((when flgs) (mv flgs 0 x86))
           (val (read-from-physical-memory p-addrs x86)))
          (mv nil val x86)))

    ///

    (defret natp-of-mv-nth-1-rb
            (natp val)
            :hints (("Goal" :in-theory (e/d* () (force (force)))))
            :rule-classes :type-prescription)

    (defret rb-no-reads-when-zp-n
            (implies (zp n)
                     (equal val 0))
            :hints (("Goal" :in-theory (e/d* () (force (force))))))

    (defthmd rb-is-rb-1-for-app-view
             (implies (app-view x86)
                      (equal (rb n addr r-x x86)
                             (rb-1 n addr r-x x86))))

    (defthm rb-returns-no-error-app-view
            (implies (and (app-view x86)
                          (canonical-address-p addr)
                          (canonical-address-p (+ -1 n addr)))
                     (equal (mv-nth 0 (rb n addr r-x x86)) nil)))

    (defthm rb-returns-x86-app-view
            (implies (app-view x86)
                     (equal (mv-nth 2 (rb n addr r-x x86)) x86)))

    (defthm-unsigned-byte-p size-of-rb
                            :hyp (and (equal m (ash n 3))
                                      (natp n))
                            :bound m
                            :concl (mv-nth 1 (rb n addr r-x x86))
                            :hints (("Goal"
                                     :do-not-induct t
                                     :in-theory (e/d* () (unsigned-byte-p))))
                            :gen-linear t
                            :hints-l (("Goal" :in-theory (e/d* () (rb)))))

    (defthm-unsigned-byte-p size-of-rb-in-app-view
                            ;; No need to know whether the addresses are canonical or not...
                            :hyp (and (app-view x86) (natp n))
                            :bound (ash n 3)
                            :concl (mv-nth 1 (rb n addr r-x x86))
                            :gen-linear t
                            :hints-l (("Goal" :in-theory (e/d* () (rb)))))

    (defthm rb-values-and-xw-rflags-in-sys-view
            (implies (and (equal (rflagsBits->ac (double-rewrite value))
                                 (rflagsBits->ac (rflags x86)))
                          (not (app-view x86))
                          (x86p x86))
                     (and (equal (mv-nth 0 (rb n addr r-x (xw :rflags nil value x86)))
                                 (mv-nth 0 (rb n addr r-x (double-rewrite x86))))
                          (equal (mv-nth 1 (rb n addr r-x (xw :rflags nil value x86)))
                                 (mv-nth 1 (rb n addr r-x (double-rewrite x86))))))
            :hints (("Goal"
                     :do-not-induct t
                     :in-theory (e/d* (rb) ()))))

    (defrule 64-bit-modep-of-rb
             (equal (64-bit-modep (mv-nth 2 (rb n addr r-x x86)))
                    (64-bit-modep x86))
             :enable 64-bit-modep
             :disable (force (force)))

    (defrule x86-operation-mode-of-rb
             (equal (x86-operation-mode (mv-nth 2 (rb n addr r-x x86)))
                    (x86-operation-mode x86))
             :enable x86-operation-mode
             :disable rb))

  ;; Definition of WB and other related events:

  (define wb-1 ((n natp "Number of bytes to be written")
                (addr  integerp "First linear address")
                ;; I could do away with the following argument (w),
                ;; but I choose to keep it around because the current
                ;; version of Codewalker expects reader and writer
                ;; functions to have similar signatures.
                (w     :type (member :w) "Type of memory access: write")
                (value natp)
                (x86))
    :guard (canonical-address-p (+ -1 n addr))
    :enabled t
    :ignore-ok t

    (if (zp n)
        (mv nil x86)
      ;; wb-1 is used only in the app-view, so it makes sense to
      ;; use wvm08 here.
      (b* (((unless (canonical-address-p addr))
            (mv t x86))
           ((mv flg0 x86)
            (wvm08 addr (loghead 8 value) x86))
           ((when flg0)
            (mv flg0 x86))
           ((mv rest-flg x86)
            (wb-1 (1- n) (1+ addr) w (logtail 8 value) x86)))
        (mv rest-flg x86)))

    ///

    (defthm wb-1-returns-x86p
      (implies (x86p x86)
               (x86p (mv-nth 1 (wb-1 n addr w value x86))))
      :hints (("Goal" :in-theory (e/d () (x86p)))))

    (local
     (defthm wb-1-returns-no-error-app-view-helper
       (implies (xr :app-view nil x86)
                (not (mv-nth 0 (wb-1 1 #.*2^47-1* w value x86))))
       :hints (("Goal" :expand (wb-1 1 #.*2^47-1* w value x86)))))

    (defthm wb-1-returns-no-error-app-view
      (implies (and (canonical-address-p addr)
                    (canonical-address-p (+ -1 n addr))
                    (app-view x86))
               (equal (mv-nth 0 (wb-1 n addr w value x86))
                      nil))
      :hints (("Goal" :in-theory (e/d (wvm08) ())))))

  (define write-to-physical-memory ((p-addrs physical-address-listp)
                                    (value natp)
                                    x86)
    :parents (reasoning-about-memory-reads-and-writes physical-memory)
    :enabled t
    :guard (not (app-view x86))
    (if (endp p-addrs)
      x86
      (b* ((addr0 (car p-addrs))
           (byte0 (loghead 8 value))
           (x86 (!memi addr0 byte0 x86)))
          (write-to-physical-memory (cdr p-addrs) (logtail 8 value) x86)))

    ///

    (defthm x86p-write-to-physical-memory
            (implies (and (x86p x86)
                          ;; The following hypothesis can be weakened to
                          ;; integer-listp.
                          (physical-address-listp p-addrs))
                     (x86p (write-to-physical-memory p-addrs value x86)))
            :hints (("Goal" :in-theory (e/d* () (force (force))))))

    (defthm xr-not-mem-write-to-physical-memory
            (implies (not (equal fld :mem))
                     (equal (xr fld index (write-to-physical-memory p-addrs bytes x86))
                            (xr fld index x86)))
            :hints (("Goal" :in-theory (e/d* () (force (force))))))

    (defthm write-to-physical-memory-xw-in-sys-view
            ;; Keep the state updated by write-to-physical-memory inside all other nests of writes.
            (implies (not (equal fld :mem))
                     (equal (write-to-physical-memory p-addrs bytes (xw fld index value x86))
                            (xw fld index value (write-to-physical-memory p-addrs bytes x86))))
            :hints (("Goal" :in-theory (e/d* (write-to-physical-memory) ()))))

    (defrule 64-bit-modep-of-write-to-physical-memory
             (equal (64-bit-modep (write-to-physical-memory p-addrs value x86))
                    (64-bit-modep x86))
             :enable 64-bit-modep
             :disable (force (force)))

    (defrule x86-operation-mode-of-write-to-physical-memory
             (equal (x86-operation-mode (write-to-physical-memory p-addrs value x86))
                    (x86-operation-mode x86))
             :enable x86-operation-mode
             :disable write-to-physical-memory))

  (define wb ((n natp "Number of bytes to be written")
              (addr integerp "First linear address")
              ;; I could do away with the following argument (w),
              ;; but I choose to keep it around because the current
              ;; version of Codewalker expects reader and writer
              ;; functions to have similar signatures.
              (w :type (member :w) "Type of memory access")
              (value natp)
              (x86))

    :ignore-ok t
    :guard (canonical-address-p (+ -1 n addr))
    :enabled t

    (if (app-view x86)
      (wb-1 n addr w value x86)
      (b* (((mv flgs p-addrs x86)
            (las-to-pas n addr :w x86))
           ((when flgs) (mv flgs x86))
           (x86 (write-to-physical-memory p-addrs value x86)))
          (mv nil x86)))

    ///

    (defthm wb-no-writes-when-zp-n
            (equal (mv-nth 1 (wb 0 addr val w x86)) x86)
            :hints (("Goal" :in-theory (e/d* () (force (force))))))

    (defthmd wb-is-wb-1-for-app-view
             (implies (app-view x86)
                      (equal (wb n addr w value x86)
                             (wb-1 n addr w value x86))))

    (defthm x86p-of-wb
            (implies (x86p x86)
                     (x86p (mv-nth 1 (wb n addr w value x86))))
            :hints (("Goal" :in-theory (e/d () (x86p)))))

    (defthm wb-returns-no-error-app-view
            (implies (and (canonical-address-p addr)
                          (canonical-address-p (+ -1 n addr))
                          (app-view x86))
                     (equal (mv-nth 0 (wb n addr w value x86)) nil))))

  (defthm wb-by-wb-1-for-app-view-induction-rule
    t
    :rule-classes ((:induction :pattern (wb n addr w value x86)
                               :condition (app-view x86)
                               :scheme (wb-1 n addr w value x86))))

  (local (in-theory (e/d () (force (force)))))

  ;; Relating rb and xr/xw in the application-level view:

  (defthm xr-rb-state-in-app-view
    (implies (app-view x86)
             (equal (xr fld index (mv-nth 2 (rb n addr r-x x86)))
                    (xr fld index x86)))
    :hints (("Goal" :in-theory (e/d* (rb rb-1) ()))))

  (defthm rb-xw-values-in-app-view
          (implies (and (app-view x86)
                        (not (equal fld :mem))
                        (not (equal fld :app-view)))
                   (and (equal (mv-nth 0 (rb n addr r-x (xw fld index value x86)))
                               (mv-nth 0 (rb n addr r-x x86)))
                        (equal (mv-nth 1 (rb n addr r-x (xw fld index value x86)))
                               (mv-nth 1 (rb n addr r-x x86)))))
          :hints (("Goal" :in-theory (e/d* (rb rb-1) ())
                   :induct (rb-1 n addr r-x x86))))

  (defthm rb-xw-state-in-app-view
    (implies (and (app-view x86)
                  (not (equal fld :app-view)))
             (equal (mv-nth 2 (rb n addr r-x (xw fld index value x86)))
                    (xw fld index value (mv-nth 2 (rb n addr r-x x86)))))
    :hints (("Goal" :in-theory (e/d* (rb rb-1) ()))))

  ;; Relating rb and xr/xw in the system-level view:

  (defthm xr-rb-1-state-in-sys-view
    (implies (and (not (app-view x86))
                  (not (equal fld :mem))
                  (not (equal fld :fault)))
             (equal (xr fld index (mv-nth 2 (rb-1 n addr r-x x86)))
                    (xr fld index x86)))
    :hints (("Goal" :in-theory (e/d* (rb rb-1) ())
             :induct (rb-1 n addr r-x x86))))

  (make-event
    (generate-xr-over-write-thms
      (remove-elements-from-list
        '(:mem :fault :tlb)
        *x86-field-names-as-keywords*)
      'rb
      (acl2::formals 'rb (w state))
      :output-index 2))

  (defthm rb-1-xw-values-in-sys-view
          (implies (and (not (app-view x86))
                        (not (equal fld :mem))
                        (not (equal fld :rflags))
                        (not (equal fld :ctr))
                        (not (equal fld :seg-visible))
                        (not (equal fld :msr))
                        (not (equal fld :fault))
                        (not (equal fld :app-view))
                        (not (equal fld :marking-view)))
                   (and (equal (mv-nth 0 (rb-1 n addr r-x (xw fld index value x86)))
                               (mv-nth 0 (rb-1 n addr r-x x86)))
                        (equal (mv-nth 1 (rb-1 n addr r-x (xw fld index value x86)))
                               (mv-nth 1 (rb-1 n addr r-x x86)))))
          :hints (("Goal" :in-theory (e/d* (rb rb-1) ())
                   :induct (rb-1 n addr r-x x86))))

  (make-event
    (generate-read-fn-over-xw-thms
      (remove-elements-from-list
        '(:mem :rflags :ctr :seg-visible :msr :fault
               :app-view :marking-view :tlb :implicit-supervisor-access)
        *x86-field-names-as-keywords*)
      'rb
      (acl2::formals 'rb (w state))
      :output-index 0))

  (make-event
    (generate-read-fn-over-xw-thms
      (remove-elements-from-list
        '(:mem :rflags :ctr :seg-visible :msr :fault
               :app-view :marking-view :tlb :implicit-supervisor-access)
        *x86-field-names-as-keywords*)
      'rb
      (acl2::formals 'rb (w state))
      :output-index 1))

  (defthm rb-1-xw-rflags-not-ac-values-in-sys-view
          (implies (and (not (app-view x86))
                        (equal (rflagsBits->ac value)
                               (rflagsBits->ac (rflags x86))))
                   (and (equal (mv-nth 0 (rb-1 n addr r-x (xw :rflags nil value x86)))
                               (mv-nth 0 (rb-1 n addr r-x x86)))
                        (equal (mv-nth 1 (rb-1 n addr r-x (xw :rflags nil value x86)))
                               (mv-nth 1 (rb-1 n addr r-x x86)))))
          :hints (("Goal" :induct (rb-1 n addr r-x x86)
                   :in-theory (e/d* (rb rb-1) ()))))

  (defthm rb-xw-rflags-not-ac-values-in-sys-view
          (implies (and (not (app-view x86))
                        (equal (rflagsBits->ac value)
                               (rflagsBits->ac (rflags x86))))
                   (and (equal (mv-nth 0 (rb n addr r-x (xw :rflags nil value x86)))
                               (mv-nth 0 (rb n addr r-x x86)))
                        (equal (mv-nth 1 (rb n addr r-x (xw :rflags nil value x86)))
                               (mv-nth 1 (rb n addr r-x x86)))))
          :hints (("Goal" :in-theory (e/d* (rb) ()))))

  (defthm rb-1-xw-state-in-sys-view
          (implies (and (not (app-view x86))
                        (not (equal fld :mem))
                        (not (equal fld :rflags))
                        (not (equal fld :ctr))
                        (not (equal fld :seg-visible))
                        (not (equal fld :msr))
                        (not (equal fld :fault))
                        (not (equal fld :app-view))
                        (not (equal fld :marking-view)))
                   (equal (mv-nth 2 (rb-1 n addr r-x (xw fld index value x86)))
                          (xw fld index value (mv-nth 2 (rb-1 n addr r-x x86)))))
          :hints (("Goal" :in-theory (e/d* (rb rb-1) ())
                   :induct (rb-1 n addr r-x x86))))

  (make-event
    (generate-write-fn-over-xw-thms
      (remove-elements-from-list
        '(:mem :rflags :ctr :seg-visible :msr :fault
               :app-view :marking-view :tlb :implicit-supervisor-access)
        *x86-field-names-as-keywords*)
      'rb
      (acl2::formals 'rb (w state))
      :output-index 2))

  (defthm rb-1-xw-rflags-not-ac-state-in-sys-view
          (implies (and (not (app-view x86))
                        (equal (rflagsBits->ac value)
                               (rflagsBits->ac (rflags x86))))
                   (equal (mv-nth 2 (rb-1 n addr r-x (xw :rflags nil value x86)))
                          (xw :rflags nil value (mv-nth 2 (rb-1 n addr r-x x86)))))
          :hints (("Goal" :in-theory (e/d* (rb rb-1) ())
                   :induct (rb-1 n addr r-x x86))))

  (defthm rb-xw-rflags-not-ac-state-in-sys-view
          (implies (and (not (app-view x86))
                        (equal (rflagsBits->ac value)
                               (rflagsBits->ac (rflags x86))))
                   (equal (mv-nth 2 (rb n addr r-x (xw :rflags nil value x86)))
                          (xw :rflags nil value (mv-nth 2 (rb n addr r-x x86)))))
          :hints (("Goal" :in-theory (e/d* (rb) (force (force))))))

  ;; Relating wb and xr/xw in the application-level view:

  (defthm xr-wb-1-in-app-view
          (implies (and (app-view x86)
                        (not (equal fld :mem)))
                   (equal (xr fld index (mv-nth 1 (wb-1 n addr w value x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d* (wb-1) ()))))

  (defthm xr-wb-in-app-view
          (implies (and (app-view x86)
                        (not (equal fld :mem)))
                   (equal (xr fld index (mv-nth 1 (wb n addr w value x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d* (wb) ()))))

  (defthm wb-1-xw-in-app-view
          ;; Keep the state updated by wb-1 inside all other nests of writes.
          (implies (and (app-view x86)
                        (not (equal fld :mem))
                        (not (equal fld :app-view)))
                   (and (equal (mv-nth 0 (wb-1 n addr w val (xw fld index value x86)))
                               (mv-nth 0 (wb-1 n addr w val x86)))
                        (equal (mv-nth 1 (wb-1 n addr w val (xw fld index value x86)))
                               (xw fld index value (mv-nth 1 (wb-1 n addr w val x86))))))
          :hints (("Goal" :in-theory (e/d* (wb-1) ()))))

  (defthm wb-xw-in-app-view
          ;; Keep the state updated by wb inside all other nests of writes.
          (implies (and (app-view x86)
                        (not (equal fld :mem))
                        (not (equal fld :app-view)))
                   (and (equal (mv-nth 0 (wb n addr w val (xw fld index value x86)))
                               (mv-nth 0 (wb n addr w val x86)))
                        (equal (mv-nth 1 (wb n addr w val (xw fld index value x86)))
                               (xw fld index value (mv-nth 1 (wb n addr w val x86))))))
          :hints (("Goal" :in-theory (e/d* (wb) ()))))

  ;; Relating wb and xr/xw in the system-level view:

  (make-event
    (generate-xr-over-write-thms
      (remove-elements-from-list
        '(:mem :fault :tlb)
        *x86-field-names-as-keywords*)
      'wb
      (acl2::formals 'wb (w state))
      :output-index 1))

  (defthm xr-fault-wb-in-system-level-marking-view
          (implies
            (not (mv-nth 0 (las-to-pas n addr :w (double-rewrite x86))))
            (equal (xr :fault nil (mv-nth 1 (wb n addr w val x86)))
                   (xr :fault nil x86)))
          :hints
          (("Goal" :do-not-induct t
            :in-theory (e/d* (wb)
                             ((:meta acl2::mv-nth-cons-meta)
                              force (force))))))

  (defrule 64-bit-modep-of-mv-nth-1-of-wb ; contributed by Eric Smith
           (equal (64-bit-modep (mv-nth 1 (wb n addr w value x86)))
                  (64-bit-modep x86))
           :hints (("Goal" :in-theory (e/d* (64-bit-modep)
                                            (force (force))))))

  (defrule x86-operation-mode-of-mv-nth-1-of-wb
           (equal (x86-operation-mode (mv-nth 1 (wb n addr w value x86)))
                  (x86-operation-mode x86))
           :hints (("Goal" :in-theory (e/d* (x86-operation-mode)
                                            (wb)))))

  ;; The following make-events generate a bunch of rules that together
  ;; say the same thing as wb-xw-in-sys-view, but these rules
  ;; are more efficient than wb-xw-in-sys-view as they match
  ;; less frequently.  Note that wb is kept inside all other nests of
  ;; writes.
  (make-event
    (generate-read-fn-over-xw-thms
      (remove-elements-from-list
        '(:mem :rflags :ctr :seg-visible :msr :fault
               :app-view :marking-view :tlb :implicit-supervisor-access)
        *x86-field-names-as-keywords*)
      'wb
      (acl2::formals 'wb (w state))
      :output-index 0))

  (make-event
    (generate-write-fn-over-xw-thms
      (remove-elements-from-list
        '(:mem :rflags :ctr :seg-visible :msr :fault
               :app-view :marking-view :tlb :implicit-supervisor-access)
        *x86-field-names-as-keywords*)
      'wb
      (acl2::formals 'wb (w state))
      :output-index 1))

  (defthm wb-xw-rflags-not-ac-in-sys-view
          ;; Keep the state updated by wb inside all other nests of writes.
          (implies (equal (rflagsBits->ac value)
                          (rflagsBits->ac (rflags x86)))
                   (and (equal (mv-nth 0 (wb n addr w val (xw :rflags nil value x86)))
                               (mv-nth 0 (wb n addr w val (double-rewrite x86))))
                        (equal (mv-nth 1 (wb n addr w val (xw :rflags nil value x86)))
                               (xw :rflags nil value (mv-nth 1 (wb n addr w val x86))))))
          :hints (("Goal" :in-theory (e/d* (wb) (write-to-physical-memory)))))

  (defthm xr-fault-wb-in-sys-view
          (implies (and (not (mv-nth 0 (las-to-pas n addr :w x86)))
                        (not (marking-view x86)))
                   (equal (xr :fault nil (mv-nth 1 (wb n addr w val x86)))
                          (xr :fault nil x86)))
          :hints
          (("Goal" :in-theory (e/d* (wb)
                                    (write-to-physical-memory force (force))))))

  (local
    (encapsulate
      ()

      (local (include-book "arithmetic-3/top" :dir :system))

      (defthm ash-and-plus
              (implies (posp n)
                       (equal (+ 8 (ash (+ -1 n) 3))
                              (ash n 3)))
              :hints (("Goal" :in-theory (e/d* (ash) ()))))

      (defthm ash-and-minus
              (implies (posp n)
                       (equal (+ -8 (ash n 3))
                              (ash (+ -1 n) 3)))
              :hints (("Goal" :in-theory (e/d* (ash) ()))))

      (defthm ash-n-3-bound
              (implies (and (not (zp n))
                            (natp n))
                       (<= 8 (ash n 3)))
              :hints (("Goal" :in-theory (e/d* (ash) ())))
              :rule-classes :linear)

      (defthm ash-separate-out
              (implies (natp n)
                       (equal (ash (+ 1 n) 3)
                              (+ 8 (ash n 3))))
              :hints (("Goal" :in-theory (e/d* (ash) ()))))))

  (defthm split-rb-in-app-view
          (implies (and (canonical-address-p (+ -1 i j lin-addr))
                        (canonical-address-p lin-addr)
                        (app-view x86)
                        (natp i)
                        (natp j))
                   (equal (mv-nth 1 (rb (+ i j) lin-addr r-x x86))
                          (b* ((low (mv-nth 1 (rb i lin-addr r-x x86)))
                               (high (mv-nth 1 (rb j (+ i lin-addr) r-x x86))))
                              (logior low (ash high (ash i 3))))))
          :hints (("Goal" :in-theory (e/d* (push-ash-inside-logior)
                                           (unsigned-byte-p
                                             force (force))))))

  (defun-nx split-wb-induction-scheme (i j lin-addr val x86)
            (cond ((or (not (natp i))
                       (not (natp j))
                       (zp (+ i j))
                       (zp i)
                       (not (canonical-address-p lin-addr))
                       (not (canonical-address-p (+ -1 i j lin-addr))))
                   (mv i j lin-addr val x86))
                  (t
                    (split-wb-induction-scheme (1- i) j (1+ lin-addr) (logtail 8 val)
                                               (mv-nth 1 (wvm08 lin-addr (loghead 8 val) x86))))))

  (local
    (defthm wb-1-1
            (implies (canonical-address-p lin-addr)
                     (equal (mv-nth 1 (wb-1 1 lin-addr w val x86))
                            (mv-nth 1 (wvm08 lin-addr (loghead 8 val) x86))))
            :hints (("Goal"
                     :expand ((wb-1 1 lin-addr w val x86))
                     :in-theory (e/d (wb-1) ())))))

  (defthm split-wb-in-app-view
          (implies (and (canonical-address-p lin-addr)
                        (canonical-address-p (+ -1 i j lin-addr))
                        (unsigned-byte-p (ash (+ i j) 3) val)
                        (app-view x86)
                        (posp i)
                        (natp j))
                   (equal (mv-nth 1 (wb-1 (+ i j) lin-addr w val x86))
                          (mv-nth 1 (wb-1 j (+ i lin-addr) w
                                          (loghead (ash j 3) (logtail (ash i 3) val))
                                          (mv-nth 1 (wb-1 i lin-addr w (loghead (ash i 3) val) x86))))))
          :hints (("Goal"
                   :induct (split-wb-induction-scheme i j lin-addr val x86)
                   :in-theory (e/d* (push-ash-inside-logior)
                                    (unsigned-byte-p))))))

;; ======================================================================

;; Defining the 8, 16, 32, 48, and 64, 80, and 128 bit memory
;; read/write functions:

;; I haven't used physical memory functions like rm-low-* and wm-low-*
;; in the system-level view below because the *-low-* functions take
;; one physical address as input and assume that the values to be read
;; or written are from contiguous physical memory locations. In the
;; functions below, there's no guarantee that the translation of
;; contiguous linear addresses will produce contiguous physical
;; addresses (though, IRL, that's likely the case). That's why there
;; are long and ugly sequences of memi and !memi below instead of nice
;; and pretty wrappers.

(local
 (defthm signed-byte-p-48-to-<-rule
   (implies (and (signed-byte-p 48 lin-addr)
                 (syntaxp (quotep n))
                 (natp n))
            (equal (signed-byte-p 48 (+ n lin-addr))
                   (< (+ n lin-addr) #.*2^47*)))))

(local
 (defthmd rb-1-in-terms-of-its-components
   ;; Ugh, dumb rule.
   (implies (and (app-view x86)
                 (canonical-address-p lin-addr)
                 (canonical-address-p (+ -1 n lin-addr))
                 (x86p x86))
            (equal (rb-1 n lin-addr r-x x86)
                   (list nil
                         (mv-nth 1 (rb-1 n lin-addr r-x x86))
                         x86)))
   :hints (("Goal"
            :expand ((rb-1 1 #.*2^47-1* r-x x86))
            :in-theory (e/d (rb-1) (force (force)))))))

(defthmd rb-1-opener-theorem
  (implies (canonical-address-p addr)
           (equal (rb-1 1 addr r-x x86)
                  (mv nil (ifix (mv-nth 1 (rvm08 addr x86))) x86)))
  :hints (("Goal" :expand ((rb-1 1 addr r-x x86))
           :in-theory (e/d* (rvm08) (force (force))))))

(defthmd wb-1-opener-theorem
  (implies (canonical-address-p addr)
           (equal (wb-1 1 addr w val x86)
                  (wvm08 addr (loghead 8 val) x86)))
  :hints (("Goal" :expand ((wb-1 1 addr w val x86))
           :in-theory (e/d* (wvm08) ()))))

(local (in-theory (e/d (rb-1-opener-theorem wb-1-opener-theorem)
                       (signed-byte-p))))

(local
 (defthm member-equal-r-w-x-lemma
   (implies (member-equal r-x '(:r :x))
            (member-equal r-x '(:r :w :x)))))

(local (in-theory (e/d* () (member-equal))))

(define rml08 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
               (r-x      :type (member  :r :x))
               (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)
  :guard-hints (("goal"
                 :in-theory (e/d* (ifix rvm08) ())))

  (mbe
    :logic
    (rb 1 lin-addr r-x x86)
    :exec
    (if (app-view x86)
      (rvm08 lin-addr x86)
      (b* (((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr) x86)
            (la-to-pa lin-addr r-x x86))
           ((when flag)
            (mv flag 0 x86))
           (byte (the (unsigned-byte 8) (memi p-addr x86))))
          (mv nil byte x86))))

  ///

  (defthm-unsigned-byte-p n08p-mv-nth-1-rml08
                          :hyp t
                          :bound 8
                          :concl (mv-nth 1 (rml08 lin-addr r-x x86))
                          :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
                          :gen-linear t
                          :hints-l (("Goal" :in-theory (e/d (unsigned-byte-p) ())))
                          :gen-type t)

  (defthm x86p-rml08
          (implies (force (x86p x86))
                   (x86p (mv-nth 2 (rml08 lin-addr r-x x86))))
          :hints (("Goal" :in-theory (e/d () (x86p)))))

  (local
    (defthm rml08-value-when-error-helper
            (implies (and (xr :app-view nil x86)
                          (mv-nth 0 (rb-1 1 addr r-x x86)))
                     (equal (mv-nth 1 (rb-1 1 addr r-x x86))
                            0))
            :hints (("Goal" :expand ((rb-1 1 addr r-x x86))))))

  (defthm rml08-value-when-error
          (implies (mv-nth 0 (rml08 addr r-x x86))
                   (equal (mv-nth 1 (rml08 addr r-x x86)) 0))
          :hints (("Goal"
                   :cases ((app-view x86))
                   :in-theory (e/d () (force (force))))))

  (defthm rml08-does-not-affect-state-in-app-view
          (implies (app-view x86)
                   (equal (mv-nth 2 (rml08 start-rip r-x x86)) x86))
          :hints (("Goal" :in-theory (e/d (rvm08) (force (force))))))

  (defthm app-view-rml08-no-error
          (implies (and (app-view x86)
                        (canonical-address-p addr)
                        (x86p x86))
                   (and (equal (mv-nth 0 (rml08 addr r-x x86)) nil)
                        (equal (mv-nth 1 (rml08 addr :x x86))
                               (memi (loghead 48 addr) x86))
                        (equal (mv-nth 2 (rml08 addr r-x x86)) x86)))
          :hints (("Goal" :in-theory (e/d (rvm08) (force (force))))))

  (defthm xr-rml08-state-in-app-view
          (implies (app-view x86)
                   (equal (xr fld index (mv-nth 2 (rml08 addr r-x x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm xr-rml08-state-in-sys-view
          (implies (and (not (app-view x86))
                        (not (equal fld :mem))
                        (not (equal fld :fault))
                        (not (equal fld :tlb)))
                   (equal (xr fld index (mv-nth 2 (rml08 addr r-x x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm rml08-xw-app-view
          (implies (and (app-view x86)
                        (not (equal fld :mem))
                        (not (equal fld :app-view)))
                   (and (equal (mv-nth 0 (rml08 addr r-x (xw fld index value x86)))
                               (mv-nth 0 (rml08 addr r-x x86)))
                        (equal (mv-nth 1 (rml08 addr r-x (xw fld index value x86)))
                               (mv-nth 1 (rml08 addr r-x x86)))
                        ;; No need for the conclusion about the state because
                        ;; "rml08-does-not-affect-state-in-app-view".
                        ))
          :hints (("Goal" :in-theory (e/d* () (rb)))))

  (defthm rml08-xw-system-mode
          (implies (and (not (app-view x86))
                        (not (equal fld :tlb))
                        (not (equal fld :fault))
                        (not (equal fld :seg-visible))
                        (not (equal fld :mem))
                        (not (equal fld :ctr))
                        (not (equal fld :msr))
                        (not (equal fld :rflags))
                        (not (equal fld :app-view))
                        (not (equal fld :marking-view))
                        (not (equal fld :implicit-supervisor-access)))
                   (and (equal (mv-nth 0 (rml08 addr r-x (xw fld index value x86)))
                               (mv-nth 0 (rml08 addr r-x x86)))
                        (equal (mv-nth 1 (rml08 addr r-x (xw fld index value x86)))
                               (mv-nth 1 (rml08 addr r-x x86)))
                        (equal (mv-nth 2 (rml08 addr r-x (xw fld index value x86)))
                               (xw fld index value (mv-nth 2 (rml08 addr r-x x86)))))))

  (defthm rml08-xw-system-mode-rflags-not-ac
          (implies (and (not (app-view x86))
                        (equal (rflagsBits->ac value)
                               (rflagsBits->ac (rflags x86))))
                   (and (equal (mv-nth 0 (rml08 addr r-x (xw :rflags nil value x86)))
                               (mv-nth 0 (rml08 addr r-x x86)))
                        (equal (mv-nth 1 (rml08 addr r-x (xw :rflags nil value x86)))
                               (mv-nth 1 (rml08 addr r-x x86)))
                        (equal (mv-nth 2 (rml08 addr r-x (xw :rflags nil value x86)))
                               (xw :rflags nil value (mv-nth 2 (rml08 addr r-x x86)))))))

  (defrule 64-bit-modep-of-rml08
           (equal (64-bit-modep (mv-nth 2 (rml08 li-addr r-x x86)))
                  (64-bit-modep x86))
           :enable 64-bit-modep
           :disable (force (force)))

  (defrule x86-operation-mode-of-rml08
           (equal (x86-operation-mode (mv-nth 2 (rml08 li-addr r-x x86)))
                  (x86-operation-mode x86))
           :enable x86-operation-mode
           :disable rml08))

(define riml08 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
                (r-x    :type (member  :r :x))
                (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)

  (mv-let (flag val x86)
          (rml08 lin-addr r-x x86)
          (mv flag (n08-to-i08 val) x86))
  ///

  (defthm-signed-byte-p i08p-mv-nth-1-riml08
                        :hyp t
                        :bound 8
                        :concl (mv-nth 1 (riml08 lin-addr r-x x86))
                        :hints (("Goal" :in-theory (e/d () (signed-byte-p))))
                        :gen-linear t
                        :hints-l (("Goal" :in-theory (e/d (signed-byte-p) ())))
                        :gen-type t)

  (defthm x86p-riml08
          (implies (force (x86p x86))
                   (x86p (mv-nth 2 (riml08 lin-addr r-x x86))))
          :hints (("Goal" :in-theory (e/d () (x86p))))
          :rule-classes (:rewrite :type-prescription)))

(define wml08 ((lin-addr :type (signed-byte   #.*max-linear-address-size*))
               (val      :type (unsigned-byte 8))
               (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)
  :guard-hints (("Goal" :in-theory (e/d* (wvm08) ())))

  (mbe
    :logic (wb 1 lin-addr :w val x86)
    :exec
    (if (app-view x86)
      (wvm08 lin-addr val x86)
      (b* (((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr) x86)
            (la-to-pa lin-addr :w x86))
           ((when flag)
            (mv flag x86))
           (byte (mbe :logic (n08 val) :exec val))
           (x86 (!memi p-addr byte x86)))
          (mv nil x86))))

  ///

  (defthm x86p-wml08
          (implies (force (x86p x86))
                   (x86p (mv-nth 1 (wml08 lin-addr val x86))))
          :hints (("Goal" :in-theory (e/d () (x86p force (force)))))
          :rule-classes (:rewrite :type-prescription))

  (defthm app-view-wml08-no-error
          (implies (and (app-view x86)
                        (canonical-address-p addr))
                   (equal (mv-nth 0 (wml08 addr val x86)) nil))
          :hints (("Goal" :in-theory (e/d (wml08 wvm08) ()))))

  (defthm xr-wml08-app-view
          (implies (and (app-view x86)
                        (not (equal fld :mem)))
                   (equal (xr fld index (mv-nth 1 (wml08 addr val x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d* (wvm08) ()))))

  (defthm xr-wml08-sys-view
          (implies (and (not (app-view x86))
                        (not (equal fld :tlb))
                        (not (equal fld :mem))
                        (not (equal fld :fault)))
                   (equal (xr fld index (mv-nth 1 (wml08 addr val x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm wml08-xw-app-view
          (implies (and (app-view x86)
                        (not (equal fld :mem))
                        (not (equal fld :app-view)))
                   (and (equal (mv-nth 0 (wml08 addr val (xw fld index value x86)))
                               (mv-nth 0 (wml08 addr val x86)))
                        (equal (mv-nth 1 (wml08 addr val (xw fld index value x86)))
                               (xw fld index value (mv-nth 1 (wml08 addr val x86))))))
          :hints (("Goal" :in-theory (e/d* (wml08 wvm08) ()))))

  (defthm wml08-xw-system-mode
          (implies (and (not (app-view x86))
                        (not (equal fld :tlb))
                        (not (equal fld :fault))
                        (not (equal fld :seg-visible))
                        (not (equal fld :mem))
                        (not (equal fld :ctr))
                        (not (equal fld :rflags))
                        (not (equal fld :msr))
                        (not (equal fld :app-view))
                        (not (equal fld :marking-view))
                        (not (equal fld :implicit-supervisor-access)))
                   (and (equal (mv-nth 0 (wml08 addr val (xw fld index value x86)))
                               (mv-nth 0 (wml08 addr val x86)))
                        (equal (mv-nth 1 (wml08 addr val (xw fld index value x86)))
                               (xw fld index value (mv-nth 1 (wml08 addr val x86))))))
          :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm wml08-xw-system-mode-rflags-not-ac
          (implies (and (not (app-view x86))
                        (equal (rflagsBits->ac value)
                               (rflagsBits->ac (rflags x86))))
                   (and (equal (mv-nth 0 (wml08 addr val (xw :rflags nil value x86)))
                               (mv-nth 0 (wml08 addr val x86)))
                        (equal (mv-nth 1 (wml08 addr val (xw :rflags nil value x86)))
                               (xw :rflags nil value (mv-nth 1 (wml08 addr val x86))))))
          :hints (("Goal" :in-theory (e/d* () (force (force)))))))

(define wiml08 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
                (val      :type (signed-byte 8))
                (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)

  (wml08 lin-addr (the (unsigned-byte 8) (n08 val)) x86)
  ///
  (defthm x86p-wiml08
          (implies (force (x86p x86))
                   (x86p (mv-nth 1 (wiml08 lin-addr val x86))))
          :hints (("Goal" :in-theory (e/d () (x86p))))
          :rule-classes (:rewrite :type-prescription)))

(local (include-book "centaur/bitops/width-find-rule" :dir :system))
(local (in-theory (e/d (bitops::unsigned-byte-p-by-find-rule) ())))

(define rml16 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
               (r-x      :type (member  :r :x))
               (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)
  :guard-hints (("Goal" :in-theory (e/d (rb-and-rvm16 rml08)
                                        ())))

  :prepwork

  ((defthmd rb-and-rvm16
            (implies (and (app-view x86)
                          (canonical-address-p lin-addr)
                          (canonical-address-p (1+ lin-addr))
                          (x86p x86))
                     (equal (rvm16 lin-addr x86)
                            (rb 2 lin-addr r-x x86)))
            :hints (("Goal"
                     :in-theory (e/d (rml08 rvm08 rvm16)
                                     (force (force)))))))

  (let* ((1+lin-addr (the (signed-byte #.*max-linear-address-size+1*)
                          (1+ (the (signed-byte #.*max-linear-address-size*)
                                   lin-addr)))))


    (if (mbe :logic (canonical-address-p 1+lin-addr)
             :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                           1+lin-addr)
                      #.*2^47*))

      (mbe :logic
           (rb 2 lin-addr r-x x86)
           :exec
           (if (app-view x86)

             (rvm16 lin-addr x86)

             (b* (((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr0) x86)
                   (la-to-pa lin-addr r-x x86))
                  ((when flag) (mv flag 0 x86))

                  (1+lin-addr
                   (the (signed-byte #.*max-linear-address-size+1*)
                        (1+ (the (signed-byte #.*max-linear-address-size*)
                                 lin-addr))))
                  ((mv flag (the (unsigned-byte #.*physical-address-size*) ?p-addr1) x86)
                   (la-to-pa 1+lin-addr r-x x86))
                  ((when flag) (mv flag 0 x86))

                  (byte0 (the (unsigned-byte 8) (memi p-addr0 x86)))
                  (byte1 (the (unsigned-byte 8) (memi p-addr1 x86)))

                  (word (the (unsigned-byte 16)
                             (logior (the (unsigned-byte 16) (ash byte1 8))
                                     byte0))))

                 (mv nil word x86))))

      (mv 'rml16 0 x86)))

  ///

  (defthm-unsigned-byte-p n16p-mv-nth-1-rml16
                          :hyp t
                          :bound 16
                          :concl (mv-nth 1 (rml16 lin-addr r-x x86))
                          :hints (("Goal" :in-theory (e/d () (signed-byte-p))))
                          :gen-linear t
                          :hints-l (("Goal" :in-theory (e/d (signed-byte-p) ())))
                          :gen-type t)

  (defthm x86p-rml16
          (implies (force (x86p x86))
                   (x86p (mv-nth 2 (rml16 lin-addr r-x x86))))
          :hints (("Goal" :in-theory (disable x86p unsigned-byte-p signed-byte-p (force))))
          :rule-classes (:rewrite :type-prescription))

  (defthm rml16-value-when-error
          (implies (mv-nth 0 (rml16 lin-addr r-x x86))
                   (equal (mv-nth 1 (rml16 lin-addr r-x x86))
                          0))
          :hints (("Goal" :in-theory (e/d (rml16)
                                          (force (force))))))

  (defthm rml16-x86-unmodified-in-app-view
          (implies (app-view x86)
                   (equal (mv-nth 2 (rml16 lin-addr r-x x86))
                          x86))
          :hints (("Goal" :in-theory (e/d (rml16
                                            unsigned-byte-p
                                            signed-byte-p)
                                          (force (force))))))

  (defthm xr-rml16-state-sys-view
          (implies (and (not (app-view x86))
                        (not (equal fld :mem))
                        (not (equal fld :fault))
                        (not (equal fld :tlb))
                        (member-equal fld *x86-field-names-as-keywords*))
                   (equal (xr fld index (mv-nth 2 (rml16 lin-addr r-x x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d (rml16 member-equal)
                                          (rb force (force))))))

  (defrule rml16-xw-app-view
           (implies (and (app-view x86)
                         (not (equal fld :mem))
                         (not (equal fld :app-view)))
                    (and (equal (mv-nth 0 (rml16 lin-addr  r-x (xw fld index value x86)))
                                (mv-nth 0 (rml16 lin-addr r-x x86)))
                         (equal (mv-nth 1 (rml16 lin-addr r-x (xw fld index value x86)))
                                (mv-nth 1 (rml16 lin-addr r-x x86)))))
           :enable (rml16)
           :disable (rb unsigned-byte-p signed-byte-p (force) force))

  (defrule rml16-xw-sys-view
           (implies
             (and (not (app-view x86))
                  (not (equal fld :fault))
                  (not (equal fld :seg-visible))
                  (not (equal fld :seg-hidden-base))
                  (not (equal fld :seg-hidden-limit))
                  (not (equal fld :seg-hidden-attr))
                  (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :msr))
                  (not (equal fld :rflags))
                  (not (equal fld :app-view))
                  (not (equal fld :marking-view))
                  (not (equal fld :tlb))
                  (not (equal fld :implicit-supervisor-access))
                  (member-equal fld *x86-field-names-as-keywords*))
             (and (equal (mv-nth 0 (rml16 lin-addr r-x (xw fld index value x86)))
                         (mv-nth 0 (rml16 lin-addr r-x x86)))
                  (equal (mv-nth 1 (rml16 lin-addr r-x (xw fld index value x86)))
                         (mv-nth 1 (rml16 lin-addr r-x x86)))
                  (equal (mv-nth 2 (rml16 lin-addr r-x (xw fld index value x86)))
                         (xw fld index value (mv-nth 2 (rml16 lin-addr r-x x86))))))
           :enable (rml16 member-equal)
           :disable (rb unsigned-byte-p signed-byte-p force (force)))

  (defrule rml16-xw-sys-view-rflags-not-ac
           (implies
             (and (not (app-view x86))
                  (equal (rflagsbits->ac value)
                         (rflagsbits->ac (rflags x86))))
             (and (equal (mv-nth 0 (rml16 lin-addr r-x (xw :rflags nil value x86)))
                         (mv-nth 0 (rml16 lin-addr r-x x86)))
                  (equal (mv-nth 1 (rml16 lin-addr r-x (xw :rflags nil value x86)))
                         (mv-nth 1 (rml16 lin-addr r-x x86)))
                  (equal (mv-nth 2 (rml16 lin-addr r-x (xw :rflags nil value x86)))
                         (xw :rflags nil value
                             (mv-nth 2 (rml16 lin-addr r-x x86))))))
           :enable (rml16)
           :disable (rb unsigned-byte-p signed-byte-p member-equal)))

(define riml16 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
                (r-x    :type (member  :r :x))
                (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)

  (mv-let (flag val x86)
          (rml16 lin-addr r-x x86)
          (mv flag (n16-to-i16 val) x86))
  ///

  (defthm-signed-byte-p i16p-mv-nth-1-riml16
                        :hyp t
                        :bound 16
                        :concl (mv-nth 1 (riml16 lin-addr r-x x86))
                        :hints (("Goal" :in-theory (e/d () (signed-byte-p))))
                        :gen-linear t
                        :hints-l (("Goal" :in-theory (e/d (signed-byte-p) ())))
                        :gen-type t)

  (defthm x86p-riml16
          (implies (force (x86p x86))
                   (x86p (mv-nth 2 (riml16 lin-addr r-x x86))))
          :hints (("Goal" :in-theory (e/d () (x86p))))
          :rule-classes (:rewrite :type-prescription)))

(define wml16
  ((lin-addr :type (signed-byte   #.*max-linear-address-size*))
   (val      :type (unsigned-byte 16))
   (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)

  :guard-hints (("Goal" :in-theory (e/d (wb-and-wvm16) ())))

  :prepwork

  ((defthmd wb-and-wvm16
            (implies (and (app-view x86)
                          (canonical-address-p lin-addr)
                          (canonical-address-p (1+ lin-addr)))
                     (equal (wvm16 lin-addr val x86)
                            (wb 2 lin-addr :w val x86)))
            :hints (("Goal"
                     :in-theory (e/d (wml08 wvm08 wvm16)
                                     (force (force) unsigned-byte-p))))))

  (if (mbt (canonical-address-p lin-addr))

    (let* ((1+lin-addr (the (signed-byte #.*max-linear-address-size+1*)
                            (1+ (the (signed-byte #.*max-linear-address-size*)
                                     lin-addr)))))

      (if (mbe :logic (canonical-address-p 1+lin-addr)
               :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                             1+lin-addr)
                        #.*2^47*))

        (mbe
          :logic
          (wb 2 lin-addr :w val x86)
          :exec
          (if (app-view x86)

            (wvm16 lin-addr val x86)

            (b* (((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr0) x86)
                  (la-to-pa lin-addr :w x86))
                 ((when flag) (mv flag x86))

                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr1) x86)
                  (la-to-pa 1+lin-addr :w x86))
                 ((when flag) (mv flag x86))

                 (byte0 (mbe
                          :logic (part-select val :low 0 :width 8)
                          :exec (the (unsigned-byte 8) (logand #xff val))))
                 (byte1 (mbe
                          :logic (part-select val :low 8 :width 8)
                          :exec (the (unsigned-byte 8)
                                     (logand #xff (ash val -8)))))

                 (x86 (!memi p-addr0 byte0 x86))
                 (x86 (!memi p-addr1 byte1 x86)))
                (mv nil x86))))

        (mv 'wml16 x86)))

    (mv 'wml16 x86))

  ///

  (defthm x86p-wml16
          (implies (force (x86p x86))
                   (x86p (mv-nth 1 (wml16 lin-addr val x86))))
          :hints (("Goal" :in-theory (e/d () (x86p unsigned-byte-p signed-byte-p force (force)))))
          :rule-classes (:rewrite :type-prescription)))

(define wiml16 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
                (val      :type (signed-byte 16))
                (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)

  (wml16 lin-addr (the (unsigned-byte 16) (n16 val)) x86)
  ///
  (defthm x86p-wiml16
          (implies (force (x86p x86))
                   (x86p (mv-nth 1 (wiml16 lin-addr val x86))))
          :hints (("Goal" :in-theory (e/d () (x86p))))
          :rule-classes (:rewrite :type-prescription)))

(define rml32 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
               (r-x    :type (member  :r :x))
               (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)
  :guard-hints (("Goal" :in-theory (e/d (rb-and-rvm32 rml08)
                                        (rb-1
                                          (:rewrite acl2::ash-0)
                                          (:rewrite acl2::zip-open)
                                          (:linear bitops::logior-<-0-linear-2)
                                          (:rewrite xr-and-ia32e-la-to-pa-in-non-marking-view)
                                          (:rewrite bitops::logior-equal-0)))))

  :prepwork

  ((defthmd rb-and-rvm32
            (implies (and (app-view x86)
                          (x86p x86)
                          (canonical-address-p lin-addr)
                          (canonical-address-p (+ 3 lin-addr)))
                     (equal
                       (rvm32 lin-addr x86)
                       (rb 4 lin-addr r-x x86)))
            :hints (("Goal"
                     :in-theory (e/d (rml08 rvm08 rvm32) (force (force)))))))

  (if (mbt (canonical-address-p lin-addr))

    (let* ((3+lin-addr (the (signed-byte #.*max-linear-address-size+1*)
                            (+ 3 (the (signed-byte #.*max-linear-address-size*)
                                      lin-addr)))))

      (if (mbe :logic (canonical-address-p 3+lin-addr)
               :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                             3+lin-addr)
                        #.*2^47*))

        (mbe :logic
             (rb 4 lin-addr r-x x86)
             :exec
             (if (app-view x86)

               (rvm32 lin-addr x86)

               (b* (((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr0) x86)
                     (la-to-pa lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))

                    (1+lin-addr (the (signed-byte #.*max-linear-address-size+1*)
                                     (+ 1 (the (signed-byte #.*max-linear-address-size*)
                                               lin-addr))))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr1) x86)
                     (la-to-pa 1+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))

                    (2+lin-addr (the (signed-byte #.*max-linear-address-size+2*)
                                     (+ 2 (the (signed-byte #.*max-linear-address-size*)
                                               lin-addr))))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr2) x86)
                     (la-to-pa 2+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))

                    (3+lin-addr (the (signed-byte #.*max-linear-address-size+3*)
                                     (+ 3 (the (signed-byte #.*max-linear-address-size*)
                                               lin-addr))))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr3) x86)
                     (la-to-pa 3+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))

                    (byte0 (the (unsigned-byte 8) (memi p-addr0 x86)))
                    (byte1 (the (unsigned-byte 8) (memi p-addr1 x86)))
                    (byte2 (the (unsigned-byte 8) (memi p-addr2 x86)))
                    (byte3 (the (unsigned-byte 8) (memi p-addr3 x86)))
                    ((the (unsigned-byte 16) word1)
                     (logior byte2 (the (unsigned-byte 16) (ash byte3 8))))
                    ((the (unsigned-byte 24) high-24)
                     (logior byte1 (the (unsigned-byte 24) (ash word1 8))))
                    ((the (unsigned-byte 32) dword)
                     (logior byte0 (the (unsigned-byte 32) (ash high-24 8)))))

                   (mv nil dword x86))))

        (mv 'rml32 0 x86)))

    (mv 'rml32 0 x86))

  ///

  (defthm-unsigned-byte-p n32p-mv-nth-1-rml32
                          :hyp t
                          :bound 32
                          :concl (mv-nth 1 (rml32 lin-addr r-x x86))
                          :hints (("Goal" :in-theory (e/d () (signed-byte-p))))
                          :gen-linear t
                          :hints-l (("Goal" :in-theory (e/d (signed-byte-p) (force (force)))))
                          :gen-type t)

  (defthm x86p-rml32
          (implies (force (x86p x86))
                   (x86p (mv-nth 2 (rml32 lin-addr r-x x86))))
          :hints (("Goal" :in-theory (disable x86p unsigned-byte-p signed-byte-p (force))))
          :rule-classes (:rewrite :type-prescription))

  (defthm rml32-value-when-error
          (implies (mv-nth 0 (rml32 lin-addr r-x x86))
                   (equal (mv-nth 1 (rml32 lin-addr r-x x86))
                          0))
          :hints (("Goal" :in-theory (e/d (rml32)
                                          (force (force))))))

  (defthm rml32-x86-unmodified-in-app-view
          (implies (app-view x86)
                   (equal (mv-nth 2 (rml32 lin-addr r-x x86))
                          x86))
          :hints (("Goal" :in-theory (e/d (rml32
                                            unsigned-byte-p
                                            signed-byte-p)
                                          (force (force))))))

  (defthm xr-rml32-state-sys-view
          (implies (and (not (app-view x86))
                        (not (equal fld :mem))
                        (not (equal fld :fault))
                        (not (equal fld :tlb))
                        (member-equal fld *x86-field-names-as-keywords*))
                   (equal (xr fld index (mv-nth 2 (rml32 lin-addr r-x x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d (rml32 member-equal)
                                          (force (force))))))

  (defrule rml32-xw-app-view
           (implies (and (app-view x86)
                         (not (equal fld :mem))
                         (not (equal fld :app-view)))
                    (and (equal (mv-nth 0 (rml32 lin-addr  r-x (xw fld index value x86)))
                                (mv-nth 0 (rml32 lin-addr r-x x86)))
                         (equal (mv-nth 1 (rml32 lin-addr r-x (xw fld index value x86)))
                                (mv-nth 1 (rml32 lin-addr r-x x86)))))
           :enable (rml32)
           :disable (rb unsigned-byte-p signed-byte-p (force) force))

  (defrule rml32-xw-sys-view
           (implies
             (and (not (app-view x86))
                  (not (equal fld :fault))
                  (not (equal fld :seg-visible))
                  (not (equal fld :seg-hidden-base))
                  (not (equal fld :seg-hidden-limit))
                  (not (equal fld :seg-hidden-attr))
                  (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :msr))
                  (not (equal fld :rflags))
                  (not (equal fld :app-view))
                  (not (equal fld :marking-view))
                  (not (equal fld :tlb))
                  (not (equal fld :implicit-supervisor-access))
                  (member-equal fld *x86-field-names-as-keywords*))
             (and (equal (mv-nth 0 (rml32 lin-addr r-x (xw fld index value x86)))
                         (mv-nth 0 (rml32 lin-addr r-x x86)))
                  (equal (mv-nth 1 (rml32 lin-addr r-x (xw fld index value x86)))
                         (mv-nth 1 (rml32 lin-addr r-x x86)))
                  (equal (mv-nth 2 (rml32 lin-addr r-x (xw fld index value x86)))
                         (xw fld index value (mv-nth 2 (rml32 lin-addr r-x x86))))))
           :enable (rml32 member-equal)
           :disable (rb unsigned-byte-p signed-byte-p force (force)))

  (defrule rml32-xw-sys-view-rflags-not-ac
           (implies
             (and (not (app-view x86))
                  (equal (rflagsbits->ac value)
                         (rflagsbits->ac (rflags x86))))
             (and (equal (mv-nth 0 (rml32 lin-addr r-x (xw :rflags nil value x86)))
                         (mv-nth 0 (rml32 lin-addr r-x x86)))
                  (equal (mv-nth 1 (rml32 lin-addr r-x (xw :rflags nil value x86)))
                         (mv-nth 1 (rml32 lin-addr r-x x86)))
                  (equal (mv-nth 2 (rml32 lin-addr r-x (xw :rflags nil value x86)))
                         (xw :rflags nil value
                             (mv-nth 2 (rml32 lin-addr r-x x86))))))
           :enable (rml32)
           :disable (rb unsigned-byte-p signed-byte-p member-equal)))

(define riml32 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
                (r-x    :type (member  :r :x))
                (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)

  (mv-let (flag val x86)
          (rml32 lin-addr r-x x86)
          (mv flag (n32-to-i32 val) x86))
  ///

  (defthm-signed-byte-p i32p-mv-nth-1-riml32
                        :hyp t
                        :bound 32
                        :concl (mv-nth 1 (riml32 lin-addr r-x x86))
                        :hints (("Goal" :in-theory (e/d () (signed-byte-p))))
                        :gen-linear t
                        :hints-l (("Goal" :in-theory (e/d (signed-byte-p) ())))
                        :gen-type t)

  (defthm x86p-riml32
          (implies (force (x86p x86))
                   (x86p (mv-nth 2 (riml32 lin-addr r-x x86))))
          :rule-classes (:rewrite :type-prescription)))

(define wml32 ((lin-addr :type (signed-byte   #.*max-linear-address-size*))
               (val      :type (unsigned-byte 32))
               (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)

  :guard-hints (("Goal" :in-theory (e/d (wb-and-wvm32)
                                        ((:rewrite acl2::ash-0)
                                         (:rewrite acl2::zip-open)
                                         (:linear bitops::logior-<-0-linear-2)
                                         (:rewrite xr-and-ia32e-la-to-pa-in-non-marking-view)
                                         (:rewrite bitops::logior-equal-0)))))

  :prepwork

  ((defthmd wb-and-wvm32
            (implies (and (app-view x86)
                          (canonical-address-p lin-addr)
                          (canonical-address-p (+ 3 lin-addr)))
                     (equal (wvm32 lin-addr val x86)
                            (wb 4 lin-addr :w val x86)))
            :hints (("Goal" :in-theory (e/d (wml08 wvm08 wvm32)
                                            (force (force)))))))

  (if (mbt (canonical-address-p lin-addr))

    (let* ((3+lin-addr (the (signed-byte #.*max-linear-address-size+1*)
                            (+ 3 (the (signed-byte #.*max-linear-address-size*)
                                      lin-addr)))))


      (if (mbe :logic (canonical-address-p 3+lin-addr)
               :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                             3+lin-addr)
                        #.*2^47*))

        (mbe
          :logic
          (wb 4 lin-addr :w val x86)
          :exec
          (if (app-view x86)
            (wvm32 lin-addr val x86)

            (b* (((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr0) x86)
                  (la-to-pa lin-addr :w x86))
                 ((when flag) (mv flag x86))

                 ((the (signed-byte #.*max-linear-address-size+1*) 1+lin-addr)
                  (+ 1 lin-addr))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr1) x86)
                  (la-to-pa 1+lin-addr :w x86))
                 ((when flag) (mv flag x86))

                 (2+lin-addr (the (signed-byte #.*max-linear-address-size+2*)
                                  (+ 2 (the (signed-byte #.*max-linear-address-size*)
                                            lin-addr))))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr2) x86)
                  (la-to-pa 2+lin-addr :w x86))
                 ((when flag) (mv flag x86))

                 (3+lin-addr (the (signed-byte #.*max-linear-address-size+3*)
                                  (+ 3 (the (signed-byte #.*max-linear-address-size*)
                                            lin-addr))))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr3) x86)
                  (la-to-pa 3+lin-addr :w x86))
                 ((when flag) (mv flag x86))

                 (byte0 (mbe
                          :logic (part-select val :low 0 :width 8)
                          :exec  (the (unsigned-byte 8) (logand #xff val))))
                 (byte1 (mbe
                          :logic (part-select val :low 8 :width 8)
                          :exec  (the (unsigned-byte 8)
                                      (logand #xff (ash val -8)))))
                 (byte2 (mbe
                          :logic (part-select val :low 16 :width 8)
                          :exec (the (unsigned-byte 8)
                                     (logand #xff (ash val -16)))))
                 (byte3 (mbe
                          :logic (part-select val :low 24 :width 8)
                          :exec (the (unsigned-byte 8)
                                     (logand #xff (ash val -24)))))

                 (x86 (!memi p-addr0 byte0 x86))
                 (x86 (!memi p-addr1 byte1 x86))
                 (x86 (!memi p-addr2 byte2 x86))
                 (x86 (!memi p-addr3 byte3 x86)))
                (mv nil x86))))

        (mv 'wml32 x86)))

    (mv 'wml32 x86))

  ///

  (defthm x86p-wml32
          (implies (force (x86p x86))
                   (x86p (mv-nth 1 (wml32 lin-addr val x86))))
          :hints (("Goal" :in-theory (e/d () (x86p force (force)))))
          :rule-classes (:rewrite :type-prescription)))

(define wiml32 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
                (val      :type (signed-byte 32))
                (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)

  (wml32 lin-addr (the (unsigned-byte 32) (n32 val)) x86)
  ///
  (defthm x86p-wiml32
          (implies (force (x86p x86))
                   (x86p (mv-nth 1 (wiml32 lin-addr val x86))))
          :hints (("Goal" :in-theory (e/d () (x86p))))
          :rule-classes (:rewrite :type-prescription)))

(local
 (defthm dumb-member-lemma
   (implies (and (not (equal r-x :r))
                 (not (equal r-x :x)))
            (not (member-equal r-x '(:r :x))))))
(local (in-theory (e/d () ((:rewrite acl2::member-eql-exec-is-member-equal)
                           (:rewrite acl2::member-of-cons)
                           (:rewrite acl2::member-when-atom)))))


(define rml48 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
               (r-x      :type (member :r :x))
               (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)
  :guard-hints (("Goal"
                 :expand ((las-to-pas 6 lin-addr r-x x86)
                          (las-to-pas 5 (+ 1 lin-addr) r-x (mv-nth 2 (ia32e-la-to-pa lin-addr r-x x86))))
                 :in-theory (e/d (rb-and-rvm48
                                   rml08
                                   rb-and-rml48-helper-1
                                   rb-and-rml48-helper-2)
                                 (not
                                   (:rewrite acl2::ash-0)
                                   (:rewrite acl2::zip-open)
                                   (:linear bitops::logior-<-0-linear-2)
                                   (:rewrite xr-and-ia32e-la-to-pa-in-non-marking-view)
                                   (:rewrite bitops::logior-equal-0)))))

  :prepwork
  ((local
     (defthmd rb-and-rvm48-helper
              (implies
                (and (app-view x86)
                     (x86p x86)
                     (canonical-address-p lin-addr)
                     (canonical-address-p (+ 5 lin-addr)))
                (equal (rvm48 lin-addr x86)
                       (list nil
                             (logior
                               (mv-nth 1 (rb 2 lin-addr r-x x86))
                               (ash (mv-nth 1 (rb 4 (+ 2 lin-addr) r-x x86)) 16))
                             x86)))
              :hints (("Goal" :use ((:instance rb-and-rvm16)
                                    (:instance rb-and-rvm32 (lin-addr (+ 2 lin-addr))))
                       :in-theory (e/d (rvm48)
                                       (force (force)))))))


   (defthmd rb-and-rvm48
            (implies (and (app-view x86)
                          (x86p x86)
                          (canonical-address-p lin-addr)
                          (canonical-address-p (+ 5 lin-addr)))
                     (equal (rvm48 lin-addr x86)
                            (rb 6 lin-addr r-x x86)))
            :hints (("Goal"
                     :in-theory (e/d (rb-and-rvm48-helper
                                       rml48-guard-proof-helper)
                                     (signed-byte-p
                                       force (force)))))))

  (if (mbt (canonical-address-p lin-addr))

    (let* ((5+lin-addr (the (signed-byte #.*max-linear-address-size+1*)
                            (+ 5 (the (signed-byte #.*max-linear-address-size*)
                                      lin-addr)))))


      (if (mbe :logic (canonical-address-p 5+lin-addr)
               :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                             5+lin-addr)
                        #.*2^47*))

        (mbe :logic
             (rb 6 lin-addr r-x x86)
             :exec
             (if (app-view x86)

               (rvm48 lin-addr x86)

               (b* (((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr0) x86)
                     (la-to-pa lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+1*) 1+lin-addr)
                     (+ 1 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr1) x86)
                     (la-to-pa 1+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+2*) 2+lin-addr)
                     (+ 2 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr2) x86)
                     (la-to-pa 2+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+3*) 3+lin-addr)
                     (+ 3 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr3) x86)
                     (la-to-pa 3+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+4*) 4+lin-addr)
                     (+ 4 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr4) x86)
                     (la-to-pa 4+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+5*) 5+lin-addr)
                     (+ 5 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr5) x86)
                     (la-to-pa 5+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))

                    (byte0 (memi p-addr0 x86))
                    (byte1 (memi p-addr1 x86))
                    (byte2 (memi p-addr2 x86))
                    (byte3 (memi p-addr3 x86))
                    (byte4 (memi p-addr4 x86))
                    (byte5 (memi p-addr5 x86))

                    (word0 (the (unsigned-byte 16)
                                (logior (the (unsigned-byte 16) (ash byte1 8))
                                        byte0)))
                    (word1 (the (unsigned-byte 16)
                                (logior (the (unsigned-byte 16) (ash byte3 8))
                                        byte2)))
                    (word2 (the (unsigned-byte 16)
                                (logior (the (unsigned-byte 16) (ash byte5 8))
                                        byte4)))
                    (dword1 (the (unsigned-byte 32)
                                 (logior (the (unsigned-byte 32) (ash word2 16))
                                         word1)))
                    (value (the (unsigned-byte 48)
                                (logior (the (unsigned-byte 48) (ash dword1 16))
                                        word0))))

                   (mv nil value x86))))

        (mv 'rml48 0 x86)))

    (mv 'rml48 0 x86))

  ///

  (defthm-unsigned-byte-p n48p-mv-nth-1-rml48
                          :hyp t
                          :bound 48
                          :concl (mv-nth 1 (rml48 lin-addr r-x x86))
                          :hints (("Goal" :in-theory (e/d () (signed-byte-p))))
                          :otf-flg t
                          :gen-linear t
                          :hints-l (("Goal" :in-theory (e/d (signed-byte-p) (rb))))
                          :gen-type t)

  (defthm x86p-rml48
          (implies (force (x86p x86))
                   (x86p (mv-nth 2 (rml48 lin-addr r-x x86))))
          :hints (("Goal" :in-theory (e/d () ((force) unsigned-byte-p signed-byte-p))))
          :rule-classes (:rewrite :type-prescription))

  (defthm rml48-value-when-error
          (implies (mv-nth 0 (rml48 lin-addr r-x x86))
                   (equal (mv-nth 1 (rml48 lin-addr r-x x86))
                          0))
          :hints (("Goal" :in-theory (e/d (rml48)
                                          (force (force))))))

  (defthm rml48-x86-unmodified-in-app-view
          (implies (app-view x86)
                   (equal (mv-nth 2 (rml48 lin-addr r-x x86))
                          x86))
          :hints (("Goal" :in-theory (e/d (rml48
                                            unsigned-byte-p
                                            signed-byte-p)
                                          (force (force))))))

  (defthm xr-rml48-state-sys-view
          (implies (and (not (app-view x86))
                        (not (equal fld :mem))
                        (not (equal fld :fault))
                        (not (equal fld :tlb))
                        (member-equal fld *x86-field-names-as-keywords*))
                   (equal (xr fld index (mv-nth 2 (rml48 lin-addr r-x x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d (rml48 member-equal)
                                          (force (force))))))

  (defrule rml48-xw-app-view
           (implies (and (app-view x86)
                         (not (equal fld :mem))
                         (not (equal fld :app-view)))
                    (and (equal (mv-nth 0 (rml48 lin-addr  r-x (xw fld index value x86)))
                                (mv-nth 0 (rml48 lin-addr r-x x86)))
                         (equal (mv-nth 1 (rml48 lin-addr r-x (xw fld index value x86)))
                                (mv-nth 1 (rml48 lin-addr r-x x86)))))
           :enable (rml48)
           :disable (rb unsigned-byte-p signed-byte-p (force) force))

  (defrule rml48-xw-sys-view
           (implies
             (and (not (app-view x86))
                  (not (equal fld :fault))
                  (not (equal fld :seg-visible))
                  (not (equal fld :seg-hidden-base))
                  (not (equal fld :seg-hidden-limit))
                  (not (equal fld :seg-hidden-attr))
                  (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :msr))
                  (not (equal fld :rflags))
                  (not (equal fld :app-view))
                  (not (equal fld :marking-view))
                  (not (equal fld :tlb))
                  (not (equal fld :implicit-supervisor-access))
                  (member-equal fld *x86-field-names-as-keywords*))
             (and (equal (mv-nth 0 (rml48 lin-addr r-x (xw fld index value x86)))
                         (mv-nth 0 (rml48 lin-addr r-x x86)))
                  (equal (mv-nth 1 (rml48 lin-addr r-x (xw fld index value x86)))
                         (mv-nth 1 (rml48 lin-addr r-x x86)))
                  (equal (mv-nth 2 (rml48 lin-addr r-x (xw fld index value x86)))
                         (xw fld index value (mv-nth 2 (rml48 lin-addr r-x x86))))))
           :enable (rml48 member-equal)
           :disable (rb unsigned-byte-p signed-byte-p force (force)))

  (defrule rml48-xw-sys-view-rflags-not-ac
           (implies
             (and (not (app-view x86))
                  (equal (rflagsbits->ac value)
                         (rflagsbits->ac (rflags x86))))
             (and (equal (mv-nth 0 (rml48 lin-addr r-x (xw :rflags nil value x86)))
                         (mv-nth 0 (rml48 lin-addr r-x x86)))
                  (equal (mv-nth 1 (rml48 lin-addr r-x (xw :rflags nil value x86)))
                         (mv-nth 1 (rml48 lin-addr r-x x86)))
                  (equal (mv-nth 2 (rml48 lin-addr r-x (xw :rflags nil value x86)))
                         (xw :rflags nil value
                             (mv-nth 2 (rml48 lin-addr r-x x86))))))
           :enable (rml48)
           :disable (rb unsigned-byte-p signed-byte-p member-equal)))

(define wml48 ((lin-addr :type (signed-byte   #.*max-linear-address-size*))
               (val      :type (unsigned-byte 48))
               (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)

  :guard-hints (("Goal"
                 :expand ((las-to-pas 6 lin-addr :w x86)
                          (las-to-pas 5 (+ 1 lin-addr) :w (mv-nth 2 (ia32e-la-to-pa lin-addr :w x86))))
                 :in-theory (e/d (wb-and-wvm48)
                                 ((:rewrite acl2::ash-0)
                                  (:rewrite acl2::zip-open)
                                  (:linear bitops::logior-<-0-linear-2)
                                  (:rewrite bitops::logior-equal-0)))))

  :prepwork

  ((defthmd wb-and-wvm48
            (implies (and (app-view x86)
                          (canonical-address-p lin-addr)
                          (canonical-address-p (+ 5 lin-addr)))
                     (equal (wvm48 lin-addr val x86)
                            (wb 6 lin-addr :w val x86)))
            :hints (("Goal" :in-theory (e/d (wml08 wvm08 wvm16 wvm32 wvm48)
                                            (force (force)))))))

  (if (mbt (canonical-address-p lin-addr))

    (let* ((5+lin-addr (the (signed-byte #.*max-linear-address-size+1*)
                            (+ 5 (the (signed-byte #.*max-linear-address-size*)
                                      lin-addr)))))


      (if (mbe :logic (canonical-address-p 5+lin-addr)
               :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                             5+lin-addr)
                        #.*2^47*))

        (mbe
          :logic
          (wb 6 lin-addr :w val x86)
          :exec
          (if (app-view x86)

            (wvm48 lin-addr val x86)

            (b* (((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr0) x86)
                  (la-to-pa lin-addr :w x86))
                 ((when flag) (mv flag x86))

                 ((the (signed-byte #.*max-linear-address-size+1*) 1+lin-addr)
                  (+ 1 lin-addr))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr1) x86)
                  (la-to-pa 1+lin-addr :w x86))
                 ((when flag) (mv flag x86))

                 (2+lin-addr (the (signed-byte #.*max-linear-address-size+2*)
                                  (+ 2 (the (signed-byte #.*max-linear-address-size*)
                                            lin-addr))))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr2) x86)
                  (la-to-pa 2+lin-addr :w x86))
                 ((when flag) (mv flag x86))

                 (3+lin-addr (the (signed-byte #.*max-linear-address-size+3*)
                                  (+ 3 (the (signed-byte #.*max-linear-address-size*)
                                            lin-addr))))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr3) x86)
                  (la-to-pa 3+lin-addr :w x86))
                 ((when flag) (mv flag x86))

                 (4+lin-addr (the (signed-byte #.*max-linear-address-size+4*)
                                  (+ 4 (the (signed-byte #.*max-linear-address-size*)
                                            lin-addr))))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr4) x86)
                  (la-to-pa 4+lin-addr :w x86))
                 ((when flag) (mv flag x86))

                 (5+lin-addr (the (signed-byte #.*max-linear-address-size+5*)
                                  (+ 5 (the (signed-byte #.*max-linear-address-size*)
                                            lin-addr))))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr5) x86)
                  (la-to-pa 5+lin-addr :w x86))
                 ((when flag) (mv flag x86))

                 (byte0 (mbe
                          :logic (part-select val :low 0 :width 8)
                          :exec  (the (unsigned-byte 8) (logand #xff val))))
                 (byte1 (mbe
                          :logic (part-select val :low 8 :width 8)
                          :exec  (the (unsigned-byte 8)
                                      (logand #xff (ash val -8)))))
                 (byte2 (mbe
                          :logic (part-select val :low 16 :width 8)
                          :exec (the (unsigned-byte 8)
                                     (logand #xff (ash val -16)))))
                 (byte3 (mbe
                          :logic (part-select val :low 24 :width 8)
                          :exec (the (unsigned-byte 8)
                                     (logand #xff (ash val -24)))))
                 (byte4 (mbe
                          :logic (part-select val :low 32 :width 8)
                          :exec (the (unsigned-byte 8)
                                     (logand #xff (ash val -32)))))
                 (byte5 (mbe
                          :logic (part-select val :low 40 :width 8)
                          :exec (the (unsigned-byte 8)
                                     (logand #xff (ash val -40)))))

                 (x86 (!memi p-addr0 byte0 x86))
                 (x86 (!memi p-addr1 byte1 x86))
                 (x86 (!memi p-addr2 byte2 x86))
                 (x86 (!memi p-addr3 byte3 x86))
                 (x86 (!memi p-addr4 byte4 x86))
                 (x86 (!memi p-addr5 byte5 x86)))
                (mv nil x86))))

        (mv 'wml48 x86)))

    (mv 'wml48 x86))

  ///

  (defthm x86p-wml48
          (implies (force (x86p x86))
                   (x86p (mv-nth 1 (wml48 lin-addr val x86))))
          :hints (("Goal" :in-theory (e/d () (x86p force (force)))))
          :rule-classes (:rewrite :type-prescription)))

(define rml64 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
               (r-x    :type (member  :r :x))
               (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)
  :guard-hints
  (("Goal"
    :expand
    ((las-to-pas 8 lin-addr r-x x86)
     (las-to-pas 7 (+ 1 lin-addr) r-x (mv-nth 2 (ia32e-la-to-pa lin-addr r-x x86)))
     (las-to-pas 6 (+ 2 lin-addr) r-x
                 (mv-nth 2 (ia32e-la-to-pa (+ 1 lin-addr) r-x
                                           (mv-nth 2 (ia32e-la-to-pa lin-addr r-x x86)))))
     (las-to-pas 5 (+ 3 lin-addr) r-x
                 (mv-nth 2 (las-to-pas 6 (+ 2 lin-addr) r-x
                                       (mv-nth 2 (ia32e-la-to-pa (+ 1 lin-addr) r-x
                                                                 (mv-nth 2 (ia32e-la-to-pa lin-addr r-x x86))))))))
    :in-theory (e/d (rb-and-rvm64 rml08)
                    (not
                      (:rewrite acl2::ash-0)
                      (:rewrite acl2::zip-open)
                      (:linear bitops::logior-<-0-linear-2)
                      (:rewrite xr-and-ia32e-la-to-pa-in-non-marking-view)
                      (:rewrite bitops::logior-equal-0)))))

  :prepwork
  (
   ;; Maybe we don't need this lemma anymore?
   (local (in-theory (e/d* () (rb-and-rvm64-helper))))

   (local
     (defthmd rb-and-rvm64-helper-1
              (implies (and (app-view x86)
                            (x86p x86)
                            (canonical-address-p lin-addr)
                            (canonical-address-p (+ 7 lin-addr)))
                       (equal (rvm64 lin-addr x86)
                              (list nil
                                    (logior (mv-nth 1 (rb-1 4 lin-addr r-x x86))
                                            (ash (mv-nth 1 (rb-1 4 (+ 4 lin-addr) r-x x86))
                                                 32))
                                    x86)))
              :hints (("Goal" :use ((:instance rb-and-rvm32)
                                    (:instance rb-and-rvm32 (lin-addr (+ 4 lin-addr))))
                       :in-theory (e/d (rvm64)
                                       (force (force)))))))


   (local
     (defthmd rb-and-rvm64-helper-2
              (implies (and (app-view x86)
                            (x86p x86)
                            (canonical-address-p lin-addr)
                            (canonical-address-p (+ 7 lin-addr)))
                       (equal
                         (logior (mv-nth 1 (rb-1 4 lin-addr r-x x86))
                                 (ash (mv-nth 1 (rb-1 4 (+ 4 lin-addr) r-x x86))
                                      32))
                         (mv-nth 1 (rb-1 8 lin-addr r-x x86))))
              :hints (("Goal"
                       :use ((:instance split-rb-in-app-view
                                        (i 4)
                                        (j 4)))
                       :in-theory (e/d () (force (force)))))))

   (defthmd rb-and-rvm64
            (implies (and (app-view x86)
                          (x86p x86)
                          (canonical-address-p lin-addr)
                          (canonical-address-p (+ 7 lin-addr)))
                     (equal (rvm64 lin-addr x86)
                            (rb 8 lin-addr r-x x86)))
            :hints (("Goal"
                     :use ((:instance rb-1-in-terms-of-its-components
                                      (n 8)))
                     :in-theory (e/d (rb-and-rvm64-helper-1
                                       rb-and-rvm64-helper-2)
                                     (rb-and-rvm32-helper
                                       rml64-guard-proof-helper
                                       signed-byte-p
                                       force (force)))))))

  (if (mbt (canonical-address-p lin-addr))

    (let* ((7+lin-addr (the (signed-byte #.*max-linear-address-size+1*)
                            (+ 7 (the (signed-byte #.*max-linear-address-size*)
                                      lin-addr)))))


      (if (mbe :logic (canonical-address-p 7+lin-addr)
               :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                             7+lin-addr)
                        #.*2^47*))

        (mbe :logic
             (rb 8 lin-addr r-x x86)

             :exec
             (if (app-view x86)

               (rvm64 lin-addr x86)

               (b* (((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr0) x86)
                     (la-to-pa lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+1*) 1+lin-addr)
                     (+ 1 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr1) x86)
                     (la-to-pa 1+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+2*) 2+lin-addr)
                     (+ 2 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr2) x86)
                     (la-to-pa 2+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+3*) 3+lin-addr)
                     (+ 3 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr3) x86)
                     (la-to-pa 3+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+4*) 4+lin-addr)
                     (+ 4 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr4) x86)
                     (la-to-pa 4+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+5*) 5+lin-addr)
                     (+ 5 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr5) x86)
                     (la-to-pa 5+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+6*) 6+lin-addr)
                     (+ 6 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr6) x86)
                     (la-to-pa 6+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+7*) 7+lin-addr)
                     (+ 7 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr7) x86)
                     (la-to-pa 7+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))

                    (byte0 (memi p-addr0 x86))
                    (byte1 (memi p-addr1 x86))
                    (byte2 (memi p-addr2 x86))
                    (byte3 (memi p-addr3 x86))
                    (byte4 (memi p-addr4 x86))
                    (byte5 (memi p-addr5 x86))
                    (byte6 (memi p-addr6 x86))
                    (byte7 (memi p-addr7 x86))

                    (word0 (the (unsigned-byte 16)
                                (logior (the (unsigned-byte 16) (ash byte1 8))
                                        byte0)))
                    (word1 (the (unsigned-byte 16)
                                (logior (the (unsigned-byte 16) (ash byte3 8))
                                        byte2)))
                    (dword0 (the (unsigned-byte 32)
                                 (logior (the (unsigned-byte 32) (ash word1 16))
                                         word0)))
                    (word2 (the (unsigned-byte 16)
                                (logior (the (unsigned-byte 16) (ash byte5 8))
                                        byte4)))
                    (word3 (the (unsigned-byte 16)
                                (logior (the (unsigned-byte 16) (ash byte7 8))
                                        byte6)))
                    (dword1 (the (unsigned-byte 32)
                                 (logior (the (unsigned-byte 32) (ash word3 16))
                                         word2)))
                    (qword (the (unsigned-byte 64)
                                (logior (the (unsigned-byte 64) (ash dword1 32))
                                        dword0))))

                   (mv nil qword x86))))

        (mv 'rml64 0 x86)))

    (mv 'rml64 0 x86))

  ///

  (defthm-unsigned-byte-p n64p-mv-nth-1-rml64
                          :hyp t
                          :bound 64
                          :concl (mv-nth 1 (rml64 lin-addr r-x x86))
                          :hints (("Goal" :in-theory (e/d () (signed-byte-p))))
                          :otf-flg t
                          :gen-linear t
                          :hints-l (("Goal" :in-theory (e/d (signed-byte-p) (rb))))
                          :gen-type t)

  (defthm x86p-rml64
          (implies (force (x86p x86))
                   (x86p (mv-nth 2 (rml64 lin-addr r-x x86))))
          :hints (("Goal" :in-theory (e/d () ((force) unsigned-byte-p signed-byte-p))))
          :rule-classes (:rewrite :type-prescription))

  (defthm rml64-value-when-error
          (implies (mv-nth 0 (rml64 lin-addr r-x x86))
                   (equal (mv-nth 1 (rml64 lin-addr r-x x86))
                          0))
          :hints (("Goal" :in-theory (e/d (rml64)
                                          (force (force))))))

  (defthm rml64-x86-unmodified-in-app-view
          (implies (app-view x86)
                   (equal (mv-nth 2 (rml64 lin-addr r-x x86))
                          x86))
          :hints (("Goal" :in-theory (e/d (rml64
                                            unsigned-byte-p
                                            signed-byte-p)
                                          (force (force))))))

  (defthm xr-rml64-state-sys-view
          (implies (and (not (app-view x86))
                        (not (equal fld :mem))
                        (not (equal fld :fault))
                        (not (equal fld :tlb))
                        (member-equal fld *x86-field-names-as-keywords*))
                   (equal (xr fld index (mv-nth 2 (rml64 lin-addr r-x x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d (rml64 member-equal)
                                          (force (force))))))

  (defrule rml64-xw-app-view
           (implies (and (app-view x86)
                         (not (equal fld :mem))
                         (not (equal fld :app-view)))
                    (and (equal (mv-nth 0 (rml64 lin-addr  r-x (xw fld index value x86)))
                                (mv-nth 0 (rml64 lin-addr r-x x86)))
                         (equal (mv-nth 1 (rml64 lin-addr r-x (xw fld index value x86)))
                                (mv-nth 1 (rml64 lin-addr r-x x86)))))
           :enable (rml64)
           :disable (rb unsigned-byte-p signed-byte-p (force) force))

  (defrule rml64-xw-sys-view
           (implies
             (and (not (app-view x86))
                  (not (equal fld :fault))
                  (not (equal fld :seg-visible))
                  (not (equal fld :seg-hidden-base))
                  (not (equal fld :seg-hidden-limit))
                  (not (equal fld :seg-hidden-attr))
                  (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :msr))
                  (not (equal fld :rflags))
                  (not (equal fld :app-view))
                  (not (equal fld :marking-view))
                  (not (equal fld :tlb))
                  (not (equal fld :implicit-supervisor-access))
                  (member-equal fld *x86-field-names-as-keywords*))
             (and (equal (mv-nth 0 (rml64 lin-addr r-x (xw fld index value x86)))
                         (mv-nth 0 (rml64 lin-addr r-x x86)))
                  (equal (mv-nth 1 (rml64 lin-addr r-x (xw fld index value x86)))
                         (mv-nth 1 (rml64 lin-addr r-x x86)))
                  (equal (mv-nth 2 (rml64 lin-addr r-x (xw fld index value x86)))
                         (xw fld index value (mv-nth 2 (rml64 lin-addr r-x x86))))))
           :enable (rml64 member-equal)
           :disable (rb unsigned-byte-p signed-byte-p force (force)))

  (defrule rml64-xw-sys-view-rflags-not-ac
           (implies
             (and (not (app-view x86))
                  (equal (rflagsbits->ac value)
                         (rflagsbits->ac (rflags x86))))
             (and (equal (mv-nth 0 (rml64 lin-addr r-x (xw :rflags nil value x86)))
                         (mv-nth 0 (rml64 lin-addr r-x x86)))
                  (equal (mv-nth 1 (rml64 lin-addr r-x (xw :rflags nil value x86)))
                         (mv-nth 1 (rml64 lin-addr r-x x86)))
                  (equal (mv-nth 2 (rml64 lin-addr r-x (xw :rflags nil value x86)))
                         (xw :rflags nil value
                             (mv-nth 2 (rml64 lin-addr r-x x86))))))
           :enable (rml64)
           :disable (rb unsigned-byte-p signed-byte-p member-equal)))

(define riml64 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
                (r-x    :type (member  :r :x))
                (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)

  (mv-let (flag val x86)
          (rml64 lin-addr r-x x86)
          (mv flag (n64-to-i64 val) x86))
  ///

  (defthm-signed-byte-p i64p-mv-nth-1-riml64
                        :hyp t
                        :bound 64
                        :concl (mv-nth 1 (riml64 lin-addr r-x x86))
                        :hints (("Goal" :in-theory (e/d () (signed-byte-p))))
                        :gen-linear t
                        :hints-l (("Goal" :in-theory (e/d (signed-byte-p) ())))
                        :gen-type t)

  (defthm x86p-riml64
          (implies (force (x86p x86))
                   (x86p (mv-nth 2 (riml64 lin-addr r-x x86))))
          :rule-classes (:rewrite :type-prescription)))

(define wml64 ((lin-addr :type (signed-byte   #.*max-linear-address-size*))
               (val      :type (unsigned-byte 64))
               (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)

  :guard-hints
  (("Goal"
    :expand
    ((las-to-pas 8 lin-addr :w x86)
     (las-to-pas 7 (+ 1 lin-addr) :w (mv-nth 2 (ia32e-la-to-pa lin-addr :w x86)))
     (las-to-pas 6 (+ 2 lin-addr) :w
                 (mv-nth 2 (ia32e-la-to-pa (+ 1 lin-addr) :w
                                           (mv-nth 2 (ia32e-la-to-pa lin-addr :w x86)))))
     (las-to-pas 5 (+ 3 lin-addr) :w
                 (mv-nth 2 (las-to-pas 6 (+ 2 lin-addr) :w
                                       (mv-nth 2 (ia32e-la-to-pa (+ 1 lin-addr) :w
                                                                 (mv-nth 2 (ia32e-la-to-pa lin-addr :w x86))))))))
    :in-theory (e/d (wb-and-wvm64)
                    ((:rewrite acl2::ash-0)
                     (:rewrite acl2::zip-open)
                     (:linear bitops::logior-<-0-linear-2)
                     (:rewrite xr-and-ia32e-la-to-pa-in-non-marking-view)
                     (:rewrite bitops::logior-equal-0)))))

  :prepwork

  ((defthmd wb-and-wvm64
            (implies (and (app-view x86)
                          (canonical-address-p lin-addr)
                          (canonical-address-p (+ 7 lin-addr)))
                     (equal (wvm64 lin-addr val x86)
                            (wb 8 lin-addr :w val x86)))
            :hints (("Goal" :in-theory (e/d (wml08 wvm08 wvm32 wvm64)
                                            (force (force)))))))

  (if (mbt (canonical-address-p lin-addr))

    (let* ((7+lin-addr (the (signed-byte #.*max-linear-address-size+2*)
                            (+ 7 (the (signed-byte #.*max-linear-address-size*)
                                      lin-addr)))))


      (if (mbe :logic (canonical-address-p 7+lin-addr)
               :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                             7+lin-addr)
                        #.*2^47*))

        (mbe
          :logic
          (wb 8 lin-addr :w val x86)
          :exec
          (if (app-view x86)

            (wvm64 lin-addr val x86)

            (b* (((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr0) x86)
                  (la-to-pa lin-addr :w x86))
                 ((when flag) (mv flag x86))
                 ((the (signed-byte #.*max-linear-address-size+1*) 1+lin-addr)
                  (+ 1 lin-addr))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr1) x86)
                  (la-to-pa 1+lin-addr :w x86))
                 ((when flag) (mv flag x86))
                 ((the (signed-byte #.*max-linear-address-size+2*) 2+lin-addr)
                  (+ 2 lin-addr))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr2) x86)
                  (la-to-pa 2+lin-addr :w x86))
                 ((when flag) (mv flag x86))
                 ((the (signed-byte #.*max-linear-address-size+3*) 3+lin-addr)
                  (+ 3 lin-addr))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr3) x86)
                  (la-to-pa 3+lin-addr :w x86))
                 ((when flag) (mv flag x86))
                 ((the (signed-byte #.*max-linear-address-size+4*) 4+lin-addr)
                  (+ 4 lin-addr))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr4) x86)
                  (la-to-pa 4+lin-addr :w x86))
                 ((when flag) (mv flag x86))
                 ((the (signed-byte #.*max-linear-address-size+5*) 5+lin-addr)
                  (+ 5 lin-addr))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr5) x86)
                  (la-to-pa 5+lin-addr :w x86))
                 ((when flag) (mv flag x86))
                 ((the (signed-byte #.*max-linear-address-size+6*) 6+lin-addr)
                  (+ 6 lin-addr))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr6) x86)
                  (la-to-pa 6+lin-addr :w x86))
                 ((when flag) (mv flag x86))
                 ((the (signed-byte #.*max-linear-address-size+7*) 7+lin-addr)
                  (+ 7 lin-addr))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr7) x86)
                  (la-to-pa 7+lin-addr :w x86))
                 ((when flag) (mv flag x86))

                 (byte0 (mbe :logic (part-select val :low 0 :width 8)
                             :exec (the (unsigned-byte 8)
                                        (logand #xff val))))
                 (byte1 (mbe :logic (part-select val :low 8 :width 8)
                             :exec (the (unsigned-byte 8)
                                        (logand #xff (ash val -8)))))
                 (byte2 (mbe :logic (part-select val :low 16 :width 8)
                             :exec (the (unsigned-byte 8)
                                        (logand #xff (ash val -16)))))
                 (byte3 (mbe :logic (part-select val :low 24 :width 8)
                             :exec (the (unsigned-byte 8)
                                        (logand #xff (ash val -24)))))
                 (byte4 (mbe :logic (part-select val :low 32 :width 8)
                             :exec (the (unsigned-byte 8)
                                        (logand #xff (ash val -32)))))
                 (byte5 (mbe :logic (part-select val :low 40 :width 8)
                             :exec (the (unsigned-byte 8)
                                        (logand #xff (ash val -40)))))
                 (byte6 (mbe :logic (part-select val :low 48 :width 8)
                             :exec (the (unsigned-byte 8)
                                        (logand #xff (ash val -48)))))
                 (byte7 (mbe :logic (part-select val :low 56 :width 8)
                             :exec (the (unsigned-byte 8)
                                        (logand #xff (ash val -56)))))

                 (x86 (!memi p-addr0 byte0 x86))
                 (x86 (!memi p-addr1 byte1 x86))
                 (x86 (!memi p-addr2 byte2 x86))
                 (x86 (!memi p-addr3 byte3 x86))
                 (x86 (!memi p-addr4 byte4 x86))
                 (x86 (!memi p-addr5 byte5 x86))
                 (x86 (!memi p-addr6 byte6 x86))
                 (x86 (!memi p-addr7 byte7 x86)))

                (mv nil x86))))

        (mv 'wml64 x86)))

    (mv 'wml64 x86))

  ///

  (defthm x86p-wml64
          (implies (force (x86p x86))
                   (x86p (mv-nth 1 (wml64 lin-addr val x86))))
          :hints (("Goal" :in-theory (e/d () (x86p force (force) unsigned-byte-p signed-byte-p))))
          :rule-classes (:rewrite :type-prescription)))

(define wiml64 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
                (val      :type (signed-byte 64))
                (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)

  (wml64 lin-addr (the (unsigned-byte 64) (n64 val)) x86)
  ///
  (defthm x86p-wiml64
          (implies (force (x86p x86))
                   (x86p (mv-nth 1 (wiml64 lin-addr val x86))))
          :hints (("Goal" :in-theory (e/d () (x86p))))
          :rule-classes (:rewrite :type-prescription)))

(define rml80 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
               (r-x      :type (member  :r :x))
               (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)
  :guard-hints
  (("Goal"
    :expand
    ((las-to-pas 10 lin-addr r-x x86)
     (las-to-pas 9 (+ 1 lin-addr) r-x (mv-nth 2 (ia32e-la-to-pa lin-addr r-x x86)))
     (las-to-pas 8 (+ 2 lin-addr) r-x
                 (mv-nth 2 (ia32e-la-to-pa (+ 1 lin-addr) r-x
                                           (mv-nth 2 (ia32e-la-to-pa lin-addr r-x x86)))))
     (las-to-pas 7 (+ 3 lin-addr) r-x
                 (mv-nth 2 (ia32e-la-to-pa (+ 2 lin-addr) r-x
                                           (mv-nth 2 (ia32e-la-to-pa
                                                       (+ 1 lin-addr) r-x
                                                       (mv-nth 2 (ia32e-la-to-pa lin-addr r-x x86))))))))
    :in-theory (e/d (rb-and-rvm80
                      rml80-in-sys-view-guard-proof-helper
                      rml08)
                    (not
                      (:rewrite acl2::ash-0)
                      (:rewrite acl2::zip-open)
                      (:linear bitops::logior-<-0-linear-2)
                      (:rewrite xr-and-ia32e-la-to-pa-in-non-marking-view)
                      (:rewrite bitops::logior-equal-0)))))

  :prepwork
  ((defthmd rb-and-rvm80
            (implies (and (app-view x86)
                          (x86p x86)
                          (canonical-address-p lin-addr)
                          (canonical-address-p (+ 9 lin-addr)))
                     (equal (rvm80 lin-addr x86)
                            (rb 10 lin-addr r-x x86)))
            :hints (("Goal"

                     :in-theory (e/d (rvm80 rb-and-rvm16 rb-and-rvm64 rml80-guard-proof-helper)
                                     (force (force)))))))

  (if (mbt (canonical-address-p lin-addr))

    (let* ((9+lin-addr (the (signed-byte #.*max-linear-address-size+1*)
                            (+ 9 (the (signed-byte #.*max-linear-address-size*)
                                      lin-addr)))))

      (if (mbe :logic (canonical-address-p 9+lin-addr)
               :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                             9+lin-addr)
                        #.*2^47*))

        (mbe :logic
             (rb 10 lin-addr r-x x86)

             :exec
             (if (app-view x86)

               (rvm80 lin-addr x86)

               (b* (((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr0) x86)
                     (la-to-pa lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+1*) 1+lin-addr)
                     (+ 1 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr1) x86)
                     (la-to-pa 1+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+2*) 2+lin-addr)
                     (+ 2 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr2) x86)
                     (la-to-pa 2+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+3*) 3+lin-addr)
                     (+ 3 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr3) x86)
                     (la-to-pa 3+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+4*) 4+lin-addr)
                     (+ 4 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr4) x86)
                     (la-to-pa 4+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+5*) 5+lin-addr)
                     (+ 5 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr5) x86)
                     (la-to-pa 5+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+6*) 6+lin-addr)
                     (+ 6 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr6) x86)
                     (la-to-pa 6+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+7*) 7+lin-addr)
                     (+ 7 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr7) x86)
                     (la-to-pa 7+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+8*) 8+lin-addr)
                     (+ 8 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr8) x86)
                     (la-to-pa 8+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))
                    ((the (signed-byte #.*max-linear-address-size+9*) 9+lin-addr)
                     (+ 9 lin-addr))
                    ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr9) x86)
                     (la-to-pa 9+lin-addr r-x x86))
                    ((when flag) (mv flag 0 x86))

                    (byte0  (memi p-addr0  x86))
                    (byte1  (memi p-addr1  x86))
                    (byte2  (memi p-addr2  x86))
                    (byte3  (memi p-addr3  x86))
                    (byte4  (memi p-addr4  x86))
                    (byte5  (memi p-addr5  x86))
                    (byte6  (memi p-addr6  x86))
                    (byte7  (memi p-addr7  x86))
                    (byte8  (memi p-addr8  x86))
                    (byte9  (memi p-addr9  x86))

                    (word0 (the (unsigned-byte 16)
                                (logior (the (unsigned-byte 16) (ash byte1 8))
                                        byte0)))
                    (word1 (the (unsigned-byte 16)
                                (logior (the (unsigned-byte 16) (ash byte3 8))
                                        byte2)))
                    (word2 (the (unsigned-byte 16)
                                (logior (the (unsigned-byte 16) (ash byte5 8))
                                        byte4)))
                    (dword0 (the (unsigned-byte 32)
                                 (logior (the (unsigned-byte 32) (ash word2 16))
                                         word1)))
                    (word3 (the (unsigned-byte 16)
                                (logior (the (unsigned-byte 16) (ash byte7 8))
                                        byte6)))
                    (word4 (the (unsigned-byte 16)
                                (logior (the (unsigned-byte 16) (ash byte9 8))
                                        byte8)))
                    (dword1 (the (unsigned-byte 32)
                                 (logior (the (unsigned-byte 32) (ash word4 16))
                                         word3)))
                    (qword (the (unsigned-byte 64)
                                (logior (the (unsigned-byte 64) (ash dword1 32))
                                        dword0)))
                    (value
                      (the (unsigned-byte 80)
                           (logior (the (unsigned-byte 80) (ash qword 16))
                                   word0))))

                   (mv nil value x86))))

        (mv 'rml80 0 x86)))

    (mv 'rml80 0 x86))

  ///

  (defthm-unsigned-byte-p n80p-mv-nth-1-rml80
                          :hyp t
                          :bound 80
                          :concl (mv-nth 1 (rml80 lin-addr r-x x86))
                          :hints (("Goal" :in-theory (e/d (rb) (signed-byte-p))))
                          :otf-flg t
                          :gen-linear t
                          :hints-l (("Goal" :in-theory (e/d (signed-byte-p) (rb))))
                          :gen-type t)

  (defthm x86p-rml80
          (implies (force (x86p x86))
                   (x86p (mv-nth 2 (rml80 lin-addr r-x x86))))
          :hints (("Goal" :in-theory (e/d () (rb unsigned-byte-p signed-byte-p (force)))))
          :rule-classes (:rewrite :type-prescription))

  (defthm rml80-value-when-error
          (implies (mv-nth 0 (rml80 lin-addr r-x x86))
                   (equal (mv-nth 1 (rml80 lin-addr r-x x86))
                          0))
          :hints (("Goal" :in-theory (e/d (rml80)
                                          (force (force))))))

  (defthm rml80-x86-unmodified-in-app-view
          (implies (app-view x86)
                   (equal (mv-nth 2 (rml80 lin-addr r-x x86))
                          x86))
          :hints (("Goal" :in-theory (e/d (rml80
                                            unsigned-byte-p
                                            signed-byte-p)
                                          (force (force))))))

  (defthm xr-rml80-state-sys-view
          (implies (and (not (app-view x86))
                        (not (equal fld :mem))
                        (not (equal fld :fault))
                        (not (equal fld :tlb))
                        (member-equal fld *x86-field-names-as-keywords*))
                   (equal (xr fld index (mv-nth 2 (rml80 lin-addr r-x x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d (rml80 member-equal)
                                          (force (force))))))

  (defrule rml80-xw-app-view
           (implies (and (app-view x86)
                         (not (equal fld :mem))
                         (not (equal fld :app-view)))
                    (and (equal (mv-nth 0 (rml80 lin-addr  r-x (xw fld index value x86)))
                                (mv-nth 0 (rml80 lin-addr r-x x86)))
                         (equal (mv-nth 1 (rml80 lin-addr r-x (xw fld index value x86)))
                                (mv-nth 1 (rml80 lin-addr r-x x86)))))
           :enable (rml80)
           :disable (rb unsigned-byte-p signed-byte-p (force) force))

  (defrule rml80-xw-sys-view
           (implies
             (and (not (app-view x86))
                  (not (equal fld :fault))
                  (not (equal fld :seg-visible))
                  (not (equal fld :seg-hidden-base))
                  (not (equal fld :seg-hidden-limit))
                  (not (equal fld :seg-hidden-attr))
                  (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :msr))
                  (not (equal fld :rflags))
                  (not (equal fld :app-view))
                  (not (equal fld :marking-view))
                  (not (equal fld :tlb))
                  (not (equal fld :implicit-supervisor-access))
                  (member-equal fld *x86-field-names-as-keywords*))
             (and (equal (mv-nth 0 (rml80 lin-addr r-x (xw fld index value x86)))
                         (mv-nth 0 (rml80 lin-addr r-x x86)))
                  (equal (mv-nth 1 (rml80 lin-addr r-x (xw fld index value x86)))
                         (mv-nth 1 (rml80 lin-addr r-x x86)))
                  (equal (mv-nth 2 (rml80 lin-addr r-x (xw fld index value x86)))
                         (xw fld index value (mv-nth 2 (rml80 lin-addr r-x x86))))))
           :enable (rml80 member-equal)
           :disable (rb unsigned-byte-p signed-byte-p force (force)))

  (defrule rml80-xw-sys-view-rflags-not-ac
           (implies
             (and (not (app-view x86))
                  (equal (rflagsbits->ac value)
                         (rflagsbits->ac (rflags x86))))
             (and (equal (mv-nth 0 (rml80 lin-addr r-x (xw :rflags nil value x86)))
                         (mv-nth 0 (rml80 lin-addr r-x x86)))
                  (equal (mv-nth 1 (rml80 lin-addr r-x (xw :rflags nil value x86)))
                         (mv-nth 1 (rml80 lin-addr r-x x86)))
                  (equal (mv-nth 2 (rml80 lin-addr r-x (xw :rflags nil value x86)))
                         (xw :rflags nil value
                             (mv-nth 2 (rml80 lin-addr r-x x86))))))
           :enable (rml80)
           :disable (rb unsigned-byte-p signed-byte-p member-equal)))

(define wml80 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
               (val      :type (unsigned-byte 80))
               (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)
  :guard-hints
  (("Goal"
    :expand
    ((las-to-pas 10 lin-addr :w x86)
     (las-to-pas 9 (+ 1 lin-addr) :w (mv-nth 2 (ia32e-la-to-pa lin-addr :w x86)))
     (las-to-pas 8 (+ 2 lin-addr) :w
                 (mv-nth 2 (ia32e-la-to-pa (+ 1 lin-addr) :w
                                           (mv-nth 2 (ia32e-la-to-pa lin-addr :w x86)))))
     (las-to-pas 7 (+ 3 lin-addr) :w
                 (mv-nth 2 (ia32e-la-to-pa (+ 2 lin-addr) :w
                                           (mv-nth 2 (ia32e-la-to-pa
                                                       (+ 1 lin-addr) :w
                                                       (mv-nth 2 (ia32e-la-to-pa lin-addr :w x86))))))))
    :in-theory (e/d (wb-and-wvm80)
                    ((:rewrite acl2::ash-0)
                     (:rewrite acl2::zip-open)
                     (:linear bitops::logior-<-0-linear-2)
                     (:rewrite xr-and-ia32e-la-to-pa-in-non-marking-view)
                     (:rewrite bitops::logior-equal-0)))))

  :prepwork

  ((defthmd wb-and-wvm80
            (implies (and (app-view x86)
                          (canonical-address-p lin-addr)
                          (canonical-address-p (+ 9 lin-addr)))
                     (equal (wvm80 lin-addr val x86)
                            (wb 10 lin-addr :w val x86)))
            :hints (("Goal" :in-theory (e/d (wml08 wvm08 wvm16 wvm32 wvm64 wvm80)
                                            (force (force)))))))

  (if (mbt (canonical-address-p lin-addr))

    (let* ((9+lin-addr (the (signed-byte #.*max-linear-address-size+1*)
                            (+ 9 (the (signed-byte #.*max-linear-address-size*)
                                      lin-addr)))))


      (if (mbe :logic (canonical-address-p 9+lin-addr)
               :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                             9+lin-addr)
                        #.*2^47*))

        (mbe
          :logic
          (wb 10 lin-addr :w val x86)

          :exec
          (if (app-view x86)

            (wvm80 lin-addr val x86)

            (b* (((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr0) x86)
                  (la-to-pa lin-addr :w x86))
                 ((when flag) (mv flag x86))
                 ((the (signed-byte #.*max-linear-address-size+1*) 1+lin-addr)
                  (+ 1 lin-addr))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr1) x86)
                  (la-to-pa 1+lin-addr :w x86))
                 ((when flag) (mv flag x86))
                 ((the (signed-byte #.*max-linear-address-size+2*) 2+lin-addr)
                  (+ 2 lin-addr))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr2) x86)
                  (la-to-pa 2+lin-addr :w x86))
                 ((when flag) (mv flag x86))
                 ((the (signed-byte #.*max-linear-address-size+3*) 3+lin-addr)
                  (+ 3 lin-addr))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr3) x86)
                  (la-to-pa 3+lin-addr :w x86))
                 ((when flag) (mv flag x86))
                 ((the (signed-byte #.*max-linear-address-size+4*) 4+lin-addr)
                  (+ 4 lin-addr))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr4) x86)
                  (la-to-pa 4+lin-addr :w x86))
                 ((when flag) (mv flag x86))
                 ((the (signed-byte #.*max-linear-address-size+5*) 5+lin-addr)
                  (+ 5 lin-addr))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr5) x86)
                  (la-to-pa 5+lin-addr :w x86))
                 ((when flag) (mv flag x86))
                 ((the (signed-byte #.*max-linear-address-size+6*) 6+lin-addr)
                  (+ 6 lin-addr))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr6) x86)
                  (la-to-pa 6+lin-addr :w x86))
                 ((when flag) (mv flag x86))
                 ((the (signed-byte #.*max-linear-address-size+7*) 7+lin-addr)
                  (+ 7 lin-addr))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr7) x86)
                  (la-to-pa 7+lin-addr :w x86))
                 ((when flag) (mv flag x86))
                 ((the (signed-byte #.*max-linear-address-size+8*) 8+lin-addr)
                  (+ 8 lin-addr))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr8) x86)
                  (la-to-pa 8+lin-addr :w x86))
                 ((when flag) (mv flag x86))
                 ((the (signed-byte #.*max-linear-address-size+9*) 9+lin-addr)
                  (+ 9 lin-addr))
                 ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr9) x86)
                  (la-to-pa 9+lin-addr :w x86))
                 ((when flag) (mv flag x86))

                 (byte0 (mbe :logic (part-select val :low 0 :width 8)
                             :exec (the (unsigned-byte 8)
                                        (logand #xff val))))
                 (byte1 (mbe :logic (part-select val :low 8 :width 8)
                             :exec (the (unsigned-byte 8)
                                        (logand #xff (ash val -8)))))
                 (byte2 (mbe :logic (part-select val :low 16 :width 8)
                             :exec (the (unsigned-byte 8)
                                        (logand #xff (ash val -16)))))
                 (byte3 (mbe :logic (part-select val :low 24 :width 8)
                             :exec (the (unsigned-byte 8)
                                        (logand #xff (ash val -24)))))
                 (byte4 (mbe :logic (part-select val :low 32 :width 8)
                             :exec (the (unsigned-byte 8)
                                        (logand #xff (ash val -32)))))
                 (byte5 (mbe :logic (part-select val :low 40 :width 8)
                             :exec (the (unsigned-byte 8)
                                        (logand #xff (ash val -40)))))
                 (byte6 (mbe :logic (part-select val :low 48 :width 8)
                             :exec (the (unsigned-byte 8)
                                        (logand #xff (ash val -48)))))
                 (byte7 (mbe :logic (part-select val :low 56 :width 8)
                             :exec (the (unsigned-byte 8)
                                        (logand #xff (ash val -56)))))
                 (byte8 (mbe :logic (part-select val :low 64 :width 8)
                             :exec (the (unsigned-byte 8)
                                        (logand #xff (ash val -64)))))
                 (byte9 (mbe :logic (part-select val :low 72 :width 8)
                             :exec (the (unsigned-byte 8)
                                        (logand #xff (ash val -72)))))

                 (x86 (!memi p-addr0 byte0 x86))
                 (x86 (!memi p-addr1 byte1 x86))
                 (x86 (!memi p-addr2 byte2 x86))
                 (x86 (!memi p-addr3 byte3 x86))
                 (x86 (!memi p-addr4 byte4 x86))
                 (x86 (!memi p-addr5 byte5 x86))
                 (x86 (!memi p-addr6 byte6 x86))
                 (x86 (!memi p-addr7 byte7 x86))
                 (x86 (!memi p-addr8 byte8 x86))
                 (x86 (!memi p-addr9 byte9 x86)))

                (mv nil x86))))

        (mv 'wml80 x86)))

    (mv 'wml80 x86))

  ///

  (defthm x86p-wml80
          (implies (force (x86p x86))
                   (x86p (mv-nth 1 (wml80 lin-addr val x86))))
          :hints (("Goal" :in-theory (e/d () (x86p rb force (force) unsigned-byte-p signed-byte-p))))
          :rule-classes (:rewrite :type-prescription)))

; Thanks to Dmitry Nadezhin for proving the equivalence of rm/wml128
; to rb/wb.

;; TODO: Prove rml128 equivalent to rb in the system-level view. (again)
(define rml128 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
                (r-x      :type (member :r :x))
                (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)
  :guard-hints (("Goal"
                 :in-theory (e/d (rb-and-rvm128
                                   rml08 rml64
                                   rb-and-rvm128-helper-1
                                   rb-and-rvm128-helper-2)
                                 (not
                                   (:rewrite acl2::ash-0)
                                   (:rewrite acl2::zip-open)
                                   (:linear bitops::logior-<-0-linear-2)
                                   (:rewrite xr-and-ia32e-la-to-pa-in-non-marking-view)
                                   (:rewrite bitops::logior-equal-0)))))

  :prepwork
  ((local
     (defthmd rb-and-rvm128-helper-1
              (implies
                (and (app-view x86)
                     (x86p x86)
                     (canonical-address-p lin-addr)
                     (canonical-address-p (+ 15 lin-addr)))
                (equal (rvm128 lin-addr x86)
                       (list
                         nil
                         (logior (mv-nth 1 (rb-1 8 lin-addr r-x x86))
                                 (ash (mv-nth 1 (rb-1 8 (+ 8 lin-addr) r-x x86))
                                      64))
                         x86)))
              :hints (("Goal" :in-theory (e/d (rvm128 rb-and-rvm64)
                                              (force (force)))))))

   (local
     (defthmd rb-and-rvm128-helper-2
              (implies
                (and (app-view x86)
                     (x86p x86)
                     (canonical-address-p lin-addr)
                     (canonical-address-p (+ 15 lin-addr)))
                (equal
                  (logior (mv-nth 1 (rb-1 8 lin-addr r-x x86))
                          (ash (mv-nth 1 (rb-1 8 (+ 8 lin-addr) r-x x86)) 64))
                  (mv-nth 1 (rb-1 16 lin-addr r-x x86))))
              :hints (("Goal"
                       :in-theory (e/d () (force (force)))
                       :use
                       ((:instance split-rb-in-app-view
                                   (i 8) (j 8)))))))

   (defthmd rb-and-rvm128
            (implies (and (app-view x86)
                          (x86p x86)
                          (canonical-address-p lin-addr)
                          (canonical-address-p (+ 15 lin-addr)))
                     (equal (rvm128 lin-addr x86)
                            (rb 16 lin-addr r-x x86)))
            :hints (("Goal"
                     :use ((:instance rb-1-in-terms-of-its-components
                                      (n 16)))
                     :in-theory (e/d (rb-and-rvm128-helper-1
                                       rb-and-rvm128-helper-2)
                                     (force (force))))))

   (defthm-unsigned-byte-p unsigned-byte-p-128-of-merge-16-u8s-linear
                           :hyp (and (unsigned-byte-p 8 h7)
                                     (unsigned-byte-p 8 h6)
                                     (unsigned-byte-p 8 h5)
                                     (unsigned-byte-p 8 h4)
                                     (unsigned-byte-p 8 h3)
                                     (unsigned-byte-p 8 h2)
                                     (unsigned-byte-p 8 h1)
                                     (unsigned-byte-p 8 h0)
                                     (unsigned-byte-p 8 l7)
                                     (unsigned-byte-p 8 l6)
                                     (unsigned-byte-p 8 l5)
                                     (unsigned-byte-p 8 l4)
                                     (unsigned-byte-p 8 l3)
                                     (unsigned-byte-p 8 l2)
                                     (unsigned-byte-p 8 l1)
                                     (unsigned-byte-p 8 l0))
                           :bound 128
                           :concl (bitops::merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0 l7 l6 l5 l4 l3 l2 l1 l0)
                           :hints (("Goal" :in-theory (e/d* () (unsigned-byte-p))))
                           :hints-l (("Goal"
                                      :in-theory
                                      (e/d* (unsigned-byte-p) (bitops::unsigned-byte-p-128-of-merge-16-u8s))
                                      :use ((:instance bitops::unsigned-byte-p-128-of-merge-16-u8s))))
                           :gen-linear t))


  (if (mbt (canonical-address-p lin-addr))

    (let* ((15+lin-addr (the (signed-byte #.*max-linear-address-size+1*)
                             (+ 15 (the (signed-byte #.*max-linear-address-size*)
                                        lin-addr)))))


      (if (mbe :logic (canonical-address-p 15+lin-addr)
               :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                             15+lin-addr)
                        #.*2^47*))

        (if (app-view x86)
          (mbe :logic (rb 16 lin-addr r-x x86)
               :exec (rvm128 lin-addr x86))

          (b* (((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr0) x86)
                (la-to-pa lin-addr r-x x86))
               ((when flag) (mv flag 0 x86))
               ((the (signed-byte #.*max-linear-address-size+1*) 1+lin-addr)
                (+ 1 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr1) x86)
                (la-to-pa 1+lin-addr r-x x86))
               ((when flag) (mv flag 0 x86))
               ((the (signed-byte #.*max-linear-address-size+2*) 2+lin-addr)
                (+ 2 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr2) x86)
                (la-to-pa 2+lin-addr r-x x86))
               ((when flag) (mv flag 0 x86))
               ((the (signed-byte #.*max-linear-address-size+3*) 3+lin-addr)
                (+ 3 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr3) x86)
                (la-to-pa 3+lin-addr r-x x86))
               ((when flag) (mv flag 0 x86))
               ((the (signed-byte #.*max-linear-address-size+4*) 4+lin-addr)
                (+ 4 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr4) x86)
                (la-to-pa 4+lin-addr r-x x86))
               ((when flag) (mv flag 0 x86))
               ((the (signed-byte #.*max-linear-address-size+5*) 5+lin-addr)
                (+ 5 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr5) x86)
                (la-to-pa 5+lin-addr r-x x86))
               ((when flag) (mv flag 0 x86))
               ((the (signed-byte #.*max-linear-address-size+6*) 6+lin-addr)
                (+ 6 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr6) x86)
                (la-to-pa 6+lin-addr r-x x86))
               ((when flag) (mv flag 0 x86))
               ((the (signed-byte #.*max-linear-address-size+7*) 7+lin-addr)
                (+ 7 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr7) x86)
                (la-to-pa 7+lin-addr r-x x86))
               ((when flag) (mv flag 0 x86))
               ((the (signed-byte #.*max-linear-address-size+8*) 8+lin-addr)
                (+ 8 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr8) x86)
                (la-to-pa 8+lin-addr r-x x86))
               ((when flag) (mv flag 0 x86))
               ((the (signed-byte #.*max-linear-address-size+9*) 9+lin-addr)
                (+ 9 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr9) x86)
                (la-to-pa 9+lin-addr r-x x86))
               ((when flag) (mv flag 0 x86))
               ((the (signed-byte #.*max-linear-address-size+10*) 10+lin-addr)
                (+ 10 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr10) x86)
                (la-to-pa 10+lin-addr r-x x86))
               ((when flag) (mv flag 0 x86))
               ((the (signed-byte #.*max-linear-address-size+11*) 11+lin-addr)
                (+ 11 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr11) x86)
                (la-to-pa 11+lin-addr r-x x86))
               ((when flag) (mv flag 0 x86))
               ((the (signed-byte #.*max-linear-address-size+12*) 12+lin-addr)
                (+ 12 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr12) x86)
                (la-to-pa 12+lin-addr r-x x86))
               ((when flag) (mv flag 0 x86))
               ((the (signed-byte #.*max-linear-address-size+13*) 13+lin-addr)
                (+ 13 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr13) x86)
                (la-to-pa 13+lin-addr r-x x86))
               ((when flag) (mv flag 0 x86))
               ((the (signed-byte #.*max-linear-address-size+14*) 14+lin-addr)
                (+ 14 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr14) x86)
                (la-to-pa 14+lin-addr r-x x86))
               ((when flag) (mv flag 0 x86))
               ((the (signed-byte #.*max-linear-address-size+15*) 15+lin-addr)
                (+ 15 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr15) x86)
                (la-to-pa 15+lin-addr r-x x86))
               ((when flag) (mv flag 0 x86))

               (byte0  (memi p-addr0  x86))
               (byte1  (memi p-addr1  x86))
               (byte2  (memi p-addr2  x86))
               (byte3  (memi p-addr3  x86))
               (byte4  (memi p-addr4  x86))
               (byte5  (memi p-addr5  x86))
               (byte6  (memi p-addr6  x86))
               (byte7  (memi p-addr7  x86))
               (byte8  (memi p-addr8  x86))
               (byte9  (memi p-addr9  x86))
               (byte10 (memi p-addr10 x86))
               (byte11 (memi p-addr11 x86))
               (byte12 (memi p-addr12 x86))
               (byte13 (memi p-addr13 x86))
               (byte14 (memi p-addr14 x86))
               (byte15 (memi p-addr15 x86))

               (oword
                 (the (unsigned-byte 128)
                      (bitops::merge-16-u8s
                        byte15 byte14 byte13 byte12
                        byte11 byte10 byte9  byte8
                        byte7  byte6  byte5  byte4
                        byte3  byte2  byte1  byte0))))

              (mv nil oword x86)))

        (mv 'rml128 0 x86)))

    (mv 'rml128 0 x86))

  ///

  (defthm-unsigned-byte-p n128p-mv-nth-1-rml128
                          :hyp t
                          :bound 128
                          :concl (mv-nth 1 (rml128 lin-addr r-x x86))
                          :hints (("Goal" :in-theory (e/d () (force (force) signed-byte-p))))
                          :gen-linear t
                          :hints-l (("Goal" :in-theory (e/d (signed-byte-p) (rb))))
                          :gen-type t)

  (defthm x86p-rml128
          (implies (force (x86p x86))
                   (x86p (mv-nth 2 (rml128 lin-addr r-x x86))))
          :hints (("Goal" :in-theory (e/d () ((force) unsigned-byte-p signed-byte-p))))
          :rule-classes (:rewrite :type-prescription))

  (defthm rml128-value-when-error
          (implies (mv-nth 0 (rml128 lin-addr r-x x86))
                   (equal (mv-nth 1 (rml128 lin-addr r-x x86))
                          0))
          :hints (("Goal" :in-theory (e/d (rml128)
                                          (force (force))))))

  (defthm rml128-x86-unmodified-in-app-view
          (implies (app-view x86)
                   (equal (mv-nth 2 (rml128 lin-addr r-x x86))
                          x86))
          :hints (("Goal" :in-theory (e/d (rml128
                                            unsigned-byte-p
                                            signed-byte-p)
                                          (force (force))))))

  (defthm xr-rml128-state-sys-view
          (implies (and (not (app-view x86))
                        (not (equal fld :mem))
                        (not (equal fld :fault))
                        (not (equal fld :tlb))
                        (member-equal fld *x86-field-names-as-keywords*))
                   (equal (xr fld index (mv-nth 2 (rml128 lin-addr r-x x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d (rml128)
                                          (force (force))))))

  (defrule rml128-xw-app-view
           (implies (and (app-view x86)
                         (not (equal fld :mem))
                         (not (equal fld :app-view)))
                    (and (equal (mv-nth 0 (rml128 lin-addr  r-x (xw fld index value x86)))
                                (mv-nth 0 (rml128 lin-addr r-x x86)))
                         (equal (mv-nth 1 (rml128 lin-addr r-x (xw fld index value x86)))
                                (mv-nth 1 (rml128 lin-addr r-x x86)))))
           :enable (rml128)
           :disable (rb unsigned-byte-p signed-byte-p (force) force))

  (defrule rml128-xw-sys-view
           (implies
             (and (not (app-view x86))
                  (not (equal fld :fault))
                  (not (equal fld :seg-visible))
                  (not (equal fld :seg-hidden-base))
                  (not (equal fld :seg-hidden-limit))
                  (not (equal fld :seg-hidden-attr))
                  (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :msr))
                  (not (equal fld :rflags))
                  (not (equal fld :app-view))
                  (not (equal fld :marking-view))
                  (not (equal fld :tlb))
                  (not (equal fld :implicit-supervisor-access))
                  (member-equal fld *x86-field-names-as-keywords*))
             (and (equal (mv-nth 0 (rml128 lin-addr r-x (xw fld index value x86)))
                         (mv-nth 0 (rml128 lin-addr r-x x86)))
                  (equal (mv-nth 1 (rml128 lin-addr r-x (xw fld index value x86)))
                         (mv-nth 1 (rml128 lin-addr r-x x86)))
                  (equal (mv-nth 2 (rml128 lin-addr r-x (xw fld index value x86)))
                         (xw fld index value (mv-nth 2 (rml128 lin-addr r-x x86))))))
           :enable (rml128)
           :disable (rb unsigned-byte-p signed-byte-p force (force)))

  (defrule rml128-xw-sys-view-rflags-not-ac
           (implies
             (and (not (app-view x86))
                  (equal (rflagsbits->ac value)
                         (rflagsbits->ac (rflags x86))))
             (and (equal (mv-nth 0 (rml128 lin-addr r-x (xw :rflags nil value x86)))
                         (mv-nth 0 (rml128 lin-addr r-x x86)))
                  (equal (mv-nth 1 (rml128 lin-addr r-x (xw :rflags nil value x86)))
                         (mv-nth 1 (rml128 lin-addr r-x x86)))
                  (equal (mv-nth 2 (rml128 lin-addr r-x (xw :rflags nil value x86)))
                         (xw :rflags nil value
                             (mv-nth 2 (rml128 lin-addr r-x x86))))))
           :enable (rml128)
           :disable (rb unsigned-byte-p signed-byte-p member-equal)))

;; TODO: Prove wml128 equivalent to rb in the system-level view (again).
(define wml128 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
                (val      :type (unsigned-byte 128))
                (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)

  :guard-hints
  (("Goal" :in-theory (e/d (wb-and-wvm128)
                           (wvm128
                             not
                             (:rewrite acl2::ash-0)
                             (:rewrite acl2::zip-open)
                             (:linear bitops::logior-<-0-linear-2)
                             (:rewrite xr-and-ia32e-la-to-pa-in-non-marking-view)
                             (:rewrite bitops::logior-equal-0)))))

  :prepwork
  ((defthmd wb-and-wvm128
            (implies (and (app-view x86)
                          (canonical-address-p lin-addr)
                          (canonical-address-p (+ 15 lin-addr)))
                     (equal (wvm128 lin-addr val x86)
                            (wb 16 lin-addr :w val x86)))
            :hints (("Goal" :in-theory (e/d (wml08 wvm08 wvm32 wvm64 wvm128)
                                            (force (force)))))))

  (if (mbt (canonical-address-p lin-addr))

    (let* ((15+lin-addr (the (signed-byte #.*max-linear-address-size+1*)
                             (+ 15 (the (signed-byte #.*max-linear-address-size*)
                                        lin-addr)))))


      (if (mbe :logic (canonical-address-p 15+lin-addr)
               :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                             15+lin-addr)
                        #.*2^47*))

        (if (app-view x86)

          (mbe :logic (wb 16 lin-addr :w val x86)
               :exec (wvm128 lin-addr val x86))

          (b* (((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr0) x86)
                (la-to-pa lin-addr :w x86))
               ((when flag) (mv flag x86))
               ((the (signed-byte #.*max-linear-address-size+1*) 1+lin-addr)
                (+ 1 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr1) x86)
                (la-to-pa 1+lin-addr :w x86))
               ((when flag) (mv flag x86))
               ((the (signed-byte #.*max-linear-address-size+2*) 2+lin-addr)
                (+ 2 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr2) x86)
                (la-to-pa 2+lin-addr :w x86))
               ((when flag) (mv flag x86))
               ((the (signed-byte #.*max-linear-address-size+3*) 3+lin-addr)
                (+ 3 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr3) x86)
                (la-to-pa 3+lin-addr :w x86))
               ((when flag) (mv flag x86))
               ((the (signed-byte #.*max-linear-address-size+4*) 4+lin-addr)
                (+ 4 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr4) x86)
                (la-to-pa 4+lin-addr :w x86))
               ((when flag) (mv flag x86))
               ((the (signed-byte #.*max-linear-address-size+5*) 5+lin-addr)
                (+ 5 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr5) x86)
                (la-to-pa 5+lin-addr :w x86))
               ((when flag) (mv flag x86))
               ((the (signed-byte #.*max-linear-address-size+6*) 6+lin-addr)
                (+ 6 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr6) x86)
                (la-to-pa 6+lin-addr :w x86))
               ((when flag) (mv flag x86))
               ((the (signed-byte #.*max-linear-address-size+7*) 7+lin-addr)
                (+ 7 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr7) x86)
                (la-to-pa 7+lin-addr :w x86))
               ((when flag) (mv flag x86))
               ((the (signed-byte #.*max-linear-address-size+8*) 8+lin-addr)
                (+ 8 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr8) x86)
                (la-to-pa 8+lin-addr :w x86))
               ((when flag) (mv flag x86))
               ((the (signed-byte #.*max-linear-address-size+9*) 9+lin-addr)
                (+ 9 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr9) x86)
                (la-to-pa 9+lin-addr :w x86))
               ((when flag) (mv flag x86))
               ((the (signed-byte #.*max-linear-address-size+10*) 10+lin-addr)
                (+ 10 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr10) x86)
                (la-to-pa 10+lin-addr :w x86))
               ((when flag) (mv flag x86))
               ((the (signed-byte #.*max-linear-address-size+11*) 11+lin-addr)
                (+ 11 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr11) x86)
                (la-to-pa 11+lin-addr :w x86))
               ((when flag) (mv flag x86))
               ((the (signed-byte #.*max-linear-address-size+12*) 12+lin-addr)
                (+ 12 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr12) x86)
                (la-to-pa 12+lin-addr :w x86))
               ((when flag) (mv flag x86))
               ((the (signed-byte #.*max-linear-address-size+13*) 13+lin-addr)
                (+ 13 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr13) x86)
                (la-to-pa 13+lin-addr :w x86))
               ((when flag) (mv flag x86))
               ((the (signed-byte #.*max-linear-address-size+14*) 14+lin-addr)
                (+ 14 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr14) x86)
                (la-to-pa 14+lin-addr :w x86))
               ((when flag) (mv flag x86))
               ((the (signed-byte #.*max-linear-address-size+15*) 15+lin-addr)
                (+ 15 lin-addr))
               ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr15) x86)
                (la-to-pa 15+lin-addr :w x86))
               ((when flag) (mv flag x86))

               (byte0 (mbe :logic (part-select val :low 0 :width 8)
                           :exec (the (unsigned-byte 8)
                                      (logand #xff val))))
               (byte1 (mbe :logic (part-select val :low 8 :width 8)
                           :exec (the (unsigned-byte 8)
                                      (logand #xff (ash val -8)))))
               (byte2 (mbe :logic (part-select val :low 16 :width 8)
                           :exec (the (unsigned-byte 8)
                                      (logand #xff (ash val -16)))))
               (byte3 (mbe :logic (part-select val :low 24 :width 8)
                           :exec (the (unsigned-byte 8)
                                      (logand #xff (ash val -24)))))
               (byte4 (mbe :logic (part-select val :low 32 :width 8)
                           :exec (the (unsigned-byte 8)
                                      (logand #xff (ash val -32)))))
               (byte5 (mbe :logic (part-select val :low 40 :width 8)
                           :exec (the (unsigned-byte 8)
                                      (logand #xff (ash val -40)))))
               (byte6 (mbe :logic (part-select val :low 48 :width 8)
                           :exec (the (unsigned-byte 8)
                                      (logand #xff (ash val -48)))))
               (byte7 (mbe :logic (part-select val :low 56 :width 8)
                           :exec (the (unsigned-byte 8)
                                      (logand #xff (ash val -56)))))
               (byte8 (mbe :logic (part-select val :low 64 :width 8)
                           :exec (the (unsigned-byte 8)
                                      (logand #xff (ash val -64)))))
               (byte9 (mbe :logic (part-select val :low 72 :width 8)
                           :exec (the (unsigned-byte 8)
                                      (logand #xff (ash val -72)))))
               (byte10 (mbe :logic (part-select val :low 80 :width 8)
                            :exec (the (unsigned-byte 8)
                                       (logand #xff (ash val -80)))))
               (byte11 (mbe :logic (part-select val :low 88 :width 8)
                            :exec (the (unsigned-byte 8)
                                       (logand #xff (ash val -88)))))
               (byte12 (mbe :logic (part-select val :low 96 :width 8)
                            :exec (the (unsigned-byte 8)
                                       (logand #xff (ash val -96)))))
               (byte13 (mbe :logic (part-select val :low 104 :width 8)
                            :exec (the (unsigned-byte 8)
                                       (logand #xff (ash val -104)))))
               (byte14 (mbe :logic (part-select val :low 112 :width 8)
                            :exec (the (unsigned-byte 8)
                                       (logand #xff (ash val -112)))))
               (byte15 (mbe :logic (part-select val :low 120 :width 8)
                            :exec (the (unsigned-byte 8)
                                       (logand #xff (ash val -120)))))

               (x86 (!memi p-addr0 byte0 x86))
               (x86 (!memi p-addr1 byte1 x86))
               (x86 (!memi p-addr2 byte2 x86))
               (x86 (!memi p-addr3 byte3 x86))
               (x86 (!memi p-addr4 byte4 x86))
               (x86 (!memi p-addr5 byte5 x86))
               (x86 (!memi p-addr6 byte6 x86))
               (x86 (!memi p-addr7 byte7 x86))
               (x86 (!memi p-addr8 byte8 x86))
               (x86 (!memi p-addr9 byte9 x86))
               (x86 (!memi p-addr10 byte10 x86))
               (x86 (!memi p-addr11 byte11 x86))
               (x86 (!memi p-addr12 byte12 x86))
               (x86 (!memi p-addr13 byte13 x86))
               (x86 (!memi p-addr14 byte14 x86))
               (x86 (!memi p-addr15 byte15 x86)))

              (mv nil x86)))


        (mv 'wml128 x86)))

    (mv 'wml128 x86))

  ///

  (defthm x86p-wml128
          (implies (force (x86p x86))
                   (x86p (mv-nth 1 (wml128 lin-addr val x86))))
          :hints (("Goal" :in-theory (e/d () (rb x86p force (force) unsigned-byte-p signed-byte-p))))
          :rule-classes (:rewrite :type-prescription)))

;; TODO: Prove rml256 equivalent to rb in the system-level view. (again)
(define rml256 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
                (r-x      :type (member :r :x))
                (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)
  :guard-hints (("Goal"
                 :in-theory (e/d (rb-and-rvm256
                                  rml08 rml128
                                  rb-and-rvm256-helper-1
                                  rb-and-rvm256-helper-2)
                                 (not
                                  (:rewrite acl2::ash-0)
                                  (:rewrite acl2::zip-open)
                                  (:linear bitops::logior-<-0-linear-2)
                                  (:rewrite xr-and-ia32e-la-to-pa-in-non-marking-view)
                                  (:rewrite bitops::logior-equal-0)))))

  :prepwork
  ((local
    (defthmd rb-and-rvm256-helper-1
      (implies
       (and (app-view x86)
            (x86p x86)
            (canonical-address-p lin-addr)
            (canonical-address-p (+ 31 lin-addr)))
       (equal (rvm256 lin-addr x86)
              (list
               nil
               (logior (mv-nth 1 (rb-1 16 lin-addr r-x x86))
                       (ash (mv-nth 1 (rb-1 16 (+ 16 lin-addr) r-x x86))
                            128))
               x86)))
      :hints (("Goal" :in-theory (e/d (rvm256 rb-and-rvm128)
                                      (force (force)))))))

   (local
    (defthmd rb-and-rvm256-helper-2
      (implies
       (and (app-view x86)
            (x86p x86)
            (canonical-address-p lin-addr)
            (canonical-address-p (+ 31 lin-addr)))
       (equal
        (logior (mv-nth 1 (rb-1 16 lin-addr r-x x86))
                (ash (mv-nth 1 (rb-1 16 (+ 16 lin-addr) r-x x86)) 128))
        (mv-nth 1 (rb-1 32 lin-addr r-x x86))))
      :hints (("Goal"
               :in-theory (e/d () (force (force)))
               :use
               ((:instance split-rb-in-app-view
                           (i 16) (j 16)))))))

   (defthmd rb-and-rvm256
     (implies (and (app-view x86)
                   (x86p x86)
                   (canonical-address-p lin-addr)
                   (canonical-address-p (+ 31 lin-addr)))
              (equal (rvm256 lin-addr x86)
                     (rb 32 lin-addr r-x x86)))
     :hints (("Goal"
              :use ((:instance rb-1-in-terms-of-its-components
                               (n 32)))
              :in-theory (e/d (rb-and-rvm256-helper-1
                               rb-and-rvm256-helper-2)
                              (force (force))))))

   (defthm-unsigned-byte-p unsigned-byte-p-256-of-merge-32-u8s-linear
     :hyp (and (unsigned-byte-p 8 h15)
               (unsigned-byte-p 8 h14)
               (unsigned-byte-p 8 h13)
               (unsigned-byte-p 8 h12)
               (unsigned-byte-p 8 h11)
               (unsigned-byte-p 8 h10)
               (unsigned-byte-p 8 h9)
               (unsigned-byte-p 8 h8)
               (unsigned-byte-p 8 h7)
               (unsigned-byte-p 8 h6)
               (unsigned-byte-p 8 h5)
               (unsigned-byte-p 8 h4)
               (unsigned-byte-p 8 h3)
               (unsigned-byte-p 8 h2)
               (unsigned-byte-p 8 h1)
               (unsigned-byte-p 8 h0)
               (unsigned-byte-p 8 l15)
               (unsigned-byte-p 8 l14)
               (unsigned-byte-p 8 l13)
               (unsigned-byte-p 8 l12)
               (unsigned-byte-p 8 l11)
               (unsigned-byte-p 8 l10)
               (unsigned-byte-p 8 l9)
               (unsigned-byte-p 8 l8)
               (unsigned-byte-p 8 l7)
               (unsigned-byte-p 8 l6)
               (unsigned-byte-p 8 l5)
               (unsigned-byte-p 8 l4)
               (unsigned-byte-p 8 l3)
               (unsigned-byte-p 8 l2)
               (unsigned-byte-p 8 l1)
               (unsigned-byte-p 8 l0))
     :bound 256
     :concl (bitops::merge-32-u8s h15 h14 h13 h12 h11 h10 h9 h8 h7 h6 h5 h4 h3 h2 h1 h0
                                  l15 l14 l13 l12 l11 l10 l9 l8 l7 l6 l5 l4 l3 l2 l1 l0)
     :hints (("Goal" :in-theory (e/d* () (unsigned-byte-p))))
     :hints-l (("Goal"
                :in-theory
                (e/d* (unsigned-byte-p) (bitops::unsigned-byte-p-256-of-merge-32-u8s))
                :use ((:instance bitops::unsigned-byte-p-256-of-merge-32-u8s))))
     :gen-linear t))


  (if (mbt (canonical-address-p lin-addr))

      (let* ((31+lin-addr (the (signed-byte #.*max-linear-address-size+1*)
                            (+ 31 (the (signed-byte #.*max-linear-address-size*)
                                    lin-addr)))))


        (if (mbe :logic (canonical-address-p 31+lin-addr)
                 :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                            31+lin-addr)
                          #.*2^47*))

            (if (app-view x86)
                (mbe :logic (rb 32 lin-addr r-x x86)
                     :exec (rvm256 lin-addr x86))

              (b* (((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr0) x86)
                    (la-to-pa lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+1*) 1+lin-addr)
                    (+ 1 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr1) x86)
                    (la-to-pa 1+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+2*) 2+lin-addr)
                    (+ 2 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr2) x86)
                    (la-to-pa 2+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+3*) 3+lin-addr)
                    (+ 3 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr3) x86)
                    (la-to-pa 3+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+4*) 4+lin-addr)
                    (+ 4 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr4) x86)
                    (la-to-pa 4+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+5*) 5+lin-addr)
                    (+ 5 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr5) x86)
                    (la-to-pa 5+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+6*) 6+lin-addr)
                    (+ 6 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr6) x86)
                    (la-to-pa 6+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+7*) 7+lin-addr)
                    (+ 7 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr7) x86)
                    (la-to-pa 7+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+8*) 8+lin-addr)
                    (+ 8 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr8) x86)
                    (la-to-pa 8+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+9*) 9+lin-addr)
                    (+ 9 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr9) x86)
                    (la-to-pa 9+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+10*) 10+lin-addr)
                    (+ 10 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr10) x86)
                    (la-to-pa 10+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+11*) 11+lin-addr)
                    (+ 11 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr11) x86)
                    (la-to-pa 11+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+12*) 12+lin-addr)
                    (+ 12 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr12) x86)
                    (la-to-pa 12+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+13*) 13+lin-addr)
                    (+ 13 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr13) x86)
                    (la-to-pa 13+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+14*) 14+lin-addr)
                    (+ 14 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr14) x86)
                    (la-to-pa 14+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+15*) 15+lin-addr)
                    (+ 15 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr15) x86)
                    (la-to-pa 15+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+15*) 16+lin-addr)
                    (+ 16 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr16) x86)
                    (la-to-pa 16+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+17*) 17+lin-addr)
                    (+ 17 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr17) x86)
                    (la-to-pa 17+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+18*) 18+lin-addr)
                    (+ 18 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr18) x86)
                    (la-to-pa 18+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+19*) 19+lin-addr)
                    (+ 19 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr19) x86)
                    (la-to-pa 19+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+20*) 20+lin-addr)
                    (+ 20 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr20) x86)
                    (la-to-pa 20+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+21*) 21+lin-addr)
                    (+ 21 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr21) x86)
                    (la-to-pa 21+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+22*) 22+lin-addr)
                    (+ 22 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr22) x86)
                    (la-to-pa 22+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+23*) 23+lin-addr)
                    (+ 23 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr23) x86)
                    (la-to-pa 23+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+24*) 24+lin-addr)
                    (+ 24 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr24) x86)
                    (la-to-pa 24+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+25*) 25+lin-addr)
                    (+ 25 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr25) x86)
                    (la-to-pa 25+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+26*) 26+lin-addr)
                    (+ 26 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr26) x86)
                    (la-to-pa 26+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+27*) 27+lin-addr)
                    (+ 27 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr27) x86)
                    (la-to-pa 27+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+28*) 28+lin-addr)
                    (+ 28 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr28) x86)
                    (la-to-pa 28+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+29*) 29+lin-addr)
                    (+ 29 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr29) x86)
                    (la-to-pa 29+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+30*) 30+lin-addr)
                    (+ 30 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr30) x86)
                    (la-to-pa 30+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+31*) 31+lin-addr)
                    (+ 31 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr31) x86)
                    (la-to-pa 31+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))

                   (byte0  (memi p-addr0  x86))
                   (byte1  (memi p-addr1  x86))
                   (byte2  (memi p-addr2  x86))
                   (byte3  (memi p-addr3  x86))
                   (byte4  (memi p-addr4  x86))
                   (byte5  (memi p-addr5  x86))
                   (byte6  (memi p-addr6  x86))
                   (byte7  (memi p-addr7  x86))
                   (byte8  (memi p-addr8  x86))
                   (byte9  (memi p-addr9  x86))
                   (byte10 (memi p-addr10 x86))
                   (byte11 (memi p-addr11 x86))
                   (byte12 (memi p-addr12 x86))
                   (byte13 (memi p-addr13 x86))
                   (byte14 (memi p-addr14 x86))
                   (byte15 (memi p-addr15 x86))

                   (byte16 (memi p-addr16 x86))
                   (byte17 (memi p-addr17 x86))
                   (byte18 (memi p-addr18 x86))
                   (byte19 (memi p-addr19 x86))
                   (byte20 (memi p-addr20 x86))
                   (byte21 (memi p-addr21 x86))
                   (byte22 (memi p-addr22 x86))
                   (byte23 (memi p-addr23 x86))
                   (byte24 (memi p-addr24 x86))
                   (byte25 (memi p-addr25 x86))
                   (byte26 (memi p-addr26 x86))
                   (byte27 (memi p-addr27 x86))
                   (byte28 (memi p-addr28 x86))
                   (byte29 (memi p-addr29 x86))
                   (byte30 (memi p-addr30 x86))
                   (byte31 (memi p-addr31 x86))

                   (xword
                    (the (unsigned-byte 256)
                         (bitops::merge-32-u8s
                          byte31 byte30 byte29 byte28
                          byte27 byte26 byte25 byte24
                          byte23 byte22 byte21 byte20
                          byte19 byte18 byte17 byte16
                          byte15 byte14 byte13 byte12
                          byte11 byte10 byte9  byte8
                          byte7  byte6  byte5  byte4
                          byte3  byte2  byte1  byte0))))

                (mv nil xword x86)))

          (mv 'rml256 0 x86)))

    (mv 'rml256 0 x86))

  ///

  (defthm-unsigned-byte-p n256p-mv-nth-1-rml256
    :hyp t
    :bound 256
    :concl (mv-nth 1 (rml256 lin-addr r-x x86))
    :hints (("Goal" :in-theory (e/d () (force (force) signed-byte-p))))
    :gen-linear t
    :hints-l (("Goal" :in-theory (e/d (signed-byte-p) (rb))))
    :gen-type t)

  (defthm x86p-rml256
    (implies (force (x86p x86))
             (x86p (mv-nth 2 (rml256 lin-addr r-x x86))))
    :hints (("Goal" :in-theory (e/d () ((force) unsigned-byte-p signed-byte-p))))
    :rule-classes (:rewrite :type-prescription))

  (defthm rml256-value-when-error
    (implies (mv-nth 0 (rml256 lin-addr r-x x86))
             (equal (mv-nth 1 (rml256 lin-addr r-x x86))
                    0))
    :hints (("Goal" :in-theory (e/d (rml256)
                                    (force (force))))))

  (defthm rml256-x86-unmodified-in-app-view
    (implies (app-view x86)
             (equal (mv-nth 2 (rml256 lin-addr r-x x86))
                    x86))
    :hints (("Goal" :in-theory (e/d (rml256
                                     unsigned-byte-p
                                     signed-byte-p)
                                    (force (force))))))

  (defthm xr-rml256-state-sys-view
    (implies (and (not (app-view x86))
                  (not (equal fld :mem))
                  (not (equal fld :fault))
                  (not (equal fld :tlb))
                  (member-equal fld *x86-field-names-as-keywords*))
             (equal (xr fld index (mv-nth 2 (rml256 lin-addr r-x x86)))
                    (xr fld index x86)))
    :hints (("Goal" :in-theory (e/d (rml256)
                                    (force (force))))))

  (defrule rml256-xw-app-view
    (implies (and (app-view x86)
                  (not (equal fld :mem))
                  (not (equal fld :app-view)))
             (and (equal (mv-nth 0 (rml256 lin-addr  r-x (xw fld index value x86)))
                         (mv-nth 0 (rml256 lin-addr r-x x86)))
                  (equal (mv-nth 1 (rml256 lin-addr r-x (xw fld index value x86)))
                         (mv-nth 1 (rml256 lin-addr r-x x86)))))
    :enable (rml256)
    :disable (rb unsigned-byte-p signed-byte-p (force) force))

  (defrule rml256-xw-sys-view
    (implies
     (and (not (app-view x86))
          (not (equal fld :fault))
          (not (equal fld :seg-visible))
          (not (equal fld :seg-hidden-base))
          (not (equal fld :seg-hidden-limit))
          (not (equal fld :seg-hidden-attr))
          (not (equal fld :mem))
          (not (equal fld :ctr))
          (not (equal fld :msr))
          (not (equal fld :rflags))
          (not (equal fld :app-view))
          (not (equal fld :marking-view))
          (not (equal fld :tlb))
          (not (equal fld :implicit-supervisor-access))
          (member-equal fld *x86-field-names-as-keywords*))
     (and (equal (mv-nth 0 (rml256 lin-addr r-x (xw fld index value x86)))
                 (mv-nth 0 (rml256 lin-addr r-x x86)))
          (equal (mv-nth 1 (rml256 lin-addr r-x (xw fld index value x86)))
                 (mv-nth 1 (rml256 lin-addr r-x x86)))
          (equal (mv-nth 2 (rml256 lin-addr r-x (xw fld index value x86)))
                 (xw fld index value (mv-nth 2 (rml256 lin-addr r-x x86))))))
    :enable (rml256)
    :disable (rb unsigned-byte-p signed-byte-p force (force)))

  (defrule rml256-xw-sys-view-rflags-not-ac
    (implies
     (and (not (app-view x86))
          (equal (rflagsbits->ac value)
                 (rflagsbits->ac (rflags x86))))
     (and (equal (mv-nth 0 (rml256 lin-addr r-x (xw :rflags nil value x86)))
                 (mv-nth 0 (rml256 lin-addr r-x x86)))
          (equal (mv-nth 1 (rml256 lin-addr r-x (xw :rflags nil value x86)))
                 (mv-nth 1 (rml256 lin-addr r-x x86)))
          (equal (mv-nth 2 (rml256 lin-addr r-x (xw :rflags nil value x86)))
                 (xw :rflags nil value
                     (mv-nth 2 (rml256 lin-addr r-x x86))))))
    :enable (rml256)
    :disable (rb unsigned-byte-p signed-byte-p member-equal)))

;; TODO: Prove wml256 equivalent to rb in the system-level view (again).
(define wml256 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
                (val      :type (unsigned-byte 256))
                (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)

  :guard-hints
  (("Goal" :in-theory (e/d (wb-and-wvm256)
                           (wvm256
                            not
                            (:rewrite acl2::ash-0)
                            (:rewrite acl2::zip-open)
                            (:linear bitops::logior-<-0-linear-2)
                            (:rewrite xr-and-ia32e-la-to-pa-in-non-marking-view)
                            (:rewrite bitops::logior-equal-0)))))

  :prepwork
  ((defthmd wb-and-wvm256
     (implies (and (app-view x86)
                   (canonical-address-p lin-addr)
                   (canonical-address-p (+ 31 lin-addr)))
              (equal (wvm256 lin-addr val x86)
                     (wb 32 lin-addr :w val x86)))
     :hints (("Goal" :in-theory (e/d (wml08 wvm08 wvm32 wvm64 wvm128 wvm256)
                                     (force (force)))))))

  (if (mbt (canonical-address-p lin-addr))

      (let* ((31+lin-addr (the (signed-byte #.*max-linear-address-size+1*)
                               (+ 31 (the (signed-byte #.*max-linear-address-size*)
                                          lin-addr)))))


        (if (mbe :logic (canonical-address-p 31+lin-addr)
                 :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                               31+lin-addr)
                          #.*2^47*))

            (if (app-view x86)

                (mbe :logic (wb 32 lin-addr :w val x86)
                     :exec (wvm256 lin-addr val x86))

              (b* (((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr0) x86)
                    (la-to-pa lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+1*) 1+lin-addr)
                    (+ 1 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr1) x86)
                    (la-to-pa 1+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+2*) 2+lin-addr)
                    (+ 2 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr2) x86)
                    (la-to-pa 2+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+3*) 3+lin-addr)
                    (+ 3 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr3) x86)
                    (la-to-pa 3+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+4*) 4+lin-addr)
                    (+ 4 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr4) x86)
                    (la-to-pa 4+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+5*) 5+lin-addr)
                    (+ 5 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr5) x86)
                    (la-to-pa 5+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+6*) 6+lin-addr)
                    (+ 6 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr6) x86)
                    (la-to-pa 6+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+7*) 7+lin-addr)
                    (+ 7 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr7) x86)
                    (la-to-pa 7+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+8*) 8+lin-addr)
                    (+ 8 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr8) x86)
                    (la-to-pa 8+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+9*) 9+lin-addr)
                    (+ 9 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr9) x86)
                    (la-to-pa 9+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+10*) 10+lin-addr)
                    (+ 10 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr10) x86)
                    (la-to-pa 10+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+11*) 11+lin-addr)
                    (+ 11 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr11) x86)
                    (la-to-pa 11+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+12*) 12+lin-addr)
                    (+ 12 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr12) x86)
                    (la-to-pa 12+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+13*) 13+lin-addr)
                    (+ 13 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr13) x86)
                    (la-to-pa 13+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+14*) 14+lin-addr)
                    (+ 14 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr14) x86)
                    (la-to-pa 14+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+15*) 15+lin-addr)
                    (+ 15 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr15) x86)
                    (la-to-pa 15+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+16*) 16+lin-addr)
                    (+ 16 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr16) x86)
                    (la-to-pa 16+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+17*) 17+lin-addr)
                    (+ 17 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr17) x86)
                    (la-to-pa 17+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+18*) 18+lin-addr)
                    (+ 18 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr18) x86)
                    (la-to-pa 18+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+19*) 19+lin-addr)
                    (+ 19 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr19) x86)
                    (la-to-pa 19+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+20*) 20+lin-addr)
                    (+ 20 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr20) x86)
                    (la-to-pa 20+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+21*) 21+lin-addr)
                    (+ 21 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr21) x86)
                    (la-to-pa 21+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+22*) 22+lin-addr)
                    (+ 22 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr22) x86)
                    (la-to-pa 22+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+23*) 23+lin-addr)
                    (+ 23 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr23) x86)
                    (la-to-pa 23+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+24*) 24+lin-addr)
                    (+ 24 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr24) x86)
                    (la-to-pa 24+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+25*) 25+lin-addr)
                    (+ 25 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr25) x86)
                    (la-to-pa 25+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+26*) 26+lin-addr)
                    (+ 26 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr26) x86)
                    (la-to-pa 26+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+27*) 27+lin-addr)
                    (+ 27 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr27) x86)
                    (la-to-pa 27+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+28*) 28+lin-addr)
                    (+ 28 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr28) x86)
                    (la-to-pa 28+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+29*) 29+lin-addr)
                    (+ 29 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr29) x86)
                    (la-to-pa 29+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+30*) 30+lin-addr)
                    (+ 30 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr30) x86)
                    (la-to-pa 30+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+31*) 31+lin-addr)
                    (+ 31 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr31) x86)
                    (la-to-pa 31+lin-addr :w x86))
                   ((when flag) (mv flag x86))

                   (byte0 (mbe :logic (part-select val :low 0 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff val))))
                   (byte1 (mbe :logic (part-select val :low 8 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff (ash val -8)))))
                   (byte2 (mbe :logic (part-select val :low 16 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff (ash val -16)))))
                   (byte3 (mbe :logic (part-select val :low 24 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff (ash val -24)))))
                   (byte4 (mbe :logic (part-select val :low 32 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff (ash val -32)))))
                   (byte5 (mbe :logic (part-select val :low 40 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff (ash val -40)))))
                   (byte6 (mbe :logic (part-select val :low 48 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff (ash val -48)))))
                   (byte7 (mbe :logic (part-select val :low 56 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff (ash val -56)))))
                   (byte8 (mbe :logic (part-select val :low 64 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff (ash val -64)))))
                   (byte9 (mbe :logic (part-select val :low 72 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff (ash val -72)))))
                   (byte10 (mbe :logic (part-select val :low 80 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -80)))))
                   (byte11 (mbe :logic (part-select val :low 88 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -88)))))
                   (byte12 (mbe :logic (part-select val :low 96 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -96)))))
                   (byte13 (mbe :logic (part-select val :low 104 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -104)))))
                   (byte14 (mbe :logic (part-select val :low 112 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -112)))))
                   (byte15 (mbe :logic (part-select val :low 120 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -120)))))
                   (byte16 (mbe :logic (part-select val :low 128 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -128)))))
                   (byte17 (mbe :logic (part-select val :low 136 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -136)))))
                   (byte18 (mbe :logic (part-select val :low 144 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -144)))))
                   (byte19 (mbe :logic (part-select val :low 152 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -152)))))
                   (byte20 (mbe :logic (part-select val :low 160 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -160)))))
                   (byte21 (mbe :logic (part-select val :low 168 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -168)))))
                   (byte22 (mbe :logic (part-select val :low 176 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -176)))))
                   (byte23 (mbe :logic (part-select val :low 184 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -184)))))
                   (byte24 (mbe :logic (part-select val :low 192 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -192)))))
                   (byte25 (mbe :logic (part-select val :low 200 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -200)))))
                   (byte26 (mbe :logic (part-select val :low 208 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -208)))))
                   (byte27 (mbe :logic (part-select val :low 216 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -216)))))
                   (byte28 (mbe :logic (part-select val :low 224 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -224)))))
                   (byte29 (mbe :logic (part-select val :low 232 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -232)))))
                   (byte30 (mbe :logic (part-select val :low 240 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -240)))))
                   (byte31 (mbe :logic (part-select val :low 248 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -248)))))

                   (x86 (!memi p-addr0 byte0 x86))
                   (x86 (!memi p-addr1 byte1 x86))
                   (x86 (!memi p-addr2 byte2 x86))
                   (x86 (!memi p-addr3 byte3 x86))
                   (x86 (!memi p-addr4 byte4 x86))
                   (x86 (!memi p-addr5 byte5 x86))
                   (x86 (!memi p-addr6 byte6 x86))
                   (x86 (!memi p-addr7 byte7 x86))
                   (x86 (!memi p-addr8 byte8 x86))
                   (x86 (!memi p-addr9 byte9 x86))
                   (x86 (!memi p-addr10 byte10 x86))
                   (x86 (!memi p-addr11 byte11 x86))
                   (x86 (!memi p-addr12 byte12 x86))
                   (x86 (!memi p-addr13 byte13 x86))
                   (x86 (!memi p-addr14 byte14 x86))
                   (x86 (!memi p-addr15 byte15 x86))
                   (x86 (!memi p-addr16 byte16 x86))
                   (x86 (!memi p-addr17 byte17 x86))
                   (x86 (!memi p-addr18 byte18 x86))
                   (x86 (!memi p-addr19 byte19 x86))
                   (x86 (!memi p-addr20 byte20 x86))
                   (x86 (!memi p-addr21 byte21 x86))
                   (x86 (!memi p-addr22 byte22 x86))
                   (x86 (!memi p-addr23 byte23 x86))
                   (x86 (!memi p-addr24 byte24 x86))
                   (x86 (!memi p-addr25 byte25 x86))
                   (x86 (!memi p-addr26 byte26 x86))
                   (x86 (!memi p-addr27 byte27 x86))
                   (x86 (!memi p-addr28 byte28 x86))
                   (x86 (!memi p-addr29 byte29 x86))
                   (x86 (!memi p-addr30 byte30 x86))
                   (x86 (!memi p-addr31 byte31 x86)))

                (mv nil x86)))


          (mv 'wml256 x86)))

    (mv 'wml256 x86))

  ///

  (defthm x86p-wml256
    (implies (force (x86p x86))
             (x86p (mv-nth 1 (wml256 lin-addr val x86))))
    :hints (("Goal" :in-theory (e/d () (rb x86p force (force) unsigned-byte-p signed-byte-p))))
    :rule-classes (:rewrite :type-prescription)))

; The following two functions, for 512 bits, are commented out because they
; currently take too long to certify: if they are uncommented, this file takes
; about 10 minutes to certify on a very fast machine, while it takes about 1
; minute when they are commented out. For now we do not need these, but we
; should speed up their proofs and uncomment them, since they will be needed to
; support certain instructions on 512 bits (e.g. involving the ZMM registers).

#|

;; TODO: Prove rml512 equivalent to rb in the system-level view. (again)
(define rml512 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
                (r-x      :type (member :r :x))
                (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)
  :guard-hints (("Goal"
                 :in-theory (e/d (rb-and-rvm512
                                  rml08 rml256
                                  rb-and-rvm512-helper-1
                                  rb-and-rvm512-helper-2)
                                 (not
                                  (:rewrite acl2::ash-0)
                                  (:rewrite acl2::zip-open)
                                  (:linear bitops::logior-<-0-linear-2)
                                  (:rewrite xr-and-ia32e-la-to-pa-in-non-marking-view)
                                  (:rewrite bitops::logior-equal-0)))))

  :prepwork
  ((local
    (defthmd rb-and-rvm512-helper-1
      (implies
       (and (app-view x86)
            (x86p x86)
            (canonical-address-p lin-addr)
            (canonical-address-p (+ 63 lin-addr)))
       (equal (rvm512 lin-addr x86)
              (list
               nil
               (logior (mv-nth 1 (rb-1 32 lin-addr r-x x86))
                       (ash (mv-nth 1 (rb-1 32 (+ 32 lin-addr) r-x x86))
                            256))
               x86)))
      :hints (("Goal" :in-theory (e/d (rvm512 rb-and-rvm256)
                                      (force (force)))))))

   (local
    (defthmd rb-and-rvm512-helper-2
      (implies
       (and (app-view x86)
            (x86p x86)
            (canonical-address-p lin-addr)
            (canonical-address-p (+ 63 lin-addr)))
       (equal
        (logior (mv-nth 1 (rb-1 32 lin-addr r-x x86))
                (ash (mv-nth 1 (rb-1 32 (+ 32 lin-addr) r-x x86)) 256))
        (mv-nth 1 (rb-1 64 lin-addr r-x x86))))
      :hints (("Goal"
               :in-theory (e/d () (force (force)))
               :use
               ((:instance split-rb-in-app-view
                           (i 32) (j 32)))))))

   (defthmd rb-and-rvm512
     (implies (and (app-view x86)
                   (x86p x86)
                   (canonical-address-p lin-addr)
                   (canonical-address-p (+ 63 lin-addr)))
              (equal (rvm512 lin-addr x86)
                     (rb 64 lin-addr r-x x86)))
     :hints (("Goal"
              :use ((:instance rb-1-in-terms-of-its-components
                               (n 64)))
              :in-theory (e/d (rb-and-rvm512-helper-1
                               rb-and-rvm512-helper-2)
                              (force (force))))))

   (defthm-unsigned-byte-p unsigned-byte-p-512-of-merge-64-u8s-linear
     :hyp (and (unsigned-byte-p 8 h31)
               (unsigned-byte-p 8 h30)
               (unsigned-byte-p 8 h29)
               (unsigned-byte-p 8 h28)
               (unsigned-byte-p 8 h27)
               (unsigned-byte-p 8 h26)
               (unsigned-byte-p 8 h25)
               (unsigned-byte-p 8 h24)
               (unsigned-byte-p 8 h23)
               (unsigned-byte-p 8 h22)
               (unsigned-byte-p 8 h21)
               (unsigned-byte-p 8 h20)
               (unsigned-byte-p 8 h19)
               (unsigned-byte-p 8 h18)
               (unsigned-byte-p 8 h17)
               (unsigned-byte-p 8 h16)
               (unsigned-byte-p 8 h15)
               (unsigned-byte-p 8 h14)
               (unsigned-byte-p 8 h13)
               (unsigned-byte-p 8 h12)
               (unsigned-byte-p 8 h11)
               (unsigned-byte-p 8 h10)
               (unsigned-byte-p 8 h9)
               (unsigned-byte-p 8 h8)
               (unsigned-byte-p 8 h7)
               (unsigned-byte-p 8 h6)
               (unsigned-byte-p 8 h5)
               (unsigned-byte-p 8 h4)
               (unsigned-byte-p 8 h3)
               (unsigned-byte-p 8 h2)
               (unsigned-byte-p 8 h1)
               (unsigned-byte-p 8 h0)
               (unsigned-byte-p 8 l31)
               (unsigned-byte-p 8 l30)
               (unsigned-byte-p 8 l29)
               (unsigned-byte-p 8 l28)
               (unsigned-byte-p 8 l27)
               (unsigned-byte-p 8 l26)
               (unsigned-byte-p 8 l25)
               (unsigned-byte-p 8 l24)
               (unsigned-byte-p 8 l23)
               (unsigned-byte-p 8 l22)
               (unsigned-byte-p 8 l21)
               (unsigned-byte-p 8 l20)
               (unsigned-byte-p 8 l19)
               (unsigned-byte-p 8 l18)
               (unsigned-byte-p 8 l17)
               (unsigned-byte-p 8 l16)
               (unsigned-byte-p 8 l15)
               (unsigned-byte-p 8 l14)
               (unsigned-byte-p 8 l13)
               (unsigned-byte-p 8 l12)
               (unsigned-byte-p 8 l11)
               (unsigned-byte-p 8 l10)
               (unsigned-byte-p 8 l9)
               (unsigned-byte-p 8 l8)
               (unsigned-byte-p 8 l7)
               (unsigned-byte-p 8 l6)
               (unsigned-byte-p 8 l5)
               (unsigned-byte-p 8 l4)
               (unsigned-byte-p 8 l3)
               (unsigned-byte-p 8 l2)
               (unsigned-byte-p 8 l1)
               (unsigned-byte-p 8 l0))
     :bound 512
     :concl (bitops::merge-64-u8s h31 h30 h29 h28 h27 h26 h25 h24 h23 h22 h21 h20 h19 h18 h17 h16
                                  h15 h14 h13 h12 h11 h10 h9 h8 h7 h6 h5 h4 h3 h2 h1 h0
                                  l31 l30 l29 l28 l27 l26 l25 l24 l23 l22 l21 l20 l19 l18 l17 l16
                                  l15 l14 l13 l12 l11 l10 l9 l8 l7 l6 l5 l4 l3 l2 l1 l0)
     :hints (("Goal" :in-theory (e/d* () (unsigned-byte-p))))
     :hints-l (("Goal"
                :in-theory
                (e/d* (unsigned-byte-p) (bitops::unsigned-byte-p-512-of-merge-64-u8s))
                :use ((:instance bitops::unsigned-byte-p-512-of-merge-64-u8s))))
     :gen-linear t))


  (if (mbt (canonical-address-p lin-addr))

      (let* ((63+lin-addr (the (signed-byte #.*max-linear-address-size+1*)
                            (+ 63 (the (signed-byte #.*max-linear-address-size*)
                                    lin-addr)))))


        (if (mbe :logic (canonical-address-p 63+lin-addr)
                 :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                            63+lin-addr)
                          #.*2^47*))

            (if (app-view x86)
                (mbe :logic (rb 64 lin-addr r-x x86)
                     :exec (rvm512 lin-addr x86))

              (b* (((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr0) x86)
                    (la-to-pa lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+1*) 1+lin-addr)
                    (+ 1 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr1) x86)
                    (la-to-pa 1+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+2*) 2+lin-addr)
                    (+ 2 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr2) x86)
                    (la-to-pa 2+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+3*) 3+lin-addr)
                    (+ 3 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr3) x86)
                    (la-to-pa 3+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+4*) 4+lin-addr)
                    (+ 4 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr4) x86)
                    (la-to-pa 4+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+5*) 5+lin-addr)
                    (+ 5 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr5) x86)
                    (la-to-pa 5+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+6*) 6+lin-addr)
                    (+ 6 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr6) x86)
                    (la-to-pa 6+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+7*) 7+lin-addr)
                    (+ 7 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr7) x86)
                    (la-to-pa 7+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+8*) 8+lin-addr)
                    (+ 8 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr8) x86)
                    (la-to-pa 8+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+9*) 9+lin-addr)
                    (+ 9 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr9) x86)
                    (la-to-pa 9+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+10*) 10+lin-addr)
                    (+ 10 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr10) x86)
                    (la-to-pa 10+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+11*) 11+lin-addr)
                    (+ 11 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr11) x86)
                    (la-to-pa 11+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+12*) 12+lin-addr)
                    (+ 12 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr12) x86)
                    (la-to-pa 12+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+13*) 13+lin-addr)
                    (+ 13 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr13) x86)
                    (la-to-pa 13+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+14*) 14+lin-addr)
                    (+ 14 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr14) x86)
                    (la-to-pa 14+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+15*) 15+lin-addr)
                    (+ 15 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr15) x86)
                    (la-to-pa 15+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+15*) 16+lin-addr)
                    (+ 16 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr16) x86)
                    (la-to-pa 16+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+17*) 17+lin-addr)
                    (+ 17 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr17) x86)
                    (la-to-pa 17+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+18*) 18+lin-addr)
                    (+ 18 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr18) x86)
                    (la-to-pa 18+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+19*) 19+lin-addr)
                    (+ 19 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr19) x86)
                    (la-to-pa 19+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+20*) 20+lin-addr)
                    (+ 20 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr20) x86)
                    (la-to-pa 20+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+21*) 21+lin-addr)
                    (+ 21 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr21) x86)
                    (la-to-pa 21+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+22*) 22+lin-addr)
                    (+ 22 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr22) x86)
                    (la-to-pa 22+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+23*) 23+lin-addr)
                    (+ 23 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr23) x86)
                    (la-to-pa 23+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+24*) 24+lin-addr)
                    (+ 24 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr24) x86)
                    (la-to-pa 24+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+25*) 25+lin-addr)
                    (+ 25 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr25) x86)
                    (la-to-pa 25+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+26*) 26+lin-addr)
                    (+ 26 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr26) x86)
                    (la-to-pa 26+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+27*) 27+lin-addr)
                    (+ 27 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr27) x86)
                    (la-to-pa 27+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+28*) 28+lin-addr)
                    (+ 28 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr28) x86)
                    (la-to-pa 28+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+29*) 29+lin-addr)
                    (+ 29 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr29) x86)
                    (la-to-pa 29+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+30*) 30+lin-addr)
                    (+ 30 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr30) x86)
                    (la-to-pa 30+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+31*) 31+lin-addr)
                    (+ 31 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr31) x86)
                    (la-to-pa 31+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+32*) 32+lin-addr)
                    (+ 32 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr32) x86)
                    (la-to-pa 32+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+33*) 33+lin-addr)
                    (+ 33 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr33) x86)
                    (la-to-pa 33+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+34*) 34+lin-addr)
                    (+ 34 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr34) x86)
                    (la-to-pa 34+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+35*) 35+lin-addr)
                    (+ 35 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr35) x86)
                    (la-to-pa 35+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+36*) 36+lin-addr)
                    (+ 36 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr36) x86)
                    (la-to-pa 36+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+37*) 37+lin-addr)
                    (+ 37 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr37) x86)
                    (la-to-pa 37+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+38*) 38+lin-addr)
                    (+ 38 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr38) x86)
                    (la-to-pa 38+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+39*) 39+lin-addr)
                    (+ 39 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr39) x86)
                    (la-to-pa 39+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+40*) 40+lin-addr)
                    (+ 40 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr40) x86)
                    (la-to-pa 40+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+41*) 41+lin-addr)
                    (+ 41 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr41) x86)
                    (la-to-pa 41+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+42*) 42+lin-addr)
                    (+ 42 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr42) x86)
                    (la-to-pa 42+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+43*) 43+lin-addr)
                    (+ 43 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr43) x86)
                    (la-to-pa 43+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+44*) 44+lin-addr)
                    (+ 44 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr44) x86)
                    (la-to-pa 44+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+45*) 45+lin-addr)
                    (+ 45 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr45) x86)
                    (la-to-pa 45+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+46*) 46+lin-addr)
                    (+ 46 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr46) x86)
                    (la-to-pa 46+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+47*) 47+lin-addr)
                    (+ 47 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr47) x86)
                    (la-to-pa 47+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+48*) 48+lin-addr)
                    (+ 48 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr48) x86)
                    (la-to-pa 48+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+49*) 49+lin-addr)
                    (+ 49 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr49) x86)
                    (la-to-pa 49+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+50*) 50+lin-addr)
                    (+ 50 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr50) x86)
                    (la-to-pa 50+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+51*) 51+lin-addr)
                    (+ 51 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr51) x86)
                    (la-to-pa 51+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+52*) 52+lin-addr)
                    (+ 52 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr52) x86)
                    (la-to-pa 52+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+53*) 53+lin-addr)
                    (+ 53 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr53) x86)
                    (la-to-pa 53+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+54*) 54+lin-addr)
                    (+ 54 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr54) x86)
                    (la-to-pa 54+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+55*) 55+lin-addr)
                    (+ 55 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr55) x86)
                    (la-to-pa 55+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+56*) 56+lin-addr)
                    (+ 56 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr56) x86)
                    (la-to-pa 56+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+57*) 57+lin-addr)
                    (+ 57 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr57) x86)
                    (la-to-pa 57+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+58*) 58+lin-addr)
                    (+ 58 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr58) x86)
                    (la-to-pa 58+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+59*) 59+lin-addr)
                    (+ 59 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr59) x86)
                    (la-to-pa 59+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+60*) 60+lin-addr)
                    (+ 60 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr60) x86)
                    (la-to-pa 60+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+61*) 61+lin-addr)
                    (+ 61 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr61) x86)
                    (la-to-pa 61+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+62*) 62+lin-addr)
                    (+ 62 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr62) x86)
                    (la-to-pa 62+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))
                   ((the (signed-byte #.*max-linear-address-size+63*) 63+lin-addr)
                    (+ 63 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr63) x86)
                    (la-to-pa 63+lin-addr r-x x86))
                   ((when flag) (mv flag 0 x86))

                   (byte0  (memi p-addr0  x86))
                   (byte1  (memi p-addr1  x86))
                   (byte2  (memi p-addr2  x86))
                   (byte3  (memi p-addr3  x86))
                   (byte4  (memi p-addr4  x86))
                   (byte5  (memi p-addr5  x86))
                   (byte6  (memi p-addr6  x86))
                   (byte7  (memi p-addr7  x86))
                   (byte8  (memi p-addr8  x86))
                   (byte9  (memi p-addr9  x86))
                   (byte10 (memi p-addr10 x86))
                   (byte11 (memi p-addr11 x86))
                   (byte12 (memi p-addr12 x86))
                   (byte13 (memi p-addr13 x86))
                   (byte14 (memi p-addr14 x86))
                   (byte15 (memi p-addr15 x86))

                   (byte16 (memi p-addr16 x86))
                   (byte17 (memi p-addr17 x86))
                   (byte18 (memi p-addr18 x86))
                   (byte19 (memi p-addr19 x86))
                   (byte20 (memi p-addr20 x86))
                   (byte21 (memi p-addr21 x86))
                   (byte22 (memi p-addr22 x86))
                   (byte23 (memi p-addr23 x86))
                   (byte24 (memi p-addr24 x86))
                   (byte25 (memi p-addr25 x86))
                   (byte26 (memi p-addr26 x86))
                   (byte27 (memi p-addr27 x86))
                   (byte28 (memi p-addr28 x86))
                   (byte29 (memi p-addr29 x86))
                   (byte30 (memi p-addr30 x86))
                   (byte31 (memi p-addr31 x86))

                   (byte32 (memi p-addr32 x86))
                   (byte33 (memi p-addr33 x86))
                   (byte34 (memi p-addr34 x86))
                   (byte35 (memi p-addr35 x86))
                   (byte36 (memi p-addr36 x86))
                   (byte37 (memi p-addr37 x86))
                   (byte38 (memi p-addr38 x86))
                   (byte39 (memi p-addr39 x86))
                   (byte40 (memi p-addr40 x86))
                   (byte41 (memi p-addr41 x86))
                   (byte42 (memi p-addr42 x86))
                   (byte43 (memi p-addr43 x86))
                   (byte44 (memi p-addr44 x86))
                   (byte45 (memi p-addr45 x86))
                   (byte46 (memi p-addr46 x86))
                   (byte47 (memi p-addr47 x86))

                   (byte48 (memi p-addr48 x86))
                   (byte49 (memi p-addr49 x86))
                   (byte50 (memi p-addr50 x86))
                   (byte51 (memi p-addr51 x86))
                   (byte52 (memi p-addr52 x86))
                   (byte53 (memi p-addr53 x86))
                   (byte54 (memi p-addr54 x86))
                   (byte55 (memi p-addr55 x86))
                   (byte56 (memi p-addr56 x86))
                   (byte57 (memi p-addr57 x86))
                   (byte58 (memi p-addr58 x86))
                   (byte59 (memi p-addr59 x86))
                   (byte60 (memi p-addr60 x86))
                   (byte61 (memi p-addr61 x86))
                   (byte62 (memi p-addr62 x86))
                   (byte63 (memi p-addr63 x86))

                   (xxword
                    (the (unsigned-byte 512)
                         (bitops::merge-64-u8s
                          byte63 byte62 byte61 byte60
                          byte59 byte58 byte57 byte56
                          byte55 byte54 byte53 byte52
                          byte51 byte50 byte49 byte48
                          byte47 byte46 byte45 byte44
                          byte43 byte42 byte41 byte40
                          byte39 byte38 byte37 byte36
                          byte35 byte34 byte33 byte32
                          byte31 byte30 byte29 byte28
                          byte27 byte26 byte25 byte24
                          byte23 byte22 byte21 byte20
                          byte19 byte18 byte17 byte16
                          byte15 byte14 byte13 byte12
                          byte11 byte10 byte9  byte8
                          byte7  byte6  byte5  byte4
                          byte3  byte2  byte1  byte0))))

                (mv nil xxword x86)))

          (mv 'rml512 0 x86)))

    (mv 'rml512 0 x86))

  ///

  (defthm-unsigned-byte-p n512p-mv-nth-1-rml512
    :hyp t
    :bound 512
    :concl (mv-nth 1 (rml512 lin-addr r-x x86))
    :hints (("Goal" :in-theory (e/d () (force (force) signed-byte-p))))
    :gen-linear t
    :hints-l (("Goal" :in-theory (e/d (signed-byte-p) (rb))))
    :gen-type t)

  (defthm x86p-rml512
    (implies (force (x86p x86))
             (x86p (mv-nth 2 (rml512 lin-addr r-x x86))))
    :hints (("Goal" :in-theory (e/d () ((force) unsigned-byte-p signed-byte-p))))
    :rule-classes (:rewrite :type-prescription))

  (defthm rml512-value-when-error
    (implies (mv-nth 0 (rml512 lin-addr r-x x86))
             (equal (mv-nth 1 (rml512 lin-addr r-x x86))
                    0))
    :hints (("Goal" :in-theory (e/d (rml512)
                                    (force (force))))))

  (defthm rml512-x86-unmodified-in-not-marking-view
    (implies (and (not (marking-view x86))
                  (not (mv-nth 0 (rml512 lin-addr r-x x86))))
             (equal (mv-nth 2 (rml512 lin-addr r-x x86))
                    x86))
    :hints (("Goal" :in-theory (e/d (rml512
                                     unsigned-byte-p
                                     signed-byte-p)
                                    (force (force))))))

  (defthm rml512-x86-unmodified-in-app-view
    (implies (app-view x86)
             (equal (mv-nth 2 (rml512 lin-addr r-x x86))
                    x86))
    :hints (("Goal" :in-theory (e/d (rml512
                                     unsigned-byte-p
                                     signed-byte-p)
                                    (force (force))))))

  (defthm xr-rml512-state-sys-view
    (implies (and (not (app-view x86))
                  (not (equal fld :mem))
                  (not (equal fld :fault))
                  (member-equal fld *x86-field-names-as-keywords*))
             (equal (xr fld index (mv-nth 2 (rml512 lin-addr r-x x86)))
                    (xr fld index x86)))
    :hints (("Goal" :in-theory (e/d (rml512)
                                    (force (force))))))

  (defrule rml512-xw-app-view
    (implies (and (app-view x86)
                  (not (equal fld :mem))
                  (not (equal fld :app-view)))
             (and (equal (mv-nth 0 (rml512 lin-addr  r-x (xw fld index value x86)))
                         (mv-nth 0 (rml512 lin-addr r-x x86)))
                  (equal (mv-nth 1 (rml512 lin-addr r-x (xw fld index value x86)))
                         (mv-nth 1 (rml512 lin-addr r-x x86)))))
    :enable (rml512)
    :disable (rb unsigned-byte-p signed-byte-p (force) force))

  (defrule rml512-xw-sys-view
    (implies
     (and (not (app-view x86))
          (not (equal fld :fault))
          (not (equal fld :seg-visible))
          (not (equal fld :seg-hidden-base))
          (not (equal fld :seg-hidden-limit))
          (not (equal fld :seg-hidden-attr))
          (not (equal fld :mem))
          (not (equal fld :ctr))
          (not (equal fld :msr))
          (not (equal fld :rflags))
          (not (equal fld :app-view))
          (not (equal fld :marking-view))
          (not (equal fld :implicit-supervisor-access))
          (member-equal fld *x86-field-names-as-keywords*))
     (and (equal (mv-nth 0 (rml512 lin-addr r-x (xw fld index value x86)))
                 (mv-nth 0 (rml512 lin-addr r-x x86)))
          (equal (mv-nth 1 (rml512 lin-addr r-x (xw fld index value x86)))
                 (mv-nth 1 (rml512 lin-addr r-x x86)))
          (equal (mv-nth 2 (rml512 lin-addr r-x (xw fld index value x86)))
                 (xw fld index value (mv-nth 2 (rml512 lin-addr r-x x86))))))
    :enable (rml512)
    :disable (rb unsigned-byte-p signed-byte-p force (force)))

  (defrule rml512-xw-sys-view-rflags-not-ac
    (implies
     (and (not (app-view x86))
          (equal (rflagsbits->ac value)
                 (rflagsbits->ac (rflags x86))))
     (and (equal (mv-nth 0 (rml512 lin-addr r-x (xw :rflags nil value x86)))
                 (mv-nth 0 (rml512 lin-addr r-x x86)))
          (equal (mv-nth 1 (rml512 lin-addr r-x (xw :rflags nil value x86)))
                 (mv-nth 1 (rml512 lin-addr r-x x86)))
          (equal (mv-nth 2 (rml512 lin-addr r-x (xw :rflags nil value x86)))
                 (xw :rflags nil value
                     (mv-nth 2 (rml512 lin-addr r-x x86))))))
    :enable (rml512)
    :disable (rb unsigned-byte-p signed-byte-p member-equal)))

;; TODO: Prove wml512 equivalent to rb in the system-level view (again).
(define wml512 ((lin-addr :type (signed-byte #.*max-linear-address-size*))
                (val      :type (unsigned-byte 512))
                (x86))

  :parents (linear-memory)
  :guard (canonical-address-p lin-addr)

  :guard-hints
  (("Goal" :in-theory (e/d (wb-and-wvm512)
                           (wvm512
                            not
                            (:rewrite acl2::ash-0)
                            (:rewrite acl2::zip-open)
                            (:linear bitops::logior-<-0-linear-2)
                            (:rewrite xr-and-ia32e-la-to-pa-in-non-marking-view)
                            (:rewrite bitops::logior-equal-0)))))

  :prepwork
  ((defthmd wb-and-wvm512
     (implies (and (app-view x86)
                   (canonical-address-p lin-addr)
                   (canonical-address-p (+ 63 lin-addr)))
              (equal (wvm512 lin-addr val x86)
                     (wb 64 lin-addr :w val x86)))
     :hints (("Goal" :in-theory (e/d (wml08 wvm08 wvm32 wvm64 wvm128 wvm256 wvm512)
                                     (force (force))))))

   ;; The guard proof needs a larger stack limit.
   (set-rewrite-stack-limit 2000))

  (if (mbt (canonical-address-p lin-addr))

      (let* ((63+lin-addr (the (signed-byte #.*max-linear-address-size+1*)
                               (+ 63 (the (signed-byte #.*max-linear-address-size*)
                                          lin-addr)))))


        (if (mbe :logic (canonical-address-p 63+lin-addr)
                 :exec (< (the (signed-byte #.*max-linear-address-size+1*)
                               63+lin-addr)
                          #.*2^47*))

            (if (app-view x86)

                (mbe :logic (wb 64 lin-addr :w val x86)
                     :exec (wvm512 lin-addr val x86))

              (b* (((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr0) x86)
                    (la-to-pa lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+1*) 1+lin-addr)
                    (+ 1 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr1) x86)
                    (la-to-pa 1+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+2*) 2+lin-addr)
                    (+ 2 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr2) x86)
                    (la-to-pa 2+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+3*) 3+lin-addr)
                    (+ 3 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr3) x86)
                    (la-to-pa 3+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+4*) 4+lin-addr)
                    (+ 4 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr4) x86)
                    (la-to-pa 4+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+5*) 5+lin-addr)
                    (+ 5 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr5) x86)
                    (la-to-pa 5+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+6*) 6+lin-addr)
                    (+ 6 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr6) x86)
                    (la-to-pa 6+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+7*) 7+lin-addr)
                    (+ 7 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr7) x86)
                    (la-to-pa 7+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+8*) 8+lin-addr)
                    (+ 8 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr8) x86)
                    (la-to-pa 8+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+9*) 9+lin-addr)
                    (+ 9 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr9) x86)
                    (la-to-pa 9+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+10*) 10+lin-addr)
                    (+ 10 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr10) x86)
                    (la-to-pa 10+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+11*) 11+lin-addr)
                    (+ 11 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr11) x86)
                    (la-to-pa 11+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+12*) 12+lin-addr)
                    (+ 12 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr12) x86)
                    (la-to-pa 12+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+13*) 13+lin-addr)
                    (+ 13 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr13) x86)
                    (la-to-pa 13+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+14*) 14+lin-addr)
                    (+ 14 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr14) x86)
                    (la-to-pa 14+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+15*) 15+lin-addr)
                    (+ 15 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr15) x86)
                    (la-to-pa 15+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+16*) 16+lin-addr)
                    (+ 16 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr16) x86)
                    (la-to-pa 16+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+17*) 17+lin-addr)
                    (+ 17 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr17) x86)
                    (la-to-pa 17+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+18*) 18+lin-addr)
                    (+ 18 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr18) x86)
                    (la-to-pa 18+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+19*) 19+lin-addr)
                    (+ 19 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr19) x86)
                    (la-to-pa 19+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+20*) 20+lin-addr)
                    (+ 20 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr20) x86)
                    (la-to-pa 20+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+21*) 21+lin-addr)
                    (+ 21 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr21) x86)
                    (la-to-pa 21+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+22*) 22+lin-addr)
                    (+ 22 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr22) x86)
                    (la-to-pa 22+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+23*) 23+lin-addr)
                    (+ 23 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr23) x86)
                    (la-to-pa 23+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+24*) 24+lin-addr)
                    (+ 24 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr24) x86)
                    (la-to-pa 24+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+25*) 25+lin-addr)
                    (+ 25 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr25) x86)
                    (la-to-pa 25+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+26*) 26+lin-addr)
                    (+ 26 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr26) x86)
                    (la-to-pa 26+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+27*) 27+lin-addr)
                    (+ 27 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr27) x86)
                    (la-to-pa 27+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+28*) 28+lin-addr)
                    (+ 28 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr28) x86)
                    (la-to-pa 28+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+29*) 29+lin-addr)
                    (+ 29 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr29) x86)
                    (la-to-pa 29+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+30*) 30+lin-addr)
                    (+ 30 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr30) x86)
                    (la-to-pa 30+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+31*) 31+lin-addr)
                    (+ 31 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr31) x86)
                    (la-to-pa 31+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+32*) 32+lin-addr)
                    (+ 32 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr32) x86)
                    (la-to-pa 32+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+33*) 33+lin-addr)
                    (+ 33 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr33) x86)
                    (la-to-pa 33+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+34*) 34+lin-addr)
                    (+ 34 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr34) x86)
                    (la-to-pa 34+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+35*) 35+lin-addr)
                    (+ 35 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr35) x86)
                    (la-to-pa 35+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+36*) 36+lin-addr)
                    (+ 36 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr36) x86)
                    (la-to-pa 36+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+37*) 37+lin-addr)
                    (+ 37 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr37) x86)
                    (la-to-pa 37+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+38*) 38+lin-addr)
                    (+ 38 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr38) x86)
                    (la-to-pa 38+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+39*) 39+lin-addr)
                    (+ 39 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr39) x86)
                    (la-to-pa 39+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+40*) 40+lin-addr)
                    (+ 40 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr40) x86)
                    (la-to-pa 40+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+41*) 41+lin-addr)
                    (+ 41 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr41) x86)
                    (la-to-pa 41+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+42*) 42+lin-addr)
                    (+ 42 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr42) x86)
                    (la-to-pa 42+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+43*) 43+lin-addr)
                    (+ 43 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr43) x86)
                    (la-to-pa 43+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+44*) 44+lin-addr)
                    (+ 44 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr44) x86)
                    (la-to-pa 44+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+45*) 45+lin-addr)
                    (+ 45 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr45) x86)
                    (la-to-pa 45+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+46*) 46+lin-addr)
                    (+ 46 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr46) x86)
                    (la-to-pa 46+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+47*) 47+lin-addr)
                    (+ 47 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr47) x86)
                    (la-to-pa 47+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+48*) 48+lin-addr)
                    (+ 48 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr48) x86)
                    (la-to-pa 48+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+49*) 49+lin-addr)
                    (+ 49 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr49) x86)
                    (la-to-pa 49+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+50*) 50+lin-addr)
                    (+ 50 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr50) x86)
                    (la-to-pa 50+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+51*) 51+lin-addr)
                    (+ 51 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr51) x86)
                    (la-to-pa 51+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+52*) 52+lin-addr)
                    (+ 52 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr52) x86)
                    (la-to-pa 52+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+53*) 53+lin-addr)
                    (+ 53 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr53) x86)
                    (la-to-pa 53+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+54*) 54+lin-addr)
                    (+ 54 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr54) x86)
                    (la-to-pa 54+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+55*) 55+lin-addr)
                    (+ 55 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr55) x86)
                    (la-to-pa 55+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+56*) 56+lin-addr)
                    (+ 56 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr56) x86)
                    (la-to-pa 56+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+57*) 57+lin-addr)
                    (+ 57 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr57) x86)
                    (la-to-pa 57+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+58*) 58+lin-addr)
                    (+ 58 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr58) x86)
                    (la-to-pa 58+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+59*) 59+lin-addr)
                    (+ 59 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr59) x86)
                    (la-to-pa 59+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+60*) 60+lin-addr)
                    (+ 60 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr60) x86)
                    (la-to-pa 60+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+61*) 61+lin-addr)
                    (+ 61 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr61) x86)
                    (la-to-pa 61+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+62*) 62+lin-addr)
                    (+ 62 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr62) x86)
                    (la-to-pa 62+lin-addr :w x86))
                   ((when flag) (mv flag x86))
                   ((the (signed-byte #.*max-linear-address-size+63*) 63+lin-addr)
                    (+ 63 lin-addr))
                   ((mv flag (the (unsigned-byte #.*physical-address-size*) p-addr63) x86)
                    (la-to-pa 63+lin-addr :w x86))
                   ((when flag) (mv flag x86))

                   (byte0 (mbe :logic (part-select val :low 0 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff val))))
                   (byte1 (mbe :logic (part-select val :low 8 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff (ash val -8)))))
                   (byte2 (mbe :logic (part-select val :low 16 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff (ash val -16)))))
                   (byte3 (mbe :logic (part-select val :low 24 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff (ash val -24)))))
                   (byte4 (mbe :logic (part-select val :low 32 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff (ash val -32)))))
                   (byte5 (mbe :logic (part-select val :low 40 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff (ash val -40)))))
                   (byte6 (mbe :logic (part-select val :low 48 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff (ash val -48)))))
                   (byte7 (mbe :logic (part-select val :low 56 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff (ash val -56)))))
                   (byte8 (mbe :logic (part-select val :low 64 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff (ash val -64)))))
                   (byte9 (mbe :logic (part-select val :low 72 :width 8)
                               :exec (the (unsigned-byte 8)
                                          (logand #xff (ash val -72)))))
                   (byte10 (mbe :logic (part-select val :low 80 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -80)))))
                   (byte11 (mbe :logic (part-select val :low 88 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -88)))))
                   (byte12 (mbe :logic (part-select val :low 96 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -96)))))
                   (byte13 (mbe :logic (part-select val :low 104 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -104)))))
                   (byte14 (mbe :logic (part-select val :low 112 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -112)))))
                   (byte15 (mbe :logic (part-select val :low 120 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -120)))))
                   (byte16 (mbe :logic (part-select val :low 128 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -128)))))
                   (byte17 (mbe :logic (part-select val :low 136 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -136)))))
                   (byte18 (mbe :logic (part-select val :low 144 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -144)))))
                   (byte19 (mbe :logic (part-select val :low 152 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -152)))))
                   (byte20 (mbe :logic (part-select val :low 160 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -160)))))
                   (byte21 (mbe :logic (part-select val :low 168 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -168)))))
                   (byte22 (mbe :logic (part-select val :low 176 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -176)))))
                   (byte23 (mbe :logic (part-select val :low 184 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -184)))))
                   (byte24 (mbe :logic (part-select val :low 192 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -192)))))
                   (byte25 (mbe :logic (part-select val :low 200 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -200)))))
                   (byte26 (mbe :logic (part-select val :low 208 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -208)))))
                   (byte27 (mbe :logic (part-select val :low 216 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -216)))))
                   (byte28 (mbe :logic (part-select val :low 224 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -224)))))
                   (byte29 (mbe :logic (part-select val :low 232 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -232)))))
                   (byte30 (mbe :logic (part-select val :low 240 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -240)))))
                   (byte31 (mbe :logic (part-select val :low 248 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -248)))))
                   (byte32 (mbe :logic (part-select val :low 256 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -256)))))
                   (byte33 (mbe :logic (part-select val :low 264 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -264)))))
                   (byte34 (mbe :logic (part-select val :low 272 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -272)))))
                   (byte35 (mbe :logic (part-select val :low 280 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -280)))))
                   (byte36 (mbe :logic (part-select val :low 288 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -288)))))
                   (byte37 (mbe :logic (part-select val :low 296 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -296)))))
                   (byte38 (mbe :logic (part-select val :low 304 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -304)))))
                   (byte39 (mbe :logic (part-select val :low 312 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -312)))))
                   (byte40 (mbe :logic (part-select val :low 320 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -320)))))
                   (byte41 (mbe :logic (part-select val :low 328 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -328)))))
                   (byte42 (mbe :logic (part-select val :low 336 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -336)))))
                   (byte43 (mbe :logic (part-select val :low 344 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -344)))))
                   (byte44 (mbe :logic (part-select val :low 352 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -352)))))
                   (byte45 (mbe :logic (part-select val :low 360 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -360)))))
                   (byte46 (mbe :logic (part-select val :low 368 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -368)))))
                   (byte47 (mbe :logic (part-select val :low 376 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -376)))))
                   (byte48 (mbe :logic (part-select val :low 384 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -384)))))
                   (byte49 (mbe :logic (part-select val :low 392 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -392)))))
                   (byte50 (mbe :logic (part-select val :low 400 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -400)))))
                   (byte51 (mbe :logic (part-select val :low 408 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -408)))))
                   (byte52 (mbe :logic (part-select val :low 416 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -416)))))
                   (byte53 (mbe :logic (part-select val :low 424 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -424)))))
                   (byte54 (mbe :logic (part-select val :low 432 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -432)))))
                   (byte55 (mbe :logic (part-select val :low 440 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -440)))))
                   (byte56 (mbe :logic (part-select val :low 448 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -448)))))
                   (byte57 (mbe :logic (part-select val :low 456 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -456)))))
                   (byte58 (mbe :logic (part-select val :low 464 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -464)))))
                   (byte59 (mbe :logic (part-select val :low 472 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -472)))))
                   (byte60 (mbe :logic (part-select val :low 480 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -480)))))
                   (byte61 (mbe :logic (part-select val :low 488 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -488)))))
                   (byte62 (mbe :logic (part-select val :low 496 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -496)))))
                   (byte63 (mbe :logic (part-select val :low 504 :width 8)
                                :exec (the (unsigned-byte 8)
                                           (logand #xff (ash val -504)))))

                   (x86 (!memi p-addr0 byte0 x86))
                   (x86 (!memi p-addr1 byte1 x86))
                   (x86 (!memi p-addr2 byte2 x86))
                   (x86 (!memi p-addr3 byte3 x86))
                   (x86 (!memi p-addr4 byte4 x86))
                   (x86 (!memi p-addr5 byte5 x86))
                   (x86 (!memi p-addr6 byte6 x86))
                   (x86 (!memi p-addr7 byte7 x86))
                   (x86 (!memi p-addr8 byte8 x86))
                   (x86 (!memi p-addr9 byte9 x86))
                   (x86 (!memi p-addr10 byte10 x86))
                   (x86 (!memi p-addr11 byte11 x86))
                   (x86 (!memi p-addr12 byte12 x86))
                   (x86 (!memi p-addr13 byte13 x86))
                   (x86 (!memi p-addr14 byte14 x86))
                   (x86 (!memi p-addr15 byte15 x86))
                   (x86 (!memi p-addr16 byte16 x86))
                   (x86 (!memi p-addr17 byte17 x86))
                   (x86 (!memi p-addr18 byte18 x86))
                   (x86 (!memi p-addr19 byte19 x86))
                   (x86 (!memi p-addr20 byte20 x86))
                   (x86 (!memi p-addr21 byte21 x86))
                   (x86 (!memi p-addr22 byte22 x86))
                   (x86 (!memi p-addr23 byte23 x86))
                   (x86 (!memi p-addr24 byte24 x86))
                   (x86 (!memi p-addr25 byte25 x86))
                   (x86 (!memi p-addr26 byte26 x86))
                   (x86 (!memi p-addr27 byte27 x86))
                   (x86 (!memi p-addr28 byte28 x86))
                   (x86 (!memi p-addr29 byte29 x86))
                   (x86 (!memi p-addr30 byte30 x86))
                   (x86 (!memi p-addr31 byte31 x86))
                   (x86 (!memi p-addr32 byte32 x86))
                   (x86 (!memi p-addr33 byte33 x86))
                   (x86 (!memi p-addr34 byte34 x86))
                   (x86 (!memi p-addr35 byte35 x86))
                   (x86 (!memi p-addr36 byte36 x86))
                   (x86 (!memi p-addr37 byte37 x86))
                   (x86 (!memi p-addr38 byte38 x86))
                   (x86 (!memi p-addr39 byte39 x86))
                   (x86 (!memi p-addr40 byte40 x86))
                   (x86 (!memi p-addr41 byte41 x86))
                   (x86 (!memi p-addr42 byte42 x86))
                   (x86 (!memi p-addr43 byte43 x86))
                   (x86 (!memi p-addr44 byte44 x86))
                   (x86 (!memi p-addr45 byte45 x86))
                   (x86 (!memi p-addr46 byte46 x86))
                   (x86 (!memi p-addr47 byte47 x86))
                   (x86 (!memi p-addr48 byte48 x86))
                   (x86 (!memi p-addr49 byte49 x86))
                   (x86 (!memi p-addr50 byte50 x86))
                   (x86 (!memi p-addr51 byte51 x86))
                   (x86 (!memi p-addr52 byte52 x86))
                   (x86 (!memi p-addr53 byte53 x86))
                   (x86 (!memi p-addr54 byte54 x86))
                   (x86 (!memi p-addr55 byte55 x86))
                   (x86 (!memi p-addr56 byte56 x86))
                   (x86 (!memi p-addr57 byte57 x86))
                   (x86 (!memi p-addr58 byte58 x86))
                   (x86 (!memi p-addr59 byte59 x86))
                   (x86 (!memi p-addr60 byte60 x86))
                   (x86 (!memi p-addr61 byte61 x86))
                   (x86 (!memi p-addr62 byte62 x86))
                   (x86 (!memi p-addr63 byte63 x86)))

                (mv nil x86)))


          (mv 'wml512 x86)))

    (mv 'wml512 x86))

  ///

  (defthm x86p-wml512
    (implies (force (x86p x86))
             (x86p (mv-nth 1 (wml512 lin-addr val x86))))
    :hints (("Goal" :in-theory (e/d () (rb x86p force (force) unsigned-byte-p signed-byte-p))))
    :rule-classes (:rewrite :type-prescription)))

|#

;; ======================================================================

(defsection Parametric-Memory-Reads-and-Writes

  :parents (linear-memory)

  :short "Functions to read/write 8/16/32/64/128/256 bits into the memory."

  (local (in-theory (e/d (member-equal) ())))

  (define rml-size ((nbytes :type (member 1 2 4 6 8 10 16 32))
                    (addr   :type (signed-byte #.*max-linear-address-size*))
                    (r-x    :type (member :r :x))
                    (x86))
    :guard (natp nbytes)
    :guard-hints (("Goal" :in-theory (e/d* (signed-byte-p) ())))
    :inline t
    :no-function t
    :enabled t
    (case nbytes
      (1 (rml08 addr r-x x86))
      (2 (rml16 addr r-x x86))
      (4 (rml32 addr r-x x86))
      (6
       ;; Use case: To fetch operands of the form m16:32 (see far jmp
       ;; instruction).
       (rml48 addr r-x x86))
      (8 (rml64 addr r-x x86))
      (10
       ;; Use case: The instructions LGDT and LIDT need to read 10
       ;; bytes at once.
       (rml80 addr r-x x86))
      (16 (rml128 addr r-x x86))
      (32 (rml256 addr r-x x86))
      (otherwise
       (if (mbe :logic (canonical-address-p (+ -1 nbytes addr))
                :exec (< (+ -1 nbytes addr) #.*2^47*))
           (rb nbytes addr r-x x86)
         (mv 'rml-size 0 x86))))

    ///

    (defthm x86p-of-mv-nth-2-of-rml-size
      (implies (force (x86p x86))
               (x86p (mv-nth 2 (rml-size bytes lin-addr r-x x86)))))

    ;; TODO Prove the following after proving the equivalence of rml128
    ;; and rb in system-level view.
    ;; (defthmd rml-size-to-rb
    ;;   (implies (and (canonical-address-p (+ -1 nbytes lin-addr))
    ;;                 (canonical-address-p lin-addr))
    ;;            (b* (((mv flg1 val x86-1)
    ;;                  (rml-size nbytes lin-addr r-x x86))
    ;;                 ((mv flg2 bytes x86-2)
    ;;                  (rb nbytes lin-addr r-x x86)))
    ;;              (and (equal flg1 flg2)
    ;;                   (equal val (if flg1 0 bytes))
    ;;                   (equal x86-1 x86-2))))
    ;;   :hints (("Goal" :in-theory (e/d* (signed-byte-p rml08 rml128 rml32 rml48 rml64 rml80 rml16)
    ;;                                    ()))))
    )

  (define riml-size ((nbytes :type (member 1 2 4 8))
                    (addr   :type (signed-byte #.*max-linear-address-size*))
                    (r-x  :type (member :r :x))
                    (x86))
    :inline t
    :no-function t
    :enabled t
    (case nbytes
      (1 (riml08 addr r-x x86))
      (2 (riml16 addr r-x x86))
      (4 (riml32 addr r-x x86))
      (8 (riml64 addr r-x x86))
      (otherwise
       (mv 'riml-size nbytes x86))))

  (define wml-size ((nbytes :type (member 1 2 4 6 8 10 16 32))
                    (addr   :type (signed-byte #.*max-linear-address-size*))
                    (val    :type (integer 0 *))
                    (x86))
    :guard (case nbytes
             (1  (n08p val))
             (2  (n16p val))
             (4  (n32p val))
             (6  (n48p val))
             (8  (n64p val))
             (10 (n80p val))
             (16 (n128p val))
             (32 (n256p val)))
    :inline t
    :no-function t
    :enabled t
    (case nbytes
      (1 (wml08 addr val x86))
      (2 (wml16 addr val x86))
      (4 (wml32 addr val x86))
      (6
       ;; Use case: To store operands of the form m16:32.
       (wml48 addr val x86))
      (8 (wml64 addr val x86))
      (10
       ;; Use case: Instructions like SGDT and SIDT write 10 bytes to
       ;; the memory.
       (wml80 addr val x86))
      (16 (wml128 addr val x86))
      (32 (wml256 addr val x86))
      (otherwise
       (if (mbe :logic (canonical-address-p (+ -1 nbytes addr))
                :exec (< (+ nbytes addr) #.*2^47-1*))
           (wb nbytes addr :w val x86)
         (mv 'wml-size x86))))

    ///

    (defthm x86p-wml-size
      (implies (force (x86p x86))
               (x86p (mv-nth 1 (wml-size nbytes lin-addr val x86))))
      :hints (("Goal" :in-theory (e/d () (rb force (force) unsigned-byte-p signed-byte-p)))))

    ;; TODO Prove the following after proving the equivalence of wml128
    ;; and wb in system-level view.
    ;; (defthmd wml-size-to-wb
    ;;   (implies (and (canonical-address-p (+ -1 nbytes lin-addr))
    ;;                 (canonical-address-p lin-addr))
    ;;            (b* (((mv flg1 x86-1)
    ;;                  (wml-size nbytes lin-addr val x86))
    ;;                 ((mv flg2 x86-2)
    ;;                  (wb nbytes lin-addr :w val x86)))
    ;;              (and (equal flg1 flg2)
    ;;                   (equal x86-1 x86-2))))
    ;;   :hints (("Goal" :in-theory (e/d* (signed-byte-p
    ;;                                     las-to-pas
    ;;                                     wml08 wml128 wml32 wml48 wml64 wml80 wml16)
    ;;                                    ()))))
    )

  (define wiml-size ((nbytes :type (member 1 2 4 8))
                    (addr   :type (signed-byte #.*max-linear-address-size*))
                    (val    :type integer)
                    (x86))
    :guard (case nbytes
             (1 (i08p val))
             (2 (i16p val))
             (4 (i32p val))
             (8 (i64p val)))
    :inline t
    :no-function t
    :enabled t
    (case nbytes
      (1 (wiml08 addr val x86))
      (2 (wiml16 addr val x86))
      (4 (wiml32 addr val x86))
      (8 (wiml64 addr val x86))
      (otherwise
       (mv 'wiml-size x86)))))

#||

;; The following definitions of rml/wml-size are nicer in one sense that
;; their definition is in terms of rb/wb, unlike in the functions
;; above, where the equivalence of rm/wml-size to rb/wb is established
;; via a theorem.  However, these nicer definitions cause some proofs
;; to fail in decoding-and-spec-utils.lisp, which I'd rather not
;; fix right now.

(define rml-size
  ((nbytes   :type (member 1 2 4 6 8 10 16))
   (lin-addr :type (signed-byte #.*max-linear-address-size*))
   (r-x    :type (member :r :x))
   (x86))
  :guard (natp nbytes)
  :guard-hints (("Goal"
                 :in-theory
                 (e/d* (signed-byte-p rml08 rml128 rml32 rml48 rml64 rml80 rml16)
                       (create-canonical-address-list-1))))
  :inline t
  :no-function t

  (if (mbt (canonical-address-p lin-addr))

      (let* ((last-lin-addr (the (signed-byte 49)
                                 (+ -1 nbytes lin-addr))))
        (if (mbe :logic (canonical-address-p last-lin-addr)
                 :exec (< (the (signed-byte 49) last-lin-addr)
                          #.*2^47*))

            (mbe
             :logic
             (b* (((mv flg bytes x86)
                   (rb (create-canonical-address-list nbytes lin-addr)
                       r-x x86))
                  (result (combine-bytes bytes)))
               (mv flg result x86))

             :exec

             (case nbytes
               (1 (rml08 lin-addr r-x x86))
               (2 (rml16 lin-addr r-x x86))
               (4 (rml32 lin-addr r-x x86))
               (6
                  ;; Use case: To fetch operands of the form m16:32 (see far jmp ; ;
                  ;; instruction). ; ;
                (rml48 lin-addr r-x x86))
               (8 (rml64 lin-addr r-x x86))
               (10
                  ;; Use case: The instructions LGDT and LIDT need to read 10 ; ;
                  ;; bytes at once. ; ;
                (rml80 lin-addr r-x x86))
               (16 (rml128 lin-addr r-x x86))
               (otherwise
                (b* (((mv flg bytes x86)
                      (rb (create-canonical-address-list nbytes lin-addr)
                          r-x x86))
                     ((when flg)
                      (mv flg 0 x86)))
                  (mv nil (combine-bytes bytes) x86)))))

          (mv 'rml-size 0 x86)))
    (mv 'rml-size 0 x86))

  ///

  (defthm x86p-of-mv-nth-2-of-rml-size
    (implies (and (signed-byte-p *max-linear-address-size* lin-addr)
                  (x86p x86))
             (x86p (mv-nth 2 (rml-size bytes lin-addr r-x x86))))))

(define wml-size
  ((nbytes   :type (member 1 2 4 6 8 10 16))
   (lin-addr :type (signed-byte #.*max-linear-address-size*))
   (val      :type (integer 0 *))
   (x86))
  :guard (and (natp nbytes)
              (case nbytes
                (1  (n08p val))
                (2  (n16p val))
                (4  (n32p val))
                (6  (n48p val))
                (8  (n64p val))
                (10 (n80p val))
                (16 (n128p val))))
  :guard-hints (("Goal" :in-theory (e/d* (signed-byte-p
                                          las-to-pas
                                          byte-ify
                                          wml08 wml128 wml32 wml48 wml64 wml80 wml16)
                                         ())))
  :inline t
  :no-function t
  (if (mbt (canonical-address-p lin-addr))
      (let* ((last-lin-addr (the (signed-byte 49)
                              (+ -1 nbytes lin-addr))))
        (if
            (mbe :logic (canonical-address-p last-lin-addr)
                 :exec (< (the (signed-byte 49) last-lin-addr)
                          #.*2^47*))
            (mbe
             :logic
             (wb (create-addr-bytes-alist
                  (create-canonical-address-list nbytes lin-addr)
                  (byte-ify nbytes val))
                 x86)
             :exec
             (case nbytes
               (1 (wml08 lin-addr val x86))
               (2 (wml16 lin-addr val x86))
               (4 (wml32 lin-addr val x86))
               (6
                  ;; Use case: To store operands of the form m16:32. ;
                (wml48 lin-addr val x86))
               (8 (wml64 lin-addr val x86))
               (10
                  ;; Use case: Instructions like SGDT and SIDT write 10 bytes to ;
                  ;; the memory. ;
                (wml80 lin-addr val x86))
               (16 (wml128 lin-addr val x86))
               (otherwise
                (wb (create-addr-bytes-alist
                     (create-canonical-address-list nbytes lin-addr)
                     (byte-ify nbytes val))
                    x86))))

          (mv 'wml-size x86)))
    (mv 'wml-size x86))

  ///

  (defthm x86p-wml-size
    (implies (force (x86p x86))
             (x86p (mv-nth 1 (wml-size nbytes lin-addr val x86))))
    :hints (("Goal" :in-theory (e/d () (rb force (force) unsigned-byte-p signed-byte-p))))))

||#

;; ======================================================================

;; Writing canonical address to memory:

;; A short note on why I couldn't make do with wiml64 to write a
;; canonical address to the memory:

;; Here's a small, compelling example.  The following is some
;; information provided by profile when running fib(24); here, wiml64
;; was used to store a canonical address in the memory in the
;; specification of the CALL (#xE8) instruction.

;; (defun X86ISA::X86-CALL-E8-OP/EN-M calls     7.50E+4
;; ...
;; Heap bytes allocated                         4.80E+6; 33.3%
;; Heap bytes allocated per call                64

;; So, for fib(24), 4,801,792 bytes are allocated on the heap!  And
;; this is with paging turned off.

;; The reason why wiml64 uses such a lot of memory is because it
;; creates bignums all the time.  But when I have to store a canonical
;; address in the memory, I *know* that I'm storing a quantity lesser
;; than 64-bits.  Thus, I use write-canonical-address-to-memory to
;; avoid the creation of bignums.  Like the other rm* and wm*
;; functions, I have an MBE inside write-canonical-address-to-memory,
;; where the :logic part is defined in terms of WB.

;; Note that write-canonical-address-to-memory is optimized in the
;; application-level view only --- in the system-level mode, it's
;; merely a call of wml64.

(define write-canonical-address-to-memory-user-exec
  ((lin-addr          :type (signed-byte  #.*max-linear-address-size*))
   (canonical-address :type (signed-byte  #.*max-linear-address-size*))
   (x86))

  :inline t
  :no-function t
  :parents (linear-memory)

  :guard (and (canonical-address-p lin-addr)
              (canonical-address-p (+ 7 lin-addr))
              (app-view x86))
  :guard-hints (("Goal" :in-theory (e/d (n16-to-i16 member-equal)
                                        ())))

  (if (mbt (and (app-view x86)
                (canonical-address-p (+ 7 lin-addr))))

      (b* (((the (unsigned-byte 32) canonical-address-low-nat)
            (n32 canonical-address))
           ((the (signed-byte 32) canonical-address-high-int)
            (mbe
             :logic
             (n16-to-i16 (part-select canonical-address :low 32 :high 47))
             :exec
             (the (signed-byte 16)
                  (ash canonical-address -32))))
           ((mv flg0 x86)
            (wml32 lin-addr canonical-address-low-nat x86))
           ((the (signed-byte #.*max-linear-address-size+1*) next-addr)
            (+ 4 lin-addr))
           ((when (mbe :logic (not (canonical-address-p next-addr))
                       :exec (<= #.*2^47*
                                 (the (signed-byte
                                       #.*max-linear-address-size+1*)
                                      next-addr))))
            (mv 'wml64-canonical-address-user-view x86))
           ((mv flg1 x86)
            (wiml32 next-addr canonical-address-high-int x86))
           ((when (or flg0 flg1))
            (mv 'wml64-canonical-address-user-view x86)))
        (mv nil x86))

    (mv 'unreachable x86)))

(local
  (defthmd wb-1-in-app-view
           (implies (and (x86p x86)
                         (app-view x86)
                         (canonical-address-p lin-addr)
                         (canonical-address-p (+ -1 n lin-addr)))
                    (equal (wb-1 n lin-addr w val x86)
                           (mv nil (mv-nth 1 (wb-1 n lin-addr w val x86)))))
           :hints (("Goal" :in-theory (e/d* (wvm08) ())))))

(local
  (defthm write-canonical-address-to-memory-user-exec-and-wb
          (implies (and (app-view x86)
                        (canonical-address-p lin-addr)
                        (canonical-address-p canonical-address)
                        (canonical-address-p (+ 7 lin-addr))
                        (x86p x86))
                   (equal (write-canonical-address-to-memory-user-exec
                            lin-addr canonical-address x86)
                          (wb 8 lin-addr :w (loghead 64 canonical-address) x86)))
          :hints (("Goal"
                   :use ((:instance split-wb-in-app-view
                                    (i 4)
                                    (j 4)
                                    (w :w)
                                    (lin-addr lin-addr)
                                    (val (loghead 64 canonical-address)))
                         (:instance wb-1-in-app-view
                                    (n 8)
                                    (lin-addr lin-addr)
                                    (w :w)
                                    (val (loghead 64 canonical-address))))
                   :in-theory (e/d*
                                (write-canonical-address-to-memory-user-exec
                                  wiml32
                                  wml32
                                  wb-and-wvm64
                                  wb-1)
                                ())))))

(define write-canonical-address-to-memory
  ((lin-addr          :type (signed-byte #.*max-linear-address-size*))
   (canonical-address :type (signed-byte #.*max-linear-address-size*))
   (x86))

  :parents (linear-memory)
  :guard-hints (("Goal" :in-theory (e/d (n16-to-i16)
                                        ())))

  (let* ((7+lin-addr (the (signed-byte #.*max-linear-address-size+2*)
                          (+ 7 lin-addr))))


    (if (mbe :logic (canonical-address-p 7+lin-addr)
             :exec (< (the (signed-byte #.*max-linear-address-size+2*)
                           7+lin-addr)
                      #.*2^47*))


      (if (app-view x86)

        (mbe :logic
             (wb 8 lin-addr :w (loghead 64 canonical-address) x86)
             :exec
             (write-canonical-address-to-memory-user-exec
               lin-addr canonical-address x86))

        (b* ((canonical-address-unsigned-val
               (mbe :logic (loghead 64 canonical-address)
                    :exec (logand #.*2^64-1* canonical-address))))
            ;; Note that calling wml64 here will be a tad expensive ---
            ;; for one, there's an extra function call. Also, the
            ;; app-view field will have to be checked
            ;; again inside wml64. However, this is better for
            ;; reasoning than laying down the code again. As it is,
            ;; performance in the system-level view is quite less than
            ;; that in application-level view.
            (wml64 lin-addr canonical-address-unsigned-val x86)))

      (mv 'write-canonical-address-to-memory-error x86)))

  ///

  (defthm x86p-write-canonical-address-to-memory
          (implies (force (x86p x86))
                   (x86p (mv-nth
                           1
                           (write-canonical-address-to-memory
                             lin-addr canonical-address x86))))
          :rule-classes (:rewrite :type-prescription)))

;; ======================================================================

(defsection program-location
  :parents (linear-memory)

  (define byte-listp (x)
    :parents (linear-memory)
    :short "Recognizer of a list of bytes"
    :enabled t
    (if (equal x nil)
        t
      (and (consp x)
           (n08p (car x))
           (byte-listp (cdr x))))
    ///

    (defthm byte-listp-implies-true-listp
      (implies (byte-listp x)
               (true-listp x))
      :rule-classes :forward-chaining)

    (defthm-unsigned-byte-p n08p-element-of-byte-listp
      :hyp (and (byte-listp acc)
                (natp m)
                (< m (len acc)))
      :bound 8
      :concl (nth m acc)
      :gen-linear t
      :gen-type t)

    (defthm repeat-byte-listp
      (implies (unsigned-byte-p 8 m)
               (byte-listp (acl2::repeat n m)))
      :hints (("Goal" :in-theory (e/d (acl2::repeat) ())))
      :rule-classes (:type-prescription :rewrite))

    (defthm len-of-nthcdr-byte-listp
      (implies (and (< m (len acc))
                    (natp m))
               (equal (len (nthcdr m acc))
                      (- (len acc) m))))

    (defthm byte-listp-revappend
      (implies (forced-and (byte-listp lst1)
                           (byte-listp lst2))
               (byte-listp (revappend lst1 lst2)))
      :rule-classes :type-prescription)

    (defthm true-listp-make-list-ac
      (implies (true-listp ac)
               (true-listp (make-list-ac n val ac)))
      :rule-classes :type-prescription)

    (defthm reverse-byte-listp
      (implies (byte-listp x)
               (byte-listp (reverse x)))
      :rule-classes (:type-prescription :rewrite))

    (defthm byte-listp-append
      (implies (forced-and (byte-listp lst1)
                           (byte-listp lst2))
               (byte-listp (append lst1 lst2)))
      :rule-classes (:rewrite :type-prescription))

    (defthm make-list-ac-byte-listp
      (implies (and (byte-listp x)
                    (n08p m))
               (byte-listp (make-list-ac n m x)))
      :rule-classes (:type-prescription :rewrite)))

  (define combine-bytes (bytes)
    :short "Combine a list of bytes, LSB-first, into a single unsigned number"
    :guard (byte-listp bytes)
    :enabled t
    (if (endp bytes)
        0
      ;; (logior (car bytes) (ash (combine-bytes (cdr bytes)) 8))
      (logapp 8 (if (mbt (unsigned-byte-p 8 (car bytes)))
                    (car bytes)
                  0)
              (combine-bytes (cdr bytes))))

    ///
    (defthm natp-combine-bytes
      (implies (force (byte-listp bytes))
               (natp (combine-bytes bytes)))
      :rule-classes :type-prescription)

    (local
     (defthm ash-n-3-+-8-lemma
       (implies (natp n)
                (equal (ash (+ 1 n) 3) (+ 8 (ash n 3))))
       :hints (("goal" :in-theory (e/d* (bitops::ihsext-inductions
                                         bitops::ihsext-recursive-redefs
                                         ash floor)
                                        ())))))

    (defthm unsigned-byte-p-of-combine-bytes
      (implies (and (equal n (ash (len bytes) 3))
                    (byte-listp bytes))
               (unsigned-byte-p n (combine-bytes bytes)))
      :hints (("Goal" :in-theory (e/d (unsigned-byte-p logapp) ())))
      :rule-classes ((:rewrite)
                     (:linear
                      :corollary
                      (implies (and (equal n (ash (len bytes) 3))
                                    (byte-listp bytes))
                               (<= 0 (combine-bytes bytes))))))

    (defthm size-of-combine-bytes
      (implies (and (equal l (len bytes))
                    (byte-listp bytes))
               (< (combine-bytes bytes) (expt 2 (ash l 3))))
      :hints (("Goal"
               :use ((:instance unsigned-byte-p-of-combine-bytes
                                (n (ash (len bytes) 3))))
               :in-theory (e/d* () (unsigned-byte-p-of-combine-bytes))))
      :rule-classes :linear))

  (local (include-book "std/lists/nthcdr" :dir :system))
  (local (include-book "std/lists/take" :dir :system))

  (defthm byte-listp-of-nthcdr
    (implies (byte-listp xs)
             (byte-listp (nthcdr n xs))))

  (defthm byte-listp-of-take
    (implies (and (byte-listp xs)
                  (<= n (len xs)))
             (byte-listp (take n xs))))

  (define combine-n-bytes ((low  natp "Index of the first byte")
                           (num  natp "Number of bytes to combine,
                                       starting at @('pos')")
                           (bytes byte-listp "LSB first"))
    :guard (<= (+ low num) (len bytes))
    :enabled t
    (if (mbt (and (<= (+ low num) (len bytes))
                  (byte-listp bytes)
                  (natp low)
                  (natp num)))
        (combine-bytes (take num (nthcdr low bytes)))
      0)

    ///

    (local
     (defthm repeat-nil-not-byte-listp
       (implies (not (zp n))
                (not (byte-listp (acl2::repeat n nil))))
       :hints (("Goal" :in-theory (e/d (acl2::repeat) ())))))

    (defthm combine-bytes-and-take-degenerate-case-1
      (implies (zp n) (equal (combine-bytes (take n bytes)) 0)))

    (defthm combine-bytes-and-take-degenerate-case-2
      (equal (combine-bytes (take n nil)) 0)
      :hints (("goal" :in-theory (e/d (acl2::repeat) ()))))

    (defthm natp-of-combine-bytes-of-take
      (implies (byte-listp bytes)
               (<= 0 (combine-bytes (take num bytes))))
      :hints (("Goal" :in-theory (e/d* () (force (force))))))

    (defthm natp-combine-n-bytes
      (implies (force (byte-listp bytes))
               (natp (combine-n-bytes low num bytes)))
      :hints (("Goal" :in-theory (e/d* () (force (force)))))
      :rule-classes
      ((:type-prescription)
       (:linear
        :corollary
        (implies (byte-listp bytes)
                 (<= 0 (combine-n-bytes low num bytes))))))

    (defthm unsigned-byte-p-of-combine-n-bytes
      (implies (and (equal n (ash num 3)) (natp num))
               (unsigned-byte-p n (combine-n-bytes low num bytes)))
      :hints (("Goal"
               :do-not-induct t
               :use ((:instance unsigned-byte-p-of-combine-bytes
                                (n (ash num 3))
                                (bytes (take num (nthcdr low bytes)))))
               :in-theory (e/d* () (unsigned-byte-p-of-combine-bytes)))))

    (defthm size-of-combine-n-bytes
      (< (combine-n-bytes low num bytes) (expt 2 (ash num 3)))
      :hints (("Goal"
               :do-not-induct t
               :use ((:instance unsigned-byte-p-of-combine-n-bytes
                                (n (ash num 3))))
               :in-theory (e/d () (unsigned-byte-p-of-combine-n-bytes))))
      :rule-classes :linear))

  (define program-at (prog-addr bytes x86)

    :parents (linear-memory)
    :non-executable t

    :short "Predicate that makes a statement about a program's location
    in the memory"
    :long "<p>We use @('program-at') to state that a program, given by
    as a list of @('bytes'), is located at contiguous addresses from
    @('prog-addr') to @('(len bytes) + prog-addr - 1') in the memory of
    the x86 state.  Note that this function is non-executable; we use it
    only for reasoning about machine-code.</p>"
    :guard (and (canonical-address-p prog-addr)
                (canonical-address-p (+ -1 (len bytes) prog-addr))
                (byte-listp bytes))

    (b* (((mv flg bytes-read ?x86)
          (rb (len bytes) prog-addr :x x86)))
        (and
          (equal flg        nil)

          ;; (combine-n-bytes 2 3 '(#xAA #xBB #xCC #xDD #xEE))
          ;; ==
          ;; (part-select (combine-bytes '(#xAA #xBB #xCC #xDD #xEE))
          ;;              :low (ash 2 3) :width (ash 3 3))

          ;; I prefer combine-n-bytes here instead of combine-bytes
          ;; because combine-n-bytes lets me think of subseqs of a list
          ;; in the same way I think about slices of a number a la
          ;; part-select.
          (equal bytes-read (combine-n-bytes 0 (len bytes) bytes))))

    ///

    (defthm program-at-xw-in-app-view
            (implies (and (app-view x86)
                          (not (equal fld :mem))
                          (not (equal fld :app-view)))
                     (equal (program-at addr bytes (xw fld index value x86))
                            (program-at addr bytes x86)))
            :hints (("Goal" :in-theory (e/d* () (rb)))))))

;; ======================================================================
