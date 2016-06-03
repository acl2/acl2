;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "../utilities/system-level-mode/marking-mode-top")

(include-book "centaur/bitops/ihs-extensions" :dir :system)
(include-book "centaur/bitops/signed-byte-p" :dir :system)
(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

;; ======================================================================

;; Misc. lemmas that need a proper home:

(encapsulate
  ()

  ;; Rewriting read-from-physical-memory to rm-low-64:

  (local
   (defthm loghead-n-ash-x-m-where-m>=n
     (implies (and (natp n)
                   (natp m)
                   (<= n m))
              (equal (loghead n (ash x m))
                     0))
     :hints (("Goal" :in-theory
              (e/d* (ihsext-inductions ihsext-recursive-redefs)
                    ())))))

  (local
   (defthm logtail-n-memi-where-n>=8
     (implies (and (x86p x86)
                   (natp n)
                   (<= 8 n))
              (equal (logtail n (xr :mem index x86)) 0))
     :hints (("Goal" :in-theory
              (e/d* (ihsext-inductions ihsext-recursive-redefs)
                    ())))))

  (local
   (defthm rewrite-read-from-physical-memory-to-rm-low-64-helper-1
     (implies (and (not (programmer-level-mode x86))
                   (physical-address-p index)
                   (x86p x86))
              (equal (loghead 8 (rm-low-64 index x86))
                     (xr :mem index x86)))
     :hints (("Goal" :in-theory (e/d* (rm-low-64
                                       rm-low-32)
                                      ())))))

  (local
   (defthm rewrite-read-from-physical-memory-to-rm-low-64-helper-2
     (implies (and (not (programmer-level-mode x86))
                   (physical-address-p index)
                   (x86p x86))
              (equal (loghead 8 (logtail 8 (rm-low-64 index x86)))
                     (xr :mem (1+ index) x86)))
     :hints (("Goal" :in-theory (e/d* (rm-low-64
                                       rm-low-32)
                                      ())))))
  (local
   (defthm rewrite-read-from-physical-memory-to-rm-low-64-helper-3
     (implies (and (not (programmer-level-mode x86))
                   (physical-address-p index)
                   (x86p x86))
              (equal (loghead 8 (logtail 16 (rm-low-64 index x86)))
                     (xr :mem (+ 2 index) x86)))
     :hints (("Goal" :in-theory (e/d* (rm-low-64
                                       rm-low-32)
                                      ())))))
  (local
   (defthm rewrite-read-from-physical-memory-to-rm-low-64-helper-4
     (implies (and (not (programmer-level-mode x86))
                   (physical-address-p index)
                   (x86p x86))
              (equal (loghead 8 (logtail 24 (rm-low-64 index x86)))
                     (xr :mem (+ 3 index) x86)))
     :hints (("Goal" :in-theory (e/d* (rm-low-64
                                       rm-low-32)
                                      ())))))
  (local
   (defthm rewrite-read-from-physical-memory-to-rm-low-64-helper-5
     (implies (and (not (programmer-level-mode x86))
                   (physical-address-p index)
                   (x86p x86))
              (equal (loghead 8 (logtail 32 (rm-low-64 index x86)))
                     (xr :mem (+ 4 index) x86)))
     :hints (("Goal" :in-theory (e/d* (rm-low-64
                                       rm-low-32)
                                      ())))))
  (local
   (defthm rewrite-read-from-physical-memory-to-rm-low-64-helper-6
     (implies (and (not (programmer-level-mode x86))
                   (physical-address-p index)
                   (x86p x86))
              (equal (loghead 8 (logtail 40 (rm-low-64 index x86)))
                     (xr :mem (+ 5 index) x86)))
     :hints (("Goal" :in-theory (e/d* (rm-low-64
                                       rm-low-32)
                                      ())))))
  (local
   (defthm rewrite-read-from-physical-memory-to-rm-low-64-helper-7
     (implies (and (not (programmer-level-mode x86))
                   (physical-address-p index)
                   (x86p x86))
              (equal (loghead 8 (logtail 48 (rm-low-64 index x86)))
                     (xr :mem (+ 6 index) x86)))
     :hints (("Goal" :in-theory (e/d* (rm-low-64
                                       rm-low-32)
                                      ())))))
  (local
   (defthm rewrite-read-from-physical-memory-to-rm-low-64-helper-8
     (implies (and (not (programmer-level-mode x86))
                   (physical-address-p index)
                   (x86p x86))
              (equal (logtail 56 (rm-low-64 index x86))
                     (xr :mem (+ 7 index) x86)))
     :hints (("Goal" :in-theory (e/d* (rm-low-64
                                       rm-low-32)
                                      ())))))

  (local
   (defthmd rewrite-read-from-physical-memory-to-rm-low-64-helper
     (implies (and (physical-address-p index)
                   (equal p-addrs
                          (list index (+ 1 index)
                                (+ 2 index)
                                (+ 3 index)
                                (+ 4 index)
                                (+ 5 index)
                                (+ 6 index)
                                (+ 7 index)))
                   (not (programmer-level-mode x86))
                   (x86p x86))
              (equal (read-from-physical-memory p-addrs x86)
                     (byte-ify 8 (rm-low-64 index x86))))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d* (read-from-physical-memory
                                byte-ify)
                               ())))))

  (defthmd rewrite-read-from-physical-memory-to-rm-low-64
    (implies (and (equal p-addrs (addr-range 8 index))
                  (physical-address-p index)
                  (not (programmer-level-mode x86))
                  (x86p x86))
             (equal (read-from-physical-memory p-addrs x86)
                    (byte-ify 8 (rm-low-64 (car p-addrs) x86))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance rewrite-read-from-physical-memory-to-rm-low-64-helper
                              (index (car p-addrs))))
             :in-theory (e/d* (create-physical-address-list
                               physical-address-listp
                               unsigned-byte-p)
                              ())))))

(def-gl-export canonical-address-p-of-lin-addr+7
  :hyp (and (canonical-address-p lin-addr)
            (equal (loghead 3 lin-addr) 0))
  :concl (canonical-address-p (+ 7 lin-addr))
  :g-bindings
  (gl::auto-bindings (:mix (:nat lin-addr 64))))

(defthmd xlate-equiv-entries-and-rm-low-64-with-xlate-equiv-memory
  (implies (and (bind-free
                 (find-an-xlate-equiv-x86
                  'read-from-physical-memory-and-xlate-equiv-memory
                  x86-1 'x86-2 mfc state)
                 (x86-2))
                (xlate-equiv-memory x86-1 x86-2)
                (physical-address-p index)
                (equal (loghead 3 index) 0))
           (xlate-equiv-entries (rm-low-64 index x86-1)
                                (rm-low-64 index x86-2)))
  :hints (("Goal"
           :cases ((disjoint-p (addr-range 8 index)
                               (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86-1))))
           :use ((:instance xlate-equiv-structures-and-xlate-equiv-entries))
           :in-theory (e/d* (xlate-equiv-memory)
                            ()))))

(defthm read-from-physical-memory-after-mv-nth-2-las-to-pas
  (implies
   (and (disjoint-p p-addrs (all-translation-governing-addresses l-addrs (double-rewrite x86)))
        (canonical-address-listp l-addrs))
   (equal (read-from-physical-memory p-addrs (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
          (read-from-physical-memory p-addrs x86)))
  :hints (("Goal"
           :in-theory (e/d* (read-from-physical-memory
                             las-to-pas
                             all-translation-governing-addresses
                             physical-address-listp
                             disjoint-p)
                            ()))))

(defthm mv-nth-1-rb-after-mv-nth-2-rb-alt
;;; !!! So expensive!!
  (implies
   (and
    (disjoint-p
     (mv-nth 1 (las-to-pas l-addrs-1 r-w-x-1 (cpl x86) (double-rewrite x86)))
     (all-translation-governing-addresses l-addrs-2 (double-rewrite x86)))
    (disjoint-p
     (mv-nth 1 (las-to-pas l-addrs-1 r-w-x-1 (cpl x86) (double-rewrite x86)))
     (all-translation-governing-addresses l-addrs-1 (double-rewrite x86)))
    (canonical-address-listp l-addrs-1))
   (equal (mv-nth 1 (rb l-addrs-1 r-w-x-1 (mv-nth 2 (rb-alt l-addrs-2 r-w-x-2 x86))))
          (mv-nth 1 (rb l-addrs-1 r-w-x-1 x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (rb rb-alt) (rewrite-rb-to-rb-alt)))))

(defthm mv-nth-2-get-prefixes-alt-no-prefix-byte
  (implies
   (and (let*
            ((flg (mv-nth 0 (rm08 start-rip :x x86)))
             (prefix-byte-group-code
              (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))))
          (and (not flg)
               (zp prefix-byte-group-code)))
        (not (zp cnt))
        (not (mv-nth 0
                     (las-to-pas
                      (create-canonical-address-list cnt start-rip)
                      :x (cpl x86) (double-rewrite x86))))
        (disjoint-p
         (mv-nth 1
                 (las-to-pas (create-canonical-address-list cnt start-rip)
                             :x (cpl x86) (double-rewrite x86)))
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses (double-rewrite x86)))))
   (equal (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86))
          (mv-nth 2 (las-to-pas (list start-rip) :x (cpl x86) x86))))
  :hints
  (("Goal" :in-theory (e/d* (get-prefixes-alt get-prefixes rm08 las-to-pas)
                            (rewrite-get-prefixes-to-get-prefixes-alt)))))

(defthm mv-nth-1-rb-after-mv-nth-2-get-prefixes-alt-no-prefix-byte
  ;; The zeroCopy program has no instructions that have any prefix
  ;; bytes.
  (implies
   (and
    (disjoint-p (mv-nth 1 (las-to-pas l-addrs-1 r-w-x-1 (cpl x86) (double-rewrite x86)))
                (all-translation-governing-addresses
                 (create-canonical-address-list cnt start-rip)
                 (double-rewrite x86)))
    (disjoint-p
     (mv-nth 1 (las-to-pas l-addrs-1 r-w-x-1 (cpl x86) (double-rewrite x86)))
     (all-translation-governing-addresses l-addrs-1 (double-rewrite x86)))
    (let*
        ((flg (mv-nth 0 (rm08 start-rip :x x86)))
         (prefix-byte-group-code
          (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))))
      (and (not flg) (zp prefix-byte-group-code)))
    (not (zp cnt))
    (not (mv-nth 0 (las-to-pas
                    (create-canonical-address-list cnt start-rip) :x (cpl x86)
                    (double-rewrite x86))))
    (disjoint-p
     (mv-nth 1 (las-to-pas (create-canonical-address-list cnt start-rip)
                           :x (cpl x86) (double-rewrite x86)))
     (open-qword-paddr-list (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
    (canonical-address-p start-rip)
    (canonical-address-listp l-addrs-1)
    (not (xr :programmer-level-mode 0 x86)))
   (equal (mv-nth 1 (rb l-addrs-1 r-w-x-1 (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86))))
          (mv-nth 1 (rb l-addrs-1 r-w-x-1 x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (rb all-translation-governing-addresses)
                            (rewrite-get-prefixes-to-get-prefixes-alt
                             force (force))))))

(defthm mv-nth-1-rb-after-mv-nth-2-las-to-pas
  (implies
   (and
    (disjoint-p
     (mv-nth 1 (las-to-pas l-addrs-1 r-w-x-1 (cpl x86) (double-rewrite x86)))
     (all-translation-governing-addresses l-addrs-2 (double-rewrite x86)))
    (disjoint-p
     (mv-nth 1 (las-to-pas l-addrs-1 r-w-x-1 (cpl x86) (double-rewrite x86)))
     (all-translation-governing-addresses l-addrs-1 (double-rewrite x86)))
    (not (xr :programmer-level-mode 0 x86))
    (canonical-address-listp l-addrs-1)
    (canonical-address-listp l-addrs-2))
   (equal (mv-nth 1 (rb l-addrs-1 r-w-x-1 (mv-nth 2 (las-to-pas l-addrs-2 r-w-x-2 cpl-2 x86))))
          (mv-nth 1 (rb l-addrs-1 r-w-x-1 (double-rewrite x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (rb) (rewrite-rb-to-rb-alt force (force))))))

;; ======================================================================

;; Introducing the system-level program:

;;  1 mov %cr3,%rax
;;  2 mov %rax,-0x18(%rsp)
;;  3 mov -0x18(%rsp),%rdx
;;  4 mov %rdi,%rax
;;  5 shr $0x24,%rax
;;  6 and $0xff8,%eax
;;  7 and $0xfffffffffffff000,%rdx
;;  8 or %rdx,%rax
;;  9 mov (%rax),%rax
;; 10 test $0x1,%al
;; 11 je 400780 <rewire_dst_to_src+0x100>
;; 12 shr $0xc,%rax
;; 13 movabs $0xffffffffff,%r8
;; 14 mov %rdi,%rcx
;; 15 and %r8,%rax
;; 16 shr $0x1b,%rcx
;; 17 and $0xff8,%ecx
;; 18 shl $0xc,%rax
;; 19 or %rcx,%rax
;; 20 mov (%rax),%rax
;; 21 mov %rax,%rcx
;; 22 and $0x81,%ecx
;; 23 cmp $0x81,%rcx
;; 24 jne 400780 <rewire_dst_to_src+0x100>
;; 25 mov %rsi,%rcx
;; 26 movabs $0xfffffc0000000,%r9
;; 27 shr $0x24,%rcx
;; 28 and %rax,%r9
;; 29 and $0xff8,%ecx
;; 30 or %rdx,%rcx
;; 31 mov (%rcx),%rax
;; 32 test $0x1,%al
;; 33 je 400780 <rewire_dst_to_src+0x100>
;; 34 shr $0xc,%rax
;; 35 mov %rsi,%rdx
;; 36 and %r8,%rax
;; 37 shr $0x1b,%rdx
;; 38 and $0xff8,%edx
;; 39 shl $0xc,%rax
;; 40 or %rdx,%rax
;; 41 movabs $0xfff000003fffffff,%rdx
;; 42 and (%rax),%rdx
;; 43 or %r9,%rdx
;; 44 mov %rdx,(%rax)
;; 45 mov %rdx,%rax
;; 46 and $0x81,%eax
;; 47 cmp $0x81,%rax
;; 48 jne 400780 <rewire_dst_to_src+0x100>
;; 49 movabs $0xfffffc0000000,%rax
;; 50 and $0x3fffffff,%esi
;; 51 and $0x3fffffff,%edi
;; 52 and %rax,%rdx
;; 53 or %r9,%rdi
;; 54 xor %eax,%eax
;; 55 or %rsi,%rdx
;; 56 cmp %rdx,%rdi
;; 57 sete %al
;; 58 retq
;; 59 nopw %cs:0x0(%rax,%rax,1)
;; 60 mov $0xffffffffffffffff,%rax
;; 61 retq
;; 62 nopl 0x0(%rax,%rax,1)

(defconst *rewire_dst_to_src*

  '(#xF #x20 #xD8 #x48 #x89 #x44 #x24 #xE8
        #x48 #x8B #x54 #x24 #xE8 #x48 #x89 #xF8
        #x48 #xC1 #xE8 #x24 #x25 #xF8 #xF #x0
        #x0 #x48 #x81 #xE2 #x0 #xF0 #xFF #xFF
        #x48 #x9 #xD0 #x48 #x8B #x0 #xA8 #x1
        #xF #x84 #xD2 #x0 #x0 #x0 #x48 #xC1 #xE8
        #xC #x49 #xB8 #xFF #xFF #xFF #xFF #xFF
        #x0 #x0 #x0 #x48 #x89 #xF9 #x4C #x21
        #xC0 #x48 #xC1 #xE9 #x1B #x81 #xE1 #xF8
        #xF #x0 #x0 #x48 #xC1 #xE0 #xC #x48 #x9
        #xC8 #x48 #x8B #x0 #x48 #x89 #xC1 #x81
        #xE1 #x81 #x0 #x0 #x0 #x48 #x81 #xF9
        #x81 #x0 #x0 #x0 #xF #x85 #x94 #x0 #x0
        #x0 #x48 #x89 #xF1 #x49 #xB9 #x0 #x0 #x0
        #xC0 #xFF #xFF #xF #x0 #x48 #xC1 #xE9
        #x24 #x49 #x21 #xC1 #x81 #xE1 #xF8 #xF
        #x0 #x0 #x48 #x9 #xD1 #x48 #x8B #x1 #xA8
        #x1 #x74 #x70 #x48 #xC1 #xE8 #xC #x48
        #x89 #xF2 #x4C #x21 #xC0 #x48 #xC1 #xEA
        #x1B #x81 #xE2 #xF8 #xF #x0 #x0 #x48
        #xC1 #xE0 #xC #x48 #x9 #xD0 #x48 #xBA
        #xFF #xFF #xFF #x3F #x0 #x0 #xF0 #xFF
        #x48 #x23 #x10 #x4C #x9 #xCA #x48 #x89
        #x10 #x48 #x89 #xD0 #x25 #x81 #x0 #x0
        #x0 #x48 #x3D #x81 #x0 #x0 #x0 #x75 #x32
        #x48 #xB8 #x0 #x0 #x0 #xC0 #xFF #xFF
        #xF #x0 #x81 #xE6 #xFF #xFF #xFF #x3F
        #x81 #xE7 #xFF #xFF #xFF #x3F #x48 #x21
        #xC2 #x4C #x9 #xCF #x31 #xC0 #x48 #x9
        #xF2 #x48 #x39 #xD7 #xF #x94 #xC0 #xC3
        #x66 #x2E #xF #x1F #x84 #x0 #x0 #x0 #x0
        #x0 #x48 #xC7 #xC0 #xFF #xFF #xFF #xFF
        #xC3 #xF #x1F #x84 #x0 #x0 #x0 #x0 #x0))

(defconst *rewire_dst_to_src-len* (len *rewire_dst_to_src*))

(defun rewire_dst_to_src-clk () 58)

;; ======================================================================

;; Control printing:
(acl2::add-untranslate-pattern-function
 (program-at (create-canonical-address-list 272 (xr :rip 0 x86))
             '(15 32 216 72 137 68 36 232 72 139 84 36 232
                  72 137 248 72 193 232 36 37 248 15 0 0
                  72 129 226 0 240 255 255 72 9 208 72 139
                  0 168 1 15 132 210 0 0 0 72 193 232 12
                  73 184 255 255 255 255 255 0 0 0 72 137
                  249 76 33 192 72 193 233 27 129 225 248
                  15 0 0 72 193 224 12 72 9 200 72 139 0
                  72 137 193 129 225 129 0 0 0 72 129 249
                  129 0 0 0 15 133 148 0 0 0 72 137 241
                  73 185 0 0 0 192 255 255 15 0 72 193 233
                  36 73 33 193 129 225 248 15 0 0 72 9 209
                  72 139 1 168 1 116 112 72 193 232 12 72
                  137 242 76 33 192 72 193 234 27 129 226
                  248 15 0 0 72 193 224 12 72 9 208 72 186
                  255 255 255 63 0 0 240 255 72 35 16 76
                  9 202 72 137 16 72 137 208 37 129 0 0 0
                  72 61 129 0 0 0 117 50 72 184 0 0 0 192
                  255 255 15 0 129 230 255 255 255 63 129
                  231 255 255 255 63 72 33 194 76 9 207
                  49 192 72 9 242 72 57 215 15 148 192 195
                  102 46 15 31 132 0 0 0 0 0 72 199 192
                  255 255 255 255 195 15 31 132 0 0 0 0 0)
             x86)
 (program-at (create-canonical-address-list (len *rewire_dst_to_src*) (xr :rip 0 x86))
             *rewire_dst_to_src*
             x86))

;; ======================================================================

;; Proof of rewire_dst_to_src effects theorem:

(defthm loghead-negative
  (implies (and (syntaxp (and (quotep n)
                              (< (cadr n) 0)))
                (< n 0)
                (integerp n))
           (equal (loghead n x) 0)))

(defthm-usb n52p-of-pml4-table-base-addr
  :hyp (x86p x86)
  :bound 52
  :concl (pml4-table-base-addr x86))

(defthm pml4-table-base-addr-and-mv-nth-1-wb
  (equal (pml4-table-base-addr (mv-nth 1 (wb addr-lst x86)))
         (pml4-table-base-addr x86)))

(defun-nx pdpt-base-addr (lin-addr x86)
  ;; Note that an existing function pdpt-base-addr is
  ;; defined in terms of rm-low-64, and hence, doesn't help for this
  ;; proof.
  (ash (loghead 40 (logtail
                    12
                    (combine-bytes
                     (mv-nth 1 (rb
                                (create-canonical-address-list
                                 8
                                 (pml4-table-entry-addr
                                  lin-addr
                                  (pml4-table-base-addr x86)))
                                :r x86)))))
       12))

;; The following is really a consequence of keeping
;; pdpt-base-addr enabled.
(defthm unsigned-byte-p-52-of-left-shifting-a-40-bit-vector-by-12
  (implies (unsigned-byte-p 64 x)
           (unsigned-byte-p 52 (ash (loghead 40 (logtail 12 x)) 12))))

(defthm pdpt-base-addr-and-mv-nth-1-wb
  (implies (and
            ;; The physical addresses corresponding to the PML4TE are
            ;; disjoint from the physical addresses pertaining to the
            ;; write.
            (disjoint-p$
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
                        :r (cpl x86) x86))
             (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
            ;; The physical addresses corresponding to the PML4TE are
            ;; disjoint from the translation-governing addresses
            ;; pertaining to the PML4TE.
            (disjoint-p$
             (mv-nth
              1
              (las-to-pas
               (create-canonical-address-list
                8
                (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
               :r (cpl x86) (double-rewrite x86)))
             (all-translation-governing-addresses
              (create-canonical-address-list
               8
               (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
              (double-rewrite x86)))
            ;; The physical addresses pertaining to the write are
            ;; disjoint from the translation-governing addresses
            ;; pertaining to the PML4TE.
            (disjoint-p$
             (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
             (all-translation-governing-addresses
              (create-canonical-address-list
               8
               (pml4-table-entry-addr
                lin-addr
                (pml4-table-base-addr x86)))
              (double-rewrite x86)))
            ;; The physical addresses corresponding to the PML4TE are
            ;; disjoint from the translation-governing addresses
            ;; pertaining to the write.
;;; TODO: Why do we need this hyp.?
            (disjoint-p$
             (all-translation-governing-addresses
              (strip-cars addr-lst)
              (double-rewrite x86))
             (mv-nth
              1
              (las-to-pas
               (create-canonical-address-list
                8
                (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
               :r (cpl x86)
               (double-rewrite x86))))
            (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
            (addr-byte-alistp addr-lst)
            (not (programmer-level-mode x86))
            (x86p x86))
           (equal (pdpt-base-addr lin-addr (mv-nth 1 (wb addr-lst x86)))
                  (pdpt-base-addr lin-addr x86)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d* (disjoint-p-commutative
                             disjoint-p$)
                            (rewrite-rb-to-rb-alt
                             member-p-strip-cars-of-remove-duplicate-keys)))))

(def-gl-export pml4-table-entry-addr-to-C-program-optimized-form
  :hyp (and (canonical-address-p v-addr)
            (equal (logtail 40 cr3) 0) ;; MBZ
            (unsigned-byte-p 64 cr3))
  :concl (equal (pml4-table-entry-addr v-addr (ash (loghead 40 (logtail 12 cr3)) 12))
                (logior (logand -4096 (logext 64 cr3))
                        (logand 4088 (loghead 28 (logtail 36 v-addr)))))
  :g-bindings
  (gl::auto-bindings (:mix (:nat v-addr 64) (:nat cr3 64))))

(def-gl-export canonical-address-p-pml4-table-entry-addr-to-C-program-optimized-form
  :hyp (and (canonical-address-p v-addr)
            (equal (logtail 40 cr3) 0) ;; MBZ
            (unsigned-byte-p 64 cr3))
  :concl (canonical-address-p
          (logior (logand -4096 (logext 64 cr3))
                  (logand 4088 (loghead 28 (logtail 36 v-addr)))))
  :g-bindings
  (gl::auto-bindings (:mix (:nat v-addr 64) (:nat cr3 64))))

(def-gl-export remove-logext-from-pml4-table-entry-addr-to-C-program-optimized-form-1
  :hyp (canonical-address-p v-addr)
  :concl (equal (logext 64 (logand 4088 (loghead 28 (logtail 36 v-addr))))
                (logand 4088 (loghead 28 (logtail 36 v-addr))))
  :g-bindings
  (gl::auto-bindings (:mix (:nat v-addr 64))))

(def-gl-export remove-logext-from-pml4-table-entry-addr-to-C-program-optimized-form-2
  :hyp (canonical-address-p v-addr)
  :concl (equal (logext 64 (loghead 28 (logtail 36 v-addr)))
                (loghead 28 (logtail 36 v-addr)))
  :g-bindings
  (gl::auto-bindings (:mix (:nat v-addr 64))))

(def-gl-export page-dir-ptr-table-entry-addr-to-C-program-optimized-form
  :hyp (and (canonical-address-p v-addr)
            (equal (loghead 12 base-addr) 0)
            (unsigned-byte-p 52 base-addr))
  :concl (equal (page-dir-ptr-table-entry-addr v-addr base-addr)
                (logior (logand 4088 (loghead 32 (logtail 27 v-addr)))
                        base-addr))
  :g-bindings
  (gl::auto-bindings (:mix (:nat v-addr 64) (:nat base-addr 64))))

(defthm canonical-address-p-page-dir-ptr-table-entry-addr-to-C-program-optimized-form
  (implies (logbitp 7 (combine-bytes
                       (mv-nth 1 (rb
                                  (create-canonical-address-list
                                   8
                                   (logior (logand 4088 (loghead 32 (logtail 27 v-addr)))
                                           (ash (loghead 40 (logtail 12 val)) 12)))
                                  :r x86))))
           (canonical-address-p
            (logior (logand 4088 (loghead 32 (logtail 27 v-addr)))
                    (ash (loghead 40 (logtail 12 val)) 12)))))

(def-gl-export remove-logext-from-page-dir-ptr-table-entry-addr-to-C-program-optimized-form
  :hyp (canonical-address-p v-addr)
  :concl (equal (logext 64 (loghead 32 (logtail 27 v-addr)))
                (loghead 32 (logtail 27 v-addr)))
  :g-bindings
  (gl::auto-bindings (:mix (:nat v-addr 64))))

(def-gl-export page-dir-ptr-table-entry-P=1-and-PS=1-zf-spec-helper-1
  :hyp (and (equal (part-select entry :low 7 :width 1) 1)
            (equal (part-select entry :low 0 :width 1) 1)
            (unsigned-byte-p 64 entry))
  :concl (equal (zf-spec
                 (loghead 64 (+ -129 (logand 129 (logext 64 (loghead 32 entry))))))
                1)
  :g-bindings
  (gl::auto-bindings (:nat entry 64)))

;; (def-gl-export page-dir-ptr-table-entry-P=1-and-PS=1-zf-spec-helper-2
;;   :hyp (and (equal (part-select source-entry :low 7 :width 1) 1)
;;             (equal (part-select source-entry :low 0 :width 1) 1)
;;             (equal (part-select destination-entry :low 7 :width 1) 1)
;;             (equal (part-select destination-entry :low 0 :width 1) 1)
;;             (unsigned-byte-p 64 source-entry)
;;             (unsigned-byte-p 64 destination-entry))
;;   :concl (equal (zf-spec
;;                  (loghead 64
;;                           (+
;;                            -129
;;                            (logand 129 (logior
;;                                         (loghead 30 destination-entry)
;;                                         (logand 3221225472 (loghead 32 source-entry)))))))
;;                 1)
;;   :g-bindings
;;   (gl::auto-bindings (:mix (:nat destination-entry 64) (:nat source-entry 64))))

(def-gl-export page-dir-ptr-table-entry-P=1-and-PS=1-zf-spec-helper-2
  :hyp (and (equal (part-select source-entry :low 7 :width 1) 1)
            (equal (part-select source-entry :low 0 :width 1) 1)
            (equal (part-select destination-entry :low 7 :width 1) 1)
            (equal (part-select destination-entry :low 0 :width 1) 1)
            (unsigned-byte-p 64 source-entry)
            (unsigned-byte-p 64 destination-entry))
  :concl (equal (zf-spec
                 (loghead 64
                          (+
                           -129
                           (logand 129 (logior
                                        (logext 64 (loghead 30 destination-entry))
                                        (logand 3221225472 (logext 64 (loghead 32 source-entry))))))))
                1)
  :g-bindings
  (gl::auto-bindings (:mix (:nat destination-entry 64) (:nat source-entry 64))))

(def-gl-export page-dir-ptr-table-entry-P=1-and-PS=1-zf-spec-helper-3
  :hyp (and (unsigned-byte-p 64 source-entry)
            (unsigned-byte-p 64 destination-entry))
  :concl (equal
          (zf-spec
           (loghead 64 (+ (logand 4503598553628672 (logext 64 source-entry))
                          (- (logand 4503598553628672
                                     (logior (logand -4503598553628673 (logext 64 destination-entry))
                                             (logand 4503598553628672 (logext 64 source-entry))))))))
          1)
  :g-bindings
  (gl::auto-bindings (:mix (:nat destination-entry 64) (:nat source-entry 64))))

;; ======================================================================

;; Assumptions:

(defun-nx x86-state-okp (x86)
  (and
   (x86p x86)
   (equal (xr :ms 0 x86) nil)
   (equal (xr :fault 0 x86) nil)
   (not (alignment-checking-enabled-p x86))
   (not (programmer-level-mode x86))
   (page-structure-marking-mode x86)
   ;; Current Privilege Level == 0.
   (equal (cpl x86) 0)
   ;; CR3's reserved bits must be zero (MBZ).
   (equal (logtail 40 (ctri *cr3* x86)) 0)))

(defun-nx program-ok-p (x86)
  (and
   ;; Program addresses are canonical.
   (canonical-address-p (+ *rewire_dst_to_src-len* (xr :rip 0 x86)))
   ;; Program is located at linear address (rip x86) in the memory.
   (program-at (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
               *rewire_dst_to_src* x86)
   ;; No errors encountered while translating the linear addresses
   ;; where the program is located.
   (not (mv-nth 0 (las-to-pas
                   (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
                   :x (cpl x86) x86)))

   ;; The following preconditions were not required in the non-marking
   ;; mode.
   ;; Physical addresses corresponding to the program are disjoint
   ;; from the paging structure physical addresses.
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
               :x (cpl x86) x86))
    (open-qword-paddr-list
     (gather-all-paging-structure-qword-addresses x86)))))

(defthmd x86-state-okp-and-program-ok-p-implies-program-alt
  (implies (and (x86-state-okp x86)
                (program-ok-p x86))
           (program-at-alt
            (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
            *rewire_dst_to_src* x86)))

(defun-nx stack-ok-p (x86)
  (and
   ;; Stack addresses are canonical.
   (canonical-address-p (+ -24 (xr :rgf *rsp* x86)))
   (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
   ;; Writing to stack: No errors encountered while translating the
   ;; linear addresses corresponding to the program stack.
   (not (mv-nth 0 (las-to-pas
                   (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                   :w (cpl x86) x86)))
   ;; Reading from stack: No errors encountered while translating the
   ;; linear addresses corresponding to the stack.
   (not (mv-nth 0 (las-to-pas
                   (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                   :r (cpl x86) x86)))
   ;; Reading from stack: The stack is located in a contiguous region
   ;; of memory --- no overlaps among physical addresses of the
   ;; stack.
   ;; I need this hypothesis so that the lemma
   ;; rb-wb-equal-in-system-level-non-marking-mode can fire.
   (no-duplicates-p
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
               :r (cpl x86) x86)))
   ;; The following preconditions were not required in the non-marking
   ;; mode.

   ;; Physical addresses corresponding to the stack are disjoint from
   ;; the paging structures physical addresses.
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
               :w (cpl x86) x86))
    (open-qword-paddr-list
     (gather-all-paging-structure-qword-addresses x86)))))

(defun-nx source-addresses-ok-p (x86)
  (and
   ;; Source addresses are canonical.
   (canonical-address-p (xr :rgf *rdi* x86))
   (canonical-address-p (+ -1 *2^30* (xr :rgf *rdi* x86)))
   ;; Source address is 1G-aligned.
   (equal (loghead 30 (xr :rgf *rdi* x86)) 0)
   ;; No errors encountered while translating the source linear
   ;; addresses.
   (not (mv-nth 0 (las-to-pas
                   (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
                   :r (cpl x86) x86)))))

(defun-nx destination-addresses-ok-p (x86)
  (and
   ;; Destination addresses are canonical.
   (canonical-address-p (xr :rgf *rsi* x86))
   (canonical-address-p (+ -1 *2^30* (xr :rgf *rsi* x86)))
   ;; Destination address is 1G-aligned.
   (equal (loghead 30 (xr :rgf *rsi* x86)) 0)
   ;; No errors encountered while translating the destination
   ;; linear addresses.
   (not
    (mv-nth 0 (las-to-pas
               (create-canonical-address-list *2^30* (xr :rgf *rsi* x86))
               :r (cpl x86) x86)))))

(defun-nx source-PML4TE-ok-p (x86)
  (and
   ;; PML4TE linear addresses are canonical.
   (canonical-address-p
    (+ 7 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))))
   ;; No errors encountered while translating the PML4TE linear addresses.
   (not (mv-nth 0 (las-to-pas
                   (create-canonical-address-list
                    8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
                   :r (cpl x86) x86)))
   ;; PML4TE has P = 1 (i.e., it is present).
   (equal
    (loghead
     1
     (logext
      64
      (combine-bytes
       (mv-nth
        1
        (rb
         (create-canonical-address-list
          8
          (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
         :r x86)))))
    1)))

(defun-nx source-PDPTE-ok-p (x86)
  (and
   ;; PDPTE linear addresses are canonical.
   (canonical-address-p
    (+ 7 (page-dir-ptr-table-entry-addr
          (xr :rgf *rdi* x86)
          (pdpt-base-addr (xr :rgf *rdi* x86) x86))))
   ;; No errors encountered while translating the PDPTE linear addresses.
   (not (mv-nth 0 (las-to-pas
                   (create-canonical-address-list
                    8
                    (page-dir-ptr-table-entry-addr
                     (xr :rgf *rdi* x86)
                     (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
                   :r (cpl x86) x86)))
   ;; PDPTE does not have the P or PS bit cleared (i.e., the
   ;; entry is present and it points to a 1G page).
   (equal (part-select
           (combine-bytes
            (mv-nth 1
                    (rb
                     (create-canonical-address-list
                      8
                      (page-dir-ptr-table-entry-addr
                       (xr :rgf *rdi* x86)
                       (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
                     :r x86)))
           :low 0 :width 1)
          1)
   (equal (part-select
           (combine-bytes
            (mv-nth 1
                    (rb
                     (create-canonical-address-list
                      8
                      (page-dir-ptr-table-entry-addr
                       (xr :rgf *rdi* x86)
                       (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
                     :r x86)))
           :low 7 :width 1)
          1)))

(defun-nx destination-PML4TE-ok-p (x86)
  (and
   ;; PML4TE linear addresses are canonical.
   (canonical-address-p
    (+ 7 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))))
   ;; No errors encountered while translating the PML4TE linear addresses.
   (not (mv-nth 0 (las-to-pas
                   (create-canonical-address-list
                    8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
                   :r (cpl x86) x86)))
   ;; PML4TE is has P = 1 (i.e., it is present).
   (equal
    (loghead
     1
     (logext
      64
      (combine-bytes
       (mv-nth
        1
        (rb
         (create-canonical-address-list
          8
          (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
         :r x86)))))
    1)))

(defun-nx destination-PDPTE-ok-p (x86)
  (and
   ;; PDPTE linear addresses are canonical.
   (canonical-address-p
    (page-dir-ptr-table-entry-addr
     (xr :rgf *rsi* x86)
     (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
   (canonical-address-p
    (+ 7 (page-dir-ptr-table-entry-addr
          (xr :rgf *rsi* x86)
          (pdpt-base-addr (xr :rgf *rsi* x86) x86))))
   ;; No errors encountered while translating the PDPTE linear
   ;; addresses on behalf of a read.
   (not (mv-nth 0 (las-to-pas
                   (create-canonical-address-list
                    8
                    (page-dir-ptr-table-entry-addr
                     (xr :rgf *rsi* x86)
                     (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
                   :r (cpl x86) x86)))
   ;; No errors encountered while translating the PDPTE linear
   ;; addresses on behalf of a write.
   (not (mv-nth 0 (las-to-pas
                   (create-canonical-address-list
                    8
                    (page-dir-ptr-table-entry-addr
                     (xr :rgf *rsi* x86)
                     (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
                   :w (cpl x86) x86)))
   ;; Destination PDPTE does not have the P or PS bit cleared (i.e.,
   ;; the entry is present and it points to a 1G page).
   (equal (part-select
           (combine-bytes
            (mv-nth 1
                    (rb
                     (create-canonical-address-list
                      8
                      (page-dir-ptr-table-entry-addr
                       (xr :rgf *rsi* x86)
                       (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
                     :r x86)))
           :low 0 :width 1)
          1)
   (equal (part-select
           (combine-bytes
            (mv-nth 1
                    (rb
                     (create-canonical-address-list
                      8
                      (page-dir-ptr-table-entry-addr
                       (xr :rgf *rsi* x86)
                       (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
                     :r x86)))
           :low 7 :width 1)
          1)))

(defun-nx return-instruction-address-ok-p (x86)
  (and ;; Return address on the stack is canonical.
   (canonical-address-p
    (logext 64
            (combine-bytes
             (mv-nth 1
                     (rb (create-canonical-address-list 8 (xr :rgf *rsp* x86))
                         :r x86)))))
   ;; Reading from stack for the final ret instruction doesn't cause
   ;; errors.
   (not (mv-nth 0 (las-to-pas
                   (create-canonical-address-list 8 (xr :rgf *rsp* x86))
                   :r (cpl x86) x86)))))

(defun-nx program-and-stack-no-interfere-p (x86)
  ;; The physical addresses corresponding to the program and stack
  ;; are disjoint.
  (disjoint-p$
   (mv-nth 1
           (las-to-pas
            (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
            :w (cpl x86) x86))
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
              :x (cpl x86) x86))))

(defun-nx source-PML4TE-and-stack-no-interfere-p (x86)
  ;; The PML4TE physical addresses are disjoint from the
  ;; stack physical addresses.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86))
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8
               (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
              :r (cpl x86) x86))))

(defun-nx source-PDPTE-and-stack-no-interfere-p (x86)
  ;; The PDPTE physical addresses are disjoint from the stack
  ;; physical addresses.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86))
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rdi* x86)
                (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
              :r (cpl x86) x86))))

(defun-nx destination-PML4TE-and-stack-no-interfere-p (x86)
  ;; The PML4TE physical addresses are disjoint from the stack
  ;; physical addresses.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86))
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8
               (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
              :r (cpl x86) x86))))

(defun-nx destination-PDPTE-and-stack-no-interfere-p (x86)
  ;; The destination PDPTE is disjoint from the stack.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86))
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
              :r (cpl x86) x86))))

(defun-nx destination-PDPTE-and-program-no-interfere-p (x86)
  ;; We need these assumptions because the destination PDPTE is
  ;; modified, and we need to make sure that this modification does
  ;; not affect the program in any way.
  (and
   ;; The physical addresses corresponding to the program are disjoint
   ;; from those of the PDPTE (on behalf of a write).
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list
                8
                (page-dir-ptr-table-entry-addr
                 (xr :rgf *rsi* x86)
                 (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
               :w (cpl x86) x86))
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
               :x (cpl x86) x86)))

   ;; Translation-governing addresses of the program are disjoint from
   ;; the PDPTE physical addresses (on behalf of a write).
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list
                8
                (page-dir-ptr-table-entry-addr
                 (xr :rgf *rsi* x86)
                 (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
               :w (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
     x86))))

(defun-nx ret-instruction-and-destination-PDPTE-no-interfere-p (x86)
  ;; The translation-governing addresses of the ret address are
  ;; disjoint from the destination PDPTE.
  (and
   ;; !!!! NOTE: This is in terms of disjoint-p instead of disjoint-p$.
   (disjoint-p
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list
                8
                (page-dir-ptr-table-entry-addr
                 (xr :rgf *rsi* x86)
                 (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
               :r (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list 8 (xr :rgf *rsp* x86)) x86))
   ;; The destination PDPTE is disjoint from the ret address
   ;; on the stack.
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list
                8
                (page-dir-ptr-table-entry-addr
                 (xr :rgf *rsi* x86)
                 (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
               :w (cpl x86) x86))
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list 8 (xr :rgf *rsp* x86))
               :r (cpl x86) x86)))
   ;; !!!! NOTE: This is in terms of disjoint-p instead of disjoint-p$.
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list 8 (xr :rgf *rsp* x86))
               :r (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (page-dir-ptr-table-entry-addr
       (xr :rgf *rsi* x86)
       (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
     x86))))

(defun-nx ret-instruction-and-destination-PML4E-no-interfere-p (x86)
  ;; The destination PML4E is disjoint from the ret address on the
  ;; stack.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list 8 (xr :rgf *rsp* x86))
              :r (cpl x86) x86))

   (all-translation-governing-addresses
    (create-canonical-address-list
     8
     (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
    x86)))

(defun-nx ret-instruction-and-source-PML4E-no-interfere-p (x86)
  ;; The destination PML4E is disjoint from the ret address on the
  ;; stack.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list 8 (xr :rgf *rsp* x86))
              :r (cpl x86) x86))

   (all-translation-governing-addresses
    (create-canonical-address-list
     8
     (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
    x86)))

(defun-nx ret-instruction-and-source-PDPTE-no-interfere-p (x86)
  ;; The destination PML4E is disjoint from the ret address on the
  ;; stack.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list 8 (xr :rgf *rsp* x86))
              :r (cpl x86) x86))

   (all-translation-governing-addresses
    (create-canonical-address-list
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rdi* x86)
      (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
    x86)))

(defun-nx return-address-and-stack-no-interfere-p (x86)
  ;; !!! FIX ME.
  (and
   (disjoint-p
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list 8 (xr :rgf *rsp* x86))
               :r (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) x86))
   (disjoint-p
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86))
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list 8 (xr :rgf *rsp* x86))
               :r (cpl x86) x86)))))

(defun-nx return-addresses-and-program-no-interfere-p (x86)
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list 8 (xr :rgf *rsp* x86))
              :r (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
    x86)))

(defun-nx return-addresses-itself-no-interfere-p (x86)
  ;; !!! FIX: The following is in terms of disjoint-p instead of disjoint-p$.
  (and
   (disjoint-p
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list 8 (xr :rgf *rsp* x86))
               :r (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list 8 (xr :rgf *rsp* x86))
     x86))
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list 8 (xr :rgf *rsp* x86))
               :r (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list 8 (xr :rgf *rsp* x86))
     x86))))

(defun-nx well-formedness-assumptions (x86)
  (and
   (x86-state-okp x86)
   (program-ok-p x86)
   (stack-ok-p x86)
   (source-addresses-ok-p x86)
   (destination-addresses-ok-p x86)
   (source-PML4TE-ok-p x86)
   (source-PDPTE-ok-p x86)
   (destination-PML4TE-ok-p x86)
   (destination-PDPTE-ok-p x86)
   (return-instruction-address-ok-p x86)))

(defun-nx non-interference-assumptions (x86)
  (and
   (program-and-stack-no-interfere-p x86)
   (source-PML4TE-and-stack-no-interfere-p x86)
   (source-PDPTE-and-stack-no-interfere-p x86)
   (destination-PML4TE-and-stack-no-interfere-p x86)
   (destination-PDPTE-and-stack-no-interfere-p x86)
   (destination-PDPTE-and-program-no-interfere-p x86)
   (ret-instruction-and-destination-PDPTE-no-interfere-p x86)
   (return-address-and-stack-no-interfere-p x86)))

(defun-nx rewire_dst_to_src-assumptions (x86)
  (and (well-formedness-assumptions x86)
       (non-interference-assumptions x86)))

;; ======================================================================

(encapsulate
  ()

  (local
   (in-theory (e/d (mv-nth-0-las-to-pas-subset-p member-p subset-p)
                   (xlate-equiv-memory-and-mv-nth-1-rm08))))

  (defthm xr-fault-ia32e-la-to-pa
    (implies (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
             (equal (xr :fault index (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                    (xr :fault index x86)))
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa
                                      ia32e-la-to-pa-pml4-table
                                      ia32e-la-to-pa-page-dir-ptr-table
                                      ia32e-la-to-pa-page-directory
                                      ia32e-la-to-pa-page-table)
                                     (force
                                      (force)
                                      (:definition not)
                                      (:meta acl2::mv-nth-cons-meta))))))

  (defthm xr-fault-rb-alt-state-in-system-level-mode
    (equal (xr :fault index (mv-nth 2 (rb-alt l-addrs r-w-x x86)))
           (xr :fault index x86))
    :hints (("Goal" :in-theory (e/d* (rb-alt las-to-pas)
                                     (rewrite-rb-to-rb-alt
                                      force (force))))))

  (defthm xr-fault-and-get-prefixes
    (implies (not (mv-nth 0 (las-to-pas
                             (create-canonical-address-list cnt start-rip)
                             :x (cpl x86) x86)))
             (equal (xr :fault index (mv-nth 2 (get-prefixes start-rip prefixes cnt x86)))
                    (xr :fault index x86)))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :in-theory (e/d* (get-prefixes rm08)
                              (rm08-to-rb
                               not force (force))))))

  (defthm xr-fault-and-get-prefixes-alt
    (equal (xr :fault index (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86)))
           (xr :fault index x86))
    :hints (("Goal" :in-theory (e/d* (get-prefixes-alt)
                                     (rewrite-get-prefixes-to-get-prefixes-alt
                                      not force (force))))))

  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
     *x86-field-names-as-keywords*)
    'rb-alt
    (acl2::formals 'rb-alt (w state))
    :output-index 0
    :hyps '(not (programmer-level-mode x86))
    :double-rewrite? t))

  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
     *x86-field-names-as-keywords*)
    'rb-alt
    (acl2::formals 'rb-alt (w state))
    :output-index 1
    :hyps '(not (programmer-level-mode x86))
    :prepwork '((local (in-theory (e/d* (rb-alt) (rewrite-rb-to-rb-alt)))))
    :double-rewrite? t))

  ;; (defthm rb-alt-xw-values-in-system-level-mode
  ;;   (implies (and (not (programmer-level-mode x86))
  ;;                 (not (equal fld :mem))
  ;;                 (not (equal fld :rflags))
  ;;                 (not (equal fld :ctr))
  ;;                 (not (equal fld :seg-visible))
  ;;                 (not (equal fld :msr))
  ;;                 (not (equal fld :fault))
  ;;                 (not (equal fld :programmer-level-mode))
  ;;                 (not (equal fld :page-structure-marking-mode)))
  ;;            (and (equal (mv-nth 0 (rb-alt addr r-w-x (xw fld index value x86)))
  ;;                        (mv-nth 0 (rb-alt addr r-w-x x86)))
  ;;                 (equal (mv-nth 1 (rb-alt addr r-w-x (xw fld index value x86)))
  ;;                        (mv-nth 1 (rb-alt addr r-w-x x86)))))
  ;;   :hints (("Goal" :in-theory (e/d* (rb-alt) (rewrite-rb-to-rb-alt force (force))))))

  (defthm rb-alt-xw-rflags-not-ac-values-in-system-level-mode
    (implies (and (not (programmer-level-mode x86))
                  (equal (rflags-slice :ac value)
                         (rflags-slice :ac (rflags x86))))
             (and (equal (mv-nth 0 (rb-alt addr r-w-x (xw :rflags 0 value x86)))
                         (mv-nth 0 (rb-alt addr r-w-x x86)))
                  (equal (mv-nth 1 (rb-alt addr r-w-x (xw :rflags 0 value x86)))
                         (mv-nth 1 (rb-alt addr r-w-x x86)))))
    :hints (("Goal" :in-theory (e/d* (rb-alt) (force (force) rewrite-rb-to-rb-alt)))))

  (make-event
   (generate-write-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
     *x86-field-names-as-keywords*)
    'rb-alt
    (acl2::formals 'rb-alt (w state))
    :output-index 2
    :hyps '(not (programmer-level-mode x86))
    :prepwork '((local (in-theory (e/d* (rb-alt) (rewrite-rb-to-rb-alt force (force))))))))

  ;; (defthm rb-alt-xw-state-in-system-level-mode
  ;;   (implies (and (not (programmer-level-mode x86))
  ;;                 (not (equal fld :mem))
  ;;                 (not (equal fld :rflags))
  ;;                 (not (equal fld :ctr))
  ;;                 (not (equal fld :seg-visible))
  ;;                 (not (equal fld :msr))
  ;;                 (not (equal fld :fault))
  ;;                 (not (equal fld :programmer-level-mode))
  ;;                 (not (equal fld :page-structure-marking-mode)))
  ;;            (equal (mv-nth 2 (rb-alt addr r-w-x (xw fld index value x86)))
  ;;                   (xw fld index value (mv-nth 2 (rb-alt addr r-w-x x86)))))
  ;;   :hints (("Goal" :in-theory (e/d* (rb-alt) (rewrite-rb-to-rb-alt force (force))))))

  (defthm rb-alt-xw-rflags-not-ac-state-in-system-level-mode
    (implies (and (not (programmer-level-mode x86))
                  (equal (rflags-slice :ac value)
                         (rflags-slice :ac (rflags x86))))
             (equal (mv-nth 2 (rb-alt addr r-w-x (xw :rflags 0 value x86)))
                    (xw :rflags 0 value (mv-nth 2 (rb-alt addr r-w-x x86)))))
    :hints (("Goal" :in-theory (e/d* (rb-alt) (rewrite-rb-to-rb-alt force (force))))))

  (defthm rb-alt-values-and-!flgi-in-system-level-mode
    (implies (and (not (equal index *ac*))
                  (not (programmer-level-mode x86))
                  (x86p x86))
             (and (equal (mv-nth 0 (rb-alt l-addrs r-w-x (!flgi index value x86)))
                         (mv-nth 0 (rb-alt l-addrs r-w-x (double-rewrite x86))))
                  (equal (mv-nth 1 (rb-alt l-addrs r-w-x (!flgi index value x86)))
                         (mv-nth 1 (rb-alt l-addrs r-w-x (double-rewrite x86))))))
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d* (rb-alt) (rewrite-rb-to-rb-alt force (force))))))

  (defthm rb-and-!flgi-state-in-system-level-mode
    (implies (and (not (equal index *ac*))
                  (not (programmer-level-mode x86))
                  (x86p x86))
             (equal (mv-nth 2 (rb lin-addr r-w-x (!flgi index value x86)))
                    (!flgi index value (mv-nth 2 (rb lin-addr r-w-x x86)))))
    :hints (("Goal"
             :do-not-induct t
             :cases ((equal index *iopl*))
             :use ((:instance rflags-slice-ac-simplify
                              (index index)
                              (rflags (xr :rflags 0 x86)))
                   (:instance rb-xw-rflags-not-ac-state-in-system-level-mode
                              (addr lin-addr)
                              (value (logior (loghead 32 (ash (loghead 1 value) (nfix index)))
                                             (logand (xr :rflags 0 x86)
                                                     (loghead 32 (lognot (expt 2 (nfix index))))))))
                   (:instance rb-xw-rflags-not-ac-state-in-system-level-mode
                              (addr lin-addr)
                              (value (logior (ash (loghead 2 value) 12)
                                             (logand 4294955007 (xr :rflags 0 x86))))))
             :in-theory (e/d* (!flgi-open-to-xw-rflags)
                              (rewrite-rb-to-rb-alt force (force))))))

  (defthm rb-alt-and-!flgi-state-in-system-level-mode
    (implies (and (not (equal index *ac*))
                  (not (programmer-level-mode x86))
                  (x86p x86))
             (equal (mv-nth 2 (rb-alt lin-addr r-w-x (!flgi index value x86)))
                    (!flgi index value (mv-nth 2 (rb-alt lin-addr r-w-x x86)))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d* (rb-alt)
                              (rewrite-rb-to-rb-alt force (force))))))

  (defthmd get-prefixes-xw-values-in-system-level-mode
    (implies (and (not (programmer-level-mode x86))
                  (not (equal fld :mem))
                  (not (equal fld :rflags))
                  (not (equal fld :ctr))
                  (not (equal fld :seg-visible))
                  (not (equal fld :msr))
                  (not (equal fld :fault))
                  (not (equal fld :programmer-level-mode))
                  (not (equal fld :page-structure-marking-mode)))
             (and (equal (mv-nth 0 (get-prefixes start-rip prefixes cnt (xw fld index value x86)))
                         (mv-nth 0 (get-prefixes start-rip prefixes cnt x86)))
                  (equal (mv-nth 1 (get-prefixes start-rip prefixes cnt (xw fld index value x86)))
                         (mv-nth 1 (get-prefixes start-rip prefixes cnt x86)))))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :expand (get-prefixes start-rip prefixes cnt (xw fld index value x86))
             :in-theory (e/d* (get-prefixes)
                              (xlate-equiv-memory-and-mv-nth-1-rm08
                               rewrite-get-prefixes-to-get-prefixes-alt
                               force (force))))))

  (defthmd get-prefixes-xw-state-in-system-level-mode
    (implies (and (not (programmer-level-mode x86))
                  (not (equal fld :mem))
                  (not (equal fld :rflags))
                  (not (equal fld :ctr))
                  (not (equal fld :seg-visible))
                  (not (equal fld :msr))
                  (not (equal fld :fault))
                  (not (equal fld :programmer-level-mode))
                  (not (equal fld :page-structure-marking-mode)))
             (equal (mv-nth 2 (get-prefixes start-rip prefixes cnt (xw fld index value x86)))
                    (xw fld index value (mv-nth 2 (get-prefixes start-rip prefixes cnt x86)))))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :expand (get-prefixes start-rip prefixes cnt (xw fld index value x86))
             :in-theory (e/d* (get-prefixes)
                              (xlate-equiv-memory-and-mv-nth-1-rm08
                               rewrite-get-prefixes-to-get-prefixes-alt
                               force (force))))))

  (local (in-theory (e/d (get-prefixes-xw-values-in-system-level-mode
                          get-prefixes-xw-state-in-system-level-mode)
                         (rewrite-get-prefixes-to-get-prefixes-alt))))
  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
     *x86-field-names-as-keywords*)
    'get-prefixes
    (acl2::formals 'get-prefixes (w state))
    :output-index 0
    :hyps '(not (programmer-level-mode x86))))
  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
     *x86-field-names-as-keywords*)
    'get-prefixes
    (acl2::formals 'get-prefixes (w state))
    :output-index 1
    :hyps '(not (programmer-level-mode x86))))

  (make-event
   (generate-write-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
     *x86-field-names-as-keywords*)
    'get-prefixes
    (acl2::formals 'get-prefixes (w state))
    :output-index 2
    :hyps '(not (programmer-level-mode x86))))

  (local (in-theory (e/d (rewrite-get-prefixes-to-get-prefixes-alt)
                         (get-prefixes-xw-values-in-system-level-mode
                          get-prefixes-xw-state-in-system-level-mode))))

  (local (in-theory (e/d (get-prefixes-alt) (rewrite-get-prefixes-to-get-prefixes-alt force (force)))))
  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
     *x86-field-names-as-keywords*)
    'get-prefixes-alt
    (acl2::formals 'get-prefixes-alt (w state))
    :output-index 0
    :hyps '(not (programmer-level-mode x86))
    :double-rewrite? t))
  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
     *x86-field-names-as-keywords*)
    'get-prefixes-alt
    (acl2::formals 'get-prefixes-alt (w state))
    :output-index 1
    :hyps '(not (programmer-level-mode x86))
    :double-rewrite? t))

  (make-event
   (generate-write-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
     *x86-field-names-as-keywords*)
    'get-prefixes-alt
    (acl2::formals 'get-prefixes-alt (w state))
    :output-index 2
    :hyps '(not (programmer-level-mode x86))))
  (local (in-theory (e/d (rewrite-get-prefixes-to-get-prefixes-alt force (force)) (get-prefixes-alt))))

  (defthm get-prefixes-xw-rflags-not-ac-state-in-system-level-mode
    (implies (and (not (programmer-level-mode x86))
                  (equal (rflags-slice :ac value)
                         (rflags-slice :ac (rflags x86))))
             (equal (mv-nth 2 (get-prefixes start-rip prefixes cnt (xw :rflags 0 value x86)))
                    (xw :rflags 0 value (mv-nth 2 (get-prefixes start-rip prefixes cnt x86)))))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :expand (get-prefixes start-rip prefixes cnt (xw :rflags 0 value x86))
             :in-theory (e/d* (get-prefixes)
                              (rewrite-get-prefixes-to-get-prefixes-alt
                               force (force))))))

  (defthm get-prefixes-and-!flgi-state-in-system-level-mode
    (implies (and (not (equal index *ac*))
                  (not (programmer-level-mode x86))
                  (x86p x86))
             (equal (mv-nth 2 (get-prefixes start-rip prefixes cnt (!flgi index value x86)))
                    (!flgi index value (mv-nth 2 (get-prefixes start-rip prefixes cnt x86)))))
    :hints (("Goal"
             :do-not-induct t
             :cases ((equal index *iopl*))
             :use ((:instance rflags-slice-ac-simplify
                              (index index)
                              (rflags (xr :rflags 0 x86)))
                   (:instance get-prefixes-xw-rflags-not-ac-state-in-system-level-mode
                              (value (logior (loghead 32 (ash (loghead 1 value) (nfix index)))
                                             (logand (xr :rflags 0 x86)
                                                     (loghead 32 (lognot (expt 2 (nfix index))))))))
                   (:instance get-prefixes-xw-rflags-not-ac-state-in-system-level-mode
                              (value (logior (ash (loghead 2 value) 12)
                                             (logand 4294955007 (xr :rflags 0 x86))))))
             :in-theory (e/d* (!flgi-open-to-xw-rflags
                               !flgi)
                              (rewrite-get-prefixes-to-get-prefixes-alt force (force))))))

  (defthm get-prefixes-xw-rflags-not-ac-values-in-system-level-mode
    (implies (and (not (programmer-level-mode x86))
                  (equal (rflags-slice :ac value)
                         (rflags-slice :ac (rflags x86))))
             (and
              (equal (mv-nth 0 (get-prefixes start-rip prefixes cnt (xw :rflags 0 value x86)))
                     (mv-nth 0 (get-prefixes start-rip prefixes cnt x86)))
              (equal (mv-nth 1 (get-prefixes start-rip prefixes cnt (xw :rflags 0 value x86)))
                     (mv-nth 1 (get-prefixes start-rip prefixes cnt x86)))))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :expand (get-prefixes start-rip prefixes cnt (xw :rflags 0 value x86))
             :in-theory (e/d* (get-prefixes)
                              (rewrite-get-prefixes-to-get-prefixes-alt
                               xlate-equiv-memory-and-two-get-prefixes-values
                               force (force))))))

  (defthm get-prefixes-values-and-!flgi-in-system-level-mode
    (implies (and (not (equal index *ac*))
                  (not (programmer-level-mode x86))
                  (x86p x86))
             (and (equal (mv-nth 0 (get-prefixes start-rip prefixes cnt (!flgi index value x86)))
                         (mv-nth 0 (get-prefixes start-rip prefixes cnt x86)))
                  (equal (mv-nth 1 (get-prefixes start-rip prefixes cnt (!flgi index value x86)))
                         (mv-nth 1 (get-prefixes start-rip prefixes cnt x86)))))
    :hints (("Goal"
             :do-not-induct t
             :cases ((equal index *iopl*))
             :use ((:instance rflags-slice-ac-simplify
                              (index index)
                              (rflags (xr :rflags 0 x86)))
                   (:instance get-prefixes-xw-rflags-not-ac-values-in-system-level-mode
                              (value (logior (loghead 32 (ash (loghead 1 value) (nfix index)))
                                             (logand (xr :rflags 0 x86)
                                                     (loghead 32 (lognot (expt 2 (nfix index))))))))
                   (:instance get-prefixes-xw-rflags-not-ac-values-in-system-level-mode
                              (value (logior (ash (loghead 2 value) 12)
                                             (logand 4294955007 (xr :rflags 0 x86))))))
             :in-theory (e/d* (!flgi-open-to-xw-rflags
                               !flgi)
                              (get-prefixes-xw-rflags-not-ac-values-in-system-level-mode
                               rewrite-get-prefixes-to-get-prefixes-alt
                               force (force))))))

  (defthm get-prefixes-alt-values-and-!flgi-in-system-level-mode
    (implies (and (not (equal index *ac*))
                  (x86p x86))
             (and (equal (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt
                                                     (!flgi index value x86)))
                         (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt (double-rewrite x86))))
                  (equal (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt
                                                     (!flgi index value x86)))
                         (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt (double-rewrite x86))))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d* (get-prefixes-alt)
                              (rewrite-get-prefixes-to-get-prefixes-alt
                               force (force))))))

  (defthm get-prefixes-alt-and-!flgi-state-in-system-level-mode
    (implies (and (not (equal index *ac*))
                  (not (programmer-level-mode x86))
                  (x86p x86))
             (equal (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt (!flgi index value x86)))
                    (!flgi index value (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86)))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d* (get-prefixes-alt)
                              (rewrite-get-prefixes-to-get-prefixes-alt
                               force (force))))))

  (defthm flgi-and-mv-nth-2-rb-alt
    (equal (flgi index (mv-nth 2 (rb-alt l-addrs r-w-x x86)))
           (flgi index x86))
    :hints (("Goal" :in-theory (e/d* (flgi) ()))))

  (defthm alignment-checking-enabled-p-and-mv-nth-2-rb-alt
    (equal (alignment-checking-enabled-p (mv-nth 2 (rb-alt l-addrs r-w-x x86)))
           (alignment-checking-enabled-p x86))
    :hints (("Goal" :in-theory (e/d* (alignment-checking-enabled-p) ()))))

  (defthm flgi-and-mv-nth-2-get-prefixes-alt
    (equal (flgi index (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86)))
           (flgi index x86))
    :hints (("Goal" :in-theory (e/d* (flgi) ()))))

  (defthm alignment-checking-enabled-p-and-mv-nth-2-get-prefixes-alt
    (equal (alignment-checking-enabled-p (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86)))
           (alignment-checking-enabled-p x86))
    :hints (("Goal" :in-theory (e/d* (alignment-checking-enabled-p) ()))))

  (defthm mv-nth-1-wb-and-!flgi-commute-in-marking-mode
    ;; Subsumes MV-NTH-1-WB-AND-!FLGI-COMMUTE
    (implies (not (equal index *ac*))
             (equal (mv-nth 1 (wb addr-lst (!flgi index val x86)))
                    (!flgi index val (mv-nth 1 (wb addr-lst x86)))))
    :hints (("Goal" :in-theory (e/d* (!flgi rflags-slice-ac-simplify
                                            !flgi-open-to-xw-rflags)
                                     (force (force))))))

  (defthm xr-fault-las-to-pas
    (implies (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86))))
             (equal (xr :fault 0 (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
                    (xr :fault 0 x86)))
    :hints (("Goal" :in-theory (e/d* (las-to-pas) (force (force))))))

  (defthm xr-fault-wb-in-system-level-marking-mode
    (implies
     (not (mv-nth 0 (las-to-pas (strip-cars addr-lst)
                                :w (loghead 2 (xr :seg-visible 1 x86))
                                (double-rewrite x86))))
     (equal (xr :fault 0 (mv-nth 1 (wb addr-lst x86)))
            (xr :fault 0 x86)))
    :hints
    (("Goal" :do-not-induct t
      :in-theory (e/d* (wb)
                       (member-p-strip-cars-of-remove-duplicate-keys
                        (:meta acl2::mv-nth-cons-meta)
                        force (force)))))))

(def-ruleset rewire_dst_to_src-disable
  '((:type-prescription natp-pml4-table-entry-addr)
    (:rewrite acl2::consp-when-member-equal-of-atom-listp)
    (:rewrite ia32e-la-to-pa-xw-state)
    (:rewrite r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-when-no-errors)
    (:linear adding-7-to-pml4-table-entry-addr)
    (:linear *physical-address-size*p-pml4-table-entry-addr)
    (:rewrite acl2::equal-of-booleans-rewrite)
    (:rewrite loghead-unequal)
    (:rewrite negative-logand-to-positive-logand-with-integerp-x)
    (:definition combine-bytes)
    (:rewrite |(logand -4096 base-addr) = base-addr when low 12 bits are 0|)
    (:rewrite xr-ia32e-la-to-pa)
    (:rewrite acl2::nfix-when-not-natp)
    (:rewrite acl2::nfix-when-natp)
    (:rewrite constant-upper-bound-of-logior-for-naturals)
    (:linear combine-bytes-size-for-rm64-programmer-level-mode)
    (:rewrite acl2::natp-when-integerp)
    (:rewrite acl2::natp-when-gte-0)
    (:rewrite 4k-aligned-physical-address-helper)
    (:rewrite bitops::signed-byte-p-of-logtail)
    (:linear adding-7-to-page-dir-ptr-table-entry-addr)
    (:linear *physical-address-size*p-page-dir-ptr-table-entry-addr)
    (:type-prescription adding-7-to-pml4-table-entry-addr)
    (:type-prescription adding-7-to-page-dir-ptr-table-entry-addr)
    (:rewrite acl2::signed-byte-p-logext)
    (:type-prescription booleanp)
    (:rewrite loghead-64-n64-to-i64-canonical-address)
    (:type-prescription pml4-table-base-addr)
    (:rewrite get-prefixes-opener-lemma-group-4-prefix)
    (:rewrite get-prefixes-opener-lemma-group-3-prefix)
    (:rewrite get-prefixes-opener-lemma-group-2-prefix)
    (:rewrite get-prefixes-opener-lemma-group-1-prefix)
    (:rewrite get-prefixes-alt-opener-lemma-group-4-prefix-in-marking-mode)
    (:rewrite get-prefixes-alt-opener-lemma-group-3-prefix-in-marking-mode)
    (:rewrite get-prefixes-alt-opener-lemma-group-2-prefix-in-marking-mode)
    (:rewrite get-prefixes-alt-opener-lemma-group-1-prefix-in-marking-mode)
    (:definition member-p)
    (:linear unsigned-byte-p-of-combine-bytes)
    (:type-prescription acl2::|x < y  =>  0 < -x+y|)
    (:rewrite default-+-2)
    (:rewrite acl2::natp-rw)
    (:rewrite ia32e-la-to-pa-lower-12-bits)
    (:rewrite default-+-1)
    (:rewrite acl2::ash-0)
    (:rewrite acl2::zip-open)
    (:rewrite loghead-of-non-integerp)
    (:type-prescription addr-byte-alistp-create-addr-bytes-alist)
    (:rewrite canonical-address-p-limits-thm-3)
    (:rewrite canonical-address-p-limits-thm-2)
    (:rewrite zf-spec-thm)
    (:linear acl2::loghead-upper-bound)
    (:linear bitops::logior-<-0-linear-2)
    (:linear size-of-combine-bytes)
    (:rewrite disjoint-p-subset-p)
    (:definition binary-append)
    (:definition create-addr-bytes-alist)
    (:rewrite member-p-of-subset-is-member-p-of-superset)
    (:linear rgfi-is-i64p . 1)
    (:rewrite member-p-cdr)
    (:rewrite bitops::unsigned-byte-p-when-unsigned-byte-p-less)
    (:rewrite acl2::difference-unsigned-byte-p)
    (:linear rgfi-is-i64p . 2)
    (:rewrite acl2::append-when-not-consp)
    (:linear rip-is-i48p . 2)
    (:linear rip-is-i48p . 1)
    (:type-prescription byte-ify)
    (:rewrite acl2::ifix-when-not-integerp)
    (:rewrite bitops::basic-unsigned-byte-p-of-+)
    (:rewrite disjoint-p-append-1)
    (:rewrite default-<-1)
    (:rewrite default-car)
    (:rewrite default-cdr)
    (:meta acl2::cancel_plus-lessp-correct)
    (:rewrite wb-not-consp-addr-lst)
    (:definition nthcdr)
    (:rewrite subset-p-cdr-y)
    (:rewrite ia32e-la-to-pa-lower-12-bits-value-of-address-when-error)
    (:rewrite default-<-2)
    (:type-prescription n52p-mv-nth-1-ia32e-la-to-pa)
    (:meta acl2::cancel_plus-equal-correct)
    (:definition nth)
    (:rewrite consp-create-addr-bytes-alist)
    (:rewrite subset-p-reflexive)
    (:meta acl2::cancel_times-equal-correct)
    (:rewrite set::sets-are-true-lists)
    (:linear rflags-is-n32p)
    (:rewrite consp-byte-ify)
    (:definition true-listp)
    (:type-prescription rflags-is-n32p)
    (:rewrite cdr-append-is-append-cdr)
    (:type-prescription bitops::logtail-natp)
    (:rewrite subset-p-cdr-x)
    (:rewrite bitops::logbitp-nonzero-of-bit)
    (:rewrite set::nonempty-means-set)
    (:type-prescription xw)
    (:type-prescription consp-create-addr-bytes-alist-in-terms-of-len)
    (:type-prescription consp-create-addr-bytes-alist)
    (:type-prescription natp-combine-bytes)
    (:type-prescription true-listp)
    (:rewrite unsigned-byte-p-of-logtail)
    (:rewrite bitops::logbitp-when-bitmaskp)
    (:type-prescription all-translation-governing-addresses)
    (:type-prescription set::setp-type)
    (:type-prescription set::empty-type)
    (:rewrite acl2::equal-constant-+)
    (:definition byte-listp)
    (:rewrite unsigned-byte-p-of-ash)
    (:rewrite bitops::normalize-logbitp-when-mods-equal)
    (:rewrite bitops::logbitp-of-negative-const)
    (:rewrite bitops::logbitp-of-mask)
    (:rewrite bitops::logbitp-of-const)
    (:rewrite greater-logbitp-of-unsigned-byte-p . 1)
    (:meta bitops::open-logbitp-of-const-lite-meta)
    (:rewrite rb-returns-byte-listp)
    (:rewrite car-of-append)
    (:type-prescription rb-returns-true-listp)
    (:rewrite bitops::signed-byte-p-when-unsigned-byte-p-smaller)
    (:rewrite bitops::signed-byte-p-when-signed-byte-p-smaller)
    (:type-prescription consp-append)
    (:type-prescription bitops::logand-natp-type-2)
    (:definition acons)
    (:rewrite unsigned-byte-p-of-combine-bytes)
    (:rewrite unsigned-byte-p-of-logior)
    (:type-prescription natp)
    (:rewrite set::in-set)
    (:type-prescription acl2::logtail-type)
    (:rewrite acl2::member-of-cons)
    (:type-prescription true-listp-create-addr-bytes-alist)
    (:type-prescription rb-returns-byte-listp)
    (:rewrite rationalp-implies-acl2-numberp)
    (:type-prescription bitops::ash-natp-type)
    (:type-prescription combine-bytes)
    (:definition n08p$inline)
    (:definition len)
    (:rewrite xr-and-ia32e-la-to-pa-page-directory-in-non-marking-mode)
    (:rewrite bitops::logsquash-of-loghead-zero)
    (:rewrite default-unary-minus)
    (:rewrite len-of-rb-in-programmer-level-mode)
    (:type-prescription acl2::true-listp-append)
    (:linear bitops::upper-bound-of-logand . 2)
    (:rewrite weed-out-irrelevant-logand-when-first-operand-constant)
    (:rewrite logand-redundant)
    (:linear ash-monotone-2)
    (:linear bitops::logand->=-0-linear-2)
    (:linear bitops::upper-bound-of-logand . 1)
    (:linear bitops::logand->=-0-linear-1)
    (:linear mv-nth-1-idiv-spec)
    (:linear mv-nth-1-div-spec)
    (:rewrite unsigned-byte-p-of-logand-2)
    (:linear acl2::expt->-1)
    (:rewrite acl2::unsigned-byte-p-loghead)
    (:type-prescription zip)
    (:linear bitops::logand-<-0-linear)
    (:rewrite bitops::logior-fold-consts)
    (:linear <=-logior)
    (:linear member-p-pos-value)
    (:linear member-p-pos-1-value)
    (:linear bitops::logior->=-0-linear)
    (:rewrite no-duplicates-p-and-append)
    (:rewrite acl2::subsetp-member . 2)
    (:rewrite acl2::subsetp-member . 1)
    (:type-prescription wr32$inline)
    (:rewrite unsigned-byte-p-of-logand-1)
    (:rewrite subset-p-cons-member-p-lemma)
    (:rewrite member-p-of-not-a-consp)
    (:rewrite get-prefixes-opener-lemma-zero-cnt)
    (:rewrite acl2::expt-with-violated-guards)
    (:rewrite bitops::basic-signed-byte-p-of-+)
    (:type-prescription ash)
    (:linear acl2::expt-is-increasing-for-base>1)
    (:definition member-equal)
    (:linear bitops::logior-<-0-linear-1)
    (:linear bitops::upper-bound-of-logior-for-naturals)
    (:linear bitops::expt-2-lower-bound-by-logbitp)
    open-qword-paddr-list
    cdr-create-canonical-address-list
    subset-p-cons-2
    (:definition addr-range)
    (:rewrite loghead-negative)
    (:rewrite member-p-cons)
    (:rewrite consp-of-create-canonical-address-list)
    (:rewrite car-create-canonical-address-list)
    (:type-prescription gather-all-paging-structure-qword-addresses)
    (:rewrite neg-addr-range=nil)
    (:definition no-duplicates-p)
    (:rewrite acl2::remove-duplicates-equal-when-atom)
    (:rewrite consp-mv-nth-1-las-to-pas)
    (:rewrite subset-p-of-nil)
    (:rewrite cdr-mv-nth-1-las-to-pas)
    (:rewrite
     mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p)
    (:rewrite get-prefixes-alt-opener-lemma-zero-cnt)
    (:rewrite member-p-of-nil)
    (:type-prescription bitops::part-select-width-low$inline)
    (:rewrite acl2::alistp-when-hons-duplicity-alist-p)
    (:rewrite
     mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p)
    (:rewrite car-mv-nth-1-las-to-pas)
    (:rewrite acl2::zp-when-integerp)
    (:type-prescription acl2::hons-duplicity-alist-p)
    (:type-prescription consp-mv-nth-1-las-to-pas)
    (:rewrite gl::nonnil-symbol-listp-true-listp)
    (:rewrite subset-p-two-create-canonical-address-lists-same-base-address)
    (:type-prescription !flgi)
    (:rewrite ia32e-la-to-pa-in-programmer-level-mode)
    (:rewrite acl2::zp-when-gt-0)
    (:rewrite acl2::logtail-identity)
    (:type-prescription acl2::nonnil-symbol-listp)
    (:rewrite acl2::hons-duplicity-alist-p-when-not-consp)
    (:rewrite acl2::consp-of-car-when-atom-listp)
    (:rewrite acl2::logext-identity)
    (:rewrite member-p-and-mult-8-qword-paddr-listp)
    (:rewrite cdr-canonical-address-listp)
    (:rewrite x86-run-halted)
    x86-fetch-decode-execute-opener
    member-p-strip-cars-of-remove-duplicate-keys
    mv-nth-1-ia32e-la-to-pa-when-error
    mv-nth-1-las-to-pas-when-error
    bitops::logand-with-negated-bitmask
    xlate-equiv-memory-and-xr-mem-from-rest-of-memory
    disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
    unsigned-byte-p))

(in-theory
 ;; For the effects theorem:
 (e/d* (instruction-decoding-and-spec-rules
        shr-spec
        shr-spec-64
        sal/shl-spec
        sal/shl-spec-64
        gpr-and-spec-1
        gpr-and-spec-4
        gpr-and-spec-8
        gpr-sub-spec-8
        gpr-or-spec-8
        gpr-xor-spec-4
        jcc/cmovcc/setcc-spec
        top-level-opcode-execute
        two-byte-opcode-decode-and-execute
        x86-operand-from-modr/m-and-sib-bytes
        x86-effective-addr
        x86-effective-addr-from-sib
        x86-operand-to-reg/mem
        rr08 rr32 rr64 wr08 wr32 wr64
        rim08 rim32 rim64
        !flgi-undefined
        write-user-rflags

        pos
        mv-nth-0-las-to-pas-subset-p
        member-p
        subset-p

        rb-alt-wb-equal-in-system-level-mode)

       (rewire_dst_to_src-disable)))

(encapsulate
  ()
  (local (in-theory (e/d () (xlate-equiv-memory-and-mv-nth-1-rm08))))

  (defthm mv-nth-0-rb-and-xw-mem-in-system-level-mode
    (implies (and (disjoint-p
                   (list index)
                   (all-translation-governing-addresses l-addrs (double-rewrite x86)))
                  (canonical-address-listp l-addrs)
                  (physical-address-p index))
             (equal (mv-nth 0 (rb l-addrs r-w-x (xw :mem index value x86)))
                    (mv-nth 0 (rb l-addrs r-w-x x86))))
    :hints (("Goal" :in-theory (e/d* (rb
                                      disjoint-p
                                      las-to-pas)
                                     (rewrite-rb-to-rb-alt
                                      force (force))))))

  (defthm read-from-physical-memory-xw-mem
    (implies (disjoint-p (list index) p-addrs)
             (equal (read-from-physical-memory p-addrs (xw :mem index value x86))
                    (read-from-physical-memory p-addrs x86)))
    :hints (("Goal" :in-theory (e/d* (read-from-physical-memory
                                      disjoint-p
                                      member-p)
                                     ()))))

  (defthm mv-nth-1-rb-and-xw-mem-in-system-level-mode
    (implies (and
              (disjoint-p
               (list index)
               (all-translation-governing-addresses l-addrs (double-rewrite x86)))
              (disjoint-p
               (list index)
               (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86))))
              (disjoint-p
               (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86)))
               (all-translation-governing-addresses l-addrs (double-rewrite x86)))
              (canonical-address-listp l-addrs)
              (physical-address-p index)
              (not (programmer-level-mode x86)))
             (equal (mv-nth 1 (rb l-addrs r-w-x (xw :mem index value x86)))
                    (mv-nth 1 (rb l-addrs r-w-x x86))))
    :hints (("Goal" :in-theory (e/d* (rb
                                      disjoint-p
                                      disjoint-p-commutative
                                      las-to-pas)
                                     (rewrite-rb-to-rb-alt
                                      xlate-equiv-memory-and-xr-mem-from-rest-of-memory
                                      force (force))))))

  (local
   (defthm get-prefixes-xw-mem-values-in-system-level-mode-helper-1
     (implies (and (not (zp cnt))
                   (canonical-address-p start-rip)
                   (canonical-address-p (+ cnt start-rip)))
              (canonical-address-p (+ 1 start-rip)))
     :hints (("Goal" :in-theory (e/d* (canonical-address-p
                                       signed-byte-p)
                                      ())))))

  (local
   (in-theory (e/d (member-p-of-nil)
                   ((:rewrite mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)
                    (:rewrite get-prefixes-opener-lemma-no-prefix-byte)
                    (:rewrite open-qword-paddr-list-and-member-p)
                    (:rewrite not-member-p-when-disjoint-p)
                    (:rewrite xlate-equiv-memory-and-two-get-prefixes-values)
                    (:rewrite r-w-x-is-irrelevant-for-mv-nth-1-las-to-pas-when-no-errors)
                    (:rewrite mult-8-qword-paddr-listp-gather-all-paging-structure-qword-addresses)
                    (:rewrite las-to-pas-values-and-xw-mem-not-member)
                    (:rewrite xlate-equiv-memory-with-mv-nth-2-las-to-pas)
                    (:type-prescription bitops::logior-natp-type)
                    (:rewrite acl2::loghead-identity)
                    (:rewrite bitops::logand-with-bitmask)
                    (:type-prescription acl2::bitmaskp$inline)
                    (:rewrite bitops::loghead-of-logior)
                    (:type-prescription bitops::logand-natp-type-1)
                    (:rewrite bitops::logtail-of-logior)
                    (:rewrite acl2::fold-consts-in-+)
                    (:type-prescription create-canonical-address-list)
                    (:rewrite member-p-canonical-address-listp)
                    (:rewrite bitops::loghead-of-logand)
                    (:rewrite bitops::logtail-of-ash)
                    (:rewrite canonical-address-p-limits-thm-1)
                    (:rewrite canonical-address-p-limits-thm-0)
                    (:rewrite bitops::logtail-of-logand)
                    (:rewrite mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free)
                    (:rewrite mv-nth-2-las-to-pas-system-level-non-marking-mode)
                    (:type-prescription member-p-physical-address-p-physical-address-listp)
                    (:type-prescription member-p-physical-address-p)
                    (:rewrite programmer-level-mode-rm08-no-error)
                    (:rewrite rb-returns-x86-programmer-level-mode)
                    (:rewrite mv-nth-2-rb-in-system-level-non-marking-mode)
                    (:rewrite rb-in-terms-of-rb-subset-p-in-system-level-mode)
                    (:rewrite rb-returns-no-error-programmer-level-mode)
                    (:rewrite gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint)
                    (:rewrite rm08-does-not-affect-state-in-programmer-level-mode)
                    (:rewrite mv-nth-2-rm08-in-system-level-non-marking-mode)
                    (:rewrite acl2::simplify-logand)
                    (:rewrite bitops::associativity-of-logand)
                    (:rewrite bitops::logior-equal-0)
                    (:type-prescription xlate-equiv-memory)
                    (:linear n43p-get-prefixes)
                    (:rewrite rm08-xw-system-mode)
                    (:rewrite rm08-xw-programmer-level-mode)
                    (:type-prescription acl2::|x < y  =>  0 < y-x|)
                    (:rewrite get-prefixes-xw-values-in-system-level-mode)
                    (:linear n08p-mv-nth-1-rm08)
                    (:rewrite bitops::loghead-of-loghead-1)
                    (:definition n43p$inline)
                    (:type-prescription logtail-*2^x-byte-pseudo-page*-of-physical-address)
                    (:type-prescription acl2::logtail$inline)
                    (:rewrite bitops::logand-fold-consts)
                    (:rewrite bitops::loghead-of-0-i)
                    (:type-prescription signed-byte-p)
                    (:rewrite loghead-ash-0)
                    (:type-prescription n43p$inline)
                    (:rewrite bitops::logtail-of-logtail)
                    (:rewrite acl2::distributivity-of-minus-over-+)
                    (:rewrite gather-all-paging-structure-qword-addresses-xw-fld!=mem-and-ctr)
                    (:rewrite bitops::loghead-of-ash-same)
                    (:rewrite bitops::signed-byte-p-monotonicity)
                    (:type-prescription rm-low-64-logand-logior-helper-1)
                    (:rewrite acl2::posp-rw)
                    (:type-prescription bitops::part-install-width-low$inline)
                    (:type-prescription bitops::natp-part-install-width-low)
                    (:rewrite acl2::natp-posp)
                    (:type-prescription n64p$inline)
                    (:rewrite bitops::logand-of-logand-self-1)
                    (:linear rm-low-64-logand-logior-helper-1)
                    (:definition n64p$inline)))))

  (local
   (defthmd disjoint-p-all-translation-governing-addresses-and-las-to-pas-subset-p
     ;; Very similar to
     ;; MV-NTH-1-LAS-TO-PAS-SUBSET-P-DISJOINT-FROM-OTHER-P-ADDRS,
     ;; DISJOINTNESS-OF-ALL-TRANSLATION-GOVERNING-ADDRESSES-FROM-ALL-TRANSLATION-GOVERNING-ADDRESSES-SUBSET-P.

     ;; This rule is tailored to rewrite terms of the form

     ;; (disjoint-p (all-translation-governing-addresses l-addrs-subset x86)
     ;;             (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86)))

     ;; where l-addrs-subset is a subset of l-addrs, and l-addrs is of
     ;; the form (create-canonical-address-list ...).

     (implies
      (and
       (bind-free (find-l-addrs-like-create-canonical-address-list-from-fn
                   'all-translation-governing-addresses 'l-addrs mfc state)
                  (l-addrs))
       ;; (syntaxp (not (cw "~% l-addrs: ~x0~%" l-addrs))) ; ;
       (disjoint-p
        (all-translation-governing-addresses l-addrs (double-rewrite x86))
        (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86))))
       (subset-p l-addrs-subset l-addrs)
       (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86)))))
      (disjoint-p (all-translation-governing-addresses l-addrs-subset x86)
                  (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86))))
     :hints
     (("Goal"
       :use ((:instance disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
                        (l-addrs l-addrs)
                        (l-addrs-subset l-addrs-subset)
                        (other-p-addrs (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))
                        (other-p-addrs-subset (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86)))))
       :in-theory (e/d* (subset-p
                         member-p
                         disjoint-p-append-1
                         las-to-pas
                         all-translation-governing-addresses)
                        ())))))

  (defthm get-prefixes-xw-mem-in-system-level-mode
    (implies
     (and
      (disjoint-p
       (mv-nth 1 (las-to-pas
                  (create-canonical-address-list cnt start-rip)
                  :x (cpl x86) (double-rewrite x86)))
       (all-translation-governing-addresses
        (create-canonical-address-list cnt start-rip) (double-rewrite x86)))
      (disjoint-p
       (list index)
       (mv-nth 1 (las-to-pas (create-canonical-address-list cnt start-rip)
                             :x (cpl x86) (double-rewrite x86))))
      (disjoint-p
       (list index)
       (all-translation-governing-addresses
        (create-canonical-address-list cnt start-rip) (double-rewrite x86)))
      (not (mv-nth 0 (las-to-pas
                      (create-canonical-address-list cnt start-rip)
                      :x (cpl x86) x86)))
      (posp cnt)
      (canonical-address-p start-rip)
      (canonical-address-p (+ cnt start-rip))
      (physical-address-p index)
      (unsigned-byte-p 8 value)
      (not (programmer-level-mode x86))
      (page-structure-marking-mode x86)
      (x86p x86))
     (and
      (equal (mv-nth 0 (get-prefixes start-rip prefixes cnt (xw :mem index value x86)))
             (mv-nth 0 (get-prefixes start-rip prefixes cnt x86)))
      (equal (mv-nth 1 (get-prefixes start-rip prefixes cnt (xw :mem index value x86)))
             (mv-nth 1 (get-prefixes start-rip prefixes cnt x86)))
      (equal (mv-nth 2 (get-prefixes start-rip prefixes cnt (xw :mem index value x86)))
             (xw :mem index value (mv-nth 2 (get-prefixes start-rip prefixes cnt x86))))))
    :hints
    (("Goal"

      :induct (get-prefixes-two-x86-induct-hint
               start-rip prefixes cnt x86 (xw :mem index value x86))
      :expand ((get-prefixes start-rip prefixes cnt (xw :mem index value x86))
               (get-prefixes start-rip prefixes cnt x86))
      :in-theory (e/d* (get-prefixes
                        disjoint-p$
                        disjoint-p-commutative
                        disjoint-p-all-translation-governing-addresses-and-las-to-pas-subset-p)
                       (mv-nth-1-rb-after-mv-nth-2-las-to-pas
                        infer-disjointness-with-all-translation-governing-addresses-from-gather-all-paging-structure-qword-addresses
                        all-translation-governing-addresses-and-xw-mem-not-member
                        r/x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors
                        xr-programmer-level-mode-mv-nth-2-las-to-pas
                        all-translation-governing-addresses-and-xw-not-mem
                        xr-seg-visible-mv-nth-2-las-to-pas
                        xr-page-structure-marking-mode-mv-nth-2-las-to-pas
                        disjoint-p
                        member-p
                        disjoint-p-cons-1
                        rewrite-get-prefixes-to-get-prefixes-alt
                        rewrite-rb-to-rb-alt
                        create-canonical-address-list
                        xlate-equiv-memory-and-two-get-prefixes-values
                        xlate-equiv-memory-and-xr-mem-from-rest-of-memory
                        xr-las-to-pas
                        rb-xw-values-in-programmer-level-mode
                        (:t acl2::expt-type-prescription-integerp)
                        bitops::commutativity-2-of-logand
                        mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                        get-prefixes-does-not-modify-x86-state-in-system-level-non-marking-mode
                        get-prefixes-does-not-modify-x86-state-in-programmer-level-mode
                        acl2::zp-open
                        not)))))

  (defthm get-prefixes-and-write-to-physical-memory
    (implies
     (and
      (disjoint-p
       (mv-nth 1
               (las-to-pas (create-canonical-address-list cnt start-rip)
                           :x (cpl x86) (double-rewrite x86)))
       (all-translation-governing-addresses
        (create-canonical-address-list cnt start-rip) (double-rewrite x86)))
      (disjoint-p
       p-addrs
       (mv-nth
        1
        (las-to-pas (create-canonical-address-list cnt start-rip)
                    :x (cpl x86) (double-rewrite x86))))
      (disjoint-p
       p-addrs
       (all-translation-governing-addresses
        (create-canonical-address-list cnt start-rip) (double-rewrite x86)))
      (not (mv-nth 0 (las-to-pas (create-canonical-address-list cnt start-rip)
                                 :x (cpl x86) x86)))
      (posp cnt)
      (canonical-address-p start-rip)
      (canonical-address-p (+ cnt start-rip))
      (physical-address-listp p-addrs)
      (byte-listp bytes)
      (equal (len p-addrs) (len bytes))
      (not (programmer-level-mode x86))
      (page-structure-marking-mode x86)
      (x86p x86))
     (and
      (equal
       (mv-nth 0 (get-prefixes start-rip prefixes cnt
                               (write-to-physical-memory p-addrs bytes x86)))
       (mv-nth 0 (get-prefixes start-rip prefixes cnt x86)))
      (equal
       (mv-nth 1 (get-prefixes start-rip prefixes cnt
                               (write-to-physical-memory p-addrs bytes x86)))
       (mv-nth 1 (get-prefixes start-rip prefixes cnt x86)))
      (equal
       (mv-nth 2 (get-prefixes start-rip prefixes cnt
                               (write-to-physical-memory p-addrs bytes x86)))
       (write-to-physical-memory p-addrs bytes
                                 (mv-nth 2 (get-prefixes start-rip prefixes cnt x86))))))
    :hints (("Goal"
             :induct (cons (write-to-physical-memory p-addrs bytes x86)
                           (byte-listp bytes))
             :in-theory (e/d* (las-to-pas-values-and-xw-mem-not-member
                               gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint
                               disjoint-p
                               member-p
                               write-to-physical-memory
                               byte-listp
                               n08p len)
                              (rewrite-get-prefixes-to-get-prefixes-alt
                               rm08-to-rb
                               rewrite-rb-to-rb-alt
                               las-to-pas-values-and-write-to-physical-memory-disjoint
                               get-prefixes-xw-mem-values-in-system-level-mode-helper-1
                               xlate-equiv-memory-and-two-get-prefixes-values)))))

  (defthm get-prefixes-alt-and-write-to-physical-memory-disjoint-from-paging-structures
    (implies
     (and
      (disjoint-p
       p-addrs
       (mv-nth 1
               (las-to-pas (create-canonical-address-list cnt start-rip)
                           :x (cpl x86) (double-rewrite x86))))
      (disjoint-p$
       p-addrs
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
      (posp cnt)
      (canonical-address-p (+ cnt start-rip))
      (physical-address-listp p-addrs)
      (byte-listp bytes)
      (equal (len p-addrs) (len bytes))
      (x86p x86))
     (and
      (equal
       (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt (write-to-physical-memory p-addrs bytes x86)))
       (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt x86)))
      (equal
       (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt (write-to-physical-memory p-addrs bytes x86)))
       (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt x86)))
      (equal
       (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt (write-to-physical-memory p-addrs bytes x86)))
       (write-to-physical-memory p-addrs bytes
                                 (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86))))))
    :hints
    (("Goal"
      :do-not-induct t
      :use ((:instance get-prefixes-and-write-to-physical-memory)
            (:instance all-translation-governing-addresses-subset-of-paging-structures
                       (l-addrs (create-canonical-address-list cnt start-rip))))
      :in-theory
      (e/d*
       (get-prefixes-alt
        subset-p
        disjoint-p$
        disjoint-p-commutative
        disjoint-p-subset-p)
       (rewrite-rb-to-rb-alt
        rewrite-get-prefixes-to-get-prefixes-alt
        get-prefixes-and-write-to-physical-memory
        xlate-equiv-memory-and-two-get-prefixes-values
        mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
        all-translation-governing-addresses-subset-of-paging-structures
        force (force))))))

  (defthm get-prefixes-alt-and-wb-in-system-level-marking-mode-disjoint-from-paging-structures
    (implies
     (and
      (disjoint-p$
       (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
      (disjoint-p
       (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
       (mv-nth 1 (las-to-pas
                  (create-canonical-address-list cnt start-rip)
                  :x (cpl x86) (double-rewrite x86))))
      (posp cnt)
      (canonical-address-p (+ cnt start-rip))
      (addr-byte-alistp addr-lst)
      (not (programmer-level-mode x86))
      (x86p x86))
     (and
      (equal
       (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt (mv-nth 1 (wb addr-lst x86))))
       (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt x86)))
      (equal
       (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt (mv-nth 1 (wb addr-lst x86))))
       (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt x86)))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d* (las-to-pas
                               disjoint-p$
                               wb
                               disjoint-p-commutative
                               infer-disjointness-with-all-translation-governing-addresses-from-gather-all-paging-structure-qword-addresses
                               xlate-equiv-memory-with-mv-nth-2-las-to-pas)
                              (rewrite-get-prefixes-to-get-prefixes-alt
                               xlate-equiv-memory-and-two-get-prefixes-values
                               xlate-equiv-memory-and-xr-mem-from-rest-of-memory)))))

  (local
   (defthm subset-p-and-open-qword-paddr-list
     (implies (subset-p x y)
              (subset-p (open-qword-paddr-list x) (open-qword-paddr-list y)))
     :hints (("Goal" :in-theory (e/d* (subset-p open-qword-paddr-list) ())))))

  (defthm disjointness-of-las-to-pas-from-subset-of-paging-structures
    (implies (and
              (equal p-addrs (addr-range 8 index))
              (disjoint-p
               (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86))
               (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86)))
              (equal (page-size (combine-bytes bytes)) 1)
              (physical-address-p index)
              (equal (loghead 3 index) 0)
              (byte-listp bytes)
              (equal (len bytes) 8)
              (not (programmer-level-mode x86)))
             (disjoint-p
              (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86))
              (open-qword-paddr-list
               (gather-all-paging-structure-qword-addresses (write-to-physical-memory p-addrs bytes x86)))))
    :hints (("Goal"
             :use ((:instance gather-all-paging-structure-qword-addresses-and-write-to-physical-memory-subset-p)
                   (:instance disjoint-p-subset-p
                              (x (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))
                              (y (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86)))
                              (a (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))
                              (b (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses (write-to-physical-memory p-addrs bytes x86))))))
             :in-theory (e/d* (subset-p
                               subset-p-reflexive)
                              (disjoint-p-subset-p
                               gather-all-paging-structure-qword-addresses-and-write-to-physical-memory-subset-p)))))

  (defthm get-prefixes-alt-and-write-to-physical-memory-paging-structures
    (implies
     (and
      (equal p-addrs (addr-range 8 index))
      (disjoint-p
       (mv-nth 1
               (las-to-pas
                (create-canonical-address-list cnt start-rip)
                :x (cpl x86) (double-rewrite x86)))
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
      (disjoint-p
       p-addrs
       (mv-nth 1
               (las-to-pas (create-canonical-address-list cnt start-rip)
                           :x (cpl x86) (double-rewrite x86))))
      (disjoint-p$
       p-addrs
       (all-translation-governing-addresses
        (create-canonical-address-list cnt start-rip)
        (double-rewrite x86)))
      (equal (page-size (combine-bytes bytes)) 1)
      (posp cnt)
      (canonical-address-p (+ cnt start-rip))
      (physical-address-listp p-addrs)
      (byte-listp bytes)
      (equal (len bytes) 8)
      (physical-address-p index)
      (equal (loghead 3 index) 0)
      (x86p x86))
     (and
      (equal
       (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt (write-to-physical-memory p-addrs bytes x86)))
       (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt x86)))
      (equal
       (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt (write-to-physical-memory p-addrs bytes x86)))
       (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt x86)))
      (equal
       (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt (write-to-physical-memory p-addrs bytes x86)))
       (write-to-physical-memory p-addrs bytes
                                 (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86))))))
    :hints
    (("Goal"
      :do-not-induct t
      :use ((:instance get-prefixes-and-write-to-physical-memory)
            (:instance all-translation-governing-addresses-subset-of-paging-structures
                       (l-addrs (create-canonical-address-list cnt start-rip)))
            (:instance disjointness-of-las-to-pas-from-subset-of-paging-structures
                       (index index)
                       (cpl (cpl x86))
                       (p-addrs (addr-range 8 index))
                       (l-addrs (create-canonical-address-list cnt start-rip))
                       (r-w-x :x)))
      :in-theory
      (e/d*
       (get-prefixes-alt
        subset-p
        disjoint-p$
        disjoint-p-subset-p)
       (disjointness-of-las-to-pas-from-subset-of-paging-structures
        rewrite-rb-to-rb-alt
        rewrite-get-prefixes-to-get-prefixes-alt
        get-prefixes-and-write-to-physical-memory
        xlate-equiv-memory-and-two-get-prefixes-values
        mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
        all-translation-governing-addresses-subset-of-paging-structures
        force (force))))))

  (defun-nx direct-map-p (count addr r-w-x cpl x86)
    (equal
     (mv-nth 1 (las-to-pas (create-canonical-address-list count addr) r-w-x cpl x86))
     (addr-range count addr)))

  (defthm get-prefixes-alt-and-wb-to-paging-structures
    (implies
     (and
      (equal (page-size value) 1)
      (direct-map-p 8 lin-addr :w (cpl x86) (double-rewrite x86))
      ;; (equal (mv-nth 1 (las-to-pas (create-canonical-address-list 8 lin-addr)
      ;;                              :w (cpl x86) (double-rewrite x86)))
      ;;        (addr-range 8 lin-addr))

      (disjoint-p
       (mv-nth 1
               (las-to-pas (create-canonical-address-list cnt start-rip)
                           :x (cpl x86) (double-rewrite x86)))
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
      (disjoint-p
       (mv-nth 1 (las-to-pas (create-canonical-address-list 8 lin-addr)
                             :w (cpl x86) (double-rewrite x86)))
       (all-translation-governing-addresses
        (create-canonical-address-list cnt start-rip) (double-rewrite x86)))
      (disjoint-p
       (mv-nth 1 (las-to-pas (create-canonical-address-list 8 lin-addr)
                             :w (cpl x86) (double-rewrite x86)))
       (mv-nth 1 (las-to-pas
                  (create-canonical-address-list cnt start-rip)
                  :x (cpl x86) (double-rewrite x86))))
      (posp cnt)
      (canonical-address-p (+ cnt start-rip))
      ;; !!
      (physical-address-p lin-addr)
      (equal (loghead 3 lin-addr) 0)
      (canonical-address-p lin-addr)
      ;; !!
      (unsigned-byte-p 64 value)
      (not (programmer-level-mode x86))
      (x86p x86))
     (and
      (equal
       (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt
                                   (mv-nth 1 (wb
                                              (create-addr-bytes-alist
                                               (create-canonical-address-list 8 lin-addr)
                                               (byte-ify 8 value))
                                              x86))))
       (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt x86)))
      (equal
       (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt
                                   (mv-nth 1 (wb
                                              (create-addr-bytes-alist
                                               (create-canonical-address-list 8 lin-addr)
                                               (byte-ify 8 value))
                                              x86))))
       (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt x86)))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance get-prefixes-alt-and-write-to-physical-memory-paging-structures
                              (index lin-addr)
                              (p-addrs (mv-nth 1 (las-to-pas (create-canonical-address-list 8 lin-addr)
                                                             :w (cpl x86) x86)))
                              (bytes (byte-ify 8 value))
                              (x86 (mv-nth 2 (las-to-pas (create-canonical-address-list 8 lin-addr)
                                                         :w (cpl x86) x86)))))
             :in-theory (e/d* (get-prefixes-alt-and-write-to-physical-memory-paging-structures
                               las-to-pas
                               acl2::loghead-identity
                               acl2::fold-consts-in-+
                               disjoint-p$
                               wb
                               infer-disjointness-with-all-translation-governing-addresses-from-gather-all-paging-structure-qword-addresses
                               xlate-equiv-memory-with-mv-nth-2-las-to-pas)
                              (rewrite-get-prefixes-to-get-prefixes-alt
                               xlate-equiv-memory-and-two-get-prefixes-values
                               xlate-equiv-memory-and-xr-mem-from-rest-of-memory))))))

(defthm xr-fault-rb-state-in-system-level-mode
  (implies (not (mv-nth 0 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86))))
           (equal (xr :fault index (mv-nth 2 (rb l-addrs r-w-x x86)))
                  (xr :fault index x86)))
  :hints (("Goal" :in-theory (e/d* (las-to-pas rb) (rewrite-rb-to-rb-alt force (force))))))

(defthm xr-ms-rb-state-in-system-level-mode
  (implies (not (mv-nth 0 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86))))
           (equal (xr :ms index (mv-nth 2 (rb l-addrs r-w-x x86)))
                  (xr :ms index x86)))
  :hints (("Goal" :in-theory (e/d* (las-to-pas rb) (rewrite-rb-to-rb-alt force (force))))))

(defun get-both-l-addrs
  (match-fn l-addrs-subset-1 l-addrs-subset-2 term-1 term-2)
  ;; (get-both-l-addrs
  ;;  'las-to-pas
  ;;  '(create-canonical-address-list 4 rgf)
  ;;  '(create-canonical-address-list 4 start-rip)
  ;;  '(mv-nth 1 (las-to-pas '(create-canonical-address-list 4 rgf) r-w-x cpl (double-rewrite x86)))
  ;;  '(mv-nth 1 (las-to-pas '(create-canonical-address-list 20 start-rip) r-w-x cpl (double-rewrite x86))))
  (if (and (consp term-1)
           (consp (cdr term-1))
           (consp (cddr term-1))
           (consp (caddr term-1))
           (consp term-2)
           (consp (cdr term-2))
           (consp (cddr term-2))
           (consp (caddr term-2)))
      (b* ((fn-1 (car (caddr term-1)))
           (fn-2 (car (caddr term-2)))
           ;; (- (cw "~%fn-1: ~x0 and fn-2: ~x1~%" fn-1 fn-2))
           ((when (or (not (equal fn-1 fn-2))
                      (and (equal fn-1 fn-2)
                           (not (equal fn-1 match-fn)))))
            ;; (cw "~%~x0 and ~x1 unequal or match-fn ~x2 not found.~%" fn-1 fn-2 match-fn)
            nil)
           (l-addrs-1 (second (caddr term-1)))
           (l-addrs-2 (second (caddr term-2)))
           ((when (and (equal `(quote ,l-addrs-subset-1) l-addrs-1)
                       (equal `(quote ,l-addrs-subset-2) l-addrs-2)))
            ;; (cw "~%l-addrs-subsets: ~x0 and ~x1~%~% l-addrs: ~x2 and ~x3~%~%"
            ;;     `(quote ,l-addrs-subset-1) `(quote ,l-addrs-subset-2) l-addrs-1 l-addrs-2)
            ;; (cw "~% equal-1 ~x0~%~% equal-2: ~x1~%~%"
            ;;     (equal `(quote ,l-addrs-subset-1) l-addrs-1)
            ;;     (equal `(quote ,l-addrs-subset-2) l-addrs-2))
            ;; Both l-addrs shouldn't be equal to their subsets,
            ;; though one of them can be.
            nil))
        `(((l-addrs-1 . ,l-addrs-1)
           (l-addrs-2 . ,l-addrs-2))))
    nil))

(defun find-both-l-addrs-from-disjoint-p$-of-las-to-pas-aux
  (l-addrs-subset-1 l-addrs-subset-2 calls)
  ;; The first alist below will be weeded out by
  ;; the syntaxp in the theorem.

  ;; (find-both-l-addrs-from-disjoint-p$-of-las-to-pas-aux
  ;;  '(create-canonical-address-list 4 rgf)
  ;;  '(create-canonical-address-list 4 start-rip)
  ;;  '((disjoint-p
  ;;     (mv-nth 1 (las-to-pas '(create-canonical-address-list 20 start-rip) r-w-x cpl x86))
  ;;     (mv-nth 1 (las-to-pas '(create-canonical-address-list 20 start-rip) r-w-x cpl x86)))
  ;;    (disjoint-p
  ;;     (mv-nth 1 (las-to-pas '(create-canonical-address-list 4 rgf) r-w-x cpl x86))
  ;;     (mv-nth 1 (las-to-pas '(create-canonical-address-list 20 start-rip) r-w-x cpl x86)))
  ;;    (disjoint-p (mv-nth 1 (las-to-pas a b c)) a)
  ;;    (disjoint-p b a)
  ;;    (disjoint-p (mv-nth 1 (las-to-pas 1 2 43)) (mv-nth 1 (las-to-pas 9 8 7)))))
  (if (endp calls)
      nil
    (append (get-both-l-addrs
             'las-to-pas l-addrs-subset-1 l-addrs-subset-2
             (second (car calls)) (third (car calls)))
            (find-both-l-addrs-from-disjoint-p$-of-las-to-pas-aux
             l-addrs-subset-1 l-addrs-subset-2
             (cdr calls)))))

(defun find-both-l-addrs-from-disjoint-p$-of-las-to-pas
  (l-addrs-subset-1 l-addrs-subset-2 mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-calls-lst 'disjoint-p$ (acl2::mfc-clause mfc)))
       ((when (not calls)) nil))
    (find-both-l-addrs-from-disjoint-p$-of-las-to-pas-aux
     l-addrs-subset-1 l-addrs-subset-2 calls)))

(defthm two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas
  ;; This rule is tailored to rewrite terms of the form to t

  ;; (disjoint-p
  ;;  (mv-nth 1 (las-to-pas l-addrs-subset-1 r-w-x-1 cpl-1 x86))
  ;;  (mv-nth 1 (las-to-pas l-addrs-subset-2 r-w-x-2 cpl-2 x86)))

  ;; where l-addrs-subset-1 is a subset of l-addrs-1, l-addrs-subset-2
  ;; is a subset of l-addrs-2, and l-addrs-1 and l-addrs-2 are of the
  ;; form (create-canonical-address-list ...).
  (implies
   (and
    (syntaxp (not (equal l-addrs-subset-1 l-addrs-subset-2)))
    (bind-free (find-both-l-addrs-from-disjoint-p$-of-las-to-pas
                l-addrs-subset-1 l-addrs-subset-2 mfc state)
               (l-addrs-1 l-addrs-2))
    ;; (syntaxp (not (cw "~%~% !!! l-addrs-1: ~x0 ~% !!! l-addrs-2: ~x0~%~%" l-addrs-1 l-addrs-2)))
    (disjoint-p$
     (mv-nth 1 (las-to-pas l-addrs-1 r-w-x-1 cpl-1 (double-rewrite x86)))
     (mv-nth 1 (las-to-pas l-addrs-2 r-w-x-2 cpl-2 (double-rewrite x86))))
    (subset-p l-addrs-subset-1 l-addrs-1)
    (subset-p l-addrs-subset-2 l-addrs-2)
    (not (mv-nth 0 (las-to-pas l-addrs-1 r-w-x-1 cpl-1 x86)))
    (not (mv-nth 0 (las-to-pas l-addrs-2 r-w-x-2 cpl-2 x86))))
   (disjoint-p
    (mv-nth 1 (las-to-pas l-addrs-subset-1 r-w-x-1 cpl-1 x86))
    (mv-nth 1 (las-to-pas l-addrs-subset-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance mv-nth-1-las-to-pas-subset-p
                            (l-addrs l-addrs-1)
                            (l-addrs-subset l-addrs-subset-1)
                            (r-w-x r-w-x-1)
                            (cpl cpl-1))
                 (:instance mv-nth-1-las-to-pas-subset-p
                            (l-addrs l-addrs-2)
                            (l-addrs-subset l-addrs-subset-2)
                            (r-w-x r-w-x-2)
                            (cpl cpl-2))
                 (:instance disjoint-p-subset-p
                            (x (mv-nth 1 (las-to-pas l-addrs-1 r-w-x-1 cpl-1 x86)))
                            (y (mv-nth 1 (las-to-pas l-addrs-2 r-w-x-2 cpl-2 x86)))
                            (a (mv-nth 1 (las-to-pas l-addrs-subset-1 r-w-x-1 cpl-1 x86)))
                            (b (mv-nth 1 (las-to-pas l-addrs-subset-2 r-w-x-2 cpl-2 x86)))))
           :in-theory (e/d* (disjoint-p$)
                            (mv-nth-1-las-to-pas-subset-p
                             disjoint-p-subset-p)))))

(in-theory (e/d* ()
                 (mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs-alt
                  mv-nth-0-las-to-pas-subset-p
                  (:type-prescription true-listp-mv-nth-1-las-to-pas)
                  (:rewrite disjoint-p-all-translation-governing-addresses-subset-p)
                  (:type-prescription rm-low-64-logand-logior-helper-1)
                  (:type-prescription n64p$inline)
                  (:definition strip-cars)
                  (:type-prescription !ms$inline)
                  (:rewrite consp-create-addr-bytes-alist-in-terms-of-len)
                  (:rewrite bitops::signed-byte-p-monotonicity)
                  (:linear mv-nth-1-gpr-sbb-spec-8)
                  (:linear mv-nth-1-gpr-add-spec-8)
                  (:linear mv-nth-1-gpr-adc-spec-8)
                  (:rewrite strip-cars-addr-byte-alistp-is-canonical-address-listp)
                  (:rewrite acl2::subsetp-member . 3)
                  (:rewrite acl2::zp-open)
                  (:type-prescription subsetp-equal)
                  (:definition addr-byte-alistp)
                  (:type-prescription acl2::|x < y  =>  0 < y-x|)
                  (:linear mv-nth-1-gpr-xor-spec-8)
                  (:type-prescription !rip$inline)
                  (:linear acl2::index-of-<-len)
                  (:type-prescription create-addr-bytes-alist)
                  (:type-prescription x86-step-unimplemented)
                  (:type-prescription strip-cars-addr-byte-alistp-is-canonical-address-listp)
                  (:type-prescription !rgfi-size$inline)
                  (:rewrite canonical-address-p-limits-thm-4)
                  (:linear mv-nth-2-gpr-sbb-spec-8)
                  (:linear mv-nth-2-gpr-add-spec-8)
                  (:linear mv-nth-2-gpr-adc-spec-8)
                  (:rewrite byte-ify-and-combine-bytes)
                  (:rewrite bitops::basic-signed-byte-p-of-binary-minus)
                  (:rewrite acl2::subsetp-member . 4)
                  (:rewrite acl2::member-when-atom)
                  (:linear mv-nth-2-gpr-xor-spec-8)
                  (:type-prescription n08p$inline)
                  (:rewrite cdr-strip-cars-is-strip-cars-cdr)
                  (:linear ctri-is-n64p)
                  (:type-prescription strip-cars)
                  (:type-prescription !rgfi$inline)
                  (:rewrite signed-byte-p-limits-thm)
                  (:rewrite canonical-address-p-and-signed-byte-p-64p-limits-1)
                  (:rewrite bitops::logbitp-of-loghead-out-of-bounds)
                  (:type-prescription bitops::natp-part-install-width-low))))

(defthm and-i-thought-i-would-never-need-these-rules
  ;; Congruence rules and extra double-rewrites didn't take me very
  ;; far, did they?  Sigh.
  (and (equal (mv-nth 0 (get-prefixes-alt start-rip cnt prefixes
                                          (mv-nth 2 (rb-alt l-addrs r-w-x x86))))
              (mv-nth 0 (get-prefixes-alt start-rip cnt prefixes x86)))
       (equal (mv-nth 1 (get-prefixes-alt start-rip cnt prefixes
                                          (mv-nth 2 (rb-alt l-addrs r-w-x x86))))
              (mv-nth 1 (get-prefixes-alt start-rip cnt prefixes x86)))
       (equal (mv-nth 0 (get-prefixes-alt start-rip-1 cnt-1 prefixes-1
                                          (mv-nth 2 (get-prefixes-alt start-rip-2 cnt-2 prefixes-2 x86))))
              (mv-nth 0 (get-prefixes-alt start-rip-1 cnt-1 prefixes-1 x86)))
       (equal (mv-nth 1 (get-prefixes-alt start-rip-1 cnt-1 prefixes-1
                                          (mv-nth 2 (get-prefixes-alt start-rip-2 cnt-2 prefixes-2 x86))))
              (mv-nth 1 (get-prefixes-alt start-rip-1 cnt-1 prefixes-1 x86)))))

(defun-nx source-PML4TE-and-program-no-interfere-p (x86)
  ;; The PML4TE physical addresses are disjoint from the
  ;; translation-governing addresses of the program.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8
               (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
              :r (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
    x86)))

(defun-nx source-PML4TE-itself-no-interfere-p (x86)
  ;; The PML4TE physical addresses are disjoint from the
  ;; translation-governing addresses of the PML4TE.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8
               (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
              :r (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list
     8
     (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
    x86)))

(defun-nx source-PML4TE-and-stack-no-interfere-p-aux (x86)
  (and
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list
                8
                (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
               :r (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list 8 (+ -24 (xr :rgf 4 x86)))
     x86))
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list 8 (+ -24 (xr :rgf 4 x86)))
               :w (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
     x86))))

(defun-nx source-PDPTE-and-program-no-interfere-p (x86)
  ;; The PDPTE physical addresses are disjoint from the
  ;; translation-governing addresses of the program.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rdi* x86)
                (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
              :r (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
    x86)))

(defun-nx source-PDPTE-itself-no-interfere-p (x86)
  ;; The PDPTE physical addresses are disjoint from the
  ;; translation-governing addresses of the PDPTE.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rdi* x86)
                (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
              :r (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rdi* x86)
      (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
    x86)))

(defun-nx source-PDPTE-and-stack-no-interfere-p-aux (x86)
  ;; The PDPTE physical addresses are disjoint from the
  ;; translation-governing addresses of the PDPTE.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rdi* x86)
                (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
              :r (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list 8 (+ -24 (xr :rgf 4 x86)))
    x86)))

(defun-nx source-PDPTE-and-source-PML4E-no-interfere-p (x86)
  ;; The PDPTE physical addresses are disjoint from the
  ;; translation-governing addresses of the PML4E.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rdi* x86)
                (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
              :r (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list
     8
     (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
    x86)))

(defun-nx destination-PML4TE-and-program-no-interfere-p (x86)
  ;; The PML4TE physical addresses are disjoint from the
  ;; translation-governing addresses of the program.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8
               (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
              :r (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
    x86)))

(defun-nx destination-PML4TE-itself-no-interfere-p (x86)
  ;; The PML4TE physical addresses are disjoint from the
  ;; translation-governing addresses of the PML4TE.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8
               (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
              :r (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list
     8
     (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
    x86)))

(defun-nx destination-PML4TE-and-stack-no-interfere-p-aux (x86)
  (and
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list
                8
                (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
               :r (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list 8 (+ -24 (xr :rgf 4 x86)))
     x86))
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
     x86))))

(defun-nx destination-PML4TE-and-source-PML4TE-no-interfere-p (x86)
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8
               (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
              :r (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list
     8
     (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
    x86)))

(defun-nx destination-PML4TE-and-source-PDPTE-no-interfere-p (x86)
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8
               (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
              :r (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rdi* x86)
      (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
    x86)))

(defun-nx program-and-stack-no-interfere-p-aux (x86)
  (disjoint-p$
   (mv-nth 1
           (las-to-pas
            (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
            :w (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
    x86)))

(defun-nx destination-PDPTE-itself-no-interfere-p (x86)
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
              :r (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rsi* x86)
      (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
    x86)))

(defun-nx destination-PDPTE-and-stack-no-interfere-p-aux (x86)
  (and
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list
                8
                (page-dir-ptr-table-entry-addr
                 (xr :rgf *rsi* x86)
                 (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
               :r (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list 8 (+ -24 (xr :rgf 4 x86)))
     x86))
   (disjoint-p$
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (page-dir-ptr-table-entry-addr
       (xr :rgf *rsi* x86)
       (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
     x86))))

(def-gl-export remove-logext-from-ash-loghead-40-expr
  :hyp (unsigned-byte-p 64 n)
  :concl (equal (logext 64 (ash (loghead 40 (logtail 12 n)) 12))
                (ash (loghead 40 (logtail 12 n)) 12))
  :g-bindings
  (gl::auto-bindings (:mix (:nat n 64))))

(defthm mv-nth-1-rb-after-mv-nth-2-rb
  ;; Since mv-nth-2-rb-in-system-level-marking-mode is disabled during
  ;; the effects proof attempt, this rule will come in useful only
  ;; when rb isn't rewritten to rb-alt, i.e., for reads from the
  ;; paging structures.  Hence, I'll use disjoint-p$ in the hyps here
  ;; instead of disjoint-p.
  (implies
   (and
    (disjoint-p$
     (mv-nth 1 (las-to-pas l-addrs-1 r-w-x-1 (cpl x86) (double-rewrite x86)))
     (all-translation-governing-addresses l-addrs-2 (double-rewrite x86)))
    (disjoint-p$
     (mv-nth 1 (las-to-pas l-addrs-1 r-w-x-1 (cpl x86) (double-rewrite x86)))
     (all-translation-governing-addresses l-addrs-1 (double-rewrite x86)))
    (canonical-address-listp l-addrs-1)
    (canonical-address-listp l-addrs-2))
   (equal (mv-nth 1 (rb l-addrs-1 r-w-x-1 (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86))))
          (mv-nth 1 (rb l-addrs-1 r-w-x-1 x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (rb disjoint-p$)
                            (rewrite-rb-to-rb-alt
                             force (force))))))

(defthm unsigned-byte-p-1-bool->bit
  ;; Why do I need this?
  (unsigned-byte-p 1 (acl2::bool->bit x)))

;; (defthmd infer-disjointness-with-all-translation-governing-addresses-from-gather-all-paging-structure-qword-addresses-with-disjoint-p$
;;   (implies (and
;;             (disjoint-p$
;;              x
;;              (open-qword-paddr-list
;;               (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
;;             (true-listp x)
;;             (canonical-address-listp l-addrs))
;;            (disjoint-p$
;;             x
;;             (all-translation-governing-addresses l-addrs x86)))
;;   :hints (("Goal" :in-theory (e/d* (disjoint-p$) ())))
;;   :rule-classes :rewrite)

(defthm infer-disjointness-with-all-translation-governing-addresses-from-gather-all-paging-structure-qword-addresses-with-both-disjoint-p-and-disjoint-p$
  (implies (and
            (disjoint-p$
             x
             (open-qword-paddr-list
              (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
            (true-listp x)
            (canonical-address-listp l-addrs))
           (disjoint-p
            x
            (all-translation-governing-addresses l-addrs x86)))
  :hints (("Goal" :in-theory (e/d* (disjoint-p$) ())))
  :rule-classes :rewrite)

(defun find-first-arg-of-disjoint-p$-when-second-arg-matches-aux
  (arg-1-var arg-2 calls)
  ;; (find-first-arg-of-disjoint-p$-when-second-arg-matches-aux
  ;;  'x
  ;;  'y
  ;;  '((disjoint-p a y)
  ;;    (disjoint-p b z)
  ;;    (disjoint-p c y)))
  (if (endp calls)
      nil
    (append
     (if (equal (third (car calls)) arg-2)
         `(((,arg-1-var . ,(second (car calls)))))
       nil)
     (find-first-arg-of-disjoint-p$-when-second-arg-matches-aux
      arg-1-var arg-2 (cdr calls)))))

(defun find-first-arg-of-disjoint-p$-when-second-arg-matches
  (arg-1-var arg-2 mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-calls-lst 'disjoint-p$ (acl2::mfc-clause mfc)))
       ((when (not calls)) nil))
    (find-first-arg-of-disjoint-p$-when-second-arg-matches-aux
     arg-1-var arg-2 calls)))

(defthm infer-disjointness-with-all-translation-governing-addresses-from-gather-all-paging-structure-qword-addresses-with-disjoint-p$-new
  (implies (and (bind-free
                 (find-first-arg-of-disjoint-p$-when-second-arg-matches
                  'x
                  '(open-qword-paddr-list
                    (gather-all-paging-structure-qword-addresses x86))
                  mfc state)
                 (x))
                ;; (syntaxp (not (equal x y)))
                (subset-p y x)
                (disjoint-p$
                 x
                 (open-qword-paddr-list
                  (gather-all-paging-structure-qword-addresses (double-rewrite x86)))))
           (disjoint-p
            y
            (open-qword-paddr-list
             (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal" :in-theory (e/d* (disjoint-p$ disjoint-p subset-p) ())))
  :rule-classes :rewrite)

(in-theory (e/d ()
                (infer-disjointness-with-all-translation-governing-addresses-from-gather-all-paging-structure-qword-addresses)))

(def-gl-export remove-logext-from-logand-and-ctri
  :hyp (unsigned-byte-p 64 n)
  :concl (equal (logext 64 (logand -4096 (logext 64 n)))
                (logand -4096 (logext 64 n)))
  :g-bindings
  (gl::auto-bindings (:mix (:nat n 64))))

(defthm get-prefixes-alt-no-prefix-byte-after-mv-nth-2-rb
  (and (equal (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt
                                          (mv-nth 2 (rb l-addrs-1 r-w-x-1 x86))))
              (mv-nth 0 (get-prefixes-alt start-rip prefixes cnt x86)))
       (equal (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt
                                          (mv-nth 2 (rb l-addrs-1 r-w-x-1 x86))))
              (mv-nth 1 (get-prefixes-alt start-rip prefixes cnt x86))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d* (rb)
                     (rewrite-rb-to-rb-alt
                      rewrite-get-prefixes-to-get-prefixes-alt
                      force (force))))))

(defthm las-to-pas-after-mv-nth-2-rb
  (and (equal (mv-nth 0 (las-to-pas l-addrs-1 r-w-x-1 cpl-1
                                    (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86))))
              (mv-nth 0 (las-to-pas l-addrs-1 r-w-x-1 cpl-1 x86)))
       (equal (mv-nth 1 (las-to-pas l-addrs-1 r-w-x-1 cpl-1
                                    (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86))))
              (mv-nth 1 (las-to-pas l-addrs-1 r-w-x-1 cpl-1 x86))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d* (rb)
                     (rewrite-rb-to-rb-alt
                      rewrite-get-prefixes-to-get-prefixes-alt
                      force (force))))))

(defthm flgi-las-to-pas
  (equal (flgi index (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
         (flgi index x86))
  :hints (("goal" :in-theory (e/d* (flgi) (force (force))))))

(defthm alignment-checking-enabled-p-and-mv-nth-2-rb
  (equal (alignment-checking-enabled-p (mv-nth 2 (rb l-addrs r-w-x x86)))
         (alignment-checking-enabled-p x86))
  :hints (("goal" :in-theory (e/d* (alignment-checking-enabled-p
                                    rb)
                                   ()))))

(defthm alignment-checking-enabled-p-and-mv-nth-2-las-to-pas
  (equal (alignment-checking-enabled-p (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
         (alignment-checking-enabled-p x86))
  :hints (("goal" :in-theory (e/d* (alignment-checking-enabled-p)
                                   ()))))

(defthm mv-nth-2-rb-alt-in-system-level-marking-mode
  (implies
   (and (not (programmer-level-mode x86))
        (not (mv-nth 0 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86))))
        (canonical-address-listp l-addrs)
        (disjoint-p (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86)))
                    (open-qword-paddr-list
                     (gather-all-paging-structure-qword-addresses (double-rewrite x86)))))
   (equal (mv-nth 2 (rb-alt l-addrs r-w-x x86))
          (mv-nth 2 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (rb-alt)
                            (rewrite-rb-to-rb-alt
                             force (force))))))

(defun int-lists-in-seq-p (xs)
  (if (endp xs)
      t
    (if (consp (cdr xs))
        (and (equal (- (cadr xs) (car xs)) 1)
             (int-lists-in-seq-p (cdr xs)))
      t)))

(defthm int-lists-in-seq-p-and-append
  (implies (and (int-lists-in-seq-p (append x y))
                (true-listp x))
           (and (int-lists-in-seq-p x)
                (int-lists-in-seq-p y))))

(local
 (defthmd not-consp-create-canonical-address-list-implies-zp-cnt
   (implies (and (not (consp (create-canonical-address-list cnt lin-addr)))
                 (canonical-address-p lin-addr))
            (zp cnt))
   :hints (("Goal" :in-theory (e/d* (create-canonical-address-list)
                                    ())))))

(local
 (defthmd consp-create-canonical-address-list-implies-posp-cnt
   (implies (and (consp (create-canonical-address-list cnt lin-addr))
                 (canonical-address-p lin-addr))
            (posp cnt))
   :hints (("Goal" :in-theory (e/d* (create-canonical-address-list)
                                    ())))))

(defthm int-lists-in-seq-p-and-append-with-create-canonical-address-list-1
  ;; I need this so that I can prove away formulas of the form:
  ;; (INT-LISTS-IN-SEQ-P
  ;;  (BINARY-APPEND (CREATE-CANONICAL-ADDRESS-LIST 2 (XR :RIP 0 X86))
  ;;                 (CONS (BINARY-+ 2 (XR :RIP 0 X86)) NIL)))
  ;; and
  ;; (INT-LISTS-IN-SEQ-P
  ;;  (BINARY-APPEND
  ;;   (CREATE-CANONICAL-ADDRESS-LIST '3
  ;;                                  (BINARY-+ '8 (XR ':RIP '0 X86)))
  ;;   (CONS (BINARY-+ '11 (XR ':RIP '0 X86))
  ;;         'NIL)))
  (implies (and (equal next-addr (+ cnt lin-addr))
                (canonical-address-p lin-addr)
                (canonical-address-p next-addr)
                (posp cnt))
           (int-lists-in-seq-p (append (create-canonical-address-list cnt lin-addr)
                                       (cons next-addr nil))))
  :hints (("Goal" :in-theory (e/d* (create-canonical-address-list
                                    zp)
                                   ()))
          ("Subgoal *1/6.1"
           :use ((:instance not-consp-create-canonical-address-list-implies-zp-cnt
                            (lin-addr (1+ lin-addr))
                            (cnt (1- cnt)))))
          ("Subgoal *1/6.2"
           :in-theory (e/d* (car-create-canonical-address-list zp) ())
           :use ((:instance consp-create-canonical-address-list-implies-posp-cnt
                            (lin-addr (1+ lin-addr))
                            (cnt (1- cnt)))))))

(defthm int-lists-in-seq-p-of-create-canonical-address-list
  (implies (and (canonical-address-p lin-addr)
                (canonical-address-p (+ -1 cnt lin-addr))
                (posp cnt))
           (int-lists-in-seq-p (create-canonical-address-list cnt lin-addr)))
  :hints (("Goal" :in-theory (e/d* (car-create-canonical-address-list zp) ()))
          ("Subgoal *1/6"
           :in-theory (e/d* (zp) ())
           :use ((:instance car-create-canonical-address-list
                            (count (1- cnt))
                            (addr (1+ lin-addr)))
                 (:instance consp-create-canonical-address-list-implies-posp-cnt
                            (lin-addr (1+ lin-addr))
                            (cnt (1- cnt)))))))

(defthm int-lists-in-seq-p-and-append-with-create-canonical-address-list-2
  ;; I need this so that I can prove away formulas of the form:
  ;; (INT-LISTS-IN-SEQ-P
  ;;  (BINARY-APPEND
  ;;   (CREATE-CANONICAL-ADDRESS-LIST '3
  ;;                                  (BINARY-+ '8 (XR ':RIP '0 X86)))
  ;;   (CREATE-CANONICAL-ADDRESS-LIST '2
  ;;                                  (BINARY-+ '11 (XR ':RIP '0 X86)))))
  (implies (and (equal lin-addr-2 (+ cnt-1 lin-addr-1))
                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (canonical-address-p (+ -1 cnt-2 lin-addr-2))
                (posp cnt-1)
                (posp cnt-2))
           (int-lists-in-seq-p (append (create-canonical-address-list cnt-1 lin-addr-1)
                                       (create-canonical-address-list cnt-2 lin-addr-2))))
  :hints (("Goal" :in-theory (e/d* (create-canonical-address-list
                                    car-create-canonical-address-list
                                    zp)
                                   ()))
          ("Subgoal *1/7.1"
           :use ((:instance not-consp-create-canonical-address-list-implies-zp-cnt
                            (lin-addr (1+ lin-addr-1))
                            (cnt (1- cnt-1)))))
          ("Subgoal *1/7.2"
           :in-theory (e/d* (car-create-canonical-address-list zp) ())
           :use ((:instance consp-create-canonical-address-list-implies-posp-cnt
                            (lin-addr (1+ lin-addr-1))
                            (cnt (1- cnt-1)))))))

(local
 (defthmd create-canonical-address-list-append-and-int-lists-in-seq-p-helper-1
   (implies (and (equal (+ (- car-x) cadr-x) 1)
                 (integerp cadr-x))
            (equal (+ 1 car-x) cadr-x))))

(local
 (defthmd create-canonical-address-list-append-and-int-lists-in-seq-p-helper-2
   (implies (and (canonical-address-listp x)
                 (int-lists-in-seq-p x))
            (equal (create-canonical-address-list (len x) (car x)) x))
   :hints (("Goal"
            :in-theory (e/d* (create-canonical-address-list
                              len)
                             ()))
           ("Subgoal *1/2"
            :use ((:instance create-canonical-address-list-append-and-int-lists-in-seq-p-helper-1
                             (car-x (car x))
                             (cadr-x (cadr x))))))))

(defthmd create-canonical-address-list-append-and-int-lists-in-seq-p
  (implies (and (int-lists-in-seq-p (append x y))
                (consp x)
                (consp y)
                (canonical-address-listp x)
                (canonical-address-listp y))
           (equal (create-canonical-address-list (+ (len x) (len y)) (car x))
                  (append x y)))
  :hints (("Goal"
           :induct (cons (append x y)
                         (create-canonical-address-list (+ (len x) (len y)) (car x)))
           :in-theory (e/d* (append create-canonical-address-list len)
                            ()))
          ("Subgoal *1/2"
           :use ((:instance create-canonical-address-list-append-and-int-lists-in-seq-p-helper-1
                            (car-x (car x))
                            (cadr-x (cadr x))))
           :in-theory (e/d* (append create-canonical-address-list len)
                            ()))
          ("Subgoal *1/3"
           :use ((:instance create-canonical-address-list-append-and-int-lists-in-seq-p-helper-1
                            (car-x (car x))
                            (cadr-x (car y)))
                 (:instance create-canonical-address-list-append-and-int-lists-in-seq-p-helper-2
                            (x y)))
           :in-theory (e/d* (append create-canonical-address-list len)
                            ()))))

(defthm combine-mv-nth-2-las-to-pas-same-r-w-x-when-addresses-in-sequence
  (implies (and
            (int-lists-in-seq-p (append l-addrs-1 l-addrs-2))
            (not (mv-nth 0 (las-to-pas l-addrs-1 r-w-x cpl (double-rewrite x86))))
            (canonical-address-listp l-addrs-1)
            (canonical-address-listp l-addrs-2)
            (consp l-addrs-1)
            (consp l-addrs-2))
           (equal (mv-nth 2 (las-to-pas l-addrs-2 r-w-x cpl
                                        (mv-nth 2 (las-to-pas l-addrs-1 r-w-x cpl x86))))
                  (mv-nth 2 (las-to-pas
                             (create-canonical-address-list
                              (+ (len l-addrs-1) (len l-addrs-2))
                              (car l-addrs-1))
                             r-w-x cpl x86))))
  :hints (("Goal"
           :use ((:instance combine-mv-nth-2-las-to-pas-same-r-w-x))
           :in-theory (e/d* (create-canonical-address-list-append-and-int-lists-in-seq-p)
                            (combine-mv-nth-2-las-to-pas-same-r-w-x)))))

(in-theory (e/d () (combine-mv-nth-2-las-to-pas-same-r-w-x)))

;; (acl2::why combine-mv-nth-2-las-to-pas-same-r-w-x-when-addresses-in-sequence)
;; (acl2::why mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free)

(defun-nx destination-PDPTE-and-destination-PML4TE-no-interfere-p (x86)
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
              :w (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list
     8
     (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
    x86)))

(defun-nx destination-PDPTE-and-source-PML4E-no-interfere-p (x86)
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
              :w (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list
     8
     (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
    x86)))

(defun-nx destination-PDPTE-and-source-PDPTE-no-interfere-p (x86)
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
              :w (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rdi* x86)
      (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
    x86)))

(defun-nx destination-PDPTE-and-program-no-interfere-p-aux (x86)
  ;; We need these assumptions because the destination PDPTE is
  ;; modified, and we need to make sure that this modification does
  ;; not affect the program in any way.
  (disjoint-p$
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
              :x (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rsi* x86)
      (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
    x86)))

(defthm xlate-equiv-memory-and-direct-map-p
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (direct-map-p count addr r-w-x cpl x86-1)
                  (direct-map-p count addr r-w-x cpl x86-2)))
  :rule-classes :congruence)

(defthm direct-map-p-and-wb-disjoint-from-xlation-governing-addrs
  (implies
   (and (equal cpl (cpl x86))
        (disjoint-p
         (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl (double-rewrite x86)))
         (all-translation-governing-addresses (create-canonical-address-list count addr) (double-rewrite x86))))
   (equal (direct-map-p count addr r-w-x cpl (mv-nth 1 (wb addr-lst x86)))
          (direct-map-p count addr r-w-x cpl (double-rewrite x86))))
  :hints (("Goal" :in-theory (e/d* () (force (force))))))

(in-theory (e/d* () (direct-map-p)))

(def-gl-thm unsigned-byte-p-52-of-dest-pdpte
  :hyp (and (signed-byte-p 64 reg)
            (unsigned-byte-p 64 val))
  :concl (unsigned-byte-p
          52
          (logior (logand 4088 (loghead 32 (logtail 27 reg)))
                  (ash (loghead 40 (logtail 12 val)) 12)))
  :g-bindings
  (gl::auto-bindings (:mix (:nat reg 64) (:nat val 64))))

(def-gl-thm unsigned-byte-p-64-of-dest-pdpte-modified-value
  :hyp (and (unsigned-byte-p 64 val-1)
            (unsigned-byte-p 64 val-2))
  :concl (unsigned-byte-p 64 (logior (logand 18442240475155922943 val-1)
                                     (logand 4503598553628672 val-2)))
  :g-bindings
  (gl::auto-bindings (:mix (:nat val-1 64) (:nat val-2 64))))

;; (defun get-l-addrs-from-disjointness-precond-aux (xlate-l-addrs calls)
;;   (declare (xargs :mode :program))
;;   (if (atom calls)
;;       nil
;;     (b* ((term (car calls))
;;          ;; (- (cw "~%~x0~%" term))
;;          )
;;       (case-match term
;;         (('disjoint-p$
;;           ('mv-nth 1 ('las-to-pas l-addrs-1 . &))
;;           ('all-translation-governing-addresses l-addrs-2 . &))
;;          (if (equal xlate-l-addrs l-addrs-2)
;;              (cons l-addrs-1 (get-l-addrs-from-disjointness-precond-aux xlate-l-addrs (cdr calls)))
;;            (get-l-addrs-from-disjointness-precond-aux xlate-l-addrs (cdr calls)))
;;          )
;;         (& (get-l-addrs-from-disjointness-precond-aux xlate-l-addrs (cdr calls)))))))

;; (defun get-l-addrs-from-disjointness-precond
;;   (fn l-addrs-var xlate-l-addrs mfc state)
;;   (declare (xargs :stobjs (state) :mode :program)
;;            (ignorable state))
;;   (b* ((calls (acl2::find-calls-lst fn (acl2::mfc-clause mfc)))
;;        ((when (not calls)) nil)
;;        (l-addrs (get-l-addrs-from-disjointness-precond-aux xlate-l-addrs calls))
;;        (alst-lst
;;         (make-bind-free-alist-lists l-addrs-var l-addrs)))
;;     alst-lst))

(defthm disjoint-p-las-to-pas-subset-p-and-all-translation-governing-addresses-subsets-1
  ;; Very similar to
  ;; mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs (but
  ;; less general and hence, less expensive).
  (implies
   (and
    (syntaxp (not (eq l-addrs-1-subset l-addrs-2)))
    (bind-free (find-l-addrs-from-program-at-or-program-at-alt-term
                'disjoint-p-las-to-pas-subset-p-and-all-translation-governing-addresses
                'l-addrs-1 mfc state)
               (l-addrs-1))
    (disjoint-p$
     (mv-nth 1 (las-to-pas l-addrs-1 :x cpl (double-rewrite x86)))
     (all-translation-governing-addresses l-addrs-2 (double-rewrite x86)))
    (subset-p l-addrs-1-subset l-addrs-1)
    (not (mv-nth 0 (las-to-pas l-addrs-1 :x cpl (double-rewrite x86)))))
   (disjoint-p (mv-nth 1 (las-to-pas l-addrs-1-subset :x cpl x86))
               (all-translation-governing-addresses l-addrs-2 x86)))
  :hints (("Goal" :in-theory (e/d* () (mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs))
           :use ((:instance mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                            (other-p-addrs (all-translation-governing-addresses l-addrs-2 x86))
                            (r-w-x :x)
                            (l-addrs l-addrs-1)
                            (l-addrs-subset l-addrs-1-subset))))))

(defthm infer-disjointness-with-all-translation-governing-addresses-from-gather-all-paging-structure-qword-addresses-with-both-disjoint-p-and-disjoint-p$-and-subset-p
  (implies
   (and
    (bind-free (find-l-addrs-from-program-at-or-program-at-alt-term
                'infer-disjointness
                'l-addrs mfc state)
               (l-addrs))
    (disjoint-p$
     (mv-nth 1 (las-to-pas l-addrs :x cpl (double-rewrite x86)))
     (open-qword-paddr-list
      (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
    (not (mv-nth 0 (las-to-pas l-addrs :x cpl (double-rewrite x86))))
    (subset-p l-addrs-subset-1 l-addrs)
    (subset-p l-addrs-subset-2 l-addrs)
    (canonical-address-listp l-addrs))
   (disjoint-p
    (mv-nth 1 (las-to-pas l-addrs-subset-1 :x cpl x86))
    (all-translation-governing-addresses l-addrs-subset-2 x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p$
                             subset-p)
                            ())
           :use ((:instance infer-disjointness-with-all-translation-governing-addresses-from-gather-all-paging-structure-qword-addresses
                            (x (mv-nth 1 (las-to-pas l-addrs :x cpl x86)))
                            (l-addrs l-addrs-subset))
                 (:instance disjoint-p-subset-p
                            (x (mv-nth 1 (las-to-pas l-addrs :x cpl x86)))
                            (y (all-translation-governing-addresses l-addrs x86))
                            (a (mv-nth 1 (las-to-pas l-addrs-subset-1 :x cpl x86)))
                            (b (all-translation-governing-addresses l-addrs-subset-2 x86))))))

  :rule-classes :rewrite)

(defthm disjointness-of-las-to-pas-from-wb-to-subset-of-paging-structures
  ;; Note that r-w-x = :x here.
  (implies (and
            (bind-free
             (find-l-addrs-from-program-at-or-program-at-alt-term
              'infer-disjointness 'l-addrs mfc state)
             (l-addrs))
            ;; The equality of
            ;; gather-all-paging-structure-qword-addresses and
            ;; las-to-pas with x86-1 and x86-2 are better than the
            ;; xlate-equiv-memory hyp because x86-2 may contain wb
            ;; terms, which don't preserve xlate-equiv-memory relation
            ;; on the x86 states.
            ;; (xlate-equiv-memory (double-rewrite x86-1) (double-rewrite x86-2))
            (equal
             (gather-all-paging-structure-qword-addresses (double-rewrite x86-2))
             (gather-all-paging-structure-qword-addresses (double-rewrite x86-1)))
            (equal (mv-nth 1 (las-to-pas l-addrs :x cpl (double-rewrite x86-1)))
                   (mv-nth 1 (las-to-pas l-addrs :x cpl (double-rewrite x86-2))))
            (equal (page-size value) 1)
            (direct-map-p 8 lin-addr :w (cpl x86-2) (double-rewrite x86-2))
            (disjoint-p$
             (mv-nth 1 (las-to-pas l-addrs :x cpl (double-rewrite x86-1)))
             (open-qword-paddr-list
              (gather-all-paging-structure-qword-addresses (double-rewrite x86-1))))
            (subset-p l-addrs-subset l-addrs)
            (not (mv-nth 0 (las-to-pas l-addrs :x cpl (double-rewrite x86-1))))
            ;; !!
            (physical-address-p lin-addr)
            (equal (loghead 3 lin-addr) 0)
            (canonical-address-p lin-addr)
            ;; !!
            (unsigned-byte-p 64 value)
            (not (programmer-level-mode x86-2)))
           (disjoint-p
            (mv-nth 1 (las-to-pas l-addrs-subset :x cpl x86-1))
            (open-qword-paddr-list
             (gather-all-paging-structure-qword-addresses
              (mv-nth 1 (wb (create-addr-bytes-alist
                             (create-canonical-address-list 8 lin-addr)
                             (byte-ify 8 value))
                            x86-2))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance disjointness-of-las-to-pas-from-subset-of-paging-structures
                            (p-addrs (addr-range 8 lin-addr))
                            (r-w-x :x)
                            (index lin-addr)
                            (bytes (byte-ify 8 value))
                            (x86 (mv-nth 2
                                         (las-to-pas (create-canonical-address-list 8 lin-addr)
                                                     :w (cpl x86-2) x86-2))))
                 (:instance disjoint-p-subset-p
                            (x (mv-nth 1 (las-to-pas l-addrs :x cpl x86-1)))
                            (y (open-qword-paddr-list
                                (gather-all-paging-structure-qword-addresses x86-1)))
                            (a (mv-nth 1 (las-to-pas l-addrs-subset :x cpl x86-1)))
                            (b (open-qword-paddr-list
                                (gather-all-paging-structure-qword-addresses x86-1))))
                 (:instance disjoint-p-subset-p
                            (x (mv-nth 1 (las-to-pas l-addrs :x cpl x86-1)))
                            (y (open-qword-paddr-list
                                (gather-all-paging-structure-qword-addresses
                                 (write-to-physical-memory
                                  (addr-range 8 lin-addr)
                                  (byte-ify 8 value)
                                  (mv-nth 2
                                          (las-to-pas (create-canonical-address-list 8 lin-addr)
                                                      :w (cpl x86-2)
                                                      x86-2))))))
                            (a (mv-nth 1 (las-to-pas l-addrs-subset :x cpl x86-1)))
                            (b (open-qword-paddr-list
                                (gather-all-paging-structure-qword-addresses
                                 (write-to-physical-memory
                                  (addr-range 8 lin-addr)
                                  (byte-ify 8 value)
                                  (mv-nth 2
                                          (las-to-pas (create-canonical-address-list 8 lin-addr)
                                                      :w (cpl x86-2)
                                                      x86-2))))))))
           :in-theory (e/d* (disjoint-p$
                             subset-p
                             subset-p-reflexive
                             wb
                             direct-map-p)
                            (disjointness-of-las-to-pas-from-subset-of-paging-structures)))))

(encapsulate
  ()
  (defthmd disjointness-of-las-to-pas-from-wb-to-subset-of-paging-structures-general
    (implies (and
              ;; The equality of
              ;; gather-all-paging-structure-qword-addresses and
              ;; las-to-pas with x86-1 and x86-2 are better than the
              ;; xlate-equiv-memory hyp because x86-2 may contain wb
              ;; terms, which don't preserve xlate-equiv-memory relation
              ;; on the x86 states.
              ;; (xlate-equiv-memory (double-rewrite x86-1) (double-rewrite x86-2))
              (equal
               (gather-all-paging-structure-qword-addresses (double-rewrite x86-2))
               (gather-all-paging-structure-qword-addresses (double-rewrite x86-1)))
              (equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86-1)))
                     (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86-2))))
              (equal (page-size value) 1)
              (direct-map-p 8 lin-addr :w (cpl x86-2) (double-rewrite x86-2))
              (disjoint-p$
               (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86-1)))
               (open-qword-paddr-list
                (gather-all-paging-structure-qword-addresses (double-rewrite x86-1))))
              (subset-p l-addrs-subset l-addrs)
              (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86-1))))
              ;; !!
              (physical-address-p lin-addr)
              (equal (loghead 3 lin-addr) 0)
              (canonical-address-p lin-addr)
              ;; !!
              (unsigned-byte-p 64 value)
              (not (programmer-level-mode x86-2)))
             (disjoint-p
              (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86-1))
              (open-qword-paddr-list
               (gather-all-paging-structure-qword-addresses
                (mv-nth 1 (wb (create-addr-bytes-alist
                               (create-canonical-address-list 8 lin-addr)
                               (byte-ify 8 value))
                              x86-2))))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance disjointness-of-las-to-pas-from-subset-of-paging-structures
                              (p-addrs (addr-range 8 lin-addr))
                              (r-w-x r-w-x)
                              (index lin-addr)
                              (bytes (byte-ify 8 value))
                              (x86 (mv-nth 2
                                           (las-to-pas (create-canonical-address-list 8 lin-addr)
                                                       :w (cpl x86-2) x86-2))))
                   (:instance disjoint-p-subset-p
                              (x (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86-1)))
                              (y (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses x86-1)))
                              (a (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86-1)))
                              (b (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses x86-1))))
                   (:instance disjoint-p-subset-p
                              (x (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86-1)))
                              (y (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses
                                   (write-to-physical-memory
                                    (addr-range 8 lin-addr)
                                    (byte-ify 8 value)
                                    (mv-nth 2
                                            (las-to-pas (create-canonical-address-list 8 lin-addr)
                                                        :w (cpl x86-2)
                                                        x86-2))))))
                              (a (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86-1)))
                              (b (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses
                                   (write-to-physical-memory
                                    (addr-range 8 lin-addr)
                                    (byte-ify 8 value)
                                    (mv-nth 2
                                            (las-to-pas (create-canonical-address-list 8 lin-addr)
                                                        :w (cpl x86-2)
                                                        x86-2))))))))
             :in-theory (e/d* (disjoint-p$
                               subset-p
                               subset-p-reflexive
                               wb
                               direct-map-p)
                              (disjointness-of-las-to-pas-from-subset-of-paging-structures)))))

  (defthm rb-alt-and-wb-to-paging-structures-disjoint
    (implies (and
              (equal (page-size value) 1)
              (direct-map-p 8 lin-addr :w (cpl x86) (double-rewrite x86))
              (disjoint-p
               (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86)))
               (open-qword-paddr-list
                (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
              (disjoint-p
               (mv-nth 1 (las-to-pas
                          (create-canonical-address-list 8 lin-addr)
                          :w (cpl x86) (double-rewrite x86)))
               (all-translation-governing-addresses l-addrs (double-rewrite x86)))
              (disjoint-p
               (mv-nth 1 (las-to-pas (create-canonical-address-list 8 lin-addr)
                                     :w (cpl x86) (double-rewrite x86)))
               (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86))))
              ;; !!
              (physical-address-p lin-addr)
              (equal (loghead 3 lin-addr) 0)
              (canonical-address-p lin-addr)
              ;; !!
              (unsigned-byte-p 64 value)
              (x86p x86))
             (and
              (equal (mv-nth 0 (rb-alt l-addrs r-w-x
                                       (mv-nth 1 (wb
                                                  (create-addr-bytes-alist
                                                   (create-canonical-address-list 8 lin-addr)
                                                   (byte-ify 8 value)) x86))))
                     (mv-nth 0 (rb-alt l-addrs r-w-x (double-rewrite x86))))
              (equal (mv-nth 1 (rb-alt l-addrs r-w-x
                                       (mv-nth 1 (wb
                                                  (create-addr-bytes-alist
                                                   (create-canonical-address-list 8 lin-addr)
                                                   (byte-ify 8 value)) x86))))
                     (mv-nth 1 (rb-alt l-addrs r-w-x (double-rewrite x86))))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance disjointness-of-las-to-pas-from-wb-to-subset-of-paging-structures-general
                              (l-addrs-subset l-addrs)
                              (cpl (cpl x86))
                              (x86-1 x86)
                              (x86-2 x86)))
             :in-theory (e/d* (disjoint-p$
                               subset-p
                               subset-p-reflexive
                               rb-alt)
                              (rewrite-rb-to-rb-alt))))))

;; Argh, ACL2's default ancestors-check is killing me --- it prevents
;; x86-fetch-decode-execute from opening up (because the first hyp of
;; get-prefixes-alt-opener-lemma-no-prefix-byte is judged more
;; complicated than its ancestors --- why?). So I'm going to use Sol's
;; trivial ancestors-check version.
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))

;; (acl2::why x86-run-opener-not-ms-not-zp-n)
;; (acl2::why x86-fetch-decode-execute-opener-in-marking-mode)
;; (acl2::why get-prefixes-alt-opener-lemma-no-prefix-byte)
;; (acl2::why get-prefixes-alt-and-wb-in-system-level-marking-mode-disjoint-from-paging-structures)
;; (acl2::why la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs)
;; (acl2::why rb-alt-wb-disjoint-in-system-level-mode)
;; (acl2::why rb-alt-wb-equal-in-system-level-mode)

;; (acl2::why mv-nth-1-rb-after-mv-nth-2-rb-alt)
;; (acl2::why all-translation-governing-addresses-and-mv-nth-1-wb-disjoint)
;; (acl2::why la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs)

;; (acl2::why mv-nth-1-rb-after-mv-nth-2-get-prefixes-alt-no-prefix-byte)

;; (acl2::why mv-nth-2-get-prefixes-alt-no-prefix-byte)
;; (acl2::why mv-nth-2-rb-in-system-level-marking-mode)
;; (acl2::why combine-mv-nth-2-las-to-pas-same-r-w-x)

;; (acl2::why mv-nth-1-rb-after-mv-nth-2-las-to-pas)
;; (acl2::why mv-nth-1-rb-after-mv-nth-2-rb)

;; (acl2::why get-prefixes-alt-and-wb-to-paging-structures)
;; (acl2::why rb-wb-disjoint-in-system-level-mode)
;; (acl2::why x86-fetch-decode-execute-opener-in-marking-mode)

;; (acl2::why mv-nth-2-get-prefixes-alt-no-prefix-byte)
;; (acl2::why rb-alt-and-wb-to-paging-structures-disjoint)

(i-am-here)

(defthmd rewire_dst_to_src-effects-45-instructions
  (implies
   ;; (rewire_dst_to_src-assumptions x86)
   (and
    (x86-state-okp x86)
    (program-ok-p x86)
    (stack-ok-p x86)
    (program-and-stack-no-interfere-p x86)
    (program-and-stack-no-interfere-p-aux x86)
    (source-addresses-ok-p x86)
    (source-PML4TE-ok-p x86)
    (source-PDPTE-ok-p x86)
    (source-PML4TE-and-stack-no-interfere-p x86)
    (source-PML4TE-and-program-no-interfere-p x86)
    (source-PML4TE-itself-no-interfere-p x86)
    (source-PML4TE-and-stack-no-interfere-p-aux x86)
    (source-PDPTE-and-stack-no-interfere-p x86)
    (source-PDPTE-and-program-no-interfere-p x86)
    (source-PDPTE-itself-no-interfere-p x86)
    (source-PDPTE-and-stack-no-interfere-p-aux x86)
    ;; This is too strong (coz equality of rbs doesnt matter, but
    ;; xlate-equiv matters), but Ill let this lie for now.
    (source-PDPTE-and-source-PML4E-no-interfere-p x86)

    (destination-addresses-ok-p x86)
    (destination-PML4TE-ok-p x86)
    (destination-PDPTE-ok-p x86)
    (destination-PML4TE-and-stack-no-interfere-p x86)
    (destination-PML4TE-and-program-no-interfere-p x86)
    (destination-PML4TE-itself-no-interfere-p x86)
    (destination-PML4TE-and-stack-no-interfere-p-aux x86)
    ;; Too strong?
    (destination-PML4TE-and-source-PML4TE-no-interfere-p x86)
    (destination-PML4TE-and-source-PDPTE-no-interfere-p x86)

    (destination-PDPTE-and-source-PML4E-no-interfere-p x86)
    (destination-PDPTE-and-source-PDPTE-no-interfere-p x86)
    (destination-PDPTE-and-destination-PML4TE-no-interfere-p x86)
    (destination-PDPTE-and-stack-no-interfere-p x86)
    (destination-PDPTE-and-program-no-interfere-p x86)
    (destination-PDPTE-and-program-no-interfere-p-aux x86)
    (destination-PDPTE-itself-no-interfere-p x86)
    (destination-PDPTE-and-stack-no-interfere-p-aux x86)

    (direct-map-p
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rsi* x86)
      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
     :w (cpl x86) x86))

   (equal (x86-run 45 x86) ;; (rewire_dst_to_src-clk)
          (XW
           :RGF *RAX*
           (LOGIOR
            (LOGAND
             -4503598553628673
             (LOGEXT
              64
              (COMBINE-BYTES
               (MV-NTH
                1
                (RB
                 (CREATE-CANONICAL-ADDRESS-LIST
                  8
                  (LOGIOR
                   (LOGAND 4088
                           (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                   (ASH
                    (LOGHEAD
                     40
                     (LOGTAIL
                      12
                      (COMBINE-BYTES
                       (MV-NTH
                        1
                        (RB
                         (CREATE-CANONICAL-ADDRESS-LIST
                          8
                          (LOGIOR
                           (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                           (LOGAND 4088
                                   (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                         :R X86)))))
                    12)))
                 :R X86)))))
            (LOGAND
             4503598553628672
             (LOGEXT
              64
              (COMBINE-BYTES
               (MV-NTH
                1
                (RB
                 (CREATE-CANONICAL-ADDRESS-LIST
                  8
                  (LOGIOR
                   (LOGAND 4088
                           (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                   (ASH
                    (LOGHEAD
                     40
                     (LOGTAIL
                      12
                      (COMBINE-BYTES
                       (MV-NTH
                        1
                        (RB
                         (CREATE-CANONICAL-ADDRESS-LIST
                          8
                          (LOGIOR
                           (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                           (LOGAND 4088
                                   (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                         :R X86)))))
                    12)))
                 :R X86))))))
           (XW
            :RGF *RCX*
            (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                    (LOGAND 4088
                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
            (XW
             :RGF *RDX*
             (LOGIOR
              (LOGAND
               -4503598553628673
               (LOGEXT
                64
                (COMBINE-BYTES
                 (MV-NTH
                  1
                  (RB
                   (CREATE-CANONICAL-ADDRESS-LIST
                    8
                    (LOGIOR
                     (LOGAND 4088
                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                     (ASH
                      (LOGHEAD
                       40
                       (LOGTAIL
                        12
                        (COMBINE-BYTES
                         (MV-NTH
                          1
                          (RB
                           (CREATE-CANONICAL-ADDRESS-LIST
                            8
                            (LOGIOR
                             (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                             (LOGAND 4088
                                     (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                           :R X86)))))
                      12)))
                   :R X86)))))
              (LOGAND
               4503598553628672
               (LOGEXT
                64
                (COMBINE-BYTES
                 (MV-NTH
                  1
                  (RB
                   (CREATE-CANONICAL-ADDRESS-LIST
                    8
                    (LOGIOR
                     (LOGAND 4088
                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                     (ASH
                      (LOGHEAD
                       40
                       (LOGTAIL
                        12
                        (COMBINE-BYTES
                         (MV-NTH
                          1
                          (RB
                           (CREATE-CANONICAL-ADDRESS-LIST
                            8
                            (LOGIOR
                             (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                             (LOGAND 4088
                                     (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                           :R X86)))))
                      12)))
                   :R X86))))))
             (XW
              :RGF *R8* 1099511627775
              (XW
               :RGF *R9*
               (LOGAND
                4503598553628672
                (LOGEXT
                 64
                 (COMBINE-BYTES
                  (MV-NTH
                   1
                   (RB
                    (CREATE-CANONICAL-ADDRESS-LIST
                     8
                     (LOGIOR
                      (LOGAND 4088
                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                      (ASH
                       (LOGHEAD
                        40
                        (LOGTAIL
                         12
                         (COMBINE-BYTES
                          (MV-NTH
                           1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST
                             8
                             (LOGIOR
                              (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                              (LOGAND
                               4088
                               (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                            :R X86)))))
                       12)))
                    :R X86)))))
               (XW
                :RIP 0 (+ 193 (XR :RIP 0 X86))
                (XW
                 :UNDEF 0 (+ 39 (NFIX (XR :UNDEF 0 X86)))
                 (!FLGI
                  *CF* 0
                  (!FLGI
                   *PF*
                   (PF-SPEC64
                    (LOGIOR
                     (LOGAND
                      18442240475155922943
                      (COMBINE-BYTES
                       (MV-NTH
                        1
                        (RB
                         (CREATE-CANONICAL-ADDRESS-LIST
                          8
                          (LOGIOR
                           (LOGAND 4088
                                   (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                           (ASH
                            (LOGHEAD
                             40
                             (LOGTAIL
                              12
                              (COMBINE-BYTES
                               (MV-NTH
                                1
                                (RB
                                 (CREATE-CANONICAL-ADDRESS-LIST
                                  8
                                  (LOGIOR
                                   (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                   (LOGAND
                                    4088
                                    (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                 :R X86)))))
                            12)))
                         :R X86))))
                     (LOGAND
                      4503598553628672
                      (COMBINE-BYTES
                       (MV-NTH
                        1
                        (RB
                         (CREATE-CANONICAL-ADDRESS-LIST
                          8
                          (LOGIOR
                           (LOGAND 4088
                                   (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                           (ASH
                            (LOGHEAD
                             40
                             (LOGTAIL
                              12
                              (COMBINE-BYTES
                               (MV-NTH
                                1
                                (RB
                                 (CREATE-CANONICAL-ADDRESS-LIST
                                  8
                                  (LOGIOR
                                   (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                   (LOGAND
                                    4088
                                    (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                 :R X86)))))
                            12)))
                         :R X86))))))
                   (!FLGI
                    *AF*
                    (LOGHEAD 1
                             (CREATE-UNDEF (+ 38 (NFIX (XR :UNDEF 0 X86)))))
                    (!FLGI
                     *ZF*
                     (ZF-SPEC
                      (LOGIOR
                       (LOGAND
                        18442240475155922943
                        (COMBINE-BYTES
                         (MV-NTH
                          1
                          (RB
                           (CREATE-CANONICAL-ADDRESS-LIST
                            8
                            (LOGIOR
                             (LOGAND 4088
                                     (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                             (ASH
                              (LOGHEAD
                               40
                               (LOGTAIL
                                12
                                (COMBINE-BYTES
                                 (MV-NTH
                                  1
                                  (RB
                                   (CREATE-CANONICAL-ADDRESS-LIST
                                    8
                                    (LOGIOR
                                     (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                     (LOGAND
                                      4088
                                      (LOGHEAD
                                       28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                   :R X86)))))
                              12)))
                           :R X86))))
                       (LOGAND
                        4503598553628672
                        (COMBINE-BYTES
                         (MV-NTH
                          1
                          (RB
                           (CREATE-CANONICAL-ADDRESS-LIST
                            8
                            (LOGIOR
                             (LOGAND 4088
                                     (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                             (ASH
                              (LOGHEAD
                               40
                               (LOGTAIL
                                12
                                (COMBINE-BYTES
                                 (MV-NTH
                                  1
                                  (RB
                                   (CREATE-CANONICAL-ADDRESS-LIST
                                    8
                                    (LOGIOR
                                     (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                     (LOGAND
                                      4088
                                      (LOGHEAD
                                       28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                   :R X86)))))
                              12)))
                           :R X86))))))
                     (!FLGI
                      *SF*
                      (SF-SPEC64
                       (LOGIOR
                        (LOGAND
                         18442240475155922943
                         (COMBINE-BYTES
                          (MV-NTH
                           1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST
                             8
                             (LOGIOR
                              (LOGAND 4088
                                      (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                              (ASH
                               (LOGHEAD
                                40
                                (LOGTAIL
                                 12
                                 (COMBINE-BYTES
                                  (MV-NTH
                                   1
                                   (RB
                                    (CREATE-CANONICAL-ADDRESS-LIST
                                     8
                                     (LOGIOR
                                      (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                      (LOGAND
                                       4088
                                       (LOGHEAD
                                        28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                    :R X86)))))
                               12)))
                            :R X86))))
                        (LOGAND
                         4503598553628672
                         (COMBINE-BYTES
                          (MV-NTH
                           1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST
                             8
                             (LOGIOR
                              (LOGAND 4088
                                      (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                              (ASH
                               (LOGHEAD
                                40
                                (LOGTAIL
                                 12
                                 (COMBINE-BYTES
                                  (MV-NTH
                                   1
                                   (RB
                                    (CREATE-CANONICAL-ADDRESS-LIST
                                     8
                                     (LOGIOR
                                      (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                      (LOGAND
                                       4088
                                       (LOGHEAD
                                        28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                    :R X86)))))
                               12)))
                            :R X86))))))
                      (!FLGI
                       *OF* 0
                       (MV-NTH
                        2
                        (LAS-TO-PAS
                         (CREATE-CANONICAL-ADDRESS-LIST 3 (+ 190 (XR :RIP 0 X86)))
                         :X 0
                         (MV-NTH
                          1
                          (WB
                           (CREATE-ADDR-BYTES-ALIST
                            (CREATE-CANONICAL-ADDRESS-LIST
                             8
                             (LOGIOR
                              (LOGAND 4088
                                      (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                              (ASH
                               (LOGHEAD
                                40
                                (LOGTAIL
                                 12
                                 (COMBINE-BYTES
                                  (MV-NTH
                                   1
                                   (RB
                                    (CREATE-CANONICAL-ADDRESS-LIST
                                     8
                                     (LOGIOR
                                      (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                      (LOGAND
                                       4088
                                       (LOGHEAD
                                        28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                    :R X86)))))
                               12)))
                            (BYTE-IFY
                             8
                             (LOGIOR
                              (LOGAND
                               18442240475155922943
                               (COMBINE-BYTES
                                (MV-NTH
                                 1
                                 (RB
                                  (CREATE-CANONICAL-ADDRESS-LIST
                                   8
                                   (LOGIOR
                                    (LOGAND
                                     4088
                                     (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                    (ASH
                                     (LOGHEAD
                                      40
                                      (LOGTAIL
                                       12
                                       (COMBINE-BYTES
                                        (MV-NTH
                                         1
                                         (RB
                                          (CREATE-CANONICAL-ADDRESS-LIST
                                           8
                                           (LOGIOR
                                            (LOGAND
                                             -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                            (LOGAND
                                             4088
                                             (LOGHEAD
                                              28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                          :R X86)))))
                                     12)))
                                  :R X86))))
                              (LOGAND
                               4503598553628672
                               (COMBINE-BYTES
                                (MV-NTH
                                 1
                                 (RB
                                  (CREATE-CANONICAL-ADDRESS-LIST
                                   8
                                   (LOGIOR
                                    (LOGAND
                                     4088
                                     (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                    (ASH
                                     (LOGHEAD
                                      40
                                      (LOGTAIL
                                       12
                                       (COMBINE-BYTES
                                        (MV-NTH
                                         1
                                         (RB
                                          (CREATE-CANONICAL-ADDRESS-LIST
                                           8
                                           (LOGIOR
                                            (LOGAND
                                             -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                            (LOGAND
                                             4088
                                             (LOGHEAD
                                              28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                          :R X86)))))
                                     12)))
                                  :R X86)))))))
                           (MV-NTH
                            2
                            (LAS-TO-PAS
                             (CREATE-CANONICAL-ADDRESS-LIST
                              6 (+ 184 (XR :RIP 0 X86)))
                             :X 0
                             (MV-NTH
                              2
                              (RB
                               (CREATE-CANONICAL-ADDRESS-LIST
                                8
                                (LOGIOR
                                 (LOGAND
                                  4088
                                  (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                 (ASH
                                  (LOGHEAD
                                   40
                                   (LOGTAIL
                                    12
                                    (COMBINE-BYTES
                                     (MV-NTH
                                      1
                                      (RB
                                       (CREATE-CANONICAL-ADDRESS-LIST
                                        8
                                        (LOGIOR
                                         (LOGAND
                                          -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                         (LOGAND
                                          4088
                                          (LOGHEAD
                                           28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                       :R X86)))))
                                  12)))
                               :R
                               (MV-NTH
                                2
                                (LAS-TO-PAS
                                 (CREATE-CANONICAL-ADDRESS-LIST
                                  40 (+ 144 (XR :RIP 0 X86)))
                                 :X 0
                                 (MV-NTH
                                  2
                                  (LAS-TO-PAS
                                   (CREATE-CANONICAL-ADDRESS-LIST
                                    3 (+ 140 (XR :RIP 0 X86)))
                                   :X 0
                                   (MV-NTH
                                    2
                                    (RB
                                     (CREATE-CANONICAL-ADDRESS-LIST
                                      8
                                      (LOGIOR
                                       (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                       (LOGAND
                                        4088
                                        (LOGHEAD
                                         28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                     :R
                                     (MV-NTH
                                      2
                                      (LAS-TO-PAS
                                       (CREATE-CANONICAL-ADDRESS-LIST
                                        32 (+ 108 (XR :RIP 0 X86)))
                                       :X 0
                                       (MV-NTH
                                        2
                                        (LAS-TO-PAS
                                         (CREATE-CANONICAL-ADDRESS-LIST
                                          18 (+ 86 (XR :RIP 0 X86)))
                                         :X 0
                                         (MV-NTH
                                          2
                                          (RB
                                           (CREATE-CANONICAL-ADDRESS-LIST
                                            8
                                            (LOGIOR
                                             (LOGAND
                                              4088
                                              (LOGHEAD
                                               32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                             (ASH
                                              (LOGHEAD
                                               40
                                               (LOGTAIL
                                                12
                                                (COMBINE-BYTES
                                                 (MV-NTH
                                                  1
                                                  (RB
                                                   (CREATE-CANONICAL-ADDRESS-LIST
                                                    8
                                                    (LOGIOR
                                                     (LOGAND
                                                      -4096
                                                      (LOGEXT
                                                       64 (XR :CTR *CR3* X86)))
                                                     (LOGAND
                                                      4088
                                                      (LOGHEAD
                                                       28
                                                       (LOGTAIL
                                                        36 (XR :RGF *RDI* X86))))))
                                                   :R X86)))))
                                              12)))
                                           :R
                                           (MV-NTH
                                            2
                                            (LAS-TO-PAS
                                             (CREATE-CANONICAL-ADDRESS-LIST
                                              40 (+ 46 (XR :RIP 0 X86)))
                                             :X 0
                                             (MV-NTH
                                              2
                                              (LAS-TO-PAS
                                               (CREATE-CANONICAL-ADDRESS-LIST
                                                4 (+ 38 (XR :RIP 0 X86)))
                                               :X 0
                                               (MV-NTH
                                                2
                                                (RB
                                                 (CREATE-CANONICAL-ADDRESS-LIST
                                                  8
                                                  (LOGIOR
                                                   (LOGAND
                                                    -4096
                                                    (LOGEXT 64 (XR :CTR *CR3* X86)))
                                                   (LOGAND
                                                    4088
                                                    (LOGHEAD
                                                     28
                                                     (LOGTAIL
                                                      36 (XR :RGF *RDI* X86))))))
                                                 :R
                                                 (MV-NTH
                                                  2
                                                  (LAS-TO-PAS
                                                   (CREATE-CANONICAL-ADDRESS-LIST
                                                    25 (+ 13 (XR :RIP 0 X86)))
                                                   :X 0
                                                   (MV-NTH
                                                    2
                                                    (LAS-TO-PAS
                                                     (CREATE-CANONICAL-ADDRESS-LIST
                                                      8 (+ -24 (XR :RGF *RSP* X86)))
                                                     :R 0
                                                     (MV-NTH
                                                      2
                                                      (LAS-TO-PAS
                                                       (CREATE-CANONICAL-ADDRESS-LIST
                                                        5 (+ 8 (XR :RIP 0 X86)))
                                                       :X 0
                                                       (MV-NTH
                                                        1
                                                        (WB
                                                         (CREATE-ADDR-BYTES-ALIST
                                                          (CREATE-CANONICAL-ADDRESS-LIST
                                                           8
                                                           (+
                                                            -24 (XR :RGF *RSP* X86)))
                                                          (BYTE-IFY
                                                           8 (XR :CTR *CR3* X86)))
                                                         (MV-NTH
                                                          2
                                                          (LAS-TO-PAS
                                                           (CREATE-CANONICAL-ADDRESS-LIST
                                                            8 (XR :RIP 0 X86))
                                                           :X 0
                                                           X86)))))))))))))))))))))))))))))))))))))))))))))))))))

  :hints (("Goal"
           :in-theory (e/d* (len
                             page-size
                             consp-of-create-canonical-address-list
                             car-create-canonical-address-list
                             cdr-create-canonical-address-list
                             loghead-negative
                             disjoint-p-all-translation-governing-addresses-subset-p)
                            (create-canonical-address-list
                             (:rewrite program-at-values-and-!flgi)
                             (:rewrite get-prefixes-opener-lemma-group-4-prefix-in-marking-mode)
                             (:rewrite rb-in-terms-of-rb-subset-p-in-system-level-mode)
                             (:rewrite get-prefixes-opener-lemma-group-3-prefix-in-marking-mode)
                             (:rewrite get-prefixes-opener-lemma-group-2-prefix-in-marking-mode)
                             (:rewrite get-prefixes-opener-lemma-group-1-prefix-in-marking-mode)
                             ;; !!! Maybe I can afford to enable the following rule now?
                             (:rewrite mv-nth-2-rb-in-system-level-marking-mode)
                             (:rewrite mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)
                             (:rewrite mv-nth-2-rb-in-system-level-non-marking-mode)
                             (:rewrite rb-returns-x86-programmer-level-mode)
                             (:linear rm-low-64-logand-logior-helper-1)
                             (:definition n64p$inline)
                             (:type-prescription xlate-equiv-memory)
                             (:rewrite program-at-alt-wb-disjoint-in-system-level-mode)
                             (:type-prescription natp-page-dir-ptr-table-entry-addr)
                             mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                             mv-nth-2-las-to-pas-system-level-non-marking-mode))
           :do-not '(preprocess)
           :do-not-induct t)))

(defthm canonical-address-p-and-logext-64
  (implies (canonical-address-p a)
           (equal (logext 64 a) a))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p
                                    (:rewrite acl2::logext-identity)
                                    (:rewrite bitops::signed-byte-p-when-signed-byte-p-smaller))
                                   ()))))

;; (defthm XR-SEG-VISIBLE-MV-NTH-2-RB-new
;;   (IMPLIES t
;;            (EQUAL (XR :SEG-VISIBLE
;;                       INDEX (MV-NTH 2 (RB L-ADDRS R-W-X X86)))
;;                   (XR :SEG-VISIBLE INDEX (double-rewrite X86))))
;;   :hints (("Goal" :cases ((programmer-level-mode x86)))))

;; (thm ;; canonical-address-p for ret instruction
;;  (implies
;;   ;; (rewire_dst_to_src-assumptions x86)
;;   (and
;;    (x86-state-okp x86)
;;    (program-ok-p x86)
;;    (stack-ok-p x86)
;;    (program-and-stack-no-interfere-p x86)
;;    (program-and-stack-no-interfere-p-aux x86)
;;    (source-addresses-ok-p x86)
;;    (source-PML4TE-ok-p x86)
;;    (source-PDPTE-ok-p x86)
;;    (source-PML4TE-and-stack-no-interfere-p x86)
;;    (source-PML4TE-and-program-no-interfere-p x86)
;;    (source-PML4TE-itself-no-interfere-p x86)
;;    (source-PML4TE-and-stack-no-interfere-p-aux x86)
;;    (source-PDPTE-and-stack-no-interfere-p x86)
;;    (source-PDPTE-and-program-no-interfere-p x86)
;;    (source-PDPTE-itself-no-interfere-p x86)
;;    (source-PDPTE-and-stack-no-interfere-p-aux x86)
;;    ;; This is too strong ('coz equality of rbs doesn't matter, but
;;    ;; xlate-equiv matters), but I'll let this lie for now.
;;    (source-PDPTE-and-source-PML4E-no-interfere-p x86)

;;    (destination-addresses-ok-p x86)
;;    (destination-PML4TE-ok-p x86)
;;    (destination-PDPTE-ok-p x86)
;;    (destination-PML4TE-and-stack-no-interfere-p x86)
;;    (destination-PML4TE-and-program-no-interfere-p x86)
;;    (destination-PML4TE-itself-no-interfere-p x86)
;;    (destination-PML4TE-and-stack-no-interfere-p-aux x86)
;;    ;; Too strong?
;;    (destination-PML4TE-and-source-PML4TE-no-interfere-p x86)
;;    (destination-PML4TE-and-source-PDPTE-no-interfere-p x86)

;;    (destination-PDPTE-and-source-PML4E-no-interfere-p x86)
;;    (destination-PDPTE-and-source-PDPTE-no-interfere-p x86)
;;    (destination-PDPTE-and-destination-PML4TE-no-interfere-p x86)
;;    (destination-PDPTE-and-stack-no-interfere-p x86)
;;    (destination-PDPTE-and-program-no-interfere-p x86)
;;    (destination-PDPTE-and-program-no-interfere-p-aux x86)
;;    (destination-PDPTE-itself-no-interfere-p x86)
;;    (destination-PDPTE-and-stack-no-interfere-p-aux x86)

;;    (direct-map-p
;;     8
;;     (page-dir-ptr-table-entry-addr
;;      (xr :rgf *rsi* x86)
;;      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
;;     :w (cpl x86) x86)

;;    (return-instruction-address-ok-p x86)
;;    (return-addresses-itself-no-interfere-p x86)
;;    ;; !!! FIX: The following is in terms of disjoint-p instead of disjoint-p$.
;;    (return-addresses-and-program-no-interfere-p x86)
;;    (ret-instruction-and-source-PML4E-no-interfere-p x86)
;;    (ret-instruction-and-source-PDPTE-no-interfere-p x86)
;;    (ret-instruction-and-destination-PML4E-no-interfere-p x86)
;;    (ret-instruction-and-destination-PDPTE-no-interfere-p x86)
;;    (return-address-and-stack-no-interfere-p x86)

;;    ;; (canonical-address-p (xr :rgf *rsp* x86))
;;    )

;;   (CANONICAL-ADDRESS-P
;;    (LOGEXT
;;     64
;;     (COMBINE-BYTES
;;      (MV-NTH
;;       1
;;       (RB
;;        (CREATE-CANONICAL-ADDRESS-LIST 8 (XR :RGF *RSP* X86))
;;        :R
;;        (MV-NTH
;;         2
;;         (LAS-TO-PAS
;;          (CREATE-CANONICAL-ADDRESS-LIST 22 (+ 224 (XR :RIP 0 X86)))
;;          :X 0
;;          (MV-NTH
;;           2
;;           (LAS-TO-PAS
;;            (CREATE-CANONICAL-ADDRESS-LIST 6 (+ 218 (XR :RIP 0 X86)))
;;            :X 0
;;            (MV-NTH
;;             2
;;             (LAS-TO-PAS
;;              (CREATE-CANONICAL-ADDRESS-LIST 10 (+ 208 (XR :RIP 0 X86)))
;;              :X 0
;;              (MV-NTH
;;               2
;;               (LAS-TO-PAS
;;                (CREATE-CANONICAL-ADDRESS-LIST 2 (+ 206 (XR :RIP 0 X86)))
;;                :X 0
;;                (MV-NTH
;;                 2
;;                 (LAS-TO-PAS
;;                  (CREATE-CANONICAL-ADDRESS-LIST 5 (+ 200 (XR :RIP 0 X86)))
;;                  :X 0
;;                  (MV-NTH
;;                   2
;;                   (LAS-TO-PAS
;;                    (CREATE-CANONICAL-ADDRESS-LIST 6 (+ 194 (XR :RIP 0 X86)))
;;                    :X 0
;;                    (MV-NTH
;;                     2
;;                     (LAS-TO-PAS
;;                      (CREATE-CANONICAL-ADDRESS-LIST
;;                       4 (+ 190 (XR :RIP 0 X86)))
;;                      :X 0
;;                      (MV-NTH
;;                       1
;;                       (WB
;;                        (CREATE-ADDR-BYTES-ALIST
;;                         (CREATE-CANONICAL-ADDRESS-LIST
;;                          8
;;                          (LOGIOR
;;                           (LOGAND
;;                            4088
;;                            (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;                           (ASH
;;                            (LOGHEAD
;;                             40
;;                             (LOGTAIL
;;                              12
;;                              (COMBINE-BYTES
;;                               (MV-NTH
;;                                1
;;                                (RB
;;                                 (CREATE-CANONICAL-ADDRESS-LIST
;;                                  8
;;                                  (LOGIOR
;;                                   (LOGAND
;;                                    -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                                   (LOGAND
;;                                    4088
;;                                    (LOGHEAD
;;                                     28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
;;                                 :R X86)))))
;;                            12)))
;;                         (BYTE-IFY
;;                          8
;;                          (LOGIOR
;;                           (LOGAND
;;                            18442240475155922943
;;                            (COMBINE-BYTES
;;                             (MV-NTH
;;                              1
;;                              (RB
;;                               (CREATE-CANONICAL-ADDRESS-LIST
;;                                8
;;                                (LOGIOR
;;                                 (LOGAND
;;                                  4088
;;                                  (LOGHEAD
;;                                   32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;                                 (ASH
;;                                  (LOGHEAD
;;                                   40
;;                                   (LOGTAIL
;;                                    12
;;                                    (COMBINE-BYTES
;;                                     (MV-NTH
;;                                      1
;;                                      (RB
;;                                       (CREATE-CANONICAL-ADDRESS-LIST
;;                                        8
;;                                        (LOGIOR
;;                                         (LOGAND
;;                                          -4096
;;                                          (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                                         (LOGAND
;;                                          4088
;;                                          (LOGHEAD
;;                                           28
;;                                           (LOGTAIL
;;                                            36 (XR :RGF *RSI* X86))))))
;;                                       :R X86)))))
;;                                  12)))
;;                               :R X86))))
;;                           (LOGAND
;;                            4503598553628672
;;                            (COMBINE-BYTES
;;                             (MV-NTH
;;                              1
;;                              (RB
;;                               (CREATE-CANONICAL-ADDRESS-LIST
;;                                8
;;                                (LOGIOR
;;                                 (LOGAND
;;                                  4088
;;                                  (LOGHEAD
;;                                   32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;                                 (ASH
;;                                  (LOGHEAD
;;                                   40
;;                                   (LOGTAIL
;;                                    12
;;                                    (COMBINE-BYTES
;;                                     (MV-NTH
;;                                      1
;;                                      (RB
;;                                       (CREATE-CANONICAL-ADDRESS-LIST
;;                                        8
;;                                        (LOGIOR
;;                                         (LOGAND
;;                                          -4096
;;                                          (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                                         (LOGAND
;;                                          4088
;;                                          (LOGHEAD
;;                                           28
;;                                           (LOGTAIL
;;                                            36 (XR :RGF *RDI* X86))))))
;;                                       :R X86)))))
;;                                  12)))
;;                               :R X86)))))))
;;                        (MV-NTH
;;                         2
;;                         (LAS-TO-PAS
;;                          (CREATE-CANONICAL-ADDRESS-LIST
;;                           6 (+ 184 (XR :RIP 0 X86)))
;;                          :X 0
;;                          (MV-NTH
;;                           2
;;                           (RB
;;                            (CREATE-CANONICAL-ADDRESS-LIST
;;                             8
;;                             (LOGIOR
;;                              (LOGAND
;;                               4088
;;                               (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;                              (ASH
;;                               (LOGHEAD
;;                                40
;;                                (LOGTAIL
;;                                 12
;;                                 (COMBINE-BYTES
;;                                  (MV-NTH
;;                                   1
;;                                   (RB
;;                                    (CREATE-CANONICAL-ADDRESS-LIST
;;                                     8
;;                                     (LOGIOR
;;                                      (LOGAND
;;                                       -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                                      (LOGAND
;;                                       4088
;;                                       (LOGHEAD
;;                                        28
;;                                        (LOGTAIL 36 (XR :RGF *RSI* X86))))))
;;                                    :R X86)))))
;;                               12)))
;;                            :R
;;                            (MV-NTH
;;                             2
;;                             (LAS-TO-PAS
;;                              (CREATE-CANONICAL-ADDRESS-LIST
;;                               40 (+ 144 (XR :RIP 0 X86)))
;;                              :X 0
;;                              (MV-NTH
;;                               2
;;                               (LAS-TO-PAS
;;                                (CREATE-CANONICAL-ADDRESS-LIST
;;                                 3 (+ 140 (XR :RIP 0 X86)))
;;                                :X 0
;;                                (MV-NTH
;;                                 2
;;                                 (RB
;;                                  (CREATE-CANONICAL-ADDRESS-LIST
;;                                   8
;;                                   (LOGIOR
;;                                    (LOGAND
;;                                     -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                                    (LOGAND
;;                                     4088
;;                                     (LOGHEAD
;;                                      28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
;;                                  :R
;;                                  (MV-NTH
;;                                   2
;;                                   (LAS-TO-PAS
;;                                    (CREATE-CANONICAL-ADDRESS-LIST
;;                                     32 (+ 108 (XR :RIP 0 X86)))
;;                                    :X 0
;;                                    (MV-NTH
;;                                     2
;;                                     (LAS-TO-PAS
;;                                      (CREATE-CANONICAL-ADDRESS-LIST
;;                                       18 (+ 86 (XR :RIP 0 X86)))
;;                                      :X 0
;;                                      (MV-NTH
;;                                       2
;;                                       (RB
;;                                        (CREATE-CANONICAL-ADDRESS-LIST
;;                                         8
;;                                         (LOGIOR
;;                                          (LOGAND
;;                                           4088
;;                                           (LOGHEAD
;;                                            32
;;                                            (LOGTAIL
;;                                             27 (XR :RGF *RDI* X86))))
;;                                          (ASH
;;                                           (LOGHEAD
;;                                            40
;;                                            (LOGTAIL
;;                                             12
;;                                             (COMBINE-BYTES
;;                                              (MV-NTH
;;                                               1
;;                                               (RB
;;                                                (CREATE-CANONICAL-ADDRESS-LIST
;;                                                 8
;;                                                 (LOGIOR
;;                                                  (LOGAND
;;                                                   -4096
;;                                                   (LOGEXT
;;                                                    64 (XR :CTR *CR3* X86)))
;;                                                  (LOGAND
;;                                                   4088
;;                                                   (LOGHEAD
;;                                                    28
;;                                                    (LOGTAIL
;;                                                     36
;;                                                     (XR :RGF *RDI* X86))))))
;;                                                :R X86)))))
;;                                           12)))
;;                                        :R
;;                                        (MV-NTH
;;                                         2
;;                                         (LAS-TO-PAS
;;                                          (CREATE-CANONICAL-ADDRESS-LIST
;;                                           40 (+ 46 (XR :RIP 0 X86)))
;;                                          :X 0
;;                                          (MV-NTH
;;                                           2
;;                                           (LAS-TO-PAS
;;                                            (CREATE-CANONICAL-ADDRESS-LIST
;;                                             4 (+ 38 (XR :RIP 0 X86)))
;;                                            :X 0
;;                                            (MV-NTH
;;                                             2
;;                                             (RB
;;                                              (CREATE-CANONICAL-ADDRESS-LIST
;;                                               8
;;                                               (LOGIOR
;;                                                (LOGAND
;;                                                 -4096
;;                                                 (LOGEXT
;;                                                  64 (XR :CTR *CR3* X86)))
;;                                                (LOGAND
;;                                                 4088
;;                                                 (LOGHEAD
;;                                                  28
;;                                                  (LOGTAIL
;;                                                   36
;;                                                   (XR :RGF *RDI* X86))))))
;;                                              :R
;;                                              (MV-NTH
;;                                               2
;;                                               (LAS-TO-PAS
;;                                                (CREATE-CANONICAL-ADDRESS-LIST
;;                                                 25 (+ 13 (XR :RIP 0 X86)))
;;                                                :X 0
;;                                                (MV-NTH
;;                                                 2
;;                                                 (LAS-TO-PAS
;;                                                  (CREATE-CANONICAL-ADDRESS-LIST
;;                                                   8
;;                                                   (+
;;                                                    -24 (XR :RGF *RSP* X86)))
;;                                                  :R 0
;;                                                  (MV-NTH
;;                                                   2
;;                                                   (LAS-TO-PAS
;;                                                    (CREATE-CANONICAL-ADDRESS-LIST
;;                                                     5 (+ 8 (XR :RIP 0 X86)))
;;                                                    :X 0
;;                                                    (MV-NTH
;;                                                     1
;;                                                     (WB
;;                                                      (CREATE-ADDR-BYTES-ALIST
;;                                                       (CREATE-CANONICAL-ADDRESS-LIST
;;                                                        8
;;                                                        (+
;;                                                         -24
;;                                                         (XR
;;                                                          :RGF *RSP* X86)))
;;                                                       (BYTE-IFY
;;                                                        8
;;                                                        (XR :CTR *CR3* X86)))
;;                                                      (MV-NTH
;;                                                       2
;;                                                       (LAS-TO-PAS
;;                                                        (CREATE-CANONICAL-ADDRESS-LIST
;;                                                         8 (XR :RIP 0 X86))
;;                                                        :X 0
;;                                                        X86))))))))))))))))))))))))))))))))))))))))))))))))))))))

;;  :hints (("Goal"
;;           :in-theory (e/d* (len
;;                             page-size
;;                             consp-of-create-canonical-address-list
;;                             car-create-canonical-address-list
;;                             cdr-create-canonical-address-list
;;                             loghead-negative
;;                             disjoint-p-all-translation-governing-addresses-subset-p)
;;                            (create-canonical-address-list
;;                             (:rewrite program-at-values-and-!flgi)
;;                             (:rewrite get-prefixes-opener-lemma-group-4-prefix-in-marking-mode)
;;                             (:rewrite rb-in-terms-of-rb-subset-p-in-system-level-mode)
;;                             (:rewrite get-prefixes-opener-lemma-group-3-prefix-in-marking-mode)
;;                             (:rewrite get-prefixes-opener-lemma-group-2-prefix-in-marking-mode)
;;                             (:rewrite get-prefixes-opener-lemma-group-1-prefix-in-marking-mode)
;;                             ;; !!! Maybe I can afford to enable the following rule now?
;;                             (:rewrite mv-nth-2-rb-in-system-level-marking-mode)
;;                             (:rewrite mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)
;;                             (:rewrite mv-nth-2-rb-in-system-level-non-marking-mode)
;;                             (:rewrite rb-returns-x86-programmer-level-mode)
;;                             (:linear rm-low-64-logand-logior-helper-1)
;;                             (:definition n64p$inline)
;;                             (:type-prescription xlate-equiv-memory)
;;                             (:rewrite program-at-alt-wb-disjoint-in-system-level-mode)
;;                             (:type-prescription natp-page-dir-ptr-table-entry-addr)
;;                             mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
;;                             mv-nth-2-las-to-pas-system-level-non-marking-mode))
;;           :do-not '(preprocess)
;;           :do-not-induct t)))

(thm ;; 46-58 instructions
 (implies
  ;; (rewire_dst_to_src-assumptions x86)
  (and
   (x86-state-okp x86)
   (program-ok-p x86)
   (stack-ok-p x86)
   (program-and-stack-no-interfere-p x86)
   (program-and-stack-no-interfere-p-aux x86)
   (source-addresses-ok-p x86)
   (source-PML4TE-ok-p x86)
   (source-PDPTE-ok-p x86)
   (source-PML4TE-and-stack-no-interfere-p x86)
   (source-PML4TE-and-program-no-interfere-p x86)
   (source-PML4TE-itself-no-interfere-p x86)
   (source-PML4TE-and-stack-no-interfere-p-aux x86)
   (source-PDPTE-and-stack-no-interfere-p x86)
   (source-PDPTE-and-program-no-interfere-p x86)
   (source-PDPTE-itself-no-interfere-p x86)
   (source-PDPTE-and-stack-no-interfere-p-aux x86)
   ;; This is too strong (coz equality of rbs doesnt matter, but
   ;; xlate-equiv matters), but Ill let this lie for now.
   (source-PDPTE-and-source-PML4E-no-interfere-p x86)

   (destination-addresses-ok-p x86)
   (destination-PML4TE-ok-p x86)
   (destination-PDPTE-ok-p x86)
   (destination-PML4TE-and-stack-no-interfere-p x86)
   (destination-PML4TE-and-program-no-interfere-p x86)
   (destination-PML4TE-itself-no-interfere-p x86)
   (destination-PML4TE-and-stack-no-interfere-p-aux x86)
   ;; Too strong?
   (destination-PML4TE-and-source-PML4TE-no-interfere-p x86)
   (destination-PML4TE-and-source-PDPTE-no-interfere-p x86)

   (destination-PDPTE-and-source-PML4E-no-interfere-p x86)
   (destination-PDPTE-and-source-PDPTE-no-interfere-p x86)
   (destination-PDPTE-and-destination-PML4TE-no-interfere-p x86)
   (destination-PDPTE-and-stack-no-interfere-p x86)
   (destination-PDPTE-and-program-no-interfere-p x86)
   (destination-PDPTE-and-program-no-interfere-p-aux x86)
   (destination-PDPTE-itself-no-interfere-p x86)
   (destination-PDPTE-and-stack-no-interfere-p-aux x86)

   (direct-map-p
    8
    (page-dir-ptr-table-entry-addr
     (xr :rgf *rsi* x86)
     (pdpt-base-addr (xr :rgf *rsi* x86) x86))
    :w (cpl x86) x86)

   ;; !!! FIX: Some of the following are in terms of disjoint-p
   ;; !!! instead of disjoint-p$.
   (return-instruction-address-ok-p x86)
   (return-addresses-itself-no-interfere-p x86)
   (return-addresses-and-program-no-interfere-p x86)
   (ret-instruction-and-source-PML4E-no-interfere-p x86)
   (ret-instruction-and-source-PDPTE-no-interfere-p x86)
   (ret-instruction-and-destination-PML4E-no-interfere-p x86)
   (ret-instruction-and-destination-PDPTE-no-interfere-p x86)
   (return-address-and-stack-no-interfere-p x86))

  (equal (x86-run 13
                  ;; Result of (x86-run 45 x86).
                  (XW
                   :RGF *RAX*
                   (LOGIOR
                    (LOGAND
                     -4503598553628673
                     (LOGEXT
                      64
                      (COMBINE-BYTES
                       (MV-NTH
                        1
                        (RB
                         (CREATE-CANONICAL-ADDRESS-LIST
                          8
                          (LOGIOR
                           (LOGAND 4088
                                   (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                           (ASH
                            (LOGHEAD
                             40
                             (LOGTAIL
                              12
                              (COMBINE-BYTES
                               (MV-NTH
                                1
                                (RB
                                 (CREATE-CANONICAL-ADDRESS-LIST
                                  8
                                  (LOGIOR
                                   (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                   (LOGAND 4088
                                           (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                 :R X86)))))
                            12)))
                         :R X86)))))
                    (LOGAND
                     4503598553628672
                     (LOGEXT
                      64
                      (COMBINE-BYTES
                       (MV-NTH
                        1
                        (RB
                         (CREATE-CANONICAL-ADDRESS-LIST
                          8
                          (LOGIOR
                           (LOGAND 4088
                                   (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                           (ASH
                            (LOGHEAD
                             40
                             (LOGTAIL
                              12
                              (COMBINE-BYTES
                               (MV-NTH
                                1
                                (RB
                                 (CREATE-CANONICAL-ADDRESS-LIST
                                  8
                                  (LOGIOR
                                   (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                   (LOGAND 4088
                                           (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                 :R X86)))))
                            12)))
                         :R X86))))))
                   (XW
                    :RGF *RCX*
                    (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                            (LOGAND 4088
                                    (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                    (XW
                     :RGF *RDX*
                     (LOGIOR
                      (LOGAND
                       -4503598553628673
                       (LOGEXT
                        64
                        (COMBINE-BYTES
                         (MV-NTH
                          1
                          (RB
                           (CREATE-CANONICAL-ADDRESS-LIST
                            8
                            (LOGIOR
                             (LOGAND 4088
                                     (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                             (ASH
                              (LOGHEAD
                               40
                               (LOGTAIL
                                12
                                (COMBINE-BYTES
                                 (MV-NTH
                                  1
                                  (RB
                                   (CREATE-CANONICAL-ADDRESS-LIST
                                    8
                                    (LOGIOR
                                     (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                     (LOGAND 4088
                                             (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                   :R X86)))))
                              12)))
                           :R X86)))))
                      (LOGAND
                       4503598553628672
                       (LOGEXT
                        64
                        (COMBINE-BYTES
                         (MV-NTH
                          1
                          (RB
                           (CREATE-CANONICAL-ADDRESS-LIST
                            8
                            (LOGIOR
                             (LOGAND 4088
                                     (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                             (ASH
                              (LOGHEAD
                               40
                               (LOGTAIL
                                12
                                (COMBINE-BYTES
                                 (MV-NTH
                                  1
                                  (RB
                                   (CREATE-CANONICAL-ADDRESS-LIST
                                    8
                                    (LOGIOR
                                     (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                     (LOGAND 4088
                                             (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                   :R X86)))))
                              12)))
                           :R X86))))))
                     (XW
                      :RGF *R8* 1099511627775
                      (XW
                       :RGF *R9*
                       (LOGAND
                        4503598553628672
                        (LOGEXT
                         64
                         (COMBINE-BYTES
                          (MV-NTH
                           1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST
                             8
                             (LOGIOR
                              (LOGAND 4088
                                      (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                              (ASH
                               (LOGHEAD
                                40
                                (LOGTAIL
                                 12
                                 (COMBINE-BYTES
                                  (MV-NTH
                                   1
                                   (RB
                                    (CREATE-CANONICAL-ADDRESS-LIST
                                     8
                                     (LOGIOR
                                      (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                      (LOGAND
                                       4088
                                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                    :R X86)))))
                               12)))
                            :R X86)))))
                       (XW
                        :RIP 0 (+ 193 (XR :RIP 0 X86))
                        (XW
                         :UNDEF 0 (+ 39 (NFIX (XR :UNDEF 0 X86)))
                         (!FLGI
                          *CF* 0
                          (!FLGI
                           *PF*
                           (PF-SPEC64
                            (LOGIOR
                             (LOGAND
                              18442240475155922943
                              (COMBINE-BYTES
                               (MV-NTH
                                1
                                (RB
                                 (CREATE-CANONICAL-ADDRESS-LIST
                                  8
                                  (LOGIOR
                                   (LOGAND 4088
                                           (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                   (ASH
                                    (LOGHEAD
                                     40
                                     (LOGTAIL
                                      12
                                      (COMBINE-BYTES
                                       (MV-NTH
                                        1
                                        (RB
                                         (CREATE-CANONICAL-ADDRESS-LIST
                                          8
                                          (LOGIOR
                                           (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                           (LOGAND
                                            4088
                                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                         :R X86)))))
                                    12)))
                                 :R X86))))
                             (LOGAND
                              4503598553628672
                              (COMBINE-BYTES
                               (MV-NTH
                                1
                                (RB
                                 (CREATE-CANONICAL-ADDRESS-LIST
                                  8
                                  (LOGIOR
                                   (LOGAND 4088
                                           (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                   (ASH
                                    (LOGHEAD
                                     40
                                     (LOGTAIL
                                      12
                                      (COMBINE-BYTES
                                       (MV-NTH
                                        1
                                        (RB
                                         (CREATE-CANONICAL-ADDRESS-LIST
                                          8
                                          (LOGIOR
                                           (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                           (LOGAND
                                            4088
                                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                         :R X86)))))
                                    12)))
                                 :R X86))))))
                           (!FLGI
                            *AF*
                            (LOGHEAD 1
                                     (CREATE-UNDEF (+ 38 (NFIX (XR :UNDEF 0 X86)))))
                            (!FLGI
                             *ZF*
                             (ZF-SPEC
                              (LOGIOR
                               (LOGAND
                                18442240475155922943
                                (COMBINE-BYTES
                                 (MV-NTH
                                  1
                                  (RB
                                   (CREATE-CANONICAL-ADDRESS-LIST
                                    8
                                    (LOGIOR
                                     (LOGAND 4088
                                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                     (ASH
                                      (LOGHEAD
                                       40
                                       (LOGTAIL
                                        12
                                        (COMBINE-BYTES
                                         (MV-NTH
                                          1
                                          (RB
                                           (CREATE-CANONICAL-ADDRESS-LIST
                                            8
                                            (LOGIOR
                                             (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                             (LOGAND
                                              4088
                                              (LOGHEAD
                                               28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                           :R X86)))))
                                      12)))
                                   :R X86))))
                               (LOGAND
                                4503598553628672
                                (COMBINE-BYTES
                                 (MV-NTH
                                  1
                                  (RB
                                   (CREATE-CANONICAL-ADDRESS-LIST
                                    8
                                    (LOGIOR
                                     (LOGAND 4088
                                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                     (ASH
                                      (LOGHEAD
                                       40
                                       (LOGTAIL
                                        12
                                        (COMBINE-BYTES
                                         (MV-NTH
                                          1
                                          (RB
                                           (CREATE-CANONICAL-ADDRESS-LIST
                                            8
                                            (LOGIOR
                                             (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                             (LOGAND
                                              4088
                                              (LOGHEAD
                                               28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                           :R X86)))))
                                      12)))
                                   :R X86))))))
                             (!FLGI
                              *SF*
                              (SF-SPEC64
                               (LOGIOR
                                (LOGAND
                                 18442240475155922943
                                 (COMBINE-BYTES
                                  (MV-NTH
                                   1
                                   (RB
                                    (CREATE-CANONICAL-ADDRESS-LIST
                                     8
                                     (LOGIOR
                                      (LOGAND 4088
                                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                      (ASH
                                       (LOGHEAD
                                        40
                                        (LOGTAIL
                                         12
                                         (COMBINE-BYTES
                                          (MV-NTH
                                           1
                                           (RB
                                            (CREATE-CANONICAL-ADDRESS-LIST
                                             8
                                             (LOGIOR
                                              (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                              (LOGAND
                                               4088
                                               (LOGHEAD
                                                28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                            :R X86)))))
                                       12)))
                                    :R X86))))
                                (LOGAND
                                 4503598553628672
                                 (COMBINE-BYTES
                                  (MV-NTH
                                   1
                                   (RB
                                    (CREATE-CANONICAL-ADDRESS-LIST
                                     8
                                     (LOGIOR
                                      (LOGAND 4088
                                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                      (ASH
                                       (LOGHEAD
                                        40
                                        (LOGTAIL
                                         12
                                         (COMBINE-BYTES
                                          (MV-NTH
                                           1
                                           (RB
                                            (CREATE-CANONICAL-ADDRESS-LIST
                                             8
                                             (LOGIOR
                                              (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                              (LOGAND
                                               4088
                                               (LOGHEAD
                                                28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                            :R X86)))))
                                       12)))
                                    :R X86))))))
                              (!FLGI
                               *OF* 0
                               (MV-NTH
                                2
                                (LAS-TO-PAS
                                 (CREATE-CANONICAL-ADDRESS-LIST 3 (+ 190 (XR :RIP 0 X86)))
                                 :X 0
                                 (MV-NTH
                                  1
                                  (WB
                                   (CREATE-ADDR-BYTES-ALIST
                                    (CREATE-CANONICAL-ADDRESS-LIST
                                     8
                                     (LOGIOR
                                      (LOGAND 4088
                                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                      (ASH
                                       (LOGHEAD
                                        40
                                        (LOGTAIL
                                         12
                                         (COMBINE-BYTES
                                          (MV-NTH
                                           1
                                           (RB
                                            (CREATE-CANONICAL-ADDRESS-LIST
                                             8
                                             (LOGIOR
                                              (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                              (LOGAND
                                               4088
                                               (LOGHEAD
                                                28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                            :R X86)))))
                                       12)))
                                    (BYTE-IFY
                                     8
                                     (LOGIOR
                                      (LOGAND
                                       18442240475155922943
                                       (COMBINE-BYTES
                                        (MV-NTH
                                         1
                                         (RB
                                          (CREATE-CANONICAL-ADDRESS-LIST
                                           8
                                           (LOGIOR
                                            (LOGAND
                                             4088
                                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                            (ASH
                                             (LOGHEAD
                                              40
                                              (LOGTAIL
                                               12
                                               (COMBINE-BYTES
                                                (MV-NTH
                                                 1
                                                 (RB
                                                  (CREATE-CANONICAL-ADDRESS-LIST
                                                   8
                                                   (LOGIOR
                                                    (LOGAND
                                                     -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                                    (LOGAND
                                                     4088
                                                     (LOGHEAD
                                                      28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                                  :R X86)))))
                                             12)))
                                          :R X86))))
                                      (LOGAND
                                       4503598553628672
                                       (COMBINE-BYTES
                                        (MV-NTH
                                         1
                                         (RB
                                          (CREATE-CANONICAL-ADDRESS-LIST
                                           8
                                           (LOGIOR
                                            (LOGAND
                                             4088
                                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                            (ASH
                                             (LOGHEAD
                                              40
                                              (LOGTAIL
                                               12
                                               (COMBINE-BYTES
                                                (MV-NTH
                                                 1
                                                 (RB
                                                  (CREATE-CANONICAL-ADDRESS-LIST
                                                   8
                                                   (LOGIOR
                                                    (LOGAND
                                                     -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                                    (LOGAND
                                                     4088
                                                     (LOGHEAD
                                                      28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                                  :R X86)))))
                                             12)))
                                          :R X86)))))))
                                   (MV-NTH
                                    2
                                    (LAS-TO-PAS
                                     (CREATE-CANONICAL-ADDRESS-LIST
                                      6 (+ 184 (XR :RIP 0 X86)))
                                     :X 0
                                     (MV-NTH
                                      2
                                      (RB
                                       (CREATE-CANONICAL-ADDRESS-LIST
                                        8
                                        (LOGIOR
                                         (LOGAND
                                          4088
                                          (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                         (ASH
                                          (LOGHEAD
                                           40
                                           (LOGTAIL
                                            12
                                            (COMBINE-BYTES
                                             (MV-NTH
                                              1
                                              (RB
                                               (CREATE-CANONICAL-ADDRESS-LIST
                                                8
                                                (LOGIOR
                                                 (LOGAND
                                                  -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                                 (LOGAND
                                                  4088
                                                  (LOGHEAD
                                                   28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                               :R X86)))))
                                          12)))
                                       :R
                                       (MV-NTH
                                        2
                                        (LAS-TO-PAS
                                         (CREATE-CANONICAL-ADDRESS-LIST
                                          40 (+ 144 (XR :RIP 0 X86)))
                                         :X 0
                                         (MV-NTH
                                          2
                                          (LAS-TO-PAS
                                           (CREATE-CANONICAL-ADDRESS-LIST
                                            3 (+ 140 (XR :RIP 0 X86)))
                                           :X 0
                                           (MV-NTH
                                            2
                                            (RB
                                             (CREATE-CANONICAL-ADDRESS-LIST
                                              8
                                              (LOGIOR
                                               (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                               (LOGAND
                                                4088
                                                (LOGHEAD
                                                 28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                             :R
                                             (MV-NTH
                                              2
                                              (LAS-TO-PAS
                                               (CREATE-CANONICAL-ADDRESS-LIST
                                                32 (+ 108 (XR :RIP 0 X86)))
                                               :X 0
                                               (MV-NTH
                                                2
                                                (LAS-TO-PAS
                                                 (CREATE-CANONICAL-ADDRESS-LIST
                                                  18 (+ 86 (XR :RIP 0 X86)))
                                                 :X 0
                                                 (MV-NTH
                                                  2
                                                  (RB
                                                   (CREATE-CANONICAL-ADDRESS-LIST
                                                    8
                                                    (LOGIOR
                                                     (LOGAND
                                                      4088
                                                      (LOGHEAD
                                                       32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                                     (ASH
                                                      (LOGHEAD
                                                       40
                                                       (LOGTAIL
                                                        12
                                                        (COMBINE-BYTES
                                                         (MV-NTH
                                                          1
                                                          (RB
                                                           (CREATE-CANONICAL-ADDRESS-LIST
                                                            8
                                                            (LOGIOR
                                                             (LOGAND
                                                              -4096
                                                              (LOGEXT
                                                               64 (XR :CTR *CR3* X86)))
                                                             (LOGAND
                                                              4088
                                                              (LOGHEAD
                                                               28
                                                               (LOGTAIL
                                                                36 (XR :RGF *RDI* X86))))))
                                                           :R X86)))))
                                                      12)))
                                                   :R
                                                   (MV-NTH
                                                    2
                                                    (LAS-TO-PAS
                                                     (CREATE-CANONICAL-ADDRESS-LIST
                                                      40 (+ 46 (XR :RIP 0 X86)))
                                                     :X 0
                                                     (MV-NTH
                                                      2
                                                      (LAS-TO-PAS
                                                       (CREATE-CANONICAL-ADDRESS-LIST
                                                        4 (+ 38 (XR :RIP 0 X86)))
                                                       :X 0
                                                       (MV-NTH
                                                        2
                                                        (RB
                                                         (CREATE-CANONICAL-ADDRESS-LIST
                                                          8
                                                          (LOGIOR
                                                           (LOGAND
                                                            -4096
                                                            (LOGEXT 64 (XR :CTR *CR3* X86)))
                                                           (LOGAND
                                                            4088
                                                            (LOGHEAD
                                                             28
                                                             (LOGTAIL
                                                              36 (XR :RGF *RDI* X86))))))
                                                         :R
                                                         (MV-NTH
                                                          2
                                                          (LAS-TO-PAS
                                                           (CREATE-CANONICAL-ADDRESS-LIST
                                                            25 (+ 13 (XR :RIP 0 X86)))
                                                           :X 0
                                                           (MV-NTH
                                                            2
                                                            (LAS-TO-PAS
                                                             (CREATE-CANONICAL-ADDRESS-LIST
                                                              8 (+ -24 (XR :RGF *RSP* X86)))
                                                             :R 0
                                                             (MV-NTH
                                                              2
                                                              (LAS-TO-PAS
                                                               (CREATE-CANONICAL-ADDRESS-LIST
                                                                5 (+ 8 (XR :RIP 0 X86)))
                                                               :X 0
                                                               (MV-NTH
                                                                1
                                                                (WB
                                                                 (CREATE-ADDR-BYTES-ALIST
                                                                  (CREATE-CANONICAL-ADDRESS-LIST
                                                                   8
                                                                   (+
                                                                    -24 (XR :RGF *RSP* X86)))
                                                                  (BYTE-IFY
                                                                   8 (XR :CTR *CR3* X86)))
                                                                 (MV-NTH
                                                                  2
                                                                  (LAS-TO-PAS
                                                                   (CREATE-CANONICAL-ADDRESS-LIST
                                                                    8 (XR :RIP 0 X86))
                                                                   :X 0
                                                                   X86))))))))))))))))))))))))))))))))))))))))))))))))))
         (XW
          :RGF *RAX* 1
          (XW
           :RGF *RCX*
           (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                   (LOGAND 4088
                           (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
           (XW
            :RGF *RDX*
            (LOGAND
             4503598553628672
             (LOGIOR
              (LOGAND
               -4503598553628673
               (LOGEXT
                64
                (COMBINE-BYTES
                 (MV-NTH
                  1
                  (RB
                   (CREATE-CANONICAL-ADDRESS-LIST
                    8
                    (LOGIOR
                     (LOGAND 4088
                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                     (ASH
                      (LOGHEAD
                       40
                       (LOGTAIL
                        12
                        (COMBINE-BYTES
                         (MV-NTH
                          1
                          (RB
                           (CREATE-CANONICAL-ADDRESS-LIST
                            8
                            (LOGIOR
                             (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                             (LOGAND 4088
                                     (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                           :R X86)))))
                      12)))
                   :R X86)))))
              (LOGAND
               4503598553628672
               (LOGEXT
                64
                (COMBINE-BYTES
                 (MV-NTH
                  1
                  (RB
                   (CREATE-CANONICAL-ADDRESS-LIST
                    8
                    (LOGIOR
                     (LOGAND 4088
                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                     (ASH
                      (LOGHEAD
                       40
                       (LOGTAIL
                        12
                        (COMBINE-BYTES
                         (MV-NTH
                          1
                          (RB
                           (CREATE-CANONICAL-ADDRESS-LIST
                            8
                            (LOGIOR
                             (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                             (LOGAND 4088
                                     (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                           :R X86)))))
                      12)))
                   :R X86)))))))
            (XW
             :RGF *RSP* (+ 8 (XR :RGF *RSP* X86))
             (XW
              :RGF *RSI* 0
              (XW
               :RGF *RDI*
               (LOGAND
                4503598553628672
                (LOGEXT
                 64
                 (COMBINE-BYTES
                  (MV-NTH
                   1
                   (RB
                    (CREATE-CANONICAL-ADDRESS-LIST
                     8
                     (LOGIOR
                      (LOGAND 4088
                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                      (ASH
                       (LOGHEAD
                        40
                        (LOGTAIL
                         12
                         (COMBINE-BYTES
                          (MV-NTH
                           1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST
                             8
                             (LOGIOR
                              (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                              (LOGAND 4088
                                      (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                            :R X86)))))
                       12)))
                    :R X86)))))
               (XW
                :RGF *R8* 1099511627775
                (XW
                 :RGF *R9*
                 (LOGAND
                  4503598553628672
                  (LOGEXT
                   64
                   (COMBINE-BYTES
                    (MV-NTH
                     1
                     (RB
                      (CREATE-CANONICAL-ADDRESS-LIST
                       8
                       (LOGIOR
                        (LOGAND 4088
                                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                        (ASH
                         (LOGHEAD
                          40
                          (LOGTAIL
                           12
                           (COMBINE-BYTES
                            (MV-NTH
                             1
                             (RB
                              (CREATE-CANONICAL-ADDRESS-LIST
                               8
                               (LOGIOR
                                (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                (LOGAND
                                 4088
                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                              :R X86)))))
                         12)))
                      :R X86)))))
                 (XW
                  :RIP 0
                  (LOGEXT
                   64
                   (COMBINE-BYTES
                    (MV-NTH 1
                            (RB (CREATE-CANONICAL-ADDRESS-LIST 8 (XR :RGF *RSP* X86))
                                :R X86))))
                  (XW
                   :UNDEF 0 (+ 46 (NFIX (XR :UNDEF 0 X86)))
                   (!FLGI
                    *CF*
                    (BOOL->BIT
                     (<
                      (LOGAND
                       4503598553628672
                       (COMBINE-BYTES
                        (MV-NTH
                         1
                         (RB
                          (CREATE-CANONICAL-ADDRESS-LIST
                           8
                           (LOGIOR
                            (LOGAND 4088
                                    (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                            (ASH
                             (LOGHEAD
                              40
                              (LOGTAIL
                               12
                               (COMBINE-BYTES
                                (MV-NTH
                                 1
                                 (RB
                                  (CREATE-CANONICAL-ADDRESS-LIST
                                   8
                                   (LOGIOR
                                    (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                    (LOGAND
                                     4088
                                     (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                  :R X86)))))
                             12)))
                          :R X86))))
                      (LOGAND
                       4503598553628672
                       (LOGIOR
                        (LOGAND
                         18442240475155922943
                         (COMBINE-BYTES
                          (MV-NTH
                           1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST
                             8
                             (LOGIOR
                              (LOGAND 4088
                                      (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                              (ASH
                               (LOGHEAD
                                40
                                (LOGTAIL
                                 12
                                 (COMBINE-BYTES
                                  (MV-NTH
                                   1
                                   (RB
                                    (CREATE-CANONICAL-ADDRESS-LIST
                                     8
                                     (LOGIOR
                                      (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                      (LOGAND
                                       4088
                                       (LOGHEAD
                                        28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                    :R X86)))))
                               12)))
                            :R X86))))
                        (LOGAND
                         4503598553628672
                         (COMBINE-BYTES
                          (MV-NTH
                           1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST
                             8
                             (LOGIOR
                              (LOGAND 4088
                                      (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                              (ASH
                               (LOGHEAD
                                40
                                (LOGTAIL
                                 12
                                 (COMBINE-BYTES
                                  (MV-NTH
                                   1
                                   (RB
                                    (CREATE-CANONICAL-ADDRESS-LIST
                                     8
                                     (LOGIOR
                                      (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                      (LOGAND
                                       4088
                                       (LOGHEAD
                                        28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                    :R X86)))))
                               12)))
                            :R X86))))))))
                    (!FLGI
                     *PF*
                     (PF-SPEC64
                      (LOGHEAD
                       64
                       (+
                        (LOGAND
                         4503598553628672
                         (LOGEXT
                          64
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST
                              8
                              (LOGIOR
                               (LOGAND 4088
                                       (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                               (ASH
                                (LOGHEAD
                                 40
                                 (LOGTAIL
                                  12
                                  (COMBINE-BYTES
                                   (MV-NTH
                                    1
                                    (RB
                                     (CREATE-CANONICAL-ADDRESS-LIST
                                      8
                                      (LOGIOR
                                       (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                       (LOGAND
                                        4088
                                        (LOGHEAD
                                         28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                     :R X86)))))
                                12)))
                             :R X86)))))
                        (-
                         (LOGAND
                          4503598553628672
                          (LOGIOR
                           (LOGAND
                            -4503598553628673
                            (LOGEXT
                             64
                             (COMBINE-BYTES
                              (MV-NTH
                               1
                               (RB
                                (CREATE-CANONICAL-ADDRESS-LIST
                                 8
                                 (LOGIOR
                                  (LOGAND
                                   4088
                                   (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                  (ASH
                                   (LOGHEAD
                                    40
                                    (LOGTAIL
                                     12
                                     (COMBINE-BYTES
                                      (MV-NTH
                                       1
                                       (RB
                                        (CREATE-CANONICAL-ADDRESS-LIST
                                         8
                                         (LOGIOR
                                          (LOGAND
                                           -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                          (LOGAND
                                           4088
                                           (LOGHEAD
                                            28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                        :R X86)))))
                                   12)))
                                :R X86)))))
                           (LOGAND
                            4503598553628672
                            (LOGEXT
                             64
                             (COMBINE-BYTES
                              (MV-NTH
                               1
                               (RB
                                (CREATE-CANONICAL-ADDRESS-LIST
                                 8
                                 (LOGIOR
                                  (LOGAND
                                   4088
                                   (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                  (ASH
                                   (LOGHEAD
                                    40
                                    (LOGTAIL
                                     12
                                     (COMBINE-BYTES
                                      (MV-NTH
                                       1
                                       (RB
                                        (CREATE-CANONICAL-ADDRESS-LIST
                                         8
                                         (LOGIOR
                                          (LOGAND
                                           -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                          (LOGAND
                                           4088
                                           (LOGHEAD
                                            28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                        :R X86)))))
                                   12)))
                                :R X86)))))))))))
                     (!FLGI
                      *AF*
                      (SUB-AF-SPEC64
                       (LOGAND
                        4503598553628672
                        (COMBINE-BYTES
                         (MV-NTH
                          1
                          (RB
                           (CREATE-CANONICAL-ADDRESS-LIST
                            8
                            (LOGIOR
                             (LOGAND 4088
                                     (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                             (ASH
                              (LOGHEAD
                               40
                               (LOGTAIL
                                12
                                (COMBINE-BYTES
                                 (MV-NTH
                                  1
                                  (RB
                                   (CREATE-CANONICAL-ADDRESS-LIST
                                    8
                                    (LOGIOR
                                     (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                     (LOGAND
                                      4088
                                      (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                   :R X86)))))
                              12)))
                           :R X86))))
                       (LOGAND
                        4503598553628672
                        (LOGIOR
                         (LOGAND
                          18442240475155922943
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST
                              8
                              (LOGIOR
                               (LOGAND 4088
                                       (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                               (ASH
                                (LOGHEAD
                                 40
                                 (LOGTAIL
                                  12
                                  (COMBINE-BYTES
                                   (MV-NTH
                                    1
                                    (RB
                                     (CREATE-CANONICAL-ADDRESS-LIST
                                      8
                                      (LOGIOR
                                       (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                       (LOGAND
                                        4088
                                        (LOGHEAD
                                         28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                     :R X86)))))
                                12)))
                             :R X86))))
                         (LOGAND
                          4503598553628672
                          (COMBINE-BYTES
                           (MV-NTH
                            1
                            (RB
                             (CREATE-CANONICAL-ADDRESS-LIST
                              8
                              (LOGIOR
                               (LOGAND 4088
                                       (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                               (ASH
                                (LOGHEAD
                                 40
                                 (LOGTAIL
                                  12
                                  (COMBINE-BYTES
                                   (MV-NTH
                                    1
                                    (RB
                                     (CREATE-CANONICAL-ADDRESS-LIST
                                      8
                                      (LOGIOR
                                       (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                       (LOGAND
                                        4088
                                        (LOGHEAD
                                         28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                     :R X86)))))
                                12)))
                             :R X86)))))))
                      (!FLGI
                       *ZF* 1
                       (!FLGI
                        *SF*
                        (SF-SPEC64
                         (LOGHEAD
                          64
                          (+
                           (LOGAND
                            4503598553628672
                            (LOGEXT
                             64
                             (COMBINE-BYTES
                              (MV-NTH
                               1
                               (RB
                                (CREATE-CANONICAL-ADDRESS-LIST
                                 8
                                 (LOGIOR
                                  (LOGAND
                                   4088
                                   (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                  (ASH
                                   (LOGHEAD
                                    40
                                    (LOGTAIL
                                     12
                                     (COMBINE-BYTES
                                      (MV-NTH
                                       1
                                       (RB
                                        (CREATE-CANONICAL-ADDRESS-LIST
                                         8
                                         (LOGIOR
                                          (LOGAND
                                           -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                          (LOGAND
                                           4088
                                           (LOGHEAD
                                            28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                        :R X86)))))
                                   12)))
                                :R X86)))))
                           (-
                            (LOGAND
                             4503598553628672
                             (LOGIOR
                              (LOGAND
                               -4503598553628673
                               (LOGEXT
                                64
                                (COMBINE-BYTES
                                 (MV-NTH
                                  1
                                  (RB
                                   (CREATE-CANONICAL-ADDRESS-LIST
                                    8
                                    (LOGIOR
                                     (LOGAND
                                      4088
                                      (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                     (ASH
                                      (LOGHEAD
                                       40
                                       (LOGTAIL
                                        12
                                        (COMBINE-BYTES
                                         (MV-NTH
                                          1
                                          (RB
                                           (CREATE-CANONICAL-ADDRESS-LIST
                                            8
                                            (LOGIOR
                                             (LOGAND
                                              -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                             (LOGAND
                                              4088
                                              (LOGHEAD
                                               28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                           :R X86)))))
                                      12)))
                                   :R X86)))))
                              (LOGAND
                               4503598553628672
                               (LOGEXT
                                64
                                (COMBINE-BYTES
                                 (MV-NTH
                                  1
                                  (RB
                                   (CREATE-CANONICAL-ADDRESS-LIST
                                    8
                                    (LOGIOR
                                     (LOGAND
                                      4088
                                      (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                     (ASH
                                      (LOGHEAD
                                       40
                                       (LOGTAIL
                                        12
                                        (COMBINE-BYTES
                                         (MV-NTH
                                          1
                                          (RB
                                           (CREATE-CANONICAL-ADDRESS-LIST
                                            8
                                            (LOGIOR
                                             (LOGAND
                                              -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                             (LOGAND
                                              4088
                                              (LOGHEAD
                                               28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                           :R X86)))))
                                      12)))
                                   :R X86)))))))))))
                        (!FLGI
                         *OF*
                         (OF-SPEC64
                          (+
                           (LOGAND
                            4503598553628672
                            (LOGEXT
                             64
                             (COMBINE-BYTES
                              (MV-NTH
                               1
                               (RB
                                (CREATE-CANONICAL-ADDRESS-LIST
                                 8
                                 (LOGIOR
                                  (LOGAND
                                   4088
                                   (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                  (ASH
                                   (LOGHEAD
                                    40
                                    (LOGTAIL
                                     12
                                     (COMBINE-BYTES
                                      (MV-NTH
                                       1
                                       (RB
                                        (CREATE-CANONICAL-ADDRESS-LIST
                                         8
                                         (LOGIOR
                                          (LOGAND
                                           -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                          (LOGAND
                                           4088
                                           (LOGHEAD
                                            28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                        :R X86)))))
                                   12)))
                                :R X86)))))
                           (-
                            (LOGAND
                             4503598553628672
                             (LOGIOR
                              (LOGAND
                               -4503598553628673
                               (LOGEXT
                                64
                                (COMBINE-BYTES
                                 (MV-NTH
                                  1
                                  (RB
                                   (CREATE-CANONICAL-ADDRESS-LIST
                                    8
                                    (LOGIOR
                                     (LOGAND
                                      4088
                                      (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                     (ASH
                                      (LOGHEAD
                                       40
                                       (LOGTAIL
                                        12
                                        (COMBINE-BYTES
                                         (MV-NTH
                                          1
                                          (RB
                                           (CREATE-CANONICAL-ADDRESS-LIST
                                            8
                                            (LOGIOR
                                             (LOGAND
                                              -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                             (LOGAND
                                              4088
                                              (LOGHEAD
                                               28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                           :R X86)))))
                                      12)))
                                   :R X86)))))
                              (LOGAND
                               4503598553628672
                               (LOGEXT
                                64
                                (COMBINE-BYTES
                                 (MV-NTH
                                  1
                                  (RB
                                   (CREATE-CANONICAL-ADDRESS-LIST
                                    8
                                    (LOGIOR
                                     (LOGAND
                                      4088
                                      (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                     (ASH
                                      (LOGHEAD
                                       40
                                       (LOGTAIL
                                        12
                                        (COMBINE-BYTES
                                         (MV-NTH
                                          1
                                          (RB
                                           (CREATE-CANONICAL-ADDRESS-LIST
                                            8
                                            (LOGIOR
                                             (LOGAND
                                              -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                             (LOGAND
                                              4088
                                              (LOGHEAD
                                               28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                           :R X86)))))
                                      12)))
                                   :R X86))))))))))
                         (MV-NTH
                          2
                          (RB
                           (CREATE-CANONICAL-ADDRESS-LIST 8 (XR :RGF *RSP* X86))
                           :R
                           (MV-NTH
                            2
                            (LAS-TO-PAS
                             (CREATE-CANONICAL-ADDRESS-LIST
                              40 (+ 206 (XR :RIP 0 X86)))
                             :X 0
                             (MV-NTH
                              2
                              (LAS-TO-PAS
                               (CREATE-CANONICAL-ADDRESS-LIST
                                15 (+ 190 (XR :RIP 0 X86)))
                               :X 0
                               (MV-NTH
                                1
                                (WB
                                 (CREATE-ADDR-BYTES-ALIST
                                  (CREATE-CANONICAL-ADDRESS-LIST
                                   8
                                   (LOGIOR
                                    (LOGAND
                                     4088
                                     (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                    (ASH
                                     (LOGHEAD
                                      40
                                      (LOGTAIL
                                       12
                                       (COMBINE-BYTES
                                        (MV-NTH
                                         1
                                         (RB
                                          (CREATE-CANONICAL-ADDRESS-LIST
                                           8
                                           (LOGIOR
                                            (LOGAND
                                             -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                            (LOGAND
                                             4088
                                             (LOGHEAD
                                              28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                          :R X86)))))
                                     12)))
                                  (BYTE-IFY
                                   8
                                   (LOGIOR
                                    (LOGAND
                                     18442240475155922943
                                     (COMBINE-BYTES
                                      (MV-NTH
                                       1
                                       (RB
                                        (CREATE-CANONICAL-ADDRESS-LIST
                                         8
                                         (LOGIOR
                                          (LOGAND
                                           4088
                                           (LOGHEAD
                                            32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                          (ASH
                                           (LOGHEAD
                                            40
                                            (LOGTAIL
                                             12
                                             (COMBINE-BYTES
                                              (MV-NTH
                                               1
                                               (RB
                                                (CREATE-CANONICAL-ADDRESS-LIST
                                                 8
                                                 (LOGIOR
                                                  (LOGAND
                                                   -4096
                                                   (LOGEXT 64 (XR :CTR *CR3* X86)))
                                                  (LOGAND
                                                   4088
                                                   (LOGHEAD
                                                    28
                                                    (LOGTAIL
                                                     36 (XR :RGF *RSI* X86))))))
                                                :R X86)))))
                                           12)))
                                        :R X86))))
                                    (LOGAND
                                     4503598553628672
                                     (COMBINE-BYTES
                                      (MV-NTH
                                       1
                                       (RB
                                        (CREATE-CANONICAL-ADDRESS-LIST
                                         8
                                         (LOGIOR
                                          (LOGAND
                                           4088
                                           (LOGHEAD
                                            32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                                          (ASH
                                           (LOGHEAD
                                            40
                                            (LOGTAIL
                                             12
                                             (COMBINE-BYTES
                                              (MV-NTH
                                               1
                                               (RB
                                                (CREATE-CANONICAL-ADDRESS-LIST
                                                 8
                                                 (LOGIOR
                                                  (LOGAND
                                                   -4096
                                                   (LOGEXT 64 (XR :CTR *CR3* X86)))
                                                  (LOGAND
                                                   4088
                                                   (LOGHEAD
                                                    28
                                                    (LOGTAIL
                                                     36 (XR :RGF *RDI* X86))))))
                                                :R X86)))))
                                           12)))
                                        :R X86)))))))
                                 (MV-NTH
                                  2
                                  (LAS-TO-PAS
                                   (CREATE-CANONICAL-ADDRESS-LIST
                                    6 (+ 184 (XR :RIP 0 X86)))
                                   :X 0
                                   (MV-NTH
                                    2
                                    (RB
                                     (CREATE-CANONICAL-ADDRESS-LIST
                                      8
                                      (LOGIOR
                                       (LOGAND
                                        4088
                                        (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                                       (ASH
                                        (LOGHEAD
                                         40
                                         (LOGTAIL
                                          12
                                          (COMBINE-BYTES
                                           (MV-NTH
                                            1
                                            (RB
                                             (CREATE-CANONICAL-ADDRESS-LIST
                                              8
                                              (LOGIOR
                                               (LOGAND
                                                -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                               (LOGAND
                                                4088
                                                (LOGHEAD
                                                 28
                                                 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                             :R X86)))))
                                        12)))
                                     :R
                                     (MV-NTH
                                      2
                                      (LAS-TO-PAS
                                       (CREATE-CANONICAL-ADDRESS-LIST
                                        40 (+ 144 (XR :RIP 0 X86)))
                                       :X 0
                                       (MV-NTH
                                        2
                                        (LAS-TO-PAS
                                         (CREATE-CANONICAL-ADDRESS-LIST
                                          3 (+ 140 (XR :RIP 0 X86)))
                                         :X 0
                                         (MV-NTH
                                          2
                                          (RB
                                           (CREATE-CANONICAL-ADDRESS-LIST
                                            8
                                            (LOGIOR
                                             (LOGAND
                                              -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                             (LOGAND
                                              4088
                                              (LOGHEAD
                                               28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                           :R
                                           (MV-NTH
                                            2
                                            (LAS-TO-PAS
                                             (CREATE-CANONICAL-ADDRESS-LIST
                                              32 (+ 108 (XR :RIP 0 X86)))
                                             :X 0
                                             (MV-NTH
                                              2
                                              (LAS-TO-PAS
                                               (CREATE-CANONICAL-ADDRESS-LIST
                                                18 (+ 86 (XR :RIP 0 X86)))
                                               :X 0
                                               (MV-NTH
                                                2
                                                (RB
                                                 (CREATE-CANONICAL-ADDRESS-LIST
                                                  8
                                                  (LOGIOR
                                                   (LOGAND
                                                    4088
                                                    (LOGHEAD
                                                     32
                                                     (LOGTAIL
                                                      27 (XR :RGF *RDI* X86))))
                                                   (ASH
                                                    (LOGHEAD
                                                     40
                                                     (LOGTAIL
                                                      12
                                                      (COMBINE-BYTES
                                                       (MV-NTH
                                                        1
                                                        (RB
                                                         (CREATE-CANONICAL-ADDRESS-LIST
                                                          8
                                                          (LOGIOR
                                                           (LOGAND
                                                            -4096
                                                            (LOGEXT
                                                             64 (XR :CTR *CR3* X86)))
                                                           (LOGAND
                                                            4088
                                                            (LOGHEAD
                                                             28
                                                             (LOGTAIL
                                                              36
                                                              (XR :RGF *RDI* X86))))))
                                                         :R X86)))))
                                                    12)))
                                                 :R
                                                 (MV-NTH
                                                  2
                                                  (LAS-TO-PAS
                                                   (CREATE-CANONICAL-ADDRESS-LIST
                                                    40 (+ 46 (XR :RIP 0 X86)))
                                                   :X 0
                                                   (MV-NTH
                                                    2
                                                    (LAS-TO-PAS
                                                     (CREATE-CANONICAL-ADDRESS-LIST
                                                      4 (+ 38 (XR :RIP 0 X86)))
                                                     :X 0
                                                     (MV-NTH
                                                      2
                                                      (RB
                                                       (CREATE-CANONICAL-ADDRESS-LIST
                                                        8
                                                        (LOGIOR
                                                         (LOGAND
                                                          -4096
                                                          (LOGEXT
                                                           64 (XR :CTR *CR3* X86)))
                                                         (LOGAND
                                                          4088
                                                          (LOGHEAD
                                                           28
                                                           (LOGTAIL
                                                            36
                                                            (XR :RGF *RDI* X86))))))
                                                       :R
                                                       (MV-NTH
                                                        2
                                                        (LAS-TO-PAS
                                                         (CREATE-CANONICAL-ADDRESS-LIST
                                                          25 (+ 13 (XR :RIP 0 X86)))
                                                         :X 0
                                                         (MV-NTH
                                                          2
                                                          (LAS-TO-PAS
                                                           (CREATE-CANONICAL-ADDRESS-LIST
                                                            8
                                                            (+
                                                             -24 (XR :RGF *RSP* X86)))
                                                           :R 0
                                                           (MV-NTH
                                                            2
                                                            (LAS-TO-PAS
                                                             (CREATE-CANONICAL-ADDRESS-LIST
                                                              5 (+ 8 (XR :RIP 0 X86)))
                                                             :X 0
                                                             (MV-NTH
                                                              1
                                                              (WB
                                                               (CREATE-ADDR-BYTES-ALIST
                                                                (CREATE-CANONICAL-ADDRESS-LIST
                                                                 8
                                                                 (+
                                                                  -24
                                                                  (XR
                                                                   :RGF *RSP* X86)))
                                                                (BYTE-IFY
                                                                 8
                                                                 (XR :CTR *CR3* X86)))
                                                               (MV-NTH
                                                                2
                                                                (LAS-TO-PAS
                                                                 (CREATE-CANONICAL-ADDRESS-LIST
                                                                  8 (XR :RIP 0 X86))
                                                                 :X 0
                                                                 X86))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

 :hints (("Goal"
          :in-theory (e/d* (len
                            page-size
                            consp-of-create-canonical-address-list
                            car-create-canonical-address-list
                            cdr-create-canonical-address-list
                            loghead-negative
                            disjoint-p-all-translation-governing-addresses-subset-p)
                           (create-canonical-address-list
                            (:rewrite program-at-values-and-!flgi)
                            (:rewrite get-prefixes-opener-lemma-group-4-prefix-in-marking-mode)
                            (:rewrite rb-in-terms-of-rb-subset-p-in-system-level-mode)
                            (:rewrite get-prefixes-opener-lemma-group-3-prefix-in-marking-mode)
                            (:rewrite get-prefixes-opener-lemma-group-2-prefix-in-marking-mode)
                            (:rewrite get-prefixes-opener-lemma-group-1-prefix-in-marking-mode)
                            ;; !!! Maybe I can afford to enable the following rule now?
                            (:rewrite mv-nth-2-rb-in-system-level-marking-mode)
                            (:rewrite mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)
                            (:rewrite mv-nth-2-rb-in-system-level-non-marking-mode)
                            (:rewrite rb-returns-x86-programmer-level-mode)
                            (:linear rm-low-64-logand-logior-helper-1)
                            (:definition n64p$inline)
                            (:type-prescription xlate-equiv-memory)
                            (:rewrite program-at-alt-wb-disjoint-in-system-level-mode)
                            (:type-prescription natp-page-dir-ptr-table-entry-addr)
                            mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                            mv-nth-2-las-to-pas-system-level-non-marking-mode
                            ;; (:REWRITE R/X-IS-IRRELEVANT-FOR-MV-NTH-2-LAS-TO-PAS-WHEN-NO-ERRORS)
                            ;; (:REWRITE XR-FAULT-AND-GET-PREFIXES-ALT)
                            ;; (:REWRITE XR-MS-MV-NTH-2-GET-PREFIXES-ALT)
                            ;; (:TYPE-PRESCRIPTION N01P-PAGE-SIZE)
                            ;; (:TYPE-PRESCRIPTION MEMBER-P-PHYSICAL-ADDRESS-P-PHYSICAL-ADDRESS-LISTP)
                            ;; (:REWRITE CDR-OF-APPEND-WHEN-CONSP)
                            ;; (:REWRITE CAR-OF-APPEND)
                            ;; (:TYPE-PRESCRIPTION MEMBER-P-PHYSICAL-ADDRESS-P)
                            ;; (:REWRITE
                            ;;  INT-LISTS-IN-SEQ-P-AND-APPEND-WITH-CREATE-CANONICAL-ADDRESS-LIST-2)
                            ;; (:REWRITE CONSP-OF-APPEND)
                            ;; (:REWRITE GET-PREFIXES-OPENER-LEMMA-NO-PREFIX-BYTE)
                            ;; (:REWRITE X86P-GET-PREFIXES)
                            ;; (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV)
                            ;; (:TYPE-PRESCRIPTION APPEND)
                            ;; (:REWRITE INT-LISTS-IN-SEQ-P-AND-APPEND)
                            ;; (:REWRITE XR-RB-STATE-IN-PROGRAMMER-LEVEL-MODE)
                            ;; (:REWRITE MV-NTH-0-GET-PREFIXES-XW-RGF)
                            ;; (:REWRITE RIGHT-CANCELLATION-FOR-+)
                            ;; (:REWRITE RM08-XW-SYSTEM-MODE)
                            ;; (:REWRITE RM08-XW-PROGRAMMER-LEVEL-MODE)
                            ;; (:REWRITE PROGRAMMER-LEVEL-MODE-RM08-NO-ERROR)
                            ;; (:REWRITE
                            ;;  GET-PREFIXES-DOES-NOT-MODIFY-X86-STATE-IN-SYSTEM-LEVEL-NON-MARKING-MODE)
                            ;; (:REWRITE GET-PREFIXES-DOES-NOT-MODIFY-X86-STATE-IN-PROGRAMMER-LEVEL-MODE)
                            ;; (:REWRITE MV-NTH-2-GET-PREFIXES-XW-RGF)
                            ;; (:REWRITE MV-NTH-1-GET-PREFIXES-XW-RGF)
                            ;; (:REWRITE LAS-TO-PAS-AFTER-MV-NTH-2-RB)
                            ;; (:TYPE-PRESCRIPTION NATP-GET-PREFIXES)
                            ;; (:REWRITE RM08-VALUE-WHEN-ERROR)
                            ;; (:DEFINITION NOT)
                            ;; (:TYPE-PRESCRIPTION X86-DECODE-SIB-P)
                            ;; (:REWRITE XLATE-EQUIV-MEMORY-AND-TWO-GET-PREFIXES-VALUES)
                            ;; (:REWRITE XLATE-EQUIV-MEMORY-AND-MV-NTH-1-RM08)
                            ;; (:REWRITE BITOPS::LOGTAIL-OF-LOGTAIL)
                            ;; (:REWRITE APPEND-SINGLETON-UNDER-SET-EQUIV)
                            ;; (:REWRITE !FLGI-UNDEFINED-AND-XW)
                            ))
          :do-not '(preprocess)
          :do-not-induct t)))

;; (def-gl-thm test-mapped-address
;;   ;; Map the destination PDPTE to contain the same value (not
;;   ;; permissions) as that in the source PDPTE.
;;   :hyp (and (unsigned-byte-p 64 source-entry)
;;             (unsigned-byte-p 64 destination-entry))
;;   ;; pointer comes from the byte-list of wb in the following s-expr.
;;   :concl (let* ((pointer (logior
;;                           (logand     4503598553628672 source-entry)
;;                           (logand 18442240475155922943 destination-entry))))
;;            (equal (ash (part-select source-entry :low 30 :width 22) 30)
;;                   (ash (part-select      pointer :low 30 :width 22) 30)))
;;   :g-bindings
;;   (gl::auto-bindings (:mix (:nat source-entry 64) (:nat destination-entry 64))))

(i-am-here)

;; ======================================================================


(encapsulate
  ()

  (def-gl-export rb-and-rm-low-64-for-direct-map-helper
    :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
              (n08p e) (n08p f) (n08p g) (n08p h))
    :concl (equal (logior a (ash b 8)
                          (ash (logior c (ash d 8)) 16)
                          (ash (logior e (ash (logior f (ash (logior g (ash h 8)) 8)) 8)) 32))
                  (logior a
                          (ash (logior b
                                       (ash (logior c
                                                    (ash
                                                     (logior d
                                                             (ash
                                                              (logior
                                                               e
                                                               (ash
                                                                (logior
                                                                 f
                                                                 (ash (logior g (ash h 8)) 8))
                                                                8)) 8)) 8)) 8)) 8)))
    :g-bindings
    (gl::auto-bindings
     (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
           (:nat e 8) (:nat f 8) (:nat g 8) (:nat h 8))))

  (defthm rb-and-rm-low-64-for-direct-map
    (implies (and
              (equal
               (mv-nth
                1
                (las-to-pas
                 (create-canonical-address-list 8 direct-mapped-addr)
                 r-w-x (cpl x86) x86))
               (addr-range 8 direct-mapped-addr))
              (not (page-structure-marking-mode x86))
              (not (programmer-level-mode x86))
              (x86p x86))
             (equal (combine-bytes
                     (mv-nth
                      1
                      (rb (create-canonical-address-list 8 direct-mapped-addr) r-w-x x86)))
                    (rm-low-64 direct-mapped-addr x86)))
    :hints (("Goal" :in-theory (e/d* (rb
                                      rm-low-64
                                      rm-low-32
                                      read-from-physical-memory
                                      rb-and-rm-low-64-for-direct-map-helper)
                                     ()))))

  (in-theory (e/d () (rb-and-rm-low-64-for-direct-map-helper))))

(defthm ia32e-la-to-pa-page-dir-ptr-table-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
  (b* ((p-addrs (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr base-addr)))
       (page-dir-ptr-table-entry (combine-bytes
                                  (mv-nth 1
                                          (rb
                                           (create-canonical-address-list
                                            8
                                            (page-dir-ptr-table-entry-addr lin-addr base-addr))
                                           :r x86))))
       (value (combine-bytes bytes)))
    (implies (and
              ;; page-dir-ptr-table-entry-addr is directly mapped.
              (equal
               (mv-nth
                1
                (las-to-pas
                 (create-canonical-address-list 8 (page-dir-ptr-table-entry-addr lin-addr base-addr))
                 :r (cpl x86) x86))
               p-addrs)
              (not (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x cpl x86)))
              (equal (page-present page-dir-ptr-table-entry)
                     (page-present value))
              (equal (page-read-write page-dir-ptr-table-entry)
                     (page-read-write value))
              (equal (page-user-supervisor page-dir-ptr-table-entry)
                     (page-user-supervisor value))
              (equal (page-execute-disable page-dir-ptr-table-entry)
                     (page-execute-disable value))
              (equal (page-size page-dir-ptr-table-entry)
                     (page-size value))
              ;; 1 G pages
              (equal (page-size page-dir-ptr-table-entry) 1)
              (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
                     (part-select value :low 13 :high 29))
              (equal (len bytes) (len p-addrs))
              (byte-listp bytes)
              (canonical-address-p lin-addr)
              (physical-address-p base-addr)
              (equal (loghead 12 base-addr) 0)
              (not (page-structure-marking-mode x86))
              (not (programmer-level-mode x86))
              (x86p x86))
             ;; ia32e-la-to-pa-page-dir-ptr-table returns the physical
             ;; address corresponding to "lin-addr" after the PDPTE
             ;; corresponding to this "lin-addr" has been modified ---
             ;; the new PDPTE is "value".
             (and (equal
                   (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x cpl
                              (write-to-physical-memory p-addrs bytes x86)))
                   nil)
                  (equal (mv-nth 1 (ia32e-la-to-pa-page-dir-ptr-table
                                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl
                                    (write-to-physical-memory p-addrs bytes x86)))
                         (logior (loghead 30 lin-addr)
                                 (ash (loghead 22 (logtail 30 value)) 30))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-dir-ptr-table)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-pml4-table-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
  (b* ((pml4-table-entry-addr (pml4-table-entry-addr lin-addr base-addr))
       (pml4-table-entry (combine-bytes
                          (mv-nth 1 (rb (create-canonical-address-list 8 pml4-table-entry-addr) :r x86))))
       (pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
       (page-dir-ptr-table-entry-addr (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
       (page-dir-ptr-table-entry
        (combine-bytes
         (mv-nth 1 (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr) :r x86))))
       (p-addrs (addr-range 8 page-dir-ptr-table-entry-addr))
       (value (combine-bytes bytes)))
    (implies (and
              ;; PML4E and PDPTE are direct mapped.
              (equal
               (mv-nth
                1
                (las-to-pas
                 (create-canonical-address-list 8 pml4-table-entry-addr)
                 :r (cpl x86) x86))
               (addr-range 8 pml4-table-entry-addr))
              (equal
               (mv-nth
                1
                (las-to-pas
                 (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
                 :r (cpl x86) x86))
               p-addrs)
              (disjoint-p (addr-range 8 pml4-table-entry-addr)
                          (addr-range 8 page-dir-ptr-table-entry-addr))
              (not (mv-nth 0 (ia32e-la-to-pa-pml4-table lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86)))

              (equal (page-present page-dir-ptr-table-entry)
                     (page-present value))
              (equal (page-read-write page-dir-ptr-table-entry)
                     (page-read-write value))
              (equal (page-user-supervisor page-dir-ptr-table-entry)
                     (page-user-supervisor value))
              (equal (page-execute-disable page-dir-ptr-table-entry)
                     (page-execute-disable value))
              (equal (page-size page-dir-ptr-table-entry)
                     (page-size value))
              ;; 1 G pages
              (equal (page-size page-dir-ptr-table-entry) 1)
              (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
                     (part-select value :low 13 :high 29))
              (equal (len bytes) (len p-addrs))
              (byte-listp bytes)
              (canonical-address-p lin-addr)
              (physical-address-p base-addr)
              (equal (loghead 12 base-addr) 0)
              (not (programmer-level-mode x86))
              (not (page-structure-marking-mode x86))
              (x86p x86))
             ;; ia32e-la-to-pa-pml4-table returns the physical address
             ;; corresponding to "lin-addr" after the PDPTE
             ;; corresponding to this "lin-addr" has been modified ---
             ;; the new PDPTE is "value".
             (and (equal
                   (mv-nth 0 (ia32e-la-to-pa-pml4-table
                              lin-addr base-addr wp smep smap ac nxe r-w-x cpl
                              (write-to-physical-memory p-addrs bytes x86)))
                   nil)
                  (equal (mv-nth 1 (ia32e-la-to-pa-pml4-table
                                    lin-addr base-addr wp smep smap ac nxe r-w-x cpl
                                    (write-to-physical-memory p-addrs bytes x86)))
                         (logior (loghead 30 lin-addr)
                                 (ash (loghead 22 (logtail 30 value)) 30))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-pml4-table)
                            (page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
  (b* ((pml4-table-base-addr (pml4-table-base-addr x86))
       (pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
       (pml4-table-entry
        (combine-bytes
         (mv-nth 1 (rb (create-canonical-address-list 8 pml4-table-entry-addr) :r x86))))
       (pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
       (page-dir-ptr-table-entry-addr (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
       (page-dir-ptr-table-entry
        (combine-bytes
         (mv-nth 1 (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr) :r x86))))
       (p-addrs (addr-range 8 page-dir-ptr-table-entry-addr))
       (value (combine-bytes bytes)))
    (implies (and
              ;; PML4E and PDPTE are direct mapped.
              (equal
               (mv-nth
                1
                (las-to-pas
                 (create-canonical-address-list 8 pml4-table-entry-addr)
                 :r (cpl x86) x86))
               (addr-range 8 pml4-table-entry-addr))
              (equal
               (mv-nth
                1
                (las-to-pas
                 (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
                 :r (cpl x86) x86))
               p-addrs)
              (disjoint-p (addr-range 8 pml4-table-entry-addr)
                          (addr-range 8 page-dir-ptr-table-entry-addr))
              (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
              (equal (page-present page-dir-ptr-table-entry)
                     (page-present value))
              (equal (page-read-write page-dir-ptr-table-entry)
                     (page-read-write value))
              (equal (page-user-supervisor page-dir-ptr-table-entry)
                     (page-user-supervisor value))
              (equal (page-execute-disable page-dir-ptr-table-entry)
                     (page-execute-disable value))
              (equal (page-size page-dir-ptr-table-entry)
                     (page-size value))
              ;; 1 G pages
              (equal (page-size page-dir-ptr-table-entry) 1)
              (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
                     (part-select value :low 13 :high 29))
              (equal (len bytes) (len p-addrs))
              (byte-listp bytes)
              (canonical-address-p lin-addr)
              (not (programmer-level-mode x86))
              (not (page-structure-marking-mode x86))
              (x86p x86))
             ;; ia32e-la-to-pa returns the physical address
             ;; corresponding to "lin-addr" after the PDPTE
             ;; corresponding to this "lin-addr" has been modified ---
             ;; the new PDPTE is "value".
             (and
              (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (write-to-physical-memory p-addrs bytes x86)))
                     nil)
              (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (write-to-physical-memory p-addrs bytes x86)))
                     (logior (loghead 30 lin-addr) (ash (loghead 22 (logtail 30 value)) 30))))))
  :hints (("Goal"
           :use ((:instance
                  ia32e-la-to-pa-pml4-table-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
                  (base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
                  (wp (cr0-slice :cr0-wp (n32 (ctri *cr0* x86))))
                  (smep (loghead 1 (bool->bit (logbitp 20 (xr :ctr *cr4* x86)))))
                  (smap 0)
                  (ac (bool->bit (logbitp 18 (xr :rflags 0 x86))))
                  (nxe (loghead 1 (bool->bit (logbitp 11 (xr :msr *ia32_efer-idx* x86)))))
                  (r-w-x r-w-x)
                  (cpl cpl)
                  (x86 x86)))
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa)
                            (ia32e-la-to-pa-pml4-table-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             not
                             force (force))))))

(defthm ia32e-la-to-pa-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr
  (implies
   (and
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pml4-table-entry
           (combine-bytes
            (mv-nth 1 (rb (create-canonical-address-list 8 pml4-table-entry-addr) :r x86))))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (combine-bytes
            (mv-nth 1 (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr) :r x86))))
    ;; PML4E and PDPTE are direct mapped.
    (equal
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 pml4-table-entry-addr)
       :r (cpl x86) x86))
     (addr-range 8 pml4-table-entry-addr))
    (equal
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r (cpl x86) x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86))
           (addr-range 8 page-dir-ptr-table-entry-addr))
    (disjoint-p
     (addr-range 8 (pml4-table-entry-addr lin-addr pml4-table-base-addr))
     (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)))
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
    (equal (page-present page-dir-ptr-table-entry)
           (page-present (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-read-write page-dir-ptr-table-entry)
           (page-read-write (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
           (page-user-supervisor (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-execute-disable page-dir-ptr-table-entry)
           (page-execute-disable (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry)
           (page-size (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
           (part-select (combine-bytes (strip-cdrs addr-lst)) :low 13 :high 29))
    (addr-byte-alistp addr-lst)
    (equal (len addr-lst) 8)
    (canonical-address-p lin-addr)
    (not (programmer-level-mode x86))
    (not (page-structure-marking-mode x86))
    (x86p x86))
   ;; ia32e-la-to-pa returns the physical address
   ;; corresponding to "lin-addr" after the PDPTE
   ;; corresponding to this "lin-addr" has been modified ---
   ;; the new PDPTE is "value".
   (and
    (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
           nil)
    (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
           (logior (loghead 30 lin-addr) (ash (loghead
                                               22
                                               (logtail 30 (combine-bytes (strip-cdrs addr-lst)))) 30)))))
  :hints (("Goal"
           :use ((:instance ia32e-la-to-pa-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
                            (bytes (strip-cdrs addr-lst))))
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             wb)
                            (ia32e-la-to-pa-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
                             member-p-strip-cars-of-remove-duplicate-keys
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             not
                             force (force))))))

(def-gl-export same-pml4-table-entry-addr-for-n-+-lin-addrs
  :hyp (and (physical-address-p pml4-table-base-addr)
            (canonical-address-p lin-addr)
            (unsigned-byte-p 30 n)
            ;; 1G aligned linear address
            (equal (loghead 30 lin-addr) 0))
  :concl (equal (pml4-table-entry-addr (+ n lin-addr) pml4-table-base-addr)
                (pml4-table-entry-addr lin-addr pml4-table-base-addr))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat pml4-table-base-addr 64) (:nat lin-addr 64) (:nat n 64))))

(def-gl-export same-pdp-table-entry-addr-for-n-+-lin-addrs
  :hyp (and (unsigned-byte-p 30 n)
            (physical-address-p pdpt-base-addr)
            (canonical-address-p lin-addr)
            ;; 1G aligned linear address
            (equal (loghead 30 lin-addr) 0))
  :concl (equal (page-dir-ptr-table-entry-addr
                 (+ n lin-addr) pdpt-base-addr)
                (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat pdpt-base-addr 64) (:nat lin-addr 64) (:nat n 64))))

(def-gl-export loghead-30-of-1G-aligned-lin-addr-+-n-1
  :hyp (and (canonical-address-p lin-addr)
            (canonical-address-p (+ n lin-addr))
            (equal (loghead 30 lin-addr) 0)
            (unsigned-byte-p 30 n))
  :concl (equal (loghead 30 (+ n lin-addr)) n)
  :g-bindings (gl::auto-bindings (:mix (:nat lin-addr 64) (:nat n 64))))

(def-gl-export loghead-30-of-1G-aligned-lin-addr-+-n-2
  :hyp (and (equal (loghead 30 (+ n lin-addr)) n)
            (canonical-address-p (+ n lin-addr))
            (canonical-address-p lin-addr)
            (unsigned-byte-p 30 n))
  :concl (equal (loghead 30 lin-addr) 0)
  :g-bindings (gl::auto-bindings (:mix (:nat lin-addr 64) (:nat n 64))))

(def-gl-export logior-to-+-for-ash-x-30
  :hyp (and (unsigned-byte-p 22 x)
            (unsigned-byte-p 30 n))
  :concl (equal (logior n (ash x 30)) (+ n (ash x 30)))
  :g-bindings
  (gl::auto-bindings (:mix (:nat n 64) (:nat x 64))))

(defthm mv-nth-0-ia32e-la-to-pa-page-dir-ptr-table-for-same-1G-page
  (implies
   (and
    (equal page-dir-ptr-table-entry-addr (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (combine-bytes
            (mv-nth 1 (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr) :r x86))))
    ;; PDPTE is direct mapped.
    (equal
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r (cpl x86) x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr pdpt-base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    ;; (equal (loghead 30 lin-addr) 0)
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (physical-address-p pdpt-base-addr)
    (equal (loghead 12 pdpt-base-addr) 0)
    (not (page-structure-marking-mode x86))
    (x86p x86))
   (equal (mv-nth 0
                  (ia32e-la-to-pa-page-dir-ptr-table
                   (+ n lin-addr) pdpt-base-addr u/s-acc r/w-acc x/d-acc
                   wp smep smap ac nxe r-w-x cpl x86))
          nil))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table)
                                   (commutativity-of-+
                                    not
                                    page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                                    page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                                    bitops::logand-with-negated-bitmask)))))

(defthm mv-nth-0-ia32e-la-to-pa-pml4-table-for-same-1G-page
  (implies
   (and
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pml4-table-entry
           (combine-bytes
            (mv-nth 1 (rb (create-canonical-address-list 8 pml4-table-entry-addr) :r x86))))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (combine-bytes
            (mv-nth 1 (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr) :r x86))))
    ;; PML4E and PDPTE are direct mapped.
    (equal
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 pml4-table-entry-addr)
       :r (cpl x86) x86))
     (addr-range 8 pml4-table-entry-addr))
    (equal
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r (cpl x86) x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-table-base-addr
                    wp smep smap ac nxe r-w-x cpl x86)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    ;; (equal (loghead 30 lin-addr) 0)
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (physical-address-p pml4-table-base-addr)
    (equal (loghead 12 pml4-table-base-addr) 0)
    (not (page-structure-marking-mode x86))
    (x86p x86))
   (equal (mv-nth 0
                  (ia32e-la-to-pa-pml4-table
                   (+ n lin-addr) pml4-table-base-addr
                   wp smep smap ac nxe r-w-x cpl x86))
          nil))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-pml4-table)
                            (commutativity-of-+
                             not
                             pml4-table-entry-addr-to-c-program-optimized-form
                             pml4-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask)))))

(defthm mv-nth-0-ia32e-la-to-pa-for-same-1G-page
  (implies
   (and
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pml4-table-entry
           (combine-bytes
            (mv-nth 1
                    (rb (create-canonical-address-list 8 pml4-table-entry-addr)
                        :r x86))))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (combine-bytes
            (mv-nth 1 (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr) :r x86))))
    (equal
     (mv-nth 1 (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr) :r (cpl x86) x86))
     (addr-range 8 pml4-table-entry-addr))
    (equal
     (mv-nth 1
             (las-to-pas
              (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
              :r (cpl x86) x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (not (page-structure-marking-mode x86))
    (x86p x86))
   (equal (mv-nth 0 (ia32e-la-to-pa (+ n lin-addr) r-w-x cpl x86))
          nil))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa)
                            (commutativity-of-+
                             not
                             pml4-table-entry-addr-to-c-program-optimized-form
                             pml4-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask)))))

(define create-canonical-address-list-alt (iteration count lin-addr)
  :enabled t
  :measure (nfix (- count iteration))
  :guard (and (natp count)
              (natp iteration)
              (<= iteration count)
              (integerp lin-addr))
  :long "An alternative way of creating canonical address lists, this
  function also gives a different induction scheme that may be
  preferable to the one suggested by @(see
  create-canonical-address-list)"
  (if (zp (- count iteration))
      nil
    (if (canonical-address-p (+ iteration lin-addr))
        (cons
         (+ iteration lin-addr)
         (create-canonical-address-list-alt (+ 1 iteration) count lin-addr))
      nil))
  ///
  (defthmd create-canonical-address-list-alt-is-create-canonical-address-list
    (equal (create-canonical-address-list-alt iteration count lin-addr)
           (create-canonical-address-list (- count iteration) (+ iteration lin-addr)))))

(def-gl-export open-mv-nth-0-las-to-pas-for-same-1G-page-general-1
  :hyp (and (< iteration m)
            (canonical-address-p lin-addr)
            (canonical-address-p (+ -1 lin-addr m))
            (integerp m)
            (<= m 1073741824)
            (natp iteration)
            (equal (loghead 30 lin-addr) 0))
  :concl (equal (loghead 30 (+ iteration lin-addr)) iteration)
  :g-bindings (gl::auto-bindings (:mix (:nat lin-addr 64) (:nat iteration 64) (:nat m 64))))

(def-gl-export open-mv-nth-0-las-to-pas-for-same-1G-page-general-2
  :hyp (and (< iteration m)
            (integerp m)
            (<= m 1073741824)
            (natp iteration))
  :concl (unsigned-byte-p 30 iteration)
  :g-bindings (gl::auto-bindings (:mix (:nat iteration 64) (:nat m 64))))

(defthmd open-mv-nth-0-las-to-pas-for-same-1G-page-general
  (implies
   (and
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pml4-table-entry
           (combine-bytes
            (mv-nth 1 (rb (create-canonical-address-list 8 pml4-table-entry-addr) :r x86))))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (combine-bytes
            (mv-nth
             1
             (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
                 :r x86))))
    (equal
     (mv-nth
      1
      (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
                  :r (cpl x86) x86))
     (addr-range 8 pml4-table-entry-addr))
    (equal
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r (cpl x86) x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
    (canonical-address-p lin-addr)
    (natp m)
    (<= m *2^30*)
    (natp iteration)
    (equal (loghead 30 lin-addr) 0)
    (not (page-structure-marking-mode x86))
    (x86p x86))
   (equal (mv-nth 0 (las-to-pas
                     (create-canonical-address-list-alt iteration m lin-addr)
                     r-w-x cpl x86))
          nil))
  :hints (("Goal"
           :induct (create-canonical-address-list-alt iteration m lin-addr)
           :in-theory (e/d* (las-to-pas
                             mv-nth-0-ia32e-la-to-pa-for-same-1G-page
                             open-mv-nth-0-las-to-pas-for-same-1G-page-general-1
                             open-mv-nth-0-las-to-pas-for-same-1G-page-general-2
                             ;; open-mv-nth-0-las-to-pas
                             )
                            (not
                             pml4-table-base-addr
                             pml4-table-entry-addr
                             page-dir-ptr-table-entry-addr
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl)))))

(defthm open-mv-nth-0-las-to-pas-for-same-1G-page
  (implies
   (and
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pml4-table-entry
           (combine-bytes
            (mv-nth 1 (rb (create-canonical-address-list 8 pml4-table-entry-addr) :r x86))))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (combine-bytes
            (mv-nth
             1
             (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
                 :r x86))))
    (equal
     (mv-nth
      1
      (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
                  :r (cpl x86) x86))
     (addr-range 8 pml4-table-entry-addr))
    (equal
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r (cpl x86) x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
    (canonical-address-p lin-addr)
    (equal (loghead 30 lin-addr) 0)
    (not (page-structure-marking-mode x86))
    (x86p x86))
   (equal (mv-nth 0 (las-to-pas (create-canonical-address-list *2^30* lin-addr)
                                r-w-x cpl x86))
          nil))
  :hints (("Goal"
           :use ((:instance open-mv-nth-0-las-to-pas-for-same-1G-page-general
                            (iteration 0)
                            (m *2^30*)))
           :in-theory (e/d* (create-canonical-address-list-alt-is-create-canonical-address-list)
                            (las-to-pas
                             ;; open-mv-nth-0-las-to-pas
                             mv-nth-0-ia32e-la-to-pa-for-same-1G-page
                             not
                             pml4-table-base-addr
                             pml4-table-entry-addr
                             page-dir-ptr-table-entry-addr
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl)))))

(defthm mv-nth-1-ia32e-la-to-pa-page-dir-ptr-table-for-same-1G-page
  (implies
   (and
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (combine-bytes
            (mv-nth 1 (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr) :r x86))))
    ;; PDPTE is direct mapped.
    (equal
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r (cpl x86) x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr pdpt-base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    ;; (equal (loghead 30 lin-addr) 0)
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (physical-address-p pdpt-base-addr)
    (equal (loghead 12 pdpt-base-addr) 0)
    (not (page-structure-marking-mode x86))
    (x86p x86))
   (equal (mv-nth 1
                  (ia32e-la-to-pa-page-dir-ptr-table
                   (+ n lin-addr) pdpt-base-addr u/s-acc r/w-acc x/d-acc
                   wp smep smap ac nxe r-w-x cpl x86))
          (+ n
             (ash
              (loghead 22
                       (logtail 30
                                (rm-low-64
                                 (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)
                                 x86)))
              30))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table)
                                   (commutativity-of-+
                                    not
                                    page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                                    page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                                    bitops::logand-with-negated-bitmask)))))

(defthm mv-nth-1-ia32e-la-to-pa-pml4-table-for-same-1G-page
  (implies
   (and
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pml4-table-entry
           (combine-bytes
            (mv-nth 1 (rb (create-canonical-address-list 8 pml4-table-entry-addr) :r x86))))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (combine-bytes
            (mv-nth 1 (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr) :r x86))))
    ;; PML4E and PDPTE are direct mapped.
    (equal
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 pml4-table-entry-addr)
       :r (cpl x86) x86))
     (addr-range 8 pml4-table-entry-addr))
    (equal
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r (cpl x86) x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-table-base-addr
                    wp smep smap ac nxe r-w-x cpl x86)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    ;; (equal (loghead 30 lin-addr) 0)
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (physical-address-p pml4-table-base-addr)
    (equal (loghead 12 pml4-table-base-addr) 0)
    (not (page-structure-marking-mode x86))
    (x86p x86))
   (equal (mv-nth 1
                  (ia32e-la-to-pa-pml4-table
                   (+ n lin-addr) pml4-table-base-addr
                   wp smep smap ac nxe r-w-x cpl x86))
          (+ n
             (ash
              (loghead 22
                       (logtail 30
                                (rm-low-64
                                 (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)
                                 x86)))
              30))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-pml4-table)
                            (commutativity-of-+
                             not
                             pml4-table-entry-addr-to-c-program-optimized-form
                             pml4-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask)))))

(defthm mv-nth-1-ia32e-la-to-pa-for-same-1G-page
  (implies
   (and
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pml4-table-entry
           (combine-bytes
            (mv-nth 1
                    (rb (create-canonical-address-list 8 pml4-table-entry-addr)
                        :r x86))))
    (equal pdpt-base-addr
           (ash (loghead 40 (logtail 12 pml4-table-entry))
                12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (combine-bytes (mv-nth 1 (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr) :r x86))))
    (equal
     (mv-nth 1 (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr) :r (cpl x86) x86))
     (addr-range 8 pml4-table-entry-addr))
    (equal
     (mv-nth 1
             (las-to-pas
              (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
              :r (cpl x86) x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (not (page-structure-marking-mode x86))
    (x86p x86))
   (equal (mv-nth 1 (ia32e-la-to-pa (+ n lin-addr) r-w-x cpl x86))
          (+ n
             (ash
              (loghead 22
                       (logtail 30
                                (rm-low-64
                                 (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)
                                 x86)))
              30))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa)
                            (commutativity-of-+
                             not
                             pml4-table-entry-addr-to-c-program-optimized-form
                             pml4-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask)))))

(def-gl-export open-mv-nth-1-las-to-pas-for-same-1G-page-general-1
  :hyp (and (< iteration m)
            (canonical-address-p lin-addr)
            (canonical-address-p (+ -1 lin-addr m))
            (integerp m)
            (<= m 1073741824)
            (natp iteration)
            (equal (loghead 30 lin-addr) 0))
  :concl (canonical-address-p (+ iteration lin-addr))
  :g-bindings (gl::auto-bindings (:mix (:nat lin-addr 64) (:nat iteration 64) (:nat m 64))))

(defthmd open-mv-nth-1-las-to-pas-for-same-1G-page-general
  (implies
   (and
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pml4-table-entry
           (combine-bytes
            (mv-nth 1 (rb (create-canonical-address-list 8 pml4-table-entry-addr) :r x86))))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (combine-bytes
            (mv-nth
             1
             (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
                 :r x86))))
    (equal
     (mv-nth
      1
      (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
                  :r (cpl x86) x86))
     (addr-range 8 pml4-table-entry-addr))
    (equal
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r (cpl x86) x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ -1 lin-addr m))
    (natp m)
    (<= m *2^30*)
    (natp iteration)
    (equal (loghead 30 lin-addr) 0)
    (not (page-structure-marking-mode x86))
    (x86p x86))
   (equal (mv-nth 1 (las-to-pas
                     (create-canonical-address-list-alt iteration m lin-addr)
                     r-w-x cpl x86))
          (addr-range
           (+ (- iteration) m)
           (+ iteration
              (ash
               (loghead 22
                        (logtail 30
                                 (rm-low-64
                                  (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)
                                  x86)))
               30)))))
  :hints (("Goal"
           :induct (create-canonical-address-list-alt iteration m lin-addr)
           :in-theory (e/d* (las-to-pas
                             open-mv-nth-1-las-to-pas-for-same-1G-page-general-1
                             open-mv-nth-0-las-to-pas-for-same-1G-page-general-1
                             open-mv-nth-0-las-to-pas-for-same-1G-page-general-2
                             open-mv-nth-0-las-to-pas-for-same-1G-page-general
                             ;; open-mv-nth-1-las-to-pas
                             mv-nth-1-ia32e-la-to-pa-for-same-1G-page)
                            (not
                             pml4-table-base-addr
                             pml4-table-entry-addr
                             page-dir-ptr-table-entry-addr
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl)))))

(def-gl-export open-mv-nth-1-las-to-pas-for-same-1G-page-general-2
  :hyp (and (canonical-address-p lin-addr)
            (equal (loghead 30 lin-addr) 0))
  :concl (canonical-address-p (+ -1 *2^30* lin-addr))
  :g-bindings (gl::auto-bindings (:mix (:nat lin-addr 64))))

(defthm open-mv-nth-1-las-to-pas-for-same-1G-page
  (implies
   (and
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pml4-table-entry
           (combine-bytes
            (mv-nth 1 (rb (create-canonical-address-list 8 pml4-table-entry-addr) :r x86))))
    (equal pdpt-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (combine-bytes
            (mv-nth
             1
             (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
                 :r x86))))
    (equal
     (mv-nth
      1
      (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
                  :r (cpl x86) x86))
     (addr-range 8 pml4-table-entry-addr))
    (equal
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r (cpl x86) x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
    (canonical-address-p lin-addr)
    (equal (loghead 30 lin-addr) 0)
    (not (page-structure-marking-mode x86))
    (x86p x86))
   (equal (mv-nth 1 (las-to-pas
                     (create-canonical-address-list *2^30* lin-addr)
                     r-w-x cpl x86))
          (addr-range
           *2^30*
           (ash
            (loghead 22
                     (logtail 30
                              (rm-low-64
                               (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)
                               x86)))
            30))))
  :hints (("Goal"
           :use ((:instance open-mv-nth-1-las-to-pas-for-same-1G-page-general
                            (iteration 0)
                            (m *2^30*))
                 (:instance open-mv-nth-1-las-to-pas-for-same-1G-page-general-2))
           :in-theory (e/d* (create-canonical-address-list-alt-is-create-canonical-address-list)
                            (open-mv-nth-1-las-to-pas-for-same-1G-page-general-2
                             las-to-pas
                             ;; open-mv-nth-0-las-to-pas
                             mv-nth-0-ia32e-la-to-pa-for-same-1G-page
                             not
                             pml4-table-base-addr
                             pml4-table-entry-addr
                             page-dir-ptr-table-entry-addr
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl)))))

(defthmd las-to-pas-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr-general
  (implies
   (and
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pml4-table-entry
           (combine-bytes
            (mv-nth 1
                    (rb (create-canonical-address-list 8 pml4-table-entry-addr)
                        :r x86))))
    (equal pdpt-base-addr
           (ash (loghead 40 (logtail 12 pml4-table-entry))
                12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (combine-bytes
            (mv-nth
             1
             (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
                 :r x86))))
    (equal
     (mv-nth
      1
      (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
                  :r (cpl x86)
                  x86))
     (addr-range 8 pml4-table-entry-addr))
    (equal
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r (cpl x86)
       x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86))
           (addr-range 8 page-dir-ptr-table-entry-addr))
    (disjoint-p
     (addr-range 8 (pml4-table-entry-addr lin-addr pml4-table-base-addr))
     (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)))
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
    (equal (page-present page-dir-ptr-table-entry)
           (page-present (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-read-write page-dir-ptr-table-entry)
           (page-read-write (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
           (page-user-supervisor (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-execute-disable page-dir-ptr-table-entry)
           (page-execute-disable (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry)
           (page-size (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
           (part-select (combine-bytes (strip-cdrs addr-lst)) :low 13 :high 29))
    (addr-byte-alistp addr-lst)
    (equal (len addr-lst) 8)
    (canonical-address-p lin-addr)
    (canonical-address-p (+ -1 lin-addr m))
    (natp m)
    (<= m *2^30*)
    (natp iteration)
    (equal (loghead 30 lin-addr) 0)
    (not (programmer-level-mode x86))
    (not (page-structure-marking-mode x86))
    (x86p x86))
   ;; las-to-pas returns the physical addresses corresponding to
   ;; linear addresses after the PDPTE corresponding to these linear
   ;; addresses have been modified --- the new PDPTE is (combine-bytes
   ;; (strip-cdrs addr-lst)).
   (and
    (equal (mv-nth 0 (las-to-pas
                      (create-canonical-address-list-alt iteration m lin-addr)
                      r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
           nil)
    (equal (mv-nth 1 (las-to-pas
                      (create-canonical-address-list-alt iteration m lin-addr)
                      r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
           (addr-range
            (+ (- iteration) m)
            (+ iteration
               (ash (loghead 22 (logtail 30 (combine-bytes (strip-cdrs addr-lst)))) 30))))))
  :hints (("Goal"
           :do-not '(preprocess)
           :induct (create-canonical-address-list-alt iteration m lin-addr)
           :in-theory (e/d*
                       (disjoint-p
                        member-p
                        las-to-pas
                        open-mv-nth-1-las-to-pas-for-same-1G-page-general-1
                        open-mv-nth-0-las-to-pas-for-same-1G-page-general-1
                        open-mv-nth-0-las-to-pas-for-same-1G-page-general-2
                        open-mv-nth-0-las-to-pas-for-same-1G-page-general
                        mv-nth-0-ia32e-la-to-pa-for-same-1G-page
                        mv-nth-1-ia32e-la-to-pa-for-same-1G-page)
                       (mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p-in-non-marking-mode
                        member-p-strip-cars-of-remove-duplicate-keys
                        page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                        page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                        bitops::logand-with-negated-bitmask
                        force (force)
                        not)))))

(defthm las-to-pas-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr
  (implies
   (and
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pml4-table-entry
           (combine-bytes
            (mv-nth 1
                    (rb (create-canonical-address-list 8 pml4-table-entry-addr)
                        :r x86))))
    (equal pdpt-base-addr
           (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (combine-bytes
            (mv-nth
             1
             (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
                 :r x86))))
    (equal
     (mv-nth
      1
      (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
                  :r (cpl x86)
                  x86))
     (addr-range 8 pml4-table-entry-addr))
    (equal
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r (cpl x86)
       x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86))
           (addr-range 8 page-dir-ptr-table-entry-addr))
    (disjoint-p
     (addr-range 8 (pml4-table-entry-addr lin-addr pml4-table-base-addr))
     (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)))
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
    (equal (page-present page-dir-ptr-table-entry)
           (page-present (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-read-write page-dir-ptr-table-entry)
           (page-read-write (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
           (page-user-supervisor (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-execute-disable page-dir-ptr-table-entry)
           (page-execute-disable (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry)
           (page-size (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
           (part-select (combine-bytes (strip-cdrs addr-lst)) :low 13 :high 29))
    (addr-byte-alistp addr-lst)
    (equal (len addr-lst) 8)
    (canonical-address-p lin-addr)
    (equal (loghead 30 lin-addr) 0)
    (not (programmer-level-mode x86))
    (not (page-structure-marking-mode x86))
    (x86p x86))
   ;; las-to-pas returns the physical addresses corresponding to
   ;; linear addresses after the PDPTE corresponding to these linear
   ;; addresses have been modified --- the new PDPTE is (combine-bytes
   ;; (strip-cdrs addr-lst)).
   (and
    (equal (mv-nth 0 (las-to-pas
                      (create-canonical-address-list *2^30* lin-addr)
                      r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
           nil)
    (equal (mv-nth 1 (las-to-pas
                      (create-canonical-address-list *2^30* lin-addr)
                      r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
           (addr-range *2^30* (ash (loghead 22 (logtail 30 (combine-bytes (strip-cdrs addr-lst)))) 30)))))
  :hints (("Goal"
           :do-not '(preprocess)
           :do-not-induct t
           :use ((:instance las-to-pas-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr-general
                            (m *2^30*)
                            (iteration 0))
                 (:instance open-mv-nth-1-las-to-pas-for-same-1G-page-general-2))
           :in-theory (e/d* (create-canonical-address-list-alt-is-create-canonical-address-list)
                            (member-p-strip-cars-of-remove-duplicate-keys
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask
                             force (force)
                             not)))))

(defthm read-from-physical-memory-and-wb-with-modified-1G-page-map-in-system-level-non-marking-mode
  (b* ((cpl (cpl x86))
       (pml4-table-base-addr (pml4-table-base-addr x86))
       (pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
       (pdpt-base-addr
        (pdpt-base-addr lin-addr x86))
       (page-dir-ptr-table-entry-addr
        (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
       (page-dir-ptr-table-entry
        (combine-bytes
         (mv-nth 1 (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr) :r x86))))
       (bytes (strip-cdrs addr-lst))
       (value (combine-bytes bytes)))
    (implies
     (and
      ;; PML4E and PDPTE are direct mapped.
      (equal
       (mv-nth
        1
        (las-to-pas
         (create-canonical-address-list 8 pml4-table-entry-addr)
         :r (cpl x86) x86))
       (addr-range 8 pml4-table-entry-addr))
      (equal
       (mv-nth
        1
        (las-to-pas
         (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
         :r (cpl x86) x86))
       (addr-range 8 page-dir-ptr-table-entry-addr))
      (equal (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl x86))
             (addr-range 8 page-dir-ptr-table-entry-addr))
      ;; The physical addresses pointed to by the new PDPTE (i.e.,
      ;; containing "value") are disjoint from the physical addresses
      ;; corresponding to the PDPTE itself.
      (disjoint-p
       (addr-range *2^30* (ash (loghead 22 (logtail 30 value)) 30))
       (addr-range 8 page-dir-ptr-table-entry-addr))
      (disjoint-p
       (addr-range 8 (pml4-table-entry-addr lin-addr pml4-table-base-addr))
       (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)))
      (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
      (equal (page-present page-dir-ptr-table-entry)
             (page-present value))
      (equal (page-read-write page-dir-ptr-table-entry)
             (page-read-write value))
      (equal (page-user-supervisor page-dir-ptr-table-entry)
             (page-user-supervisor value))
      (equal (page-execute-disable page-dir-ptr-table-entry)
             (page-execute-disable value))
      (equal (page-size page-dir-ptr-table-entry)
             (page-size value))
      (equal (page-size page-dir-ptr-table-entry) 1)
      (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
             (part-select value :low 13 :high 29))
      (addr-byte-alistp addr-lst)
      (equal (len addr-lst) 8)
      (canonical-address-p lin-addr)
      (canonical-address-p (+ -1 *2^30* lin-addr))
      ;; 1G-aligned linear address
      (equal (loghead 30 lin-addr) 0)
      (not (programmer-level-mode x86))
      (not (page-structure-marking-mode x86))
      (x86p x86))
     (equal (read-from-physical-memory
             (addr-range *2^30* (ash (loghead 22 (logtail 30 value)) 30))
             (mv-nth 1 (wb addr-lst x86)))
            (read-from-physical-memory
             (addr-range *2^30* (ash (loghead 22 (logtail 30 value)) 30))
             x86))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :in-theory (e/d* (disjoint-p
                             member-p
                             wb
                             page-dir-ptr-table-entry-addr
                             pml4-table-entry-addr)
                            (read-from-physical-memory
                             member-p-strip-cars-of-remove-duplicate-keys
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask
                             force (force)
                             not
                             rewire_dst_to_src-disable)))))

(defthm rb-wb-equal-with-modified-1G-page-map-in-system-level-non-marking-mode
  (implies
   (and
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pml4-table-entry
           (combine-bytes
            (mv-nth 1
                    (rb (create-canonical-address-list 8 pml4-table-entry-addr)
                        :r x86))))
    (equal pdpt-base-addr
           (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
           (combine-bytes
            (mv-nth
             1
             (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
                 :r x86))))
    (equal
     (mv-nth
      1
      (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
                  :r (cpl x86)
                  x86))
     (addr-range 8 pml4-table-entry-addr))
    (equal
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r (cpl x86)
       x86))
     (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86))
           (addr-range 8 page-dir-ptr-table-entry-addr))
    (disjoint-p
     (addr-range 8 (pml4-table-entry-addr lin-addr pml4-table-base-addr))
     (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr)))
    (disjoint-p
     (addr-range *2^30* (ash (loghead 22 (logtail 30 (combine-bytes (strip-cdrs addr-lst)))) 30))
     (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
;;;
    (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x (cpl x86) x86)))
;;;
    (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
    (not (mv-nth 0 (las-to-pas (create-canonical-address-list *2^30* lin-addr)
                               r-w-x (cpl x86) x86)))
    (equal (page-present page-dir-ptr-table-entry)
           (page-present (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-read-write page-dir-ptr-table-entry)
           (page-read-write (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
           (page-user-supervisor (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-execute-disable page-dir-ptr-table-entry)
           (page-execute-disable (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry)
           (page-size (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
           (part-select (combine-bytes (strip-cdrs addr-lst)) :low 13 :high 29))
    (addr-byte-alistp addr-lst)
    (equal (len addr-lst) 8)
    (canonical-address-p lin-addr)
    (equal (loghead 30 lin-addr) 0)
    (not (programmer-level-mode x86))
    (not (page-structure-marking-mode x86))
    (x86p x86))
   (and (equal (mv-nth 0 (rb (create-canonical-address-list *2^30* lin-addr)
                             r-w-x (mv-nth 1 (wb addr-lst x86)))) nil)
        (equal (mv-nth 1 (rb (create-canonical-address-list *2^30* lin-addr)
                             r-w-x (mv-nth 1 (wb addr-lst x86))))
               (read-from-physical-memory
                (addr-range *2^30* (ash (loghead 22 (logtail 30 (combine-bytes (strip-cdrs addr-lst)))) 30))
                x86))))
  :hints (("Goal"
           :use
           ((:instance read-from-physical-memory-and-wb-with-modified-1G-page-map-in-system-level-non-marking-mode)
            (:instance open-mv-nth-1-las-to-pas-for-same-1G-page-general-2))
           :do-not-induct t
           :do-not '(preprocess)
           :in-theory (e/d* (rb disjoint-p member-p)
                            (read-from-physical-memory
                             read-from-physical-memory-and-wb-with-modified-1G-page-map-in-system-level-non-marking-mode
                             wb
                             member-p-strip-cars-of-remove-duplicate-keys
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask
                             force (force)
                             not)))))

(def-gl-export entry-attributes-unchanged-when-destination-PDPTE-modified
  :hyp (and (unsigned-byte-p 64 dest-pdpte)
            (unsigned-byte-p 64 src-pdpte))
  :concl (and
          (equal (page-present (logior (logand 18442240475155922943 dest-pdpte)
                                       (logand 4503598553628672 src-pdpte)))
                 (page-present dest-pdpte))
          (equal (page-read-write (logior (logand 18442240475155922943 dest-pdpte)
                                          (logand 4503598553628672 src-pdpte)))
                 (page-read-write dest-pdpte))
          (equal (page-user-supervisor (logior (logand 18442240475155922943 dest-pdpte)
                                               (logand 4503598553628672 src-pdpte)))
                 (page-user-supervisor dest-pdpte))
          (equal (page-execute-disable (logior (logand 18442240475155922943 dest-pdpte)
                                               (logand 4503598553628672 src-pdpte)))
                 (page-execute-disable dest-pdpte))
          (equal (page-size (logior (logand 18442240475155922943 dest-pdpte)
                                    (logand 4503598553628672 src-pdpte)))
                 (page-size dest-pdpte)))
  :g-bindings
  (gl::auto-bindings (:mix (:nat src-pdpte 64) (:nat dest-pdpte 64))))

(defthm rb-of-1G-in-terms-of-read-from-physical-memory
  (implies (and (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86)))
           (equal
            (mv-nth 1 (rb (create-canonical-address-list *2^30* (xr :rgf *rdi* x86)) :r x86))
            (read-from-physical-memory
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
                        :r (cpl x86) x86))
             x86)))
  :hints (("Goal"
           :do-not '(preprocess)
           :do-not-induct t
           :in-theory (e/d* (rb-wb-equal-in-system-level-non-marking-mode
                             pos member-p subset-p
                             page-size
                             rb)

                            (rewire_dst_to_src-clk
                             (rewire_dst_to_src-clk)

                             pml4-table-base-addr
                             pdpt-base-addr
                             pml4-table-entry-addr
                             page-dir-ptr-table-entry-addr

                             pml4-table-entry-addr-to-c-program-optimized-form
                             pml4-table-entry-addr-to-c-program-optimized-form-gl
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl

                             not
                             bitops::logand-with-negated-bitmask
                             unsigned-byte-p
                             force (force))))))

;; ----------------------------------------------------------------------

(defun-nx direct-map-p (x86)
  ;; Direct map for paging structures, specifically source and
  ;; destination PML4E and PDPTE.
  (and
   ;; Source:
   (equal (mv-nth 1 (las-to-pas
                     (create-canonical-address-list
                      8
                      (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
                     :r (cpl x86) x86))
          (addr-range
           8
           (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))))

   (equal
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list
                8
                (page-dir-ptr-table-entry-addr
                 (xr :rgf *rdi* x86)
                 (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
               :r 0 x86))
    (addr-range
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rdi* x86)
      (pdpt-base-addr (xr :rgf *rdi* x86) x86))))

   ;; Destination:
   (equal
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list
                8
                (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
               :r (cpl x86) x86))
    (addr-range
     8
     (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))))

   (equal
    (mv-nth 1 (las-to-pas
               (create-canonical-address-list
                8
                (page-dir-ptr-table-entry-addr
                 (xr :rgf *rsi* x86)
                 (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
               :r 0 x86))
    (addr-range
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rsi* x86)
      (pdpt-base-addr (xr :rgf *rsi* x86) x86))))))

(defun-nx source-physical-addresses-and-destination-PDPTE-no-interfere-p (x86)
  ;; The source physical addresses are disjoint from the the physical
  ;; addresses of the destination PDPTE.
  (disjoint-p
   (addr-range *2^30*
               (ash (loghead 22 (logtail 30
                                         (rm-low-64
                                          (page-dir-ptr-table-entry-addr
                                           (xr :rgf *rdi* x86)
                                           (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                                          x86)))
                    30))
   (addr-range 8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86)))))

(defun-nx destination-PML4E-and-destination-PDPTE-no-interfere-p (x86)
  (disjoint-p
   (addr-range 8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
   (addr-range 8 (page-dir-ptr-table-entry-addr
                  (xr :rgf *rsi* x86)
                  (pdpt-base-addr (xr :rgf *rsi* x86) x86)))))

(defun-nx destination-translation-governing-addresses-and-stack-no-interfere-p (x86)
  ;; The translation-governing addresses of the destination are disjoint
  ;; from the physical addresses corresponding to the stack.
  (disjoint-p
   (mv-nth 1 (las-to-pas
              (create-canonical-address-list
               8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list *2^30* (xr :rgf *rsi* x86)) x86)))

(defun-nx source-addresses-and-stack-no-interfere-p (x86)
  ;; The source addresses are disjoint from the physical addresses
  ;; corresponding to the stack.
  (disjoint-p
   (addr-range
    *2^30*
    (ash
     (loghead
      22
      (logtail
       30
       (rm-low-64 (page-dir-ptr-table-entry-addr
                   (xr :rgf *rdi* x86)
                   (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                  x86)))
     30))
   (mv-nth
    1
    (las-to-pas (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                :w (cpl x86) x86))))

(defun-nx more-non-interference-assumptions (x86)
  (and (source-physical-addresses-and-destination-PDPTE-no-interfere-p x86)
       (destination-PML4E-and-destination-PDPTE-no-interfere-p x86)
       (destination-translation-governing-addresses-and-stack-no-interfere-p x86)
       (source-addresses-and-stack-no-interfere-p x86)))

;; ----------------------------------------------------------------------

(defthm rewire_dst_to_src-after-the-copy-source-p-addrs-open
  (implies (and (equal cpl (cpl x86))
                (rewire_dst_to_src-assumptions x86)
                (direct-map-p x86))

           (equal
            (mv-nth 1 (las-to-pas (create-canonical-address-list
                                   *2^30* (xr :rgf *rdi* x86)) :r cpl x86))
            (addr-range *2^30*
                        (ash (loghead 22
                                      (logtail 30
                                               (rm-low-64
                                                (page-dir-ptr-table-entry-addr
                                                 (xr :rgf *rdi* x86)
                                                 (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                                                x86)))
                             30))))
  :hints (("Goal"
           :use ((:instance las-to-pas-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr-general
                            (lin-addr (xr :rgf *rdi* x86))
                            (r-w-x :r)
                            (cpl (cpl x86))))
           :do-not '(preprocess)
           :do-not-induct t
           :in-theory (e/d* (pdpt-base-addr
                             pml4-table-base-addr
                             pos
                             page-size)
                            (rewire_dst_to_src-clk
                             (rewire_dst_to_src-clk)
                             addr-range
                             (addr-range)
                             pml4-table-entry-addr
                             natp-pml4-table-entry-addr
                             page-dir-ptr-table-entry-addr
                             pml4-table-entry-addr-to-c-program-optimized-form
                             pml4-table-entry-addr-to-c-program-optimized-form-gl
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                             disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
                             acl2::consp-when-member-equal-of-atom-listp
                             r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-when-no-errors
                             ia32e-la-to-pa-xw-state
                             (:linear adding-7-to-pml4-table-entry-addr)
                             (:linear *physical-address-size*p-pml4-table-entry-addr)
                             (:rewrite las-to-pas-xw-state)
                             (:rewrite acl2::equal-of-booleans-rewrite)
                             (:rewrite loghead-unequal)
                             (:rewrite negative-logand-to-positive-logand-with-integerp-x)
                             (:definition combine-bytes)
                             (:rewrite |(logand -4096 base-addr) = base-addr when low 12 bits are 0|)
                             not
                             unsigned-byte-p-of-combine-bytes
                             unsigned-byte-p-of-logtail
                             disjoint-p-subset-p
                             acl2::loghead-identity
                             acl2::ash-0
                             acl2::zip-open
                             acl2::logtail-identity
                             bitops::logand-with-negated-bitmask
                             member-p-strip-cars-of-remove-duplicate-keys
                             unsigned-byte-p
                             force (force))))))

(defthm rewire_dst_to_src-after-the-copy-destination==source
  (implies (and (rewire_dst_to_src-assumptions x86)
                (direct-map-p x86)
                (more-non-interference-assumptions x86))
           (equal
            ;; Destination, after the copy:
            (mv-nth 1 (rb  (create-canonical-address-list *2^30* (xr :rgf *rsi* x86))
                           :r (x86-run (rewire_dst_to_src-clk) x86)))
            ;; Source, before the copy:
            (mv-nth 1 (rb (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
                          :r x86))))
  :hints (("Goal"
           :do-not '(preprocess)
           :do-not-induct t
           :in-theory (e/d* (rb-wb-equal-in-system-level-non-marking-mode
                             pos
                             pdpt-base-addr
                             page-size)

                            (rewire_dst_to_src-clk
                             (rewire_dst_to_src-clk)
                             (addr-range)
                             addr-range

                             pml4-table-base-addr
                             ;; pdpt-base-addr
                             pml4-table-entry-addr
                             page-dir-ptr-table-entry-addr

                             pml4-table-entry-addr-to-c-program-optimized-form
                             pml4-table-entry-addr-to-c-program-optimized-form-gl
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl

                             disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
                             acl2::consp-when-member-equal-of-atom-listp
                             r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-when-no-errors
                             ia32e-la-to-pa-xw-state
                             (:linear adding-7-to-pml4-table-entry-addr)
                             (:linear *physical-address-size*p-pml4-table-entry-addr)
                             (:rewrite las-to-pas-xw-state)
                             (:rewrite acl2::equal-of-booleans-rewrite)
                             (:rewrite loghead-unequal)
                             (:rewrite negative-logand-to-positive-logand-with-integerp-x)
                             (:definition combine-bytes)
                             (:rewrite |(logand -4096 base-addr) = base-addr when low 12 bits are 0|)
                             member-p-strip-cars-of-remove-duplicate-keys
                             not
                             bitops::logand-with-negated-bitmask
                             unsigned-byte-p
                             force (force))))))

;; ======================================================================

;; (defthm rm-low-64-and-xlate-equiv-memory-disjoint-from-its-translation-governing-addresses
;;   (implies (and (bind-free
;;                  (find-an-xlate-equiv-x86
;;                   'rm-low-64-and-xlate-equiv-memory
;;                   x86-1 'x86-2 mfc state)
;;                  (x86-2))
;;                 (syntaxp (and (not (eq x86-2 x86-1))
;;                               ;; x86-2 must be smaller than x86-1.
;;                               (term-order x86-2 x86-1)))
;;                 (xlate-equiv-memory (double-rewrite x86-1) x86-2)
;;                 (x86p x86-1)
;;                 (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86-1)))
;;                 (canonical-address-p lin-addr)
;;                 (equal (loghead 3 lin-addr) 0))
;;            (xlate-equiv-entries
;;             (rm-low-64
;;              (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86-1)) x86-1)
;;             (rm-low-64
;;              (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86-1)) x86-2)))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :in-theory (e/d* (ia32e-la-to-pa-lower-12-bits)
;;                             ()))))

;; (defthm read-from-physical-memory-and-xlate-equiv-memory-disjoint-from-its-translation-governing-addresses
;;   (implies (and (bind-free
;;                  (find-an-xlate-equiv-x86
;;                   'read-from-physical-memory-and-xlate-equiv-memory
;;                   x86-1 'x86-2 mfc state)
;;                  (x86-2))
;;                 (syntaxp (and (not (eq x86-2 x86-1))
;;                               ;; x86-2 must be smaller than x86-1.
;;                               (term-order x86-2 x86-1)))
;;                 (xlate-equiv-memory (double-rewrite x86-1) x86-2)
;;                 (not (mv-nth 0 (las-to-pas (create-canonical-address-list 8 lin-addr) r-w-x cpl (double-rewrite x86-1))))
;;                 (canonical-address-p lin-addr)
;;                 (equal (loghead 3 lin-addr) 0))
;;            (xlate-equiv-entries
;;             (read-from-physical-memory
;;              (mv-nth 1 (las-to-pas (create-canonical-address-list 8 lin-addr) r-w-x cpl x86-1)) x86-1)
;;             (read-from-physical-memory
;;              (mv-nth 1 (las-to-pas (create-canonical-address-list 8 lin-addr) r-w-x cpl x86-1)) x86-2)))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :in-theory (e/d* (read-from-physical-memory)
;;                             ()))))

;; (defthm mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-its-translation-governing-addresses
;;   (implies (and (bind-free
;;                  (find-an-xlate-equiv-x86
;;                   'mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-its-translation-governing-addresses
;;                   x86-1 'x86-2 mfc state)
;;                  (x86-2))
;;                 (syntaxp (and
;;                           (not (eq x86-2 x86-1))
;;                           ;; x86-2 must be smaller than x86-1.
;;                           (term-order x86-2 x86-1)))
;;                 (xlate-equiv-memory (double-rewrite x86-1) x86-2)
;;                 (disjoint-p
;;                  (mv-nth 1 (las-to-pas
;;                             (create-canonical-address-list 8 lin-addr)
;;                             r-w-x (cpl x86-1) (double-rewrite x86-1)))
;;                  (all-translation-governing-addresses
;;                   (create-canonical-address-list 8 lin-addr) (double-rewrite x86-1)))
;;                 (canonical-address-p lin-addr)
;;                 (equal (loghead 3 lin-addr) 0))
;;            (xlate-equiv-entries
;;             (mv-nth 1 (rb (create-canonical-address-list 8 lin-addr) r-w-x x86-1))
;;             (mv-nth 1 (rb (create-canonical-address-list 8 lin-addr) r-w-x x86-2))))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :use ((:instance xlate-equiv-memory-in-programmer-level-mode-implies-equal-states))
;;            :in-theory (e/d* (rb) (force (force)))))
;;   :otf-flg t)

;; (local
;;  (defthm disjoint-p-all-translation-governing-addresses-and-las-to-pas-subset-p
;;    ;; Follows from MV-NTH-1-LAS-TO-PAS-SUBSET-P-DISJOINT-FROM-OTHER-P-ADDRS.

;;    ;; This rule is tailored to rewrite terms of the form

;;    ;; (disjoint-p (all-translation-governing-addresses l-addrs-subset x86)
;;    ;;             (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86)))

;;    ;; where l-addrs-subset is a subset of l-addrs, and l-addrs is of
;;    ;; the form (create-canonical-address-list ...).

;;    (implies
;;     (and
;;      (bind-free (find-l-addrs-like-create-canonical-address-list-from-fn
;;                  'all-translation-governing-addresses 'l-addrs mfc state)
;;                 (l-addrs))
;;      ;; (syntaxp (not (cw "~% l-addrs: ~x0~%" l-addrs)))
;;      (disjoint-p
;;       (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86)))
;;       (all-translation-governing-addresses l-addrs (double-rewrite x86)))
;;      (subset-p l-addrs-subset l-addrs)
;;      (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86)))))
;;     (disjoint-p (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86))
;;                 (all-translation-governing-addresses l-addrs-subset x86)))
;;    :hints
;;    (("Goal"
;;      :use ((:instance disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
;;                       (l-addrs l-addrs)
;;                       (l-addrs-subset l-addrs-subset)
;;                       (other-p-addrs (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))
;;                       (other-p-addrs-subset (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86)))))
;;      :in-theory (e/d* (subset-p
;;                        member-p
;;                        disjoint-p-append-1
;;                        las-to-pas
;;                        all-translation-governing-addresses
;;                        disjoint-p-commutative)
;;                       ())))))


||#
