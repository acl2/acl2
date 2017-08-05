;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "system-level-mode/marking-mode-top" :dir :proof-utils :ttags :all)

(include-book "centaur/bitops/ihs-extensions" :dir :system)
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

;; ======================================================================

(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))

(defconst *program*
  '(#xf8 ;; CLC
    #xf9 ;; STC
    ;; Padding so that get-prefixes-alt works...
    0 0 0 0 0 0 0 0
    0 0 0 0 0 0))

(defun-nx preconditions (x86)
  (and
   ;; The x86 state is well-formed.
   (x86p x86)
   ;; The model is operating in the system-level marking mode.
   (not (programmer-level-mode x86))
   (page-structure-marking-mode x86)
   ;; The program is located at linear addresses ranging from (rip
   ;; x86) to (+ -1 (len *program*) (rip x86)).
   (program-at (rip x86) *program* x86)
   ;; No error is encountered when translating the program's linear
   ;; addresses to physical addresses.
   (not (mv-nth 0 (las-to-pas (len *program*) (rip x86) :x x86)))
   ;; The program's physical addresses are disjoint from the physical
   ;; addresses of the paging structures.  .
   (disjoint-p$
    (mv-nth 1 (las-to-pas (len *program*) (rip x86) :x x86))
    (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86)))
   ;; The addresses where the program is located are canonical.
   (canonical-address-p (rip x86))
   (canonical-address-p (+ (len *program*) (rip x86)))
   ;; The initial state is error-free.
   (equal (ms x86) nil)
   (equal (fault x86) nil)))

;; (acl2::why x86-fetch-decode-execute-opener-in-marking-mode)
;; (acl2::why get-prefixes-alt-opener-lemma-no-prefix-byte)
;; (acl2::why one-read-with-rb-alt-from-program-at-alt-in-marking-mode)
;; (acl2::why many-reads-with-rb-alt-from-program-at-alt-in-marking-mode)

(defthm program-effects-1
  (implies (preconditions x86)
           (equal (x86-run 1 x86)
                  (xw :rip 0 (+ 1 (xr :rip 0 x86))
                      (!flgi *cf* 0
                             (mv-nth 2
                                     (las-to-pas 1 (xr :rip 0 x86) :x x86))))))
  :hints (("Goal" :in-theory (e/d* (x86-cmc/clc/stc/cld/std
                                    rm08
                                    pos
                                    mv-nth-0-las-to-pas-subset-p
                                    member-p
                                    subset-p
                                    disjoint-p$)
                                   ()))))

(local
 (defthmd mv-nth-1-las-to-pas-subset-p-helper-1
   (implies (and (<= n-2 n-1)
                 (not (mv-nth 0 (las-to-pas n-1 addr r-w-x x86)))
                 (natp n-1))
            (subset-p (mv-nth 1 (las-to-pas n-2 addr r-w-x x86))
                      (mv-nth 1 (las-to-pas n-1 addr r-w-x x86))))
   :hints (("Goal" :in-theory (e/d* (subset-p las-to-pas) ())))))

(local
 (defthmd mv-nth-1-las-to-pas-subset-p-helper-2
   (implies
    (and (<= (+ addr-1 n-2) (+ addr-1 n-1))
         (not (mv-nth 0 (las-to-pas (+ -1 n-1) (+ 1 addr-1) r-w-x x86)))
         (integerp n-1)
         (< 0 n-2))
    (subset-p (mv-nth 1 (las-to-pas n-2 addr-1 r-w-x x86))
              (cons (mv-nth 1 (ia32e-la-to-pa addr-1 r-w-x x86))
                    (mv-nth 1
                            (las-to-pas (+ -1 n-1)
                                        (+ 1 addr-1)
                                        r-w-x x86)))))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance mv-nth-1-las-to-pas-subset-p-helper-1
                             (addr addr-1)))
            :expand ((las-to-pas n-1 addr-1 r-w-x x86))
            :in-theory (e/d* (las-to-pas subset-p) ())))))

(defthm mv-nth-1-las-to-pas-subset-p-less-strict
  (implies (and (<= addr-1 addr-2)
                (<= (+ n-2 addr-2) (+ n-1 addr-1))
                (not (mv-nth 0 (las-to-pas n-1 addr-1 r-w-x x86)))
                (posp n-1) (posp n-2) (integerp addr-2))
           (subset-p (mv-nth 1 (las-to-pas n-2 addr-2 r-w-x x86))
                     (mv-nth 1 (las-to-pas n-1 addr-1 r-w-x x86))))
  :hints (("Goal" :in-theory (e/d* (las-to-pas
                                    mv-nth-1-las-to-pas-subset-p-helper-2
                                    subset-p)
                                   ()))))

(defthm disjointness-of-program-bytes-from-paging-structures
  (implies (and
            (bind-free
             (find-program-at-alt-info 'prog-addr 'bytes mfc state)
             (prog-addr bytes))
            (program-at-alt prog-addr bytes x86)
            ;; <n,lin-addr> is a non-strict subset of <(len bytes),prog-addr>.
            (<= prog-addr lin-addr)
            (<= (+ n lin-addr) (+ (len bytes) prog-addr))
            (posp n) (integerp lin-addr))
           (disjoint-p (mv-nth 1 (las-to-pas n lin-addr :x x86))
                       (open-qword-paddr-list
                        (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal"
           :do-not-induct t
           :cases ((= (+ n lin-addr) (+ (len bytes) prog-addr)))
           :use ((:instance program-at-alt-implies-program-addresses-properties)
                 (:instance disjoint-p-subset-p
                            (x (mv-nth 1 (las-to-pas (len bytes) prog-addr :x x86)))
                            (y
                             (open-qword-paddr-list
                              (gather-all-paging-structure-qword-addresses x86)))
                            (a (mv-nth 1 (las-to-pas n lin-addr :x x86)))
                            (b (open-qword-paddr-list
                                (gather-all-paging-structure-qword-addresses x86)))))
           :in-theory (e/d* (disjoint-p$)
                            (disjoint-p-subset-p
                             mv-nth-1-las-to-pas-subset-p)))))

(defthm program-effects-2
  (implies (preconditions x86)
           (equal (x86-run 2 x86)
                  (xw :rip 0 (+ 2 (xr :rip 0 x86))
                      (!flgi *cf* 1
                             (mv-nth 2
                                     (las-to-pas 2 (xr :rip 0 x86) :x x86))))))
  :hints (("Goal" :in-theory (e/d* (x86-cmc/clc/stc/cld/std
                                    rm08
                                    pos
                                    mv-nth-0-las-to-pas-subset-p
                                    member-p
                                    subset-p
                                    disjoint-p$)
                                   ()))))

;; ======================================================================
