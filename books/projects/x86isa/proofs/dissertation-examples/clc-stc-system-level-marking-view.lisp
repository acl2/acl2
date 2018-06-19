;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "sys-view/marking-view-top" :dir :proof-utils :ttags :all)

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
   ;; The model is operating in 64-bit mode.
   (64-bit-modep x86)
   ;; The model is operating in the system-level marking view.
   (not (app-view x86))
   (marking-view x86)
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

;; (acl2::why x86-fetch-decode-execute-opener-in-marking-view)
;; (acl2::why get-prefixes-alt-opener-lemma-no-prefix-byte)
;; (acl2::why one-read-with-rb-alt-from-program-at-alt-in-marking-view)
;; (acl2::why many-reads-with-rb-alt-from-program-at-alt-in-marking-view)

(defthm program-effects-1
  (implies (preconditions x86)
           (equal (x86-run 1 x86)
                  (xw :rip 0 (+ 1 (xr :rip 0 x86))
                      (!flgi *cf* 0
                             (mv-nth 2
                                     (las-to-pas 1 (xr :rip 0 x86) :x x86))))))
  :hints (("Goal" :in-theory (e/d* (x86-cmc/clc/stc/cld/std
                                    rml08
                                    pos
                                    mv-nth-0-las-to-pas-subset-p
                                    member-p
                                    subset-p
                                    disjoint-p$)
                                   ()))))


(defthm program-effects-2
  (implies (preconditions x86)
           (equal (x86-run 2 x86)
                  (xw :rip 0 (+ 2 (xr :rip 0 x86))
                      (!flgi *cf* 1
                             (mv-nth 2
                                     (las-to-pas 2 (xr :rip 0 x86) :x x86))))))
  :hints (("Goal" :in-theory (e/d* (x86-cmc/clc/stc/cld/std
                                    rml08
                                    pos
                                    mv-nth-0-las-to-pas-subset-p
                                    member-p
                                    subset-p
                                    disjoint-p$)
                                   ()))))

;; ======================================================================
