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
(include-book "gather-paging-structures" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "std/lists/sets" :dir :system))

(local (in-theory (e/d () (unsigned-byte-p signed-byte-p))))

;; ======================================================================

(local
 (encapsulate
   ()

   (defthm member-p-remove-duplicates-equal-iff-member-p
     (iff (member-p index (remove-duplicates-equal a))
          (member-p index a))
     :hints (("Goal"
              :in-theory (e/d* (member-p-iff-member-equal)
                               (member-p)))))

   (defthm member-p-and-gather-qword-addresses-corresponding-to-1-entry
     (implies (and (<=
                    (ash (ia32e-page-tablesbits->reference-addr
                          (rm-low-64 superior-structure-paddr x86))
                         12)
                    e)
                   (< e
                      (+
                       4096
                       (ash (ia32e-page-tablesbits->reference-addr
                             (rm-low-64 superior-structure-paddr x86))
                            12)))
                   ;; The following hypothesis isn't necessary if
                   ;; gather-qword-addresses-corresponding-to-1-entry
                   ;; is modified to collect an over-approximation of
                   ;; inferior paddrs.
                   ;; (equal (page-present (rm-low-64 superior-structure-paddr x86)) 1)
                   (equal (page-size (rm-low-64 superior-structure-paddr x86)) 0)
                   (physical-address-p e)
                   (equal (loghead 3 e) 0))
              (member-p e (gather-qword-addresses-corresponding-to-1-entry
                           superior-structure-paddr x86)))
     :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry
                                       member-p)
                                      ()))))

   (defthm member-p-when-gather-qword-addresses-corresponding-to-1-entry-then-member-p-entries-aux
     (implies (and (member-p e
                             (gather-qword-addresses-corresponding-to-1-entry
                              superior-structure-paddr x86))
                   (member-p superior-structure-paddr superior-structure-paddrs))
              (member-p e
                        (gather-qword-addresses-corresponding-to-entries-aux
                         superior-structure-paddrs x86)))
     :hints (("Goal" :in-theory (e/d* (member-p
                                       gather-qword-addresses-corresponding-to-entries-aux)
                                      ()))))

   (defthm gather-qword-addresses-corresponding-to-entries-aux-and-entries
     (implies (member-p e
                        (gather-qword-addresses-corresponding-to-entries-aux
                         superior-structure-paddrs x86))
              (member-p e
                        (gather-qword-addresses-corresponding-to-entries
                         superior-structure-paddrs x86)))
     :hints (("Goal" :in-theory (e/d* (member-p
                                       gather-qword-addresses-corresponding-to-entries)
                                      ()))))


   (local
    (defthm member-p-after-remove-duplicates-equal-of-superior-paddrs-in-gather-qword-addresses-corresponding-to-entries-aux-1
      (implies (member-p e (gather-qword-addresses-corresponding-to-entries-aux (remove-duplicates-equal superior-structure-paddrs) x86))
               (member-p e (gather-qword-addresses-corresponding-to-entries-aux superior-structure-paddrs x86)))
      :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries-aux member-p) ())))))

   (local
    (defthm member-p-after-remove-duplicates-equal-of-superior-paddrs-in-gather-qword-addresses-corresponding-to-entries-aux-2
      (implies (member-p e (gather-qword-addresses-corresponding-to-entries-aux superior-structure-paddrs x86))
               (member-p e (gather-qword-addresses-corresponding-to-entries-aux (remove-duplicates-equal superior-structure-paddrs) x86)))
      :hints (("Goal"
               :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries-aux member-p)
                                (member-p-when-gather-qword-addresses-corresponding-to-1-entry-then-member-p-entries-aux)))
              ("Subgoal *1/2"
               ;; Ugh.
               :use ((:instance member-p-when-gather-qword-addresses-corresponding-to-1-entry-then-member-p-entries-aux
                                (e e)
                                (superior-structure-paddr (car superior-structure-paddrs))
                                (superior-structure-paddrs (cdr superior-structure-paddrs))))
               :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries-aux member-p)
                                (member-p-when-gather-qword-addresses-corresponding-to-1-entry-then-member-p-entries-aux))))))

   (defthm member-p-after-remove-duplicates-equal-of-superior-paddrs-in-gather-qword-addresses-corresponding-to-entries-aux
     (iff (member-p e (gather-qword-addresses-corresponding-to-entries-aux (remove-duplicates-equal superior-structure-paddrs) x86))
          (member-p e (gather-qword-addresses-corresponding-to-entries-aux superior-structure-paddrs x86))))))

;; ======================================================================

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm <=-logior
    (and (implies (and (natp x) (natp y))
                  (<= y (logior x y)))
         (implies (and (natp x) (natp y))
                  (<= x (logior x y))))
    :rule-classes :linear))

(local
 (defthm pml4-table-entry-addr-is-at-the-first-level
   (implies (and (equal base-addr (pml4-table-base-addr x86))
                 (canonical-address-p lin-addr))
            (member-p (pml4-table-entry-addr lin-addr base-addr)
                      (gather-pml4-table-qword-addresses x86)))
   :hints (("Goal"
            :in-theory (e/d* (pml4-table-entry-addr
                              gather-pml4-table-qword-addresses
                              member-p
                              cr3bits->pdb)
                             ())))))

(defthm pml4-table-entry-addr-is-a-member-of-gather-all-paging-structure-qword-addresses
  (implies (and (equal base-addr (pml4-table-base-addr x86))
                (canonical-address-p lin-addr))
           (member-p (pml4-table-entry-addr lin-addr base-addr)
                     (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
                            (gather-pml4-table-qword-addresses)))))

;; ======================================================================

(local
 (defthm page-dir-ptr-table-entry-addr-is-at-the-second-level
   (implies
    (and (canonical-address-p lin-addr)
         (equal base-addr (page-dir-ptr-table-base-addr lin-addr x86))
         ;; The following hyps are not needed when an
         ;; over-approximation of paging addresses is collected
         ;; instead.
         ;; (equal
         ;;  (page-present
         ;;   (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
         ;;  1)
         (equal
          (page-size
           (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
          0))
    (member-p (page-dir-ptr-table-entry-addr lin-addr base-addr)
              (gather-qword-addresses-corresponding-to-entries-aux
               (gather-pml4-table-qword-addresses x86)
               x86)))
   :hints (("Goal"
            :use
            ((:instance pml4-table-entry-addr-is-a-member-of-gather-all-paging-structure-qword-addresses
                        (base-addr (pml4-table-base-addr x86)))
             (:instance member-p-when-gather-qword-addresses-corresponding-to-1-entry-then-member-p-entries-aux
                        (e (page-dir-ptr-table-entry-addr
                            lin-addr
                            (page-dir-ptr-table-base-addr lin-addr x86)))
                        (superior-structure-paddr
                         (pml4-table-entry-addr
                          lin-addr (pml4-table-base-addr x86)))
                        (superior-structure-paddrs (gather-pml4-table-qword-addresses x86))))
            :in-theory (e/d* (page-dir-ptr-table-entry-addr
                              gather-all-paging-structure-qword-addresses
                              gather-qword-addresses-corresponding-to-entries
                              gather-qword-addresses-corresponding-to-entries-aux
                              member-p
                              cr3bits->pdb
                              ia32e-page-tablesbits->reference-addr)
                             (pml4-table-entry-addr-is-a-member-of-gather-all-paging-structure-qword-addresses
                              member-p-when-gather-qword-addresses-corresponding-to-1-entry-then-member-p-entries-aux))))))

(defthm page-dir-ptr-table-entry-addr-is-a-member-of-gather-all-paging-structure-qword-addresses
  (implies
   (and (equal base-addr (page-dir-ptr-table-base-addr lin-addr x86))
        ;; The following two hyps are not needed when an
        ;; over-approximation of paging addresses is collected
        ;; instead.
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
         0)
        (canonical-address-p lin-addr))
   (member-p (page-dir-ptr-table-entry-addr lin-addr base-addr)
             (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal" :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
                                   ()))))

;; ======================================================================

(local
 (defthm page-directory-entry-addr-is-at-the-third-level
   (implies
    (and (equal base-addr (page-directory-base-addr lin-addr x86))
         ;; The following four hyps are not needed when an
         ;; over-approximation of paging addresses is collected
         ;; instead.
         ;; (equal
         ;;  (page-present
         ;;   (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
         ;;  1)
         (equal
          (page-size
           (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
          0)
         ;; (equal
         ;;  (page-present
         ;;   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
         ;;  1)
         (equal
          (page-size
           (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
          0)
         (canonical-address-p lin-addr))
    (member-p
     (page-directory-entry-addr lin-addr base-addr)
     (gather-qword-addresses-corresponding-to-entries-aux
      (gather-qword-addresses-corresponding-to-entries-aux
       (gather-pml4-table-qword-addresses x86)
       x86)
      x86)))
   :hints (("Goal"
            :use ((:instance page-dir-ptr-table-entry-addr-is-a-member-of-gather-all-paging-structure-qword-addresses
                             (base-addr (page-dir-ptr-table-base-addr lin-addr x86)))
                  (:instance member-p-when-gather-qword-addresses-corresponding-to-1-entry-then-member-p-entries-aux
                             (e (page-directory-entry-addr
                                 lin-addr
                                 (page-directory-base-addr lin-addr x86)))
                             (superior-structure-paddr
                              (page-dir-ptr-table-entry-addr
                               lin-addr
                               (page-dir-ptr-table-base-addr lin-addr x86)))
                             (superior-structure-paddrs
                              (gather-qword-addresses-corresponding-to-entries-aux
                               (gather-pml4-table-qword-addresses x86)
                               x86))))
            :in-theory (e/d* (page-directory-entry-addr
                              gather-qword-addresses-corresponding-to-entries
                              gather-qword-addresses-corresponding-to-entries-aux
                              gather-all-paging-structure-qword-addresses
                              member-p
                              ia32e-page-tablesbits->reference-addr
                              cr3bits->pdb)
                             (member-p-when-gather-qword-addresses-corresponding-to-1-entry-then-member-p-entries-aux
                              page-dir-ptr-table-entry-addr-is-a-member-of-gather-all-paging-structure-qword-addresses))))))

(defthm page-directory-entry-addr-is-a-member-of-gather-all-paging-structure-qword-addresses
  (implies
   (and (equal base-addr (page-directory-base-addr lin-addr x86))
        ;; The following four hyps are not needed when an
        ;; over-approximation of paging addresses is collected
        ;; instead.
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
         0)
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
         0)
        (canonical-address-p lin-addr))
   (member-p
    (page-directory-entry-addr lin-addr base-addr)
    (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :use ((:instance page-directory-entry-addr-is-at-the-third-level
                            (base-addr (page-directory-base-addr lin-addr x86))))
           :in-theory (e/d* (gather-all-paging-structure-qword-addresses
                             gather-qword-addresses-corresponding-to-entries)
                            (page-directory-entry-addr-is-at-the-third-level)))))

;; ======================================================================

(local
 (defthm page-table-entry-addr-is-at-the-fourth-level
   (implies
    (and (equal base-addr (page-table-base-addr lin-addr x86))
         ;; The following six hyps are not needed when an
         ;; over-approximation of paging addresses is collected
         ;; instead.
         ;; (equal
         ;;  (page-present
         ;;   (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
         ;;  1)
         (equal
          (page-size
           (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
          0)
         ;; (equal
         ;;  (page-present
         ;;   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
         ;;  1)
         (equal
          (page-size
           (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
          0)
         ;; (equal
         ;;  (page-present
         ;;   (rm-low-64 (page-directory-entry-addr lin-addr (page-directory-base-addr lin-addr x86)) x86))
         ;;  1)
         (equal
          (page-size
           (rm-low-64 (page-directory-entry-addr lin-addr (page-directory-base-addr lin-addr x86)) x86))
          0)
         (canonical-address-p lin-addr))
    (member-p
     (page-table-entry-addr lin-addr base-addr)
     (gather-qword-addresses-corresponding-to-entries-aux
      (gather-qword-addresses-corresponding-to-entries-aux
       (gather-qword-addresses-corresponding-to-entries-aux
        (gather-pml4-table-qword-addresses x86)
        x86)
       x86)
      x86)))
   :hints (("Goal"
            :use ((:instance page-directory-entry-addr-is-a-member-of-gather-all-paging-structure-qword-addresses
                             (base-addr (page-directory-base-addr lin-addr x86)))
                  (:instance member-p-when-gather-qword-addresses-corresponding-to-1-entry-then-member-p-entries-aux
                             (e (page-table-entry-addr
                                 lin-addr
                                 (page-table-base-addr lin-addr x86)))
                             (superior-structure-paddr
                              (page-directory-entry-addr
                               lin-addr
                               (page-directory-base-addr lin-addr x86)))
                             (superior-structure-paddrs
                              (gather-qword-addresses-corresponding-to-entries-aux
                               (gather-qword-addresses-corresponding-to-entries-aux
                                (gather-pml4-table-qword-addresses x86)
                                x86)
                               x86))))
            :in-theory (e/d* (page-table-entry-addr
                              gather-qword-addresses-corresponding-to-entries
                              gather-qword-addresses-corresponding-to-entries-aux
                              gather-all-paging-structure-qword-addresses
                              member-p
                              ia32e-page-tablesbits->reference-addr
                              cr3bits->pdb)
                             (page-directory-base-addr
                              member-p-when-gather-qword-addresses-corresponding-to-1-entry-then-member-p-entries-aux
                              page-dir-ptr-table-entry-addr-is-a-member-of-gather-all-paging-structure-qword-addresses))))))

(local
 (defthm gather-qword-addresses-corresponding-to-1-entry-subsetp-equal-entries-aux
   (implies (member-equal a b)
            (subsetp-equal (gather-qword-addresses-corresponding-to-1-entry a x86)
                           (gather-qword-addresses-corresponding-to-entries-aux b x86)))
   :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries-aux)
                                    ())))))

(local
 (defthmd subsetp-equal-and-gather-qword-addresses-corresponding-to-entries-aux-1
   (implies (subsetp-equal (cons e a) b)
            (subsetp-equal
             (append (gather-qword-addresses-corresponding-to-1-entry e x86)
                     (gather-qword-addresses-corresponding-to-entries-aux a x86))
             (gather-qword-addresses-corresponding-to-entries-aux b x86)))
   :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries-aux append subsetp-equal std::set-equiv) ())))))

(local
 (defthmd subsetp-equal-and-gather-qword-addresses-corresponding-to-entries-aux-2
   (implies (subsetp-equal b (cons e a))
            (subsetp-equal
             (gather-qword-addresses-corresponding-to-entries-aux b x86)
             (append (gather-qword-addresses-corresponding-to-1-entry e x86)
                     (gather-qword-addresses-corresponding-to-entries-aux a x86))))
   :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries-aux append subsetp-equal std::set-equiv) ())))))

(local
 (defthm set-equiv-and-gather-qword-addresses-corresponding-to-entries-aux-helper
   (implies (std::set-equiv (cons e a) b)
            (std::set-equiv
             (gather-qword-addresses-corresponding-to-entries-aux b x86)
             (append (gather-qword-addresses-corresponding-to-1-entry e x86)
                     (gather-qword-addresses-corresponding-to-entries-aux a x86))))
   :hints (("Goal" :in-theory (e/d* (std::set-equiv) ())
            :use ((:instance subsetp-equal-and-gather-qword-addresses-corresponding-to-entries-aux-1)
                  (:instance subsetp-equal-and-gather-qword-addresses-corresponding-to-entries-aux-2))))))

(local
 (defthm set-equiv-and-gather-qword-addresses-corresponding-to-entries-aux-cong
   (implies (std::set-equiv a b)
            (std::set-equiv (gather-qword-addresses-corresponding-to-entries-aux a x86)
                            (gather-qword-addresses-corresponding-to-entries-aux b x86)))
   :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries-aux)
                                    ())))
   :rule-classes :congruence))

(defthm set-equiv-implies-iff-member-p-2-cong
  (implies (acl2::set-equiv x y)
           (iff (member-p a x) (member-p a y)))
  :hints (("Goal" :in-theory (e/d* (member-p-iff-member-equal) ())))
  :rule-classes :congruence)

(local
 (defthm member-p-after-remove-duplicates-equal-of-superior-paddrs-in-gather-qword-addresses-corresponding-to-entries-aux-new
   (iff
    (member-p e (gather-qword-addresses-corresponding-to-entries-aux
                 (gather-qword-addresses-corresponding-to-entries-aux
                  superior-structure-paddrs
                  x86)
                 x86))
    (member-p e (gather-qword-addresses-corresponding-to-entries-aux
                 (gather-qword-addresses-corresponding-to-entries-aux
                  (remove-duplicates-equal superior-structure-paddrs)
                  x86)
                 x86)))))

(defthm page-table-entry-addr-is-a-member-of-gather-all-paging-structure-qword-addresses
  (implies
   (and (equal base-addr (page-table-base-addr lin-addr x86))
        ;; The following six hyps are not needed when an
        ;; over-approximation of paging addresses is collected
        ;; instead.
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
         0)
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
         0)
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (page-directory-entry-addr lin-addr (page-directory-base-addr lin-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (page-directory-entry-addr lin-addr (page-directory-base-addr lin-addr x86)) x86))
         0)
        (canonical-address-p lin-addr))
   (member-p
    (page-table-entry-addr lin-addr base-addr)
    (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :do-not '(preprocess)
           :use ((:instance page-table-entry-addr-is-at-the-fourth-level
                            (base-addr (page-table-base-addr lin-addr x86)))
                 (:instance member-p-after-remove-duplicates-equal-of-superior-paddrs-in-gather-qword-addresses-corresponding-to-entries-aux-new
                            (e (page-table-entry-addr
                                lin-addr
                                (page-table-base-addr lin-addr x86)))
                            (superior-structure-paddrs
                             (gather-qword-addresses-corresponding-to-entries-aux
                              (gather-pml4-table-qword-addresses x86)
                              x86))))
           :in-theory (e/d* (gather-all-paging-structure-qword-addresses
                             gather-qword-addresses-corresponding-to-entries)
                            (page-directory-base-addr
                             page-table-entry-addr-is-at-the-fourth-level
                             member-p-after-remove-duplicates-equal-of-superior-paddrs-in-gather-qword-addresses-corresponding-to-entries-aux-new)))))

;; ----------------------------------------------------------------------

(defthm pml4-table-entry-addresses-subset-of-open-qword-paddr-list-gather-all-paging-structure-qword-addresses
  (implies (and (equal base-addr (pml4-table-base-addr x86))
                (canonical-address-p lin-addr))
           (subset-p
            (addr-range 8 (pml4-table-entry-addr lin-addr base-addr))
            (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal" :in-theory (e/d* (subset-p)
                                   ()))))

(defthm page-dir-ptr-table-entry-addresses-subset-of-open-qword-paddr-list-gather-all-paging-structure-qword-addresses
  (implies (and (equal base-addr (page-dir-ptr-table-base-addr lin-addr x86))
                ;; The following two hyps are not needed when an
                ;; over-approximation of paging addresses is collected
                ;; instead.
                ;; (equal
                ;;  (page-present
                ;;   (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
                ;;  1)
                (equal
                 (page-size
                  (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
                 0)
                (canonical-address-p lin-addr))
           (subset-p
            (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr base-addr))
            (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal" :in-theory (e/d* (subset-p)
                                   ()))))

(defthm page-directory-entry-addresses-subset-of-open-qword-paddr-list-gather-all-paging-structure-qword-addresses
  (implies
   (and (equal base-addr (page-directory-base-addr lin-addr x86))
        ;; The following four hyps are not needed when an
        ;; over-approximation of paging addresses is collected
        ;; instead.
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
         0)
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
         0)
        (canonical-address-p lin-addr))
   (subset-p
    (addr-range 8 (page-directory-entry-addr lin-addr base-addr))
    (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

(defthm page-table-entry-addresses-subset-of-open-qword-paddr-list-gather-all-paging-structure-qword-addresses
  (implies
   (and (equal base-addr (page-table-base-addr lin-addr x86))
        ;; The following six hyps are not needed when an
        ;; over-approximation of paging addresses is collected
        ;; instead.
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
         0)
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
         0)
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (page-directory-entry-addr lin-addr (page-directory-base-addr lin-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (page-directory-entry-addr lin-addr (page-directory-base-addr lin-addr x86)) x86))
         0)
        (canonical-address-p lin-addr))
   (subset-p
    (addr-range 8 (page-table-entry-addr lin-addr base-addr))
    (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal"
           :in-theory (e/d* (subset-p)
                            ()))))

;; ======================================================================
