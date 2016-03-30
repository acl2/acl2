;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "../utilities/system-level-mode/paging-defs")

(include-book "centaur/bitops/ihs-extensions" :dir :system)
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

;; ======================================================================

;; Introducing the system-level program:

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

;; Some lemmas before we can prove the effects theorem: these lemmas
;; will go into the proofs/utilities/system-level-mode/paging-defs.

;; Lemmas about canonical-address-p:

(defthm canonical-address-p-and-logext-48
  (implies (canonical-address-p a)
           (equal (logext 48 a) a))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p) ()))))

;; ----------------------------------------------------------------------

;; TODO: Move to !flgi's define.

(local
 (defthmd !flgi-open-to-xw-rflags
   ;; Rewriting (!flgi ...) to (xw :rflags ...) so that rules like
   ;; ia32e-la-to-pa-xw-rflags-not-ac can apply when trying to prove
   ;; ia32e-la-to-pa-values-and-!flgi.
   (implies (x86p x86)
            (equal (!flgi index value x86)
                   (if (equal index *iopl*)
                       (xw :rflags 0
                           (logior (ash (loghead 2 value) 12)
                                   (logand 4294955007 (xr :rflags 0 x86)))
                           x86)
                     (if (not (equal index *ac*))
                         (xw :rflags 0
                             (logior (loghead 32 (ash (loghead 1 value) (nfix index)))
                                     (logand (xr :rflags 0 x86)
                                             (loghead 32 (lognot (expt 2 (nfix index))))))
                             x86)
                       (!flgi index value x86)))))
   :hints (("Goal" :in-theory (e/d* (!flgi) ())))))

;; TODO: Move to ia32e-la-to-pa's define:

(local
 (defthmd ia32e-la-to-pa-values-and-!flgi-helper
   ;; The RHS from !flgi-and-xw-rflags satisfies the hyps of ia32e-la-to-pa-xw-rflags-not-ac
   (and (equal (rflags-slice :ac (logior (ash (loghead 2 value) 12) (logand 4294955007 rflags)))
               (rflags-slice :ac rflags))
        (implies
         (and (not (equal index *ac*))
              (not (equal index *iopl*)))
         (equal (rflags-slice :ac (logior (loghead 32 (ash (loghead 1 value) (nfix index)))
                                          (logand rflags (loghead 32 (lognot (expt 2 (nfix index)))))))
                (rflags-slice :ac rflags))))
   :hints ((bitops::logbitp-reasoning))))

(defthm ia32e-la-to-pa-values-and-!flgi
  (implies (and (not (equal index *ac*))
                (x86p x86))
           (and (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (!flgi index value x86)))
                       (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (!flgi index value x86)))
                       (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))))
  :hints (("Goal"
           :cases ((equal index *iopl*))
           :use ((:instance ia32e-la-to-pa-values-and-!flgi-helper
                            (index index)
                            (rflags (xr :rflags 0 x86)))
                 (:instance ia32e-la-to-pa-xw-rflags-not-ac
                            (value (logior (loghead 32 (ash (loghead 1 value) (nfix index)))
                                           (logand (xr :rflags 0 x86)
                                                   (loghead 32 (lognot (expt 2 (nfix index))))))))
                 (:instance ia32e-la-to-pa-xw-rflags-not-ac
                            (value (logior (ash (loghead 2 value) 12)
                                           (logand 4294955007 (xr :rflags 0 x86))))))
           :in-theory (e/d* (!flgi-open-to-xw-rflags)
                            (ia32e-la-to-pa-xw-rflags-not-ac)))))

(defthm ia32e-la-to-pa-values-and-!flgi-undefined
  (implies (and (not (equal index *ac*))
                (x86p x86))
           (and (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (!flgi-undefined index x86)))
                       (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (!flgi-undefined index x86)))
                       (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))))
  :hints (("Goal" :in-theory (e/d* (!flgi-undefined) ()))))

;; TODO: Move to las-to-pas's define.

(defthm las-to-pas-values-and-!flgi
  (implies (and (not (equal index *ac*))
                (not (page-structure-marking-mode x86))
                (x86p x86))
           (and (equal (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (!flgi index value x86)))
                       (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                (equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (!flgi index value x86)))
                       (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86))))))

(defthm las-to-pas-values-and-!flgi-undefined
  (implies (and (not (equal index *ac*))
                (not (page-structure-marking-mode x86))
                (x86p x86))
           (and (equal (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (!flgi-undefined index x86)))
                       (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                (equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (!flgi-undefined index x86)))
                       (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))))
  :hints (("Goal" :in-theory (e/d* (!flgi-undefined) ()))))

;; TODO: Move to rb's define:

(defthm len-of-rb-in-system-level-mode
  (implies (and (not (mv-nth 0 (las-to-pas l-addrs r-w-x (cpl x86) x86)))
                (not (xr :programmer-level-mode 0 x86)))
           (equal (len (mv-nth 1 (rb l-addrs r-w-x x86))) (len l-addrs)))
  :hints (("Goal" :in-theory (e/d* (rb) (force (force))))))

(defthm rb-values-and-!flgi
  (implies (and (not (equal index *ac*))
                (not (page-structure-marking-mode x86))
                (not (programmer-level-mode x86))
                (x86p x86))
           (and (equal (mv-nth 0 (rb lin-addr r-w-x (!flgi index value x86)))
                       (mv-nth 0 (rb lin-addr r-w-x x86)))
                (equal (mv-nth 1 (rb lin-addr r-w-x (!flgi index value x86)))
                       (mv-nth 1 (rb lin-addr r-w-x x86)))))
  :hints (("Goal" :in-theory (e/d* (rb) ()))))

(defthm rb-values-and-!flgi-undefined
  (implies (and (not (equal index *ac*))
                (not (page-structure-marking-mode x86))
                (not (programmer-level-mode x86))
                (x86p x86))
           (and (equal (mv-nth 0 (rb lin-addr r-w-x (!flgi-undefined index x86)))
                       (mv-nth 0 (rb lin-addr r-w-x x86)))
                (equal (mv-nth 1 (rb lin-addr r-w-x (!flgi-undefined index x86)))
                       (mv-nth 1 (rb lin-addr r-w-x x86)))))
  :hints (("Goal" :in-theory (e/d* (!flgi-undefined) ()))))

;; TODO: Move to wb's define:

(defthm mv-nth-1-wb-and-!flgi-commute
  (implies (and (not (equal index *ac*))
                (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 1 (wb addr-lst (!flgi index val x86)))
                  (!flgi index val (mv-nth 1 (wb addr-lst x86)))))
  :hints (("Goal" :in-theory (e/d* (!flgi
                                    ia32e-la-to-pa-values-and-!flgi-helper
                                    !flgi-open-to-xw-rflags)
                                   (force (force))))))

(defthm mv-nth-1-wb-and-!flgi-undefined-commute
  (implies (and (not (equal index *ac*))
                (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 1 (wb addr-lst (!flgi-undefined index x86)))
                  (!flgi-undefined index (mv-nth 1 (wb addr-lst x86)))))
  :hints (("Goal" :in-theory (e/d* (!flgi-undefined) ()))))

(defthm xr-fault-wb-in-system-level-mode
  (implies (and (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (page-structure-marking-mode x86)))
           (equal (xr :fault 0 (mv-nth 1 (wb addr-lst x86)))
                  (xr :fault 0 x86)))
  :hints
  (("Goal" :in-theory (e/d* (wb)
                            (write-to-physical-memory force (force))))))

(defthm wb-not-consp-addr-lst
  (implies (not (consp addr-lst))
           (equal (mv-nth 1 (wb addr-lst x86))
                  x86))
  :hints (("Goal" :in-theory (e/d* (wb) (force (force))))))

(defthm xr-mem-wb-in-system-level-mode
  (implies (and (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (disjoint-p (list index)
                            (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (page-structure-marking-mode x86))
                (not (programmer-level-mode x86)))
           (equal (xr :mem index (mv-nth 1 (wb addr-lst x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (wb disjoint-p member-p)
                                   (write-to-physical-memory
                                    (:meta acl2::mv-nth-cons-meta)
                                    force (force))))))

;; TODO: Move to alignment-checking-enabled-p's define:

(defthm alignment-checking-enabled-p-and-mv-nth-1-wb
  (equal (alignment-checking-enabled-p (mv-nth 1 (wb addr-lst x86)))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (e/d* (alignment-checking-enabled-p
                                    wb
                                    write-to-physical-memory
                                    flgi)
                                   (member-p-strip-cars-of-remove-duplicate-keys)))))

;; TODO: Move to paging-defs.

(defthm rm-low-32-wb-in-system-level-mode
  (implies (and (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (disjoint-p (addr-range 4 index)
                            (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (page-structure-marking-mode x86)))
           (equal (rm-low-32 index (mv-nth 1 (wb addr-lst x86)))
                  (rm-low-32 index x86)))
  :hints (("Goal" :in-theory (e/d* (rm-low-32 disjoint-p member-p)
                                   (write-to-physical-memory
                                    (:meta acl2::mv-nth-cons-meta)
                                    force (force))))))

;; TODO: Remove these two DUMB opener lemmas about addr-range.

(local
 (defthmd open-addr-range-4
   (implies (integerp x)
            (equal (addr-range 4 x)
                   (list x (+ 1 x) (+ 2 x) (+ 3 x))))))

(local
 (defthmd open-addr-range-8
   (implies (integerp x)
            (equal (addr-range 8 x)
                   (list x (+ 1 x) (+ 2 x) (+ 3 x)
                         (+ 4 x) (+ 5 x) (+ 6 x) (+ 7 x))))))

(defthm rm-low-64-wb-in-system-level-mode
  (implies (and (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (disjoint-p (addr-range 8 index)
                            (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (page-structure-marking-mode x86))
                (integerp index))
           (equal (rm-low-64 index (mv-nth 1 (wb addr-lst x86)))
                  (rm-low-64 index x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (rm-low-64
                             disjoint-p
                             open-addr-range-8
                             open-addr-range-4)
                            (write-to-physical-memory
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm mv-nth-0-paging-entry-no-page-fault-p-and-mv-nth-1-wb
  (equal (mv-nth 0
                 (paging-entry-no-page-fault-p
                  structure-type lin-addr
                  entry u/s-acc r/w-acc x/d-acc wp
                  smep smap ac nxe r-w-x cpl
                  (mv-nth 1 (wb addr-lst x86))
                  access-type))
         (mv-nth 0
                 (paging-entry-no-page-fault-p
                  structure-type lin-addr
                  entry u/s-acc r/w-acc x/d-acc wp
                  smep smap ac nxe r-w-x cpl x86
                  access-type)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (page-fault-exception
                             paging-entry-no-page-fault-p)
                            (wb
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-page-table-values-and-mv-nth-1-wb
  (implies (and (equal cpl (cpl x86))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (disjoint-p
                 (translation-governing-addresses-for-page-table lin-addr base-addr x86)
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (not (page-structure-marking-mode x86))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (and
            (equal (mv-nth 0
                           (ia32e-la-to-pa-page-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 0
                           (ia32e-la-to-pa-page-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))
            (equal (mv-nth 1
                           (ia32e-la-to-pa-page-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 1
                           (ia32e-la-to-pa-page-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-table)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-page-directory-values-and-mv-nth-1-wb
  (implies (and (equal cpl (cpl x86))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (disjoint-p
                 (translation-governing-addresses-for-page-directory lin-addr base-addr x86)
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (not (page-structure-marking-mode x86))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (and
            (equal (mv-nth 0
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 0
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))
            (equal (mv-nth 1
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 1
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-directory)
                            (wb
                             translation-governing-addresses-for-page-table
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-page-dir-ptr-table-values-and-mv-nth-1-wb
  (implies (and (equal cpl (cpl x86))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table lin-addr base-addr x86)
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (not (page-structure-marking-mode x86))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (and
            (equal (mv-nth 0
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 0
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))
            (equal (mv-nth 1
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 1
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-dir-ptr-table)
                            (wb
                             translation-governing-addresses-for-page-directory
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-pml4-table-values-and-mv-nth-1-wb
  (implies (and (equal cpl (cpl x86))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (disjoint-p
                 (translation-governing-addresses-for-pml4-table lin-addr base-addr x86)
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (not (page-structure-marking-mode x86))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (and
            (equal (mv-nth 0
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl
                            (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 0
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86)))
            (equal (mv-nth 1
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl
                            (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 1
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-pml4-table)
                            (wb
                             translation-governing-addresses-for-page-dir-ptr-table
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-values-and-mv-nth-1-wb
  (implies (and (equal cpl (cpl x86))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (disjoint-p (translation-governing-addresses lin-addr x86)
                            (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (not (page-structure-marking-mode x86))
                (canonical-address-p lin-addr))
           (and
            (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
            (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa)
                            (wb
                             translation-governing-addresses-for-pml4-table
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm la-to-pas-values-and-mv-nth-1-wb
  (implies (and (equal cpl (cpl x86))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (disjoint-p (all-translation-governing-addresses l-addrs x86)
                            (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (not (page-structure-marking-mode x86))
                (canonical-address-listp l-addrs))
           (and
            (equal (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
            (equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))))
  :hints (("Goal"
           :induct (all-translation-governing-addresses l-addrs x86)
           :in-theory (e/d* ()
                            (wb
                             translation-governing-addresses
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

;; ----------------------------------------------------------------------

;; TODO: Move to paging-defs and disable
;; translation-governing-addresses there.

(defun find-l-addrs-from-fn
  (fn l-addrs-var mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-calls-lst fn (acl2::mfc-clause mfc)))
       ((when (not calls))
        ;; fn term not encountered.
        nil)
       (l-addrs (get-subterm-from-list-of-terms 1 calls))
       (alst-lst (make-bind-free-alist-lists l-addrs-var l-addrs)))
    alst-lst))

(defthm disjointness-of-translation-governing-addresses-from-all-translation-governing-addresses
  (implies (and (bind-free
                 (find-l-addrs-from-fn 'all-translation-governing-addresses 'l-addrs mfc state)
                 (l-addrs))
                (disjoint-p (all-translation-governing-addresses l-addrs x86) other-p-addrs)
                (member-p lin-addr l-addrs))
           (disjoint-p (translation-governing-addresses lin-addr x86) other-p-addrs))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

(in-theory (e/d* () (translation-governing-addresses)))

(defthm disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
  (implies (and (bind-free
                 (find-l-addrs-from-fn 'all-translation-governing-addresses 'l-addrs mfc state)
                 (l-addrs))
                (syntaxp (not (eq l-addrs-subset l-addrs)))
                (disjoint-p (all-translation-governing-addresses l-addrs x86) other-p-addrs)
                (subset-p l-addrs-subset l-addrs))
           (disjoint-p (all-translation-governing-addresses l-addrs-subset x86) other-p-addrs))
  :hints (("Goal" :in-theory (e/d* (subset-p member-p) ()))))

(defthm translation-governing-addresses-and-!flgi
  (equal (translation-governing-addresses lin-addr (!flgi index value x86))
         (translation-governing-addresses lin-addr x86))
  :hints (("Goal" :in-theory (e/d* (!flgi) (translation-governing-addresses force (force))))))

(defthm translation-governing-addresses-and-!flgi-undefined
  (equal (translation-governing-addresses lin-addr (!flgi-undefined index x86))
         (translation-governing-addresses lin-addr x86))
  :hints (("Goal" :in-theory (e/d* (!flgi-undefined) (translation-governing-addresses force (force))))))

(defthm all-translation-governing-addresses-and-!flgi
  (equal (all-translation-governing-addresses l-addrs (!flgi index value x86))
         (all-translation-governing-addresses l-addrs x86))
  :hints (("Goal" :in-theory (e/d* () (force (force))))))

(defthm all-translation-governing-addresses-and-!flgi-undefined
  (equal (all-translation-governing-addresses l-addrs (!flgi-undefined index x86))
         (all-translation-governing-addresses l-addrs x86))
  :hints (("Goal" :in-theory (e/d* () (force (force))))))

(defthm translation-governing-addresses-and-write-to-physical-memory-disjoint
  (implies (and (disjoint-p (translation-governing-addresses lin-addr x86) p-addrs)
                (physical-address-listp p-addrs))
           (equal (translation-governing-addresses lin-addr (write-to-physical-memory p-addrs bytes x86))
                  (translation-governing-addresses lin-addr x86)))
  :hints (("Goal" :induct (write-to-physical-memory p-addrs bytes x86)
           :in-theory (e/d* (disjoint-p disjoint-p-commutative) (translation-governing-addresses)))))

(defthm translation-governing-addresses-and-mv-nth-1-wb-disjoint-p
  (implies (and (disjoint-p
                 (translation-governing-addresses lin-addr x86)
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86))
                (x86p x86))
           (equal (translation-governing-addresses lin-addr (mv-nth 1 (wb addr-lst x86)))
                  (translation-governing-addresses lin-addr x86)))
  :hints (("Goal" :in-theory (e/d* (disjoint-p wb) ()))))

(defthm all-translation-governing-addresses-and-mv-nth-1-wb-disjoint
  (implies (and (disjoint-p
                 (all-translation-governing-addresses l-addrs x86)
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86))
                (x86p x86))
           (equal (all-translation-governing-addresses l-addrs (mv-nth 1 (wb addr-lst x86)))
                  (all-translation-governing-addresses l-addrs x86)))
  :hints (("Goal"
           :in-theory (e/d* (all-translation-governing-addresses) ())
           :induct (all-translation-governing-addresses l-addrs x86))))

;; ----------------------------------------------------------------------

;; TODO: Move to /machine/x86-top-level-memory.lisp inside the
;; program-at define.

(defthm program-at-xw-in-system-level-mode
  (implies (and (not (programmer-level-mode x86))
                (not (equal fld :mem))
                (not (equal fld :rflags))
                (not (equal fld :ctr))
                (not (equal fld :seg-visible))
                (not (equal fld :msr))
                (not (equal fld :fault))
                (not (equal fld :programmer-level-mode))
                (not (equal fld :page-structure-marking-mode)))
           (equal (program-at l-addrs bytes (xw fld index value x86))
                  (program-at l-addrs bytes x86)))
  :hints (("Goal" :in-theory (e/d* (program-at) ()))))

(defthm program-at-xw-rflags-not-ac-values-in-system-level-mode
  (implies (and (not (programmer-level-mode x86))
                (equal (rflags-slice :ac value)
                       (rflags-slice :ac (rflags x86))))
           (equal (program-at l-addrs bytes (xw :rflags 0 value x86))
                  (program-at l-addrs bytes x86)))
  :hints (("Goal" :in-theory (e/d* (program-at) ()))))

(defthm program-at-values-and-!flgi
  (implies (and (not (equal index *ac*))
                (not (page-structure-marking-mode x86))
                (not (programmer-level-mode x86))
                (x86p x86))
           (equal (program-at l-addrs bytes (!flgi index value x86))
                  (program-at l-addrs bytes x86)))
  :hints (("Goal" :in-theory (e/d* (program-at) ()))))

(defthm program-at-values-and-!flgi-undefined
  (implies (and (not (equal index *ac*))
                (not (page-structure-marking-mode x86))
                (not (programmer-level-mode x86))
                (x86p x86))
           (equal (program-at l-addrs bytes (!flgi-undefined index x86))
                  (program-at l-addrs bytes x86)))
  :hints (("Goal" :in-theory (e/d* (program-at) ()))))

;; ----------------------------------------------------------------------

;; TODO: Move to paging-defs.

(defthmd r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x-1 cpl x86)))
                (syntaxp (not (eq r-w-x-2 r-w-x-1)))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x-2 cpl x86))))
           (equal (mv-nth 1
                          (ia32e-la-to-pa-page-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x-2 cpl x86))
                  (mv-nth 1
                          (ia32e-la-to-pa-page-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x-1 cpl x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-table)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-directory-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-directory
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x-1 cpl x86)))
                (syntaxp (not (eq r-w-x-2 r-w-x-1)))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-directory
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x-2 cpl x86))))
           (equal (mv-nth 1
                          (ia32e-la-to-pa-page-directory
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x-2 cpl x86))
                  (mv-nth 1
                          (ia32e-la-to-pa-page-directory
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x-1 cpl x86))))
  :hints (("Goal"
           :use ((:instance r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr (ash
                                        (loghead
                                         40
                                         (logtail
                                          12
                                          (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                                (logand 18446744073709547520
                                                                                        (loghead 52 base-addr)))
                                                     x86)))
                                        12))
                            (u/s-acc (logand
                                      u/s-acc
                                      (page-user-supervisor
                                       (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                             (logand 18446744073709547520
                                                                                     (loghead 52 base-addr)))
                                                  x86))))
                            (r/w-acc (logand
                                      r/w-acc
                                      (page-read-write
                                       (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                             (logand 18446744073709547520
                                                                                     (loghead 52 base-addr)))
                                                  x86))))
                            (x/d-acc
                             (logand
                              x/d-acc
                              (page-execute-disable
                               (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                     (logand 18446744073709547520
                                                                             (loghead 52 base-addr)))
                                          x86))))))
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-directory)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-dir-ptr-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x-1 cpl x86)))
                (syntaxp (not (eq r-w-x-2 r-w-x-1)))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x-2 cpl x86))))
           (equal (mv-nth 1
                          (ia32e-la-to-pa-page-dir-ptr-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x-2 cpl x86))
                  (mv-nth 1
                          (ia32e-la-to-pa-page-dir-ptr-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x-1 cpl x86))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-directory-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr (ash
                                        (loghead
                                         40
                                         (logtail
                                          12
                                          (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                                    (logand 18446744073709547520
                                                                                            (loghead 52 base-addr)))
                                                     x86)))
                                        12))
                            (u/s-acc (logand
                                      u/s-acc
                                      (page-user-supervisor
                                       (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                                 (logand 18446744073709547520
                                                                                         (loghead 52 base-addr)))
                                                  x86))))
                            (r/w-acc (logand
                                      r/w-acc
                                      (page-read-write
                                       (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                                 (logand 18446744073709547520
                                                                                         (loghead 52 base-addr)))
                                                  x86))))
                            (x/d-acc
                             (logand
                              x/d-acc
                              (page-execute-disable
                               (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                         (logand 18446744073709547520
                                                                                 (loghead 52 base-addr)))
                                          x86))))))
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-dir-ptr-table)
                            (r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-table-when-no-errors
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-pml4-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-pml4-table
                              lin-addr base-addr wp smep smap ac nxe r-w-x-1 cpl x86)))
                (syntaxp (not (eq r-w-x-2 r-w-x-1)))
                (not (mv-nth 0
                             (ia32e-la-to-pa-pml4-table
                              lin-addr base-addr wp smep smap ac nxe r-w-x-2 cpl x86))))
           (equal (mv-nth 1
                          (ia32e-la-to-pa-pml4-table
                           lin-addr base-addr wp smep smap ac nxe r-w-x-2 cpl x86))
                  (mv-nth 1
                          (ia32e-la-to-pa-pml4-table
                           lin-addr base-addr wp smep smap ac nxe r-w-x-1 cpl x86))))
  :hints (("Goal"
           :use ((:instance r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-dir-ptr-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr (ash
                                        (loghead
                                         40
                                         (logtail
                                          12
                                          (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr)
                                                                            (logand 18446744073709547520
                                                                                    (loghead 52 base-addr)))
                                                     x86)))
                                        12))
                            (u/s-acc (page-user-supervisor
                                      (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr)
                                                                        (logand 18446744073709547520
                                                                                (loghead 52 base-addr)))
                                                 x86)))
                            (r/w-acc (page-read-write
                                      (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr)
                                                                        (logand 18446744073709547520
                                                                                (loghead 52 base-addr)))
                                                 x86)))
                            (x/d-acc
                             (page-execute-disable
                              (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr)
                                                                (logand 18446744073709547520
                                                                        (loghead 52 base-addr)))
                                         x86)))))
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-pml4-table)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defun find-almost-matching-ia32e-la-to-pas-aux (free-r-w-x-var new-arg-lists original-arg-list)
  (if (endp new-arg-lists)
      nil
    (b* ((new-arg-list (car new-arg-lists))
         (matching? (and (equal (first new-arg-list)  (first original-arg-list)) ;; lin-addr
                         (not (equal (second new-arg-list) (second original-arg-list))) ;; r-w-x
                         (equal (third new-arg-list)  (third original-arg-list)) ;; cpl
                         (equal (fourth new-arg-list) (fourth original-arg-list))))) ;; x86
      (if matching?
          (cons (acons free-r-w-x-var ;; original r-w-x
                       (second new-arg-list)
                       nil)
                (find-almost-matching-ia32e-la-to-pas-aux free-r-w-x-var (cdr new-arg-lists) original-arg-list))
        (find-almost-matching-ia32e-la-to-pas-aux free-r-w-x-var (cdr new-arg-lists) original-arg-list)))))

(defun find-almost-matching-ia32e-la-to-pas
  (fn-name free-r-w-x-var original-arg-list mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-calls-lst fn-name (acl2::mfc-clause mfc)))
       ((when (not calls))
        ;; ia32e-la-to-pa term not encountered.
        nil)
       (new-arg-lists (strip-cdrs calls)))
    (find-almost-matching-ia32e-la-to-pas-aux free-r-w-x-var new-arg-lists original-arg-list)))

(defthm r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-when-no-errors
  (implies (and (bind-free (find-almost-matching-ia32e-la-to-pas
                            'ia32e-la-to-pa 'r-w-x-1
                            (list lin-addr r-w-x-2 cpl x86) mfc state)
                           (r-w-x-1))
                (syntaxp (and
                          ;; The bind-free ensures that r-w-x-2 and
                          ;; r-w-x-1 are unequal, but I'll still leave
                          ;; this thing in.
                          (not (eq r-w-x-2 r-w-x-1))
                          ;; r-w-x-2 must be smaller than r-w-x-1.
                          (term-order r-w-x-2 r-w-x-1)))
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x-1 cpl x86)))
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x-2 cpl x86))))
           (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x-2 cpl x86))
                  (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x-1 cpl x86))))
  :hints (("Goal"
           :use ((:instance r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-pml4-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))
                            (wp (bool->bit (logbitp 16 (xr :ctr *cr0* x86))))
                            (smep (loghead 1 (bool->bit (logbitp 20 (xr :ctr *cr4* x86)))))
                            (smap 0)
                            (ac (bool->bit (logbitp 18 (xr :rflags 0 x86))))
                            (nxe (loghead 1 (bool->bit (logbitp 11 (xr :msr *ia32_efer-idx* x86)))))))
           :in-theory (e/d* (ia32e-la-to-pa) ()))))

(defthm r-w-x-is-irrelevant-for-mv-nth-1-las-to-pas-when-no-errors
  (implies (and (bind-free (find-almost-matching-ia32e-la-to-pas
                            'las-to-pas 'r-w-x-1 (list l-addrs r-w-x-2 cpl x86) mfc state)
                           (r-w-x-1))
                (syntaxp (and
                          ;; The bind-free ensures that r-w-x-2 and
                          ;; r-w-x-1 are unequal, but I'll still leave
                          ;; this thing in.
                          (not (eq r-w-x-2 r-w-x-1))
                          ;; r-w-x-2 must be smaller than r-w-x-1.
                          (term-order r-w-x-2 r-w-x-1)))
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x-1 cpl x86)))
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x-2 cpl x86)))
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 1 (las-to-pas l-addrs r-w-x-2 cpl x86))
                  (mv-nth 1 (las-to-pas l-addrs r-w-x-1 cpl x86))))
  :hints (("Goal" :in-theory (e/d* (r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-when-no-errors)
                                   ()))))

(defthmd las-to-pas-subset-p
  ;; This is a pretty expensive rule --- a more general version of
  ;; las-to-pas-subset-p-with-l-addrs-from-bind-free.
  (implies (and (bind-free
                 (find-l-addrs-from-fn 'las-to-pas 'l-addrs mfc state)
                 (l-addrs))
                (syntaxp (not (eq l-addrs-subset l-addrs)))
                (subset-p l-addrs-subset l-addrs)
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 0 (las-to-pas l-addrs-subset r-w-x cpl x86))
                  nil))
  :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

(defthm las-to-pas-subset-p-with-l-addrs-from-bind-free
  ;; This rule will help in fetching instructions.
  (implies (and (bind-free
                 (find-l-addrs-from-fn 'program-at 'l-addrs mfc state)
                 (l-addrs))
                (syntaxp (not (eq l-addrs-subset l-addrs)))
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                (subset-p l-addrs-subset l-addrs)
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 0 (las-to-pas l-addrs-subset r-w-x cpl x86))
                  nil))
  :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

;; ----------------------------------------------------------------------


;; ======================================================================

;; General lemmas:

(defthm loghead-negative
  (implies (and (syntaxp (and (quotep n)
                              (< (cadr n) 0)))
                (< n 0)
                (integerp n))
           (equal (loghead n x) 0)))

;; ======================================================================

;; Stuff to prove rewire_dst_to_src effects theorem:

;; (acl2::why x86-run-opener-not-ms-not-zp-n)
;; (acl2::why x86-fetch-decode-execute-opener)
;; (acl2::why get-prefixes-opener-lemma-no-prefix-byte)
;; (acl2::why ia32e-la-to-pa-values-and-mv-nth-1-wb)
;; (acl2::why rb-in-terms-of-nth-and-pos-in-system-level-non-marking-mode)
;; (acl2::why combine-bytes-rb-in-terms-of-rb-subset-p-in-system-level-non-marking-mode)
;; (acl2::why program-at-wb-disjoint-in-system-level-non-marking-mode)
;; (acl2::why rb-wb-disjoint-in-system-level-non-marking-mode)
;; (acl2::why disjointness-of-translation-governing-addresses-from-all-translation-governing-addresses)
;; (acl2::why la-to-pas-values-and-mv-nth-1-wb)

;; Argh, ACL2's default ancestors-check is killing me --- it prevents
;; program-at-wb-disjoint-in-system-level-non-marking-mode from being
;; used. So, I'm going to use Sol's trivial ancestors-check version.
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))

;; TODO: Should I move this to machine/ia32e-paging and use it
;; elsewhere? I'd need to define other table's base addresses as well.
;; Anyway, maybe I should disable pml4-table-base-addr and
;; page-dir-ptr-table-base-addr everywhere.
(defun pml4-table-base-addr (x86)
  (declare (xargs :stobjs x86))
  (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))

(defthm-usb n52p-of-pml4-table-base-addr
  :hyp (x86p x86)
  :bound 52
  :concl (pml4-table-base-addr x86))

(defthm pml4-table-base-addr-and-mv-nth-1-wb
  (equal (pml4-table-base-addr (mv-nth 1 (wb addr-lst x86)))
         (pml4-table-base-addr x86)))

(defun-nx page-dir-ptr-table-base-addr (lin-addr x86)
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
;; page-dir-ptr-table-base-addr enabled.
(defthm unsigned-byte-p-52-of-left-shifting-a-40-bit-vector-by-12
  (implies (unsigned-byte-p 64 x)
           (unsigned-byte-p 52 (ash (loghead 40 (logtail 12 x)) 12))))

(defthm page-dir-ptr-table-base-addr-and-mv-nth-1-wb
  (implies (and
            (disjoint-p
             (mv-nth
              1
              (las-to-pas
               (create-canonical-address-list
                8
                (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
               :r (cpl x86) x86))
             (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list
               8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
              x86)
             (mv-nth 1
                     (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
            (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
            (not (programmer-level-mode x86))
            (not (page-structure-marking-mode x86))
            (x86p x86))
           (equal (page-dir-ptr-table-base-addr lin-addr (mv-nth 1 (wb addr-lst x86)))
                  (page-dir-ptr-table-base-addr lin-addr x86)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d* () (member-p-strip-cars-of-remove-duplicate-keys)))))

(def-gl-export pml4-table-entry-addr-to-C-program-optimized-form
  :hyp (and (canonical-address-p v-addr)
            (equal (logtail 40 cr3) 0) ;; MBZ
            (unsigned-byte-p 64 cr3))
  :concl (equal (pml4-table-entry-addr v-addr (ash (loghead 40 (logtail 12 cr3)) 12))
                (logior (logand -4096 (logext 64 cr3))
                        (logand 4088 (loghead 28 (logtail 36 v-addr)))))
  :g-bindings
  (gl::auto-bindings (:mix (:nat v-addr 64) (:nat cr3 64))))

(def-gl-export page-dir-ptr-table-entry-addr-to-C-program-optimized-form
  :hyp (and (canonical-address-p v-addr)
            (equal (loghead 12 base-addr) 0)
            (unsigned-byte-p 52 base-addr))
  :concl (equal (page-dir-ptr-table-entry-addr v-addr base-addr)
                (logior (logand 4088 (loghead 32 (logtail 27 v-addr)))
                        base-addr))
  :g-bindings
  (gl::auto-bindings (:mix (:nat v-addr 64) (:nat base-addr 64))))

(def-gl-export page-dir-ptr-table-entry-P=1-and-PS=1-zf-spec-helper-1
  :hyp (and (equal (part-select entry :low 7 :width 1) 1)
            (equal (part-select entry :low 0 :width 1) 1)
            (unsigned-byte-p 64 entry))
  :concl (equal (zf-spec (loghead 64 (+ -129 (logand 129 (loghead 32 entry))))) 1)
  :g-bindings
  (gl::auto-bindings (:nat entry 64)))

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
                                        (loghead 30 destination-entry)
                                        (logand 3221225472 (loghead 32 source-entry)))))))
                1)
  :g-bindings
  (gl::auto-bindings (:mix (:nat destination-entry 64) (:nat source-entry 64))))

;; TODO: Ugh, why is this thing here? Shouldn't these two be disabled
;; earlier on or not at all
(in-theory (e/d () (las-to-pas all-translation-governing-addresses)))

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

;; TODO: Move to rb's define.
(defthm unsigned-byte-p-of-combine-bytes-and-rb-in-system-level-mode
  (implies (and (syntaxp (quotep m))
                (syntaxp (quotep n))
                (equal m (ash n 3))
                (natp n)
                (not (mv-nth 0 (las-to-pas (create-canonical-address-list n lin-addr) :r (cpl x86) x86)))
                (canonical-address-p (+ -1 n lin-addr))
                (canonical-address-p lin-addr)
                (not (xr :programmer-level-mode 0 x86))
                (x86p x86))
           (unsigned-byte-p m (combine-bytes (mv-nth 1 (rb (create-canonical-address-list n lin-addr) :r x86))))))

(defun rewire_dst_to_src-clk () 58)

(defthm rewire_dst_to_src-effects
  (implies (and
            (equal prog-len (len *rewire_dst_to_src*))
            (x86p x86)
            (not (programmer-level-mode x86))
            (not (page-structure-marking-mode x86))
            (not (alignment-checking-enabled-p x86))

            ;; CR3's reserved bits must be zero (MBZ).
            (equal (logtail 40 (ctri *cr3* x86)) 0)

            ;; Source address is canonical.
            (canonical-address-p (xr :rgf *rdi* x86))
            ;; (canonical-address-p (+ 7 (xr :rgf *rdi* x86)))
            ;; Source address is 1G-aligned.
            (equal (loghead 30 (xr :rgf *rdi* x86)) 0)
            ;; Destination address is canonical.
            (canonical-address-p (xr :rgf *rsi* x86))
            ;; (canonical-address-p (+ 7 (xr :rgf *rsi* x86)))
            ;; Destination address is 1G-aligned.
            (equal (loghead 30 (xr :rgf *rsi* x86)) 0)
            ;; Program addresses are canonical.
            (canonical-address-p (+ prog-len (xr :rip 0 x86)))
            ;; (canonical-address-p (xr :rip 0 x86))
            ;; Stack addresses are canonical.
            (canonical-address-p (+ -24 (xr :rgf *rsp* x86)))
            ;; (canonical-address-p (xr :rgf *rsp* x86))
            (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
            (equal (xr :ms 0 x86) nil)
            (equal (xr :fault 0 x86) nil)
            (equal (cpl x86) 0)
            (program-at (create-canonical-address-list prog-len (xr :rip 0 x86))
                        *rewire_dst_to_src* x86)

            ;; No errors encountered while translating the linear
            ;; addresses where the program is located.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list prog-len (xr :rip 0 x86))
                            :x (cpl x86) x86)))
            ;; Writing to stack: No errors encountered while
            ;; translating the linear addresses corresponding to the
            ;; program stack.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                            :w (cpl x86) x86)))
            ;; Reading from stack: No errors encountered while
            ;; translating the linear addresses corresponding to the
            ;; stack.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                            :r (cpl x86) x86)))
            ;; Reading from stack: The stack is located in a
            ;; contiguous region of memory --- no overlaps among
            ;; physical addresses of the stack. I need this hypothesis
            ;; so that rb-wb-equal-in-system-level-non-marking-mode
            ;; can fire.
            (no-duplicates-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                        :r (cpl x86) x86)))
            ;; The physical addresses corresponding to the program and
            ;; stack are disjoint.
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list prog-len (xr :rip 0 x86))
                        :x (cpl x86) x86))
             (mv-nth 1
                     (las-to-pas
                      (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                      :w (cpl x86) x86)))
            ;; Translation-governing addresses of the program are
            ;; disjoint from the physical addresses of the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list prog-len (xr :rip 0 x86))
              x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                        :w (cpl x86) x86)))
            ;; Translation-governing addresses of the stack are
            ;; disjoint from the physical addresses of the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
              x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                        :w (cpl x86) x86)))

            ;; ============================================================

            ;; Assumptions about the source PML4TE:

            ;; PML4TE linear addresses are canonical.
            ;; (canonical-address-p
            ;;  (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
            (canonical-address-p
             (+ 7 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))))

            ;; No errors encountered while translating the PML4TE linear addresses.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list
                             8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
                            :r (cpl x86) x86)))
            ;; The translation-governing addresses of PML4TE addresses
            ;; are disjoint from the physical addresses corresponding
            ;; to the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list
               8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
              x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
            ;; The PML4TE physical addresses are disjoint from the
            ;; stack physical addresses.
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
                        :r (cpl x86) x86))
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))

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
             1)

            ;; ------------------------------------------------------------

            ;; Assumptions about the source PDPTE:

            ;; PDPTE linear addresses are canonical.
            ;; (canonical-address-p
            ;;  (page-dir-ptr-table-entry-addr
            ;;   (xr :rgf *rdi* x86)
            ;;   (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
            (canonical-address-p
             (+ 7 (page-dir-ptr-table-entry-addr
                   (xr :rgf *rdi* x86)
                   (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86))))

            ;; No errors encountered while translating the PDPTE linear addresses.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list
                             8
                             (page-dir-ptr-table-entry-addr
                              (xr :rgf *rdi* x86)
                              (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                            :r (cpl x86) x86)))
            ;; The translation-governing addresses of PDPTE addresses
            ;; are disjoint from the physical addresses corresponding
            ;; to the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rdi* x86)
                (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
              x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
            ;; The PDPTE physical addresses are disjoint from the
            ;; stack physical addresses.
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (page-dir-ptr-table-entry-addr
                          (xr :rgf *rdi* x86)
                          (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                        :r (cpl x86) x86))
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))

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
                                (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
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
                                (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                              :r x86)))
                    :low 7 :width 1)
                   1)

            ;; ============================================================

            ;; Assumptions about the destination PML4TE:

            ;; PML4TE linear addresses are canonical.
            ;; (canonical-address-p
            ;;  (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
            (canonical-address-p
             (+ 7 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))))

            ;; No errors encountered while translating the PML4TE linear addresses.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list
                             8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
                            :r (cpl x86) x86)))
            ;; The translation-governing addresses of PML4TE addresses
            ;; are disjoint from the physical addresses corresponding
            ;; to the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list
               8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
              x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
            ;; The PML4TE physical addresses are disjoint from the
            ;; stack physical addresses.
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
                        :r (cpl x86) x86))
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))

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
             1)

            ;; ------------------------------------------------------------

            ;; Assumptions about the destination PDPTE:

            ;; PDPTE linear addresses are canonical.
            ;; (canonical-address-p
            ;;  (page-dir-ptr-table-entry-addr
            ;;   (xr :rgf *rsi* x86)
            ;;   (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
            (canonical-address-p
             (+ 7 (page-dir-ptr-table-entry-addr
                   (xr :rgf *rsi* x86)
                   (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86))))

            ;; No errors encountered while translating the PDPTE
            ;; linear addresses on behalf of a read.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list
                             8
                             (page-dir-ptr-table-entry-addr
                              (xr :rgf *rsi* x86)
                              (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                            :r (cpl x86) x86)))
            ;; No errors encountered while translating the PDPTE
            ;; linear addresses on behalf of a write.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list
                             8
                             (page-dir-ptr-table-entry-addr
                              (xr :rgf *rsi* x86)
                              (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                            :w (cpl x86) x86)))
            ;; The translation-governing addresses of PDPTE addresses
            ;; are disjoint from the physical addresses corresponding
            ;; to the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
              x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
            ;; The PDPTE physical addresses are disjoint from the
            ;; stack physical addresses.
            ;; (disjoint-p
            ;;  (mv-nth 1 (las-to-pas
            ;;             (create-canonical-address-list
            ;;              8
            ;;              (page-dir-ptr-table-entry-addr
            ;;               (xr :rgf *rsi* x86)
            ;;               (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
            ;;             :r (cpl x86) x86))
            ;;  (mv-nth 1 (las-to-pas
            ;;             (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))

            ;; The physical addresses corresponding to the program are
            ;; disjoint from those of the PDPTE (on behalf of a
            ;; write).
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list prog-len (xr :rip 0 x86))
                        :x (cpl x86) x86))
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (page-dir-ptr-table-entry-addr
                          (xr :rgf *rsi* x86)
                          (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                        :w (cpl x86) x86)))

            ;; Translation-governing addresses of the program are
            ;; disjoint from the PDPTE physical addresses (on behalf
            ;; of a write).
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list prog-len (xr :rip 0 x86))
              x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (page-dir-ptr-table-entry-addr
                          (xr :rgf *rsi* x86)
                          (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                        :w (cpl x86) x86)))
            ;; Translation-governing addresses of the stack are
            ;; disjoint from the physical addresses of the PDPTE (on
            ;; behalf of a write).
            ;; (disjoint-p
            ;;  (all-translation-governing-addresses
            ;;   (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
            ;;   x86)
            ;;  (mv-nth 1 (las-to-pas
            ;;             (create-canonical-address-list
            ;;              8
            ;;              (page-dir-ptr-table-entry-addr
            ;;               (xr :rgf *rsi* x86)
            ;;               (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
            ;;             :w (cpl x86) x86)))

            ;; Destination PDPTE does not have the P or PS bit cleared
            ;; (i.e., the entry is present and it points to a 1G
            ;; page).
            (equal (part-select
                    (combine-bytes
                     (mv-nth 1
                             (rb
                              (create-canonical-address-list
                               8
                               (page-dir-ptr-table-entry-addr
                                (xr :rgf *rsi* x86)
                                (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
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
                                (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                              :r x86)))
                    :low 7 :width 1)
                   1)

            ;; ======================================================================
            ;; For the final ret instruction:

            ;; Reading from stack for the final ret instruction
            ;; doesn't cause errors.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list 8 (xr :rgf *rsp* x86))
                            :r (cpl x86) x86)))

            ;; The program and the ret address on the stack are
            ;; disjoint.
            ;; (disjoint-p
            ;;  (mv-nth 1 (las-to-pas
            ;;             (create-canonical-address-list prog-len (xr :rip 0 x86))
            ;;             :x (cpl x86) x86))
            ;;  (mv-nth 1 (las-to-pas
            ;;             (create-canonical-address-list 8 (xr :rgf *rsp* x86))
            ;;             :r (cpl x86) x86)))

            ;; The translation-governing addresses of the ret address
            ;; are disjoint from the destination PDPTE.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list 8 (xr :rgf *rsp* x86)) x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (page-dir-ptr-table-entry-addr
                          (xr :rgf *rsi* x86)
                          (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                        :r (cpl x86) x86)))

            ;; The destination PDPTE is disjoint from the ret address
            ;; on the stack.
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (xr :rgf *rsp* x86))
                        :r (cpl x86) x86))
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (page-dir-ptr-table-entry-addr
                          (xr :rgf *rsi* x86)
                          (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                        :r (cpl x86) x86)))
            ;; The destination PDPTE is disjoint from the rest of the stack.
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (page-dir-ptr-table-entry-addr
                          (xr :rgf *rsi* x86)
                          (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                        :r (cpl x86) x86))
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))

            ;; The ret address on the stack is disjoint from the rest
            ;; of the stack.
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (xr :rgf *rsp* x86))
                        :r (cpl x86) x86))
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))

            ;; The translation-governing addresses of the return
            ;; address on the stack are disjoint from the physical
            ;; addresses of the rest of the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list 8 (xr :rgf *rsp* x86)) x86)
             (mv-nth 1
                     (las-to-pas (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                                 :w (cpl x86) x86)))

            ;; Return address on the stack is canonical.
            (canonical-address-p
             (logext 64
                     (combine-bytes
                      (mv-nth 1
                              (rb (create-canonical-address-list 8 (xr :rgf *rsp* x86))
                                  :r x86))))))

           (equal (x86-run (rewire_dst_to_src-clk) x86)
                  (xw
                   :rgf *rax* 1
                   (xw
                    :rgf *rcx*
                    (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
                    (xw
                     :rgf *rdx*
                     (logand
                      4503598553628672
                      (logior
                       (logand
                        -4503598553628673
                        (logext
                         64
                         (combine-bytes
                          (mv-nth
                           1
                           (rb
                            (create-canonical-address-list
                             8
                             (page-dir-ptr-table-entry-addr
                              (xr :rgf *rsi* x86)
                              (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                            :r x86)))))
                       (logand
                        4503598553628672
                        (logext
                         64
                         (combine-bytes
                          (mv-nth
                           1
                           (rb
                            (create-canonical-address-list
                             8
                             (page-dir-ptr-table-entry-addr
                              (xr :rgf *rdi* x86)
                              (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                            :r x86)))))))
                     (xw
                      :rgf *rsp* (+ 8 (xr :rgf *rsp* x86))
                      (xw
                       :rgf *rsi* 0
                       (xw
                        :rgf *rdi*
                        (logand
                         4503598553628672
                         (logext
                          64
                          (combine-bytes
                           (mv-nth
                            1
                            (rb
                             (create-canonical-address-list
                              8
                              (page-dir-ptr-table-entry-addr
                               (xr :rgf *rdi* x86)
                               (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                             :r x86)))))
                        (xw
                         :rgf *r8* 1099511627775
                         (xw
                          :rgf *r9*
                          (logand
                           4503598553628672
                           (logext
                            64
                            (combine-bytes
                             (mv-nth
                              1
                              (rb
                               (create-canonical-address-list
                                8
                                (page-dir-ptr-table-entry-addr
                                 (xr :rgf *rdi* x86)
                                 (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                               :r x86)))))
                          (xw
                           :rip 0
                           (logext
                            64
                            (combine-bytes
                             (mv-nth
                              1
                              (rb (create-canonical-address-list 8 (xr :rgf *rsp* x86))
                                  :r x86))))
                           (xw
                            :undef 0 (+ 46 (nfix (xr :undef 0 x86)))
                            (!flgi
                             *cf*
                             (loghead
                              1
                              (bool->bit
                               (<
                                (logand
                                 4503598553628672
                                 (combine-bytes
                                  (mv-nth
                                   1
                                   (rb
                                    (create-canonical-address-list
                                     8
                                     (page-dir-ptr-table-entry-addr
                                      (xr :rgf *rdi* x86)
                                      (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                                    :r x86))))
                                (logand
                                 4503598553628672
                                 (logior
                                  (logand
                                   18442240475155922943
                                   (combine-bytes
                                    (mv-nth
                                     1
                                     (rb
                                      (create-canonical-address-list
                                       8
                                       (page-dir-ptr-table-entry-addr
                                        (xr :rgf *rsi* x86)
                                        (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                                      :r x86))))
                                  (logand
                                   4503598553628672
                                   (combine-bytes
                                    (mv-nth
                                     1
                                     (rb
                                      (create-canonical-address-list
                                       8
                                       (page-dir-ptr-table-entry-addr
                                        (xr :rgf *rdi* x86)
                                        (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                                      :r x86)))))))))
                             (!flgi
                              *pf*
                              (pf-spec64
                               (loghead
                                64
                                (+
                                 (logand
                                  4503598553628672
                                  (logext
                                   64
                                   (combine-bytes
                                    (mv-nth
                                     1
                                     (rb
                                      (create-canonical-address-list
                                       8
                                       (page-dir-ptr-table-entry-addr
                                        (xr :rgf *rdi* x86)
                                        (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                                      :r x86)))))
                                 (-
                                  (logand
                                   4503598553628672
                                   (logior
                                    (logand
                                     -4503598553628673
                                     (logext
                                      64
                                      (combine-bytes
                                       (mv-nth
                                        1
                                        (rb
                                         (create-canonical-address-list
                                          8
                                          (page-dir-ptr-table-entry-addr
                                           (xr :rgf *rsi* x86)
                                           (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                                         :r x86)))))
                                    (logand
                                     4503598553628672
                                     (logext
                                      64
                                      (combine-bytes
                                       (mv-nth
                                        1
                                        (rb
                                         (create-canonical-address-list
                                          8
                                          (page-dir-ptr-table-entry-addr
                                           (xr :rgf *rdi* x86)
                                           (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                                         :r x86)))))))))))
                              (!flgi
                               *af*
                               (sub-af-spec64
                                (logand
                                 4503598553628672
                                 (combine-bytes
                                  (mv-nth
                                   1
                                   (rb
                                    (create-canonical-address-list
                                     8
                                     (page-dir-ptr-table-entry-addr
                                      (xr :rgf *rdi* x86)
                                      (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                                    :r x86))))
                                (logand
                                 4503598553628672
                                 (logior
                                  (logand
                                   18442240475155922943
                                   (combine-bytes
                                    (mv-nth
                                     1
                                     (rb
                                      (create-canonical-address-list
                                       8
                                       (page-dir-ptr-table-entry-addr
                                        (xr :rgf *rsi* x86)
                                        (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                                      :r x86))))
                                  (logand
                                   4503598553628672
                                   (combine-bytes
                                    (mv-nth
                                     1
                                     (rb
                                      (create-canonical-address-list
                                       8
                                       (page-dir-ptr-table-entry-addr
                                        (xr :rgf *rdi* x86)
                                        (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                                      :r x86)))))))
                               (!flgi
                                *zf* 1
                                (!flgi
                                 *sf*
                                 (sf-spec64
                                  (loghead
                                   64
                                   (+
                                    (logand
                                     4503598553628672
                                     (logext
                                      64
                                      (combine-bytes
                                       (mv-nth
                                        1
                                        (rb
                                         (create-canonical-address-list
                                          8
                                          (page-dir-ptr-table-entry-addr
                                           (xr :rgf *rdi* x86)
                                           (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                                         :r x86)))))
                                    (-
                                     (logand
                                      4503598553628672
                                      (logior
                                       (logand
                                        -4503598553628673
                                        (logext
                                         64
                                         (combine-bytes
                                          (mv-nth
                                           1
                                           (rb
                                            (create-canonical-address-list
                                             8
                                             (page-dir-ptr-table-entry-addr
                                              (xr :rgf *rsi* x86)
                                              (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                                            :r x86)))))
                                       (logand
                                        4503598553628672
                                        (logext
                                         64
                                         (combine-bytes
                                          (mv-nth
                                           1
                                           (rb
                                            (create-canonical-address-list
                                             8
                                             (page-dir-ptr-table-entry-addr
                                              (xr :rgf *rdi* x86)
                                              (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                                            :r x86)))))))))))
                                 (!flgi
                                  *of*
                                  (of-spec64
                                   (+
                                    (logand
                                     4503598553628672
                                     (logext
                                      64
                                      (combine-bytes
                                       (mv-nth
                                        1
                                        (rb
                                         (create-canonical-address-list
                                          8
                                          (page-dir-ptr-table-entry-addr
                                           (xr :rgf *rdi* x86)
                                           (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                                         :r x86)))))
                                    (-
                                     (logand
                                      4503598553628672
                                      (logior
                                       (logand
                                        -4503598553628673
                                        (logext
                                         64
                                         (combine-bytes
                                          (mv-nth
                                           1
                                           (rb
                                            (create-canonical-address-list
                                             8
                                             (page-dir-ptr-table-entry-addr
                                              (xr :rgf *rsi* x86)
                                              (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                                            :r x86)))))
                                       (logand
                                        4503598553628672
                                        (logext
                                         64
                                         (combine-bytes
                                          (mv-nth
                                           1
                                           (rb
                                            (create-canonical-address-list
                                             8
                                             (page-dir-ptr-table-entry-addr
                                              (xr :rgf *rdi* x86)
                                              (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                                            :r x86))))))))))
                                  (mv-nth
                                   1
                                   (wb
                                    (create-addr-bytes-alist
                                     (create-canonical-address-list
                                      8
                                      (page-dir-ptr-table-entry-addr
                                       (xr :rgf *rsi* x86)
                                       (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                                     (byte-ify
                                      8
                                      (logior
                                       (logand
                                        18442240475155922943
                                        (combine-bytes
                                         (mv-nth
                                          1
                                          (rb
                                           (create-canonical-address-list
                                            8
                                            (page-dir-ptr-table-entry-addr
                                             (xr :rgf *rsi* x86)
                                             (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                                           :r x86))))
                                       (logand
                                        4503598553628672
                                        (combine-bytes
                                         (mv-nth
                                          1
                                          (rb
                                           (create-canonical-address-list
                                            8
                                            (page-dir-ptr-table-entry-addr
                                             (xr :rgf *rdi* x86)
                                             (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                                           :r x86)))))))
                                    (mv-nth 1
                                            (wb (create-addr-bytes-alist
                                                 (create-canonical-address-list
                                                  8 (+ -24 (xr :rgf *rsp* x86)))
                                                 (byte-ify 8 (xr :ctr *cr3* x86)))
                                                x86))))))))))))))))))))))
  :hints (("Goal"
           :do-not '(preprocess)
           :do-not-induct t
           :in-theory (e/d* (instruction-decoding-and-spec-rules
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

                             rb-wb-equal-in-system-level-non-marking-mode

                             pos member-p subset-p)

                            (member-p-strip-cars-of-remove-duplicate-keys
                             wb-remove-duplicate-writes-in-system-level-non-marking-mode
                             las-to-pas

                             (:REWRITE MV-NTH-1-IA32E-LA-TO-PA-SYSTEM-LEVEL-NON-MARKING-MODE-WHEN-ERROR)
                             (:REWRITE IA32E-LA-TO-PA-LOWER-12-BITS-ERROR)
                             (:REWRITE
                              DISJOINTNESS-OF-ALL-TRANSLATION-GOVERNING-ADDRESSES-FROM-ALL-TRANSLATION-GOVERNING-ADDRESSES-SUBSET-P)
                             (:TYPE-PRESCRIPTION NATP-PML4-TABLE-ENTRY-ADDR)
                             (:REWRITE ACL2::CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP)
                             (:REWRITE IA32E-LA-TO-PA-XW-STATE)
                             (:REWRITE R-W-X-IS-IRRELEVANT-FOR-MV-NTH-1-IA32E-LA-TO-PA-WHEN-NO-ERRORS)
                             (:LINEAR ADDING-7-TO-PML4-TABLE-ENTRY-ADDR)
                             (:LINEAR *PHYSICAL-ADDRESS-SIZE*P-PML4-TABLE-ENTRY-ADDR)
                             (:REWRITE LAS-TO-PAS-XW-STATE)
                             (:REWRITE ACL2::EQUAL-OF-BOOLEANS-REWRITE)
                             (:REWRITE LOGHEAD-UNEQUAL)
                             (:REWRITE NEGATIVE-LOGAND-TO-POSITIVE-LOGAND-WITH-INTEGERP-X)
                             (:DEFINITION COMBINE-BYTES)
                             (:REWRITE |(logand -4096 base-addr) = base-addr when low 12 bits are 0|)
                             (:REWRITE XR-IA32E-LA-TO-PA)
                             (:REWRITE ACL2::NFIX-WHEN-NOT-NATP)
                             (:REWRITE ACL2::NFIX-WHEN-NATP)
                             (:REWRITE CONSTANT-UPPER-BOUND-OF-LOGIOR-FOR-NATURALS)
                             (:LINEAR COMBINE-BYTES-SIZE-FOR-RM64-PROGRAMMER-LEVEL-MODE)
                             (:REWRITE ACL2::NATP-WHEN-INTEGERP)
                             (:REWRITE ACL2::NATP-WHEN-GTE-0)
                             (:REWRITE 4K-ALIGNED-PHYSICAL-ADDRESS-HELPER)
                             (:REWRITE BITOPS::SIGNED-BYTE-P-OF-LOGTAIL)
                             (:LINEAR ADDING-7-TO-PAGE-DIR-PTR-TABLE-ENTRY-ADDR)
                             (:LINEAR *PHYSICAL-ADDRESS-SIZE*P-PAGE-DIR-PTR-TABLE-ENTRY-ADDR)
                             (:TYPE-PRESCRIPTION ADDING-7-TO-PML4-TABLE-ENTRY-ADDR)
                             (:TYPE-PRESCRIPTION ADDING-7-TO-PAGE-DIR-PTR-TABLE-ENTRY-ADDR)
                             (:REWRITE ACL2::SIGNED-BYTE-P-LOGEXT)
                             (:TYPE-PRESCRIPTION BOOLEANP)
                             (:REWRITE LOGHEAD-64-N64-TO-I64-CANONICAL-ADDRESS)
                             (:TYPE-PRESCRIPTION PML4-TABLE-BASE-ADDR)
                             (:REWRITE GET-PREFIXES-OPENER-LEMMA-GROUP-4-PREFIX)
                             (:REWRITE GET-PREFIXES-OPENER-LEMMA-GROUP-3-PREFIX)
                             (:REWRITE GET-PREFIXES-OPENER-LEMMA-GROUP-2-PREFIX)
                             (:REWRITE GET-PREFIXES-OPENER-LEMMA-GROUP-1-PREFIX)
                             (:REWRITE MV-NTH-1-LAS-TO-PAS-SYSTEM-LEVEL-NON-MARKING-MODE-WHEN-ERROR)
                             (:REWRITE
                              COMBINE-BYTES-RB-IN-TERMS-OF-RB-SUBSET-P-IN-SYSTEM-LEVEL-NON-MARKING-MODE)
                             (:DEFINITION MEMBER-P)
                             (:LINEAR UNSIGNED-BYTE-P-OF-COMBINE-BYTES)
                             (:TYPE-PRESCRIPTION ACL2::|x < y  =>  0 < -x+y|)
                             (:REWRITE DEFAULT-+-2)
                             (:REWRITE ACL2::NATP-RW)
                             (:REWRITE IA32E-LA-TO-PA-LOWER-12-BITS)
                             (:REWRITE DEFAULT-+-1)
                             (:REWRITE ACL2::ASH-0)
                             (:REWRITE ACL2::ZIP-OPEN)
                             (:REWRITE LOGHEAD-OF-NON-INTEGERP)
                             (:TYPE-PRESCRIPTION ADDR-BYTE-ALISTP-CREATE-ADDR-BYTES-ALIST)
                             (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-3)
                             (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-2)
                             (:REWRITE ZF-SPEC-THM)
                             (:LINEAR ACL2::LOGHEAD-UPPER-BOUND)
                             (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2)
                             (:LINEAR SIZE-OF-COMBINE-BYTES)
                             (:REWRITE DISJOINT-P-SUBSET-P)
                             (:DEFINITION BINARY-APPEND)
                             (:DEFINITION CREATE-ADDR-BYTES-ALIST)
                             (:REWRITE MEMBER-P-OF-SUBSET-IS-MEMBER-P-OF-SUPERSET)
                             (:LINEAR RGFI-IS-I64P . 1)
                             (:REWRITE MEMBER-P-CDR)
                             (:REWRITE BITOPS::UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-LESS)
                             (:REWRITE ACL2::DIFFERENCE-UNSIGNED-BYTE-P)
                             (:LINEAR RGFI-IS-I64P . 2)
                             (:REWRITE ACL2::APPEND-WHEN-NOT-CONSP)
                             (:LINEAR RIP-IS-I48P . 2)
                             (:LINEAR RIP-IS-I48P . 1)
                             (:TYPE-PRESCRIPTION BYTE-IFY)
                             (:REWRITE ACL2::IFIX-WHEN-NOT-INTEGERP)
                             (:REWRITE BITOPS::BASIC-UNSIGNED-BYTE-P-OF-+)
                             (:REWRITE DISJOINT-P-APPEND-1)
                             (:REWRITE DEFAULT-<-1)
                             (:REWRITE DEFAULT-CAR)
                             (:REWRITE DEFAULT-CDR)
                             (:META ACL2::CANCEL_PLUS-LESSP-CORRECT)
                             (:REWRITE WB-NOT-CONSP-ADDR-LST)
                             (:DEFINITION NTHCDR)
                             (:REWRITE SUBSET-P-CDR-Y)
                             (:REWRITE IA32E-LA-TO-PA-LOWER-12-BITS-VALUE-OF-ADDRESS-WHEN-ERROR)
                             (:REWRITE DEFAULT-<-2)
                             (:TYPE-PRESCRIPTION N52P-MV-NTH-1-IA32E-LA-TO-PA)
                             (:META ACL2::CANCEL_PLUS-EQUAL-CORRECT)
                             (:DEFINITION NTH)
                             (:REWRITE CONSP-CREATE-ADDR-BYTES-ALIST)
                             (:REWRITE SUBSET-P-REFLEXIVE)
                             (:META ACL2::CANCEL_TIMES-EQUAL-CORRECT)
                             (:REWRITE SET::SETS-ARE-TRUE-LISTS)
                             (:LINEAR RFLAGS-IS-N32P)
                             (:REWRITE CONSP-BYTE-IFY)
                             (:DEFINITION TRUE-LISTP)
                             (:TYPE-PRESCRIPTION RFLAGS-IS-N32P)
                             (:REWRITE CDR-APPEND-IS-APPEND-CDR)
                             (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP)
                             (:REWRITE DISJOINT-P-MEMBERS-OF-TRUE-LIST-LIST-DISJOINT-P)
                             (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P-AUX)
                             (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P)
                             (:REWRITE SUBSET-P-CDR-X)
                             (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT)
                             (:REWRITE SET::NONEMPTY-MEANS-SET)
                             (:TYPE-PRESCRIPTION XW)
                             (:TYPE-PRESCRIPTION CONSP-CREATE-ADDR-BYTES-ALIST-IN-TERMS-OF-LEN)
                             (:TYPE-PRESCRIPTION CONSP-CREATE-ADDR-BYTES-ALIST)
                             (:TYPE-PRESCRIPTION NATP-COMBINE-BYTES)
                             (:TYPE-PRESCRIPTION TRUE-LISTP)
                             (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL)
                             (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP)
                             (:TYPE-PRESCRIPTION ALL-TRANSLATION-GOVERNING-ADDRESSES)
                             (:TYPE-PRESCRIPTION SET::SETP-TYPE)
                             (:TYPE-PRESCRIPTION SET::EMPTY-TYPE)
                             (:REWRITE ACL2::EQUAL-CONSTANT-+)
                             (:DEFINITION BYTE-LISTP)
                             (:REWRITE UNSIGNED-BYTE-P-OF-ASH)
                             (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL)
                             (:REWRITE BITOPS::LOGBITP-OF-NEGATIVE-CONST)
                             (:REWRITE BITOPS::LOGBITP-OF-MASK)
                             (:REWRITE BITOPS::LOGBITP-OF-CONST)
                             (:REWRITE GREATER-LOGBITP-OF-UNSIGNED-BYTE-P . 1)
                             (:META BITOPS::OPEN-LOGBITP-OF-CONST-LITE-META)
                             (:REWRITE RB-RETURNS-BYTE-LISTP)
                             (:REWRITE CAR-OF-APPEND)
                             (:TYPE-PRESCRIPTION RB-RETURNS-TRUE-LISTP)
                             (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER)
                             (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-SIGNED-BYTE-P-SMALLER)
                             (:TYPE-PRESCRIPTION CONSP-APPEND)
                             (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2)
                             (:DEFINITION ACONS)
                             (:REWRITE UNSIGNED-BYTE-P-OF-COMBINE-BYTES)
                             (:REWRITE UNSIGNED-BYTE-P-OF-LOGIOR)
                             (:TYPE-PRESCRIPTION NATP)
                             (:REWRITE SET::IN-SET)
                             (:TYPE-PRESCRIPTION ACL2::LOGTAIL-TYPE)
                             (:REWRITE ACL2::MEMBER-OF-CONS)
                             (:TYPE-PRESCRIPTION TRUE-LISTP-CREATE-ADDR-BYTES-ALIST)
                             (:TYPE-PRESCRIPTION RB-RETURNS-BYTE-LISTP)
                             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)
                             (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE)
                             (:TYPE-PRESCRIPTION COMBINE-BYTES)
                             (:DEFINITION N08P$INLINE)
                             (:DEFINITION LEN)
                             (:REWRITE XR-MV-NTH-2-IA32E-LA-TO-PA)
                             (:REWRITE BITOPS::LOGSQUASH-OF-LOGHEAD-ZERO)
                             (:REWRITE DEFAULT-UNARY-MINUS)
                             (:REWRITE LEN-OF-RB-IN-PROGRAMMER-LEVEL-MODE)
                             (:TYPE-PRESCRIPTION ACL2::BITP$INLINE)
                             (:TYPE-PRESCRIPTION ACL2::TRUE-LISTP-APPEND)
                             (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2)
                             (:REWRITE WEED-OUT-IRRELEVANT-LOGAND-WHEN-FIRST-OPERAND-CONSTANT)
                             (:REWRITE LOGAND-REDUNDANT)
                             (:LINEAR ASH-MONOTONE-2)
                             (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2)
                             (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 1)
                             (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1)
                             (:REWRITE
                              MV-NTH-1-IA32E-LA-TO-PA-MEMBER-OF-MV-NTH-1-LAS-TO-PAS-IF-LIN-ADDR-MEMBER-P)
                             (:LINEAR MV-NTH-1-IDIV-SPEC)
                             (:LINEAR MV-NTH-1-DIV-SPEC)
                             (:REWRITE UNSIGNED-BYTE-P-OF-LOGAND-2)
                             (:LINEAR ACL2::EXPT->-1)
                             (:REWRITE ACL2::UNSIGNED-BYTE-P-LOGHEAD)
                             (:TYPE-PRESCRIPTION ZIP)
                             (:LINEAR BITOPS::LOGAND-<-0-LINEAR)
                             (:REWRITE BITOPS::LOGIOR-FOLD-CONSTS)
                             (:LINEAR <=-LOGIOR)
                             (:LINEAR MEMBER-P-POS-VALUE)
                             (:LINEAR MEMBER-P-POS-1-VALUE)
                             (:LINEAR BITOPS::LOGIOR->=-0-LINEAR)
                             (:REWRITE NO-DUPLICATES-P-AND-APPEND)
                             (:REWRITE ACL2::SUBSETP-MEMBER . 2)
                             (:REWRITE ACL2::SUBSETP-MEMBER . 1)
                             (:TYPE-PRESCRIPTION WR32$INLINE)
                             (:REWRITE UNSIGNED-BYTE-P-OF-LOGAND-1)
                             (:REWRITE SUBSET-P-CONS-MEMBER-P-LEMMA)
                             (:REWRITE MEMBER-P-OF-NOT-A-CONSP)
                             (:REWRITE GET-PREFIXES-OPENER-LEMMA-ZERO-CNT)
                             (:REWRITE ACL2::EXPT-WITH-VIOLATED-GUARDS)
                             (:REWRITE BITOPS::BASIC-SIGNED-BYTE-P-OF-+)
                             (:TYPE-PRESCRIPTION ASH)
                             (:LINEAR ACL2::EXPT-IS-INCREASING-FOR-BASE>1)
                             (:DEFINITION MEMBER-EQUAL)
                             (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1)
                             (:LINEAR BITOPS::UPPER-BOUND-OF-LOGIOR-FOR-NATURALS)
                             (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP)

                             bitops::logand-with-negated-bitmask
                             unsigned-byte-p
                             force (force))))))

;; ======================================================================

;; TODO: Move to define of write-to-physical-memory.

(defthm rm-low-64-and-write-to-physical-memory-disjoint
  (implies (disjoint-p (addr-range 8 p-addr-1) p-addrs-2)
           (equal (rm-low-64 p-addr-1 (write-to-physical-memory p-addrs-2 bytes x86))
                  (rm-low-64 p-addr-1 x86)))
  :hints (("Goal" :in-theory (e/d* (rm-low-64 rm-low-32 disjoint-p)
                                   (force (force))))))

(defthm xr-mem-write-to-physical-memory-member
  (implies (and (member-p index p-addrs)
                (no-duplicates-p p-addrs))
           (equal (xr :mem index (write-to-physical-memory p-addrs bytes x86))
                  (nth (pos index p-addrs) bytes)))
  :hints (("Goal" :in-theory (e/d* (member-p pos) (force (force))))))

(encapsulate
  ()

  ;; This whole encapsulate is just a quick and ugly hack.

  (def-gl-export expand-combine-bytes-of-len-8-helper-1
    :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
              (n08p e) (n08p f) (n08p g) (n08p h))
    :concl (equal (combine-bytes (list a b c d e f g h))
                  (logior a (ash b 8)
                          (ash (logior c (ash d 8)) 16)
                          (ash (logior e (ash f 8) (ash (logior g (ash h 8)) 16)) 32)))
    :g-bindings
    (gl::auto-bindings
     (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
           (:nat e 8) (:nat f 8) (:nat g 8) (:nat h 8))))

  (in-theory (e/d () (expand-combine-bytes-of-len-8-helper-1)))

  (defthmd expand-combine-bytes-of-len-8-helper-2
    (implies (and (byte-listp bytes)
                  (equal (len bytes) 8))
             (equal (list (car bytes)
                          (cadr bytes)
                          (caddr bytes)
                          (cadddr bytes)
                          (car (cddddr bytes))
                          (cadr (cddddr bytes))
                          (caddr (cddddr bytes))
                          (cadddr (cddddr bytes)))
                    bytes)))

  (defthmd expand-combine-bytes-of-len-8-helper-3
    (implies (and (byte-listp bytes)
                  (equal (len bytes) 8))
             (and (unsigned-byte-p 8 (car bytes))
                  (unsigned-byte-p 8 (cadr bytes))
                  (unsigned-byte-p 8 (caddr bytes))
                  (unsigned-byte-p 8 (cadddr bytes))
                  (unsigned-byte-p 8 (car (cddddr bytes)))
                  (unsigned-byte-p 8 (cadr (cddddr bytes)))
                  (unsigned-byte-p 8 (caddr (cddddr bytes)))
                  (unsigned-byte-p 8 (cadddr (cddddr bytes))))))

  (defthmd expand-combine-bytes-of-len-8-helper-4
    (implies (and (byte-listp bytes)
                  (equal (len bytes) 8))
             (equal (combine-bytes (list (car bytes)
                                         (cadr bytes)
                                         (caddr bytes)
                                         (cadddr bytes)
                                         (car (cddddr bytes))
                                         (cadr (cddddr bytes))
                                         (caddr (cddddr bytes))
                                         (cadddr (cddddr bytes))))
                    (combine-bytes bytes)))
    :hints (("Goal"
             :in-theory (e/d* () (combine-bytes not))
             :use ((:instance expand-combine-bytes-of-len-8-helper-2)))))

  (defthmd expand-combine-bytes-of-len-8
    (implies (and (byte-listp bytes)
                  (equal (len bytes) 8))
             (equal (combine-bytes bytes)
                    (logior (car bytes)
                            (ash (cadr bytes) 8)
                            (ash (logior (caddr bytes)
                                         (ash (cadddr bytes) 8))
                                 16)
                            (ash (logior (car (cddddr bytes))
                                         (ash (cadr (cddddr bytes)) 8)
                                         (ash (logior (caddr (cddddr bytes))
                                                      (ash (cadddr (cddddr bytes)) 8))
                                              16))
                                 32))))
    :hints (("Goal"
             :use (
                   (:instance expand-combine-bytes-of-len-8-helper-1
                              (a (car bytes))
                              (b (cadr bytes))
                              (c (caddr bytes))
                              (d (cadddr bytes))
                              (e (car (cddddr bytes)))
                              (f (cadr (cddddr bytes)))
                              (g (caddr (cddddr bytes)))
                              (h (cadddr (cddddr bytes))))
                   (:instance expand-combine-bytes-of-len-8-helper-2)
                   (:instance expand-combine-bytes-of-len-8-helper-3)
                   (:instance expand-combine-bytes-of-len-8-helper-4))
             :in-theory (e/d* ()
                              (acl2::simplify-logior
                               (:linear bitops::logior-<-0-linear-2)
                               (:linear ash-monotone-2)
                               not)))))

  (defthm rm-low-64-and-write-to-physical-memory-equal
    (implies (and (equal p-addrs-2 (addr-range 8 p-addr-1))
                  (equal (len bytes) (len p-addrs-2))
                  (byte-listp bytes)
                  (not (programmer-level-mode x86)))
             (equal (rm-low-64 p-addr-1 (write-to-physical-memory p-addrs-2 bytes x86))
                    (combine-bytes bytes)))
    :hints (("Goal"
             :expand ((combine-bytes bytes))
             :in-theory (e/d* (rm-low-64 rm-low-32 member-p expand-combine-bytes-of-len-8)
                              (force (force)))))))

(defthm mv-nth-0-paging-entry-no-page-fault-p-and-write-to-physical-memory
  (equal (mv-nth 0
                 (paging-entry-no-page-fault-p
                  structure-type lin-addr entry
                  u/s-acc r/w-acc x/d-acc
                  wp smep smap ac nxe r-w-x cpl
                  (write-to-physical-memory p-addrs bytes x86)
                  ignored))
         (mv-nth 0
                 (paging-entry-no-page-fault-p
                  structure-type lin-addr entry
                  u/s-acc r/w-acc x/d-acc
                  wp smep smap ac nxe r-w-x cpl
                  x86 ignored)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             paging-entry-no-page-fault-p
                             page-fault-exception)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

;; TODO: Move to proofs/utilities/disjoint.

(defthm no-duplicates-p-and-addr-range
  (no-duplicates-p (addr-range n x))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

(defthm nth-pos-of-addr-range-first
  (implies (and (integerp index)
                (posp n))
           (equal (pos index (addr-range n index)) 0))
  :hints (("Goal" :in-theory (e/d* (pos) ()))))

(defthm nth-pos-of-list-first
  (implies (and (syntaxp (not (and (consp xs)
                                   (eq (car xs) 'addr-range))))
                (equal index (car xs))
                (consp xs))
           (equal (pos index xs) 0))
  :hints (("Goal" :in-theory (e/d* (pos) ()))))

(defthm neg-addr-range=nil
  (implies (negp i) (equal (addr-range i n) nil)))

;; TODO: Move to define of paging-entry-no-page-fault-p.

(defthm mv-nth-0-paging-entry-no-page-fault-p-and-similar-entries
  (implies (and (equal (page-present entry-1)
                       (page-present entry-2))
                (syntaxp (not (eq entry-1 entry-2)))
                (syntaxp (and (consp entry-1)
                              (equal (car entry-1) 'combine-bytes)))
                (equal (page-read-write entry-1)
                       (page-read-write entry-2))
                (equal (page-user-supervisor entry-1)
                       (page-user-supervisor entry-2))
                (equal (page-execute-disable entry-1)
                       (page-execute-disable entry-2))
                (equal (page-size entry-1)
                       (page-size entry-2))
                (if (equal structure-type 1)
                    ;; For Page Directory
                    (equal (part-select entry-1 :low 13 :high 20)
                           (part-select entry-2 :low 13 :high 20))
                  ;; For Page Directory Pointer Table
                  (if (equal structure-type 2)
                      (equal (part-select entry-1 :low 13 :high 29)
                             (part-select entry-2 :low 13 :high 29))
                    t))
                (unsigned-byte-p 2 structure-type)
                (unsigned-byte-p 64 entry-1)
                (unsigned-byte-p 64 entry-2))
           (equal (mv-nth 0
                          (paging-entry-no-page-fault-p
                           structure-type lin-addr entry-1
                           u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x cpl
                           x86 ignored))
                  (mv-nth 0
                          (paging-entry-no-page-fault-p
                           structure-type lin-addr entry-2
                           u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x cpl
                           x86 ignored))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             paging-entry-no-page-fault-p
                             page-fault-exception)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm mv-nth-0-paging-entry-no-page-fault-p-is-independent-of-lin-addr
  (implies
   (not
    (mv-nth
     0
     (paging-entry-no-page-fault-p structure-type
                                   lin-addr entry u/s-acc r/w-acc
                                   x/d-acc wp smep smap ac nxe r-w-x
                                   cpl x86 supervisor-mode-access-type)))
   (equal
    (mv-nth
     0
     (paging-entry-no-page-fault-p structure-type (+ n lin-addr)
                                   entry u/s-acc r/w-acc
                                   x/d-acc wp smep smap ac nxe r-w-x
                                   cpl x86 supervisor-mode-access-type))
    nil))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                                    paging-entry-no-page-fault-p)
                                   (commutativity-of-+
                                    not
                                    page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                                    page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                                    bitops::logand-with-negated-bitmask)))))


(encapsulate
  ()

  ;; TODO: Leave this encapsulate in this book.

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

;; TODO: Move to paging-defs, with a note on how more lemmas like this
;; can be found in this zero-copy file.
(defthm ia32e-la-to-pa-page-table-values-and-write-to-translation-governing-address
  (b* ((p-addrs (translation-governing-addresses-for-page-table lin-addr base-addr x86))
       (page-table-entry (rm-low-64 (page-table-entry-addr lin-addr base-addr) x86))
       (value (combine-bytes bytes)))
    (implies (and (not (mv-nth 0
                               (ia32e-la-to-pa-page-table
                                lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                wp smep smap ac nxe r-w-x cpl x86)))
                  (equal (page-present page-table-entry)
                         (page-present value))
                  (equal (page-read-write page-table-entry)
                         (page-read-write value))
                  (equal (page-user-supervisor page-table-entry)
                         (page-user-supervisor value))
                  (equal (page-execute-disable page-table-entry)
                         (page-execute-disable value))
                  (equal (page-size page-table-entry)
                         (page-size value))

                  (equal (len bytes) (len p-addrs))
                  (byte-listp bytes)
                  (canonical-address-p lin-addr)
                  (physical-address-p base-addr)
                  (equal (loghead 12 base-addr) 0)
                  (x86p x86))
             (and (equal
                   (mv-nth 0 (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x cpl
                              (write-to-physical-memory p-addrs bytes x86)))
                   nil)
                  (equal (mv-nth 1 (ia32e-la-to-pa-page-table
                                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl
                                    (write-to-physical-memory p-addrs bytes x86)))
                         (logior (loghead 12 lin-addr)
                                 (ash (loghead 40 (logtail 12 value))
                                      12))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-table)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

;; TODO: Leave the following in this book.

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
       (page-dir-ptr-table-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
       (page-dir-ptr-table-entry-addr (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
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
       (page-dir-ptr-table-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
       (page-dir-ptr-table-entry-addr (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
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
    (equal page-dir-ptr-table-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
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
     (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)))
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


;; TODO: Leave the following gl-lemmas in this book, unless you later
;; generalize them. In that case, at least the first two can be moved
;; to the defines of pml4-table-entry-addr and
;; page-dir-ptr-table-entry.

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
            (physical-address-p page-dir-ptr-table-base-addr)
            (canonical-address-p lin-addr)
            ;; 1G aligned linear address
            (equal (loghead 30 lin-addr) 0))
  :concl (equal (page-dir-ptr-table-entry-addr
                 (+ n lin-addr) page-dir-ptr-table-base-addr)
                (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat page-dir-ptr-table-base-addr 64) (:nat lin-addr 64) (:nat n 64))))

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

;; (def-gl-export loghead-30-of-1G-aligned-lin-addr-+-n-remove-logext
;;   ;; See CANONICAL-ADDRESS-P-AND-LOGEXT-48
;;   :hyp (and (canonical-address-p lin-addr)
;;             (canonical-address-p (+ n lin-addr))
;;             (equal (loghead 30 lin-addr) 0)
;;             (unsigned-byte-p 30 n))
;;   :concl (equal (logext 48 (+ n lin-addr)) (+ n lin-addr))
;;   :g-bindings
;;   (gl::auto-bindings (:mix (:nat lin-addr 64) (:nat n 64))))

(def-gl-export logior-to-+-for-ash-x-30
  :hyp (and (unsigned-byte-p 22 x)
            (unsigned-byte-p 30 n))
  :concl (equal (logior n (ash x 30)) (+ n (ash x 30)))
  :g-bindings
  (gl::auto-bindings (:mix (:nat n 64) (:nat x 64))))

(defthm mv-nth-0-ia32e-la-to-pa-page-dir-ptr-table-for-same-1G-page
  (implies
   (and
    (equal page-dir-ptr-table-entry-addr (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
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
                    lin-addr page-dir-ptr-table-base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    ;; (equal (loghead 30 lin-addr) 0)
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (physical-address-p page-dir-ptr-table-base-addr)
    (equal (loghead 12 page-dir-ptr-table-base-addr) 0)
    (not (page-structure-marking-mode x86))
    (x86p x86))
   (equal (mv-nth 0
                  (ia32e-la-to-pa-page-dir-ptr-table
                   (+ n lin-addr) page-dir-ptr-table-base-addr u/s-acc r/w-acc x/d-acc
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
    (equal page-dir-ptr-table-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
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
    (equal page-dir-ptr-table-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
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

(defthmd open-mv-nth-0-las-to-pas
  (implies (and (canonical-address-p lin-addr)
                (not (zp n))
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 0 (las-to-pas (create-canonical-address-list n lin-addr) r-w-x cpl x86))
                  (if (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
                      (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
                    (mv-nth 0 (las-to-pas (create-canonical-address-list (+ -1 n) (+ 1 lin-addr))
                                          r-w-x cpl x86)))))
  :hints (("Goal" :in-theory (e/d* (las-to-pas) ()))))

(defthmd open-mv-nth-1-las-to-pas
  (implies (and (canonical-address-p lin-addr)
                (not (zp n))
                (not (mv-nth 0 (las-to-pas (create-canonical-address-list n lin-addr) r-w-x cpl x86)))
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 1 (las-to-pas (create-canonical-address-list n lin-addr) r-w-x cpl x86))
                  (cons (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
                        (mv-nth 1 (las-to-pas (create-canonical-address-list (+ -1 n) (+ 1 lin-addr))
                                              r-w-x cpl x86)))))
  :hints (("Goal" :in-theory (e/d* (las-to-pas) ()))))

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
    (equal page-dir-ptr-table-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
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
                             open-mv-nth-0-las-to-pas)
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
    (equal page-dir-ptr-table-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
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
                             open-mv-nth-0-las-to-pas
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
           (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
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
                    lin-addr page-dir-ptr-table-base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    ;; (equal (loghead 30 lin-addr) 0)
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (physical-address-p page-dir-ptr-table-base-addr)
    (equal (loghead 12 page-dir-ptr-table-base-addr) 0)
    (not (page-structure-marking-mode x86))
    (x86p x86))
   (equal (mv-nth 1
                  (ia32e-la-to-pa-page-dir-ptr-table
                   (+ n lin-addr) page-dir-ptr-table-base-addr u/s-acc r/w-acc x/d-acc
                   wp smep smap ac nxe r-w-x cpl x86))
          (+ n
             (ash
              (loghead 22
                       (logtail 30
                                (rm-low-64
                                 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
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
    (equal page-dir-ptr-table-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
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
                                 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
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
    (equal page-dir-ptr-table-base-addr
           (ash (loghead 40 (logtail 12 pml4-table-entry))
                12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
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
                                 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
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
    (equal page-dir-ptr-table-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
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
                                  (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                                  x86)))
               30)))))
  :hints (("Goal"
           :induct (create-canonical-address-list-alt iteration m lin-addr)
           :in-theory (e/d* (las-to-pas
                             open-mv-nth-1-las-to-pas-for-same-1G-page-general-1
                             open-mv-nth-0-las-to-pas-for-same-1G-page-general-1
                             open-mv-nth-0-las-to-pas-for-same-1G-page-general-2
                             open-mv-nth-0-las-to-pas-for-same-1G-page-general
                             open-mv-nth-1-las-to-pas
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
    (equal page-dir-ptr-table-base-addr (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
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
                               (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
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
                             open-mv-nth-0-las-to-pas
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
    (equal page-dir-ptr-table-base-addr
           (ash (loghead 40 (logtail 12 pml4-table-entry))
                12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
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
     (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)))
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
           :in-theory (e/d* (disjoint-p
                             member-p
                             las-to-pas
                             open-mv-nth-1-las-to-pas-for-same-1G-page-general-1
                             open-mv-nth-0-las-to-pas-for-same-1G-page-general-1
                             open-mv-nth-0-las-to-pas-for-same-1G-page-general-2
                             open-mv-nth-0-las-to-pas-for-same-1G-page-general
                             mv-nth-0-ia32e-la-to-pa-for-same-1G-page
                             mv-nth-1-ia32e-la-to-pa-for-same-1G-page
                             open-mv-nth-1-las-to-pas)
                            (commutativity-of-+
                             member-p-strip-cars-of-remove-duplicate-keys
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask
                             force (force)
                             not
                             (:REWRITE XR-IA32E-LA-TO-PA)
                             (:REWRITE XR-MV-NTH-2-IA32E-LA-TO-PA)
                             (:REWRITE IA32E-LA-TO-PA-LOWER-12-BITS-ERROR)
                             (:REWRITE MV-NTH-1-IA32E-LA-TO-PA-SYSTEM-LEVEL-NON-MARKING-MODE-WHEN-ERROR)
                             (:REWRITE X86P-MV-NTH-2-IA32E-LA-TO-PA)
                             (:REWRITE WB-REMOVE-DUPLICATE-WRITES-IN-SYSTEM-LEVEL-NON-MARKING-MODE)
                             (:REWRITE MV-NTH-1-LAS-TO-PAS-SYSTEM-LEVEL-NON-MARKING-MODE-WHEN-ERROR)
                             (:REWRITE IA32E-LA-TO-PA-LOWER-12-BITS-VALUE-OF-ADDRESS-WHEN-ERROR)
                             (:REWRITE ACL2::LOGHEAD-IDENTITY)
                             (:REWRITE MV-NTH-2-LAS-TO-PAS-SYSTEM-LEVEL-NON-MARKING-MODE)
                             (:REWRITE WB-RETURNS-X86P)
                             (:DEFINITION DISJOINT-P)
                             (:DEFINITION ADDR-BYTE-ALISTP)
                             (:REWRITE LOGHEAD-OF-NON-INTEGERP)
                             (:REWRITE IA32E-LA-TO-PA-LOWER-12-BITS)
                             (:DEFINITION MEMBER-P)
                             (:REWRITE ACL2::CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP)
                             (:REWRITE ACL2::ASH-0)
                             (:TYPE-PRESCRIPTION NATP-COMBINE-BYTES)
                             (:TYPE-PRESCRIPTION N64P-RM-LOW-64)
                             (:REWRITE ACL2::ZIP-OPEN)
                             (:REWRITE BITOPS::UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-LESS)
                             (:DEFINITION CREATE-CANONICAL-ADDRESS-LIST)
                             (:REWRITE
                              MV-NTH-0-IA32E-LA-TO-PA-MEMBER-OF-MV-NTH-1-LAS-TO-PAS-IF-LIN-ADDR-MEMBER-P)
                             (:DEFINITION COMBINE-BYTES)
                             (:REWRITE LOGHEAD-UNEQUAL)
                             (:REWRITE DEFAULT-+-2)
                             (:REWRITE DEFAULT-+-1)
                             (:REWRITE LOGHEAD-NEGATIVE)
                             (:REWRITE CDR-CREATE-CANONICAL-ADDRESS-LIST)
                             (:REWRITE CONSP-OF-CREATE-CANONICAL-ADDRESS-LIST)
                             (:REWRITE CAR-CREATE-CANONICAL-ADDRESS-LIST)
                             (:TYPE-PRESCRIPTION N01P-PAGE-USER-SUPERVISOR)
                             (:TYPE-PRESCRIPTION N01P-PAGE-READ-WRITE)
                             (:TYPE-PRESCRIPTION N01P-PAGE-PRESENT)
                             (:TYPE-PRESCRIPTION N01P-PAGE-EXECUTE-DISABLE)
                             (:REWRITE ACL2::EQUAL-OF-BOOLEANS-REWRITE)
                             (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-3)
                             (:DEFINITION N08P$INLINE)
                             (:REWRITE ACL2::IFIX-WHEN-NOT-INTEGERP)
                             (:TYPE-PRESCRIPTION MEMBER-P)
                             (:TYPE-PRESCRIPTION N01P-PAGE-SIZE)
                             (:DEFINITION STRIP-CARS)
                             (:REWRITE BITOPS::BASIC-UNSIGNED-BYTE-P-OF-+)
                             (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-2)
                             (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-1)
                             (:DEFINITION BYTE-LISTP)
                             (:TYPE-PRESCRIPTION SIGNED-BYTE-P)
                             (:REWRITE R-W-X-IS-IRRELEVANT-FOR-MV-NTH-1-IA32E-LA-TO-PA-WHEN-NO-ERRORS)
                             (:TYPE-PRESCRIPTION N52P-MV-NTH-1-IA32E-LA-TO-PA)
                             (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL)
                             (:META ACL2::CANCEL_TIMES-EQUAL-CORRECT)
                             (:META ACL2::CANCEL_PLUS-EQUAL-CORRECT)
                             (:REWRITE MEMBER-P-OF-NOT-A-CONSP)
                             (:REWRITE MEMBER-P-CDR)
                             (:LINEAR UNSIGNED-BYTE-P-OF-COMBINE-BYTES)
                             (:LINEAR SIZE-OF-COMBINE-BYTES)
                             (:REWRITE CDR-STRIP-CARS-IS-STRIP-CARS-CDR)
                             (:REWRITE R-W-X-IS-IRRELEVANT-FOR-MV-NTH-1-LAS-TO-PAS-WHEN-NO-ERRORS)
                             (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP)
                             (:REWRITE LAS-TO-PAS-SUBSET-P-WITH-L-ADDRS-FROM-BIND-FREE)
                             (:REWRITE WB-NOT-CONSP-ADDR-LST)
                             (:TYPE-PRESCRIPTION ALL-TRANSLATION-GOVERNING-ADDRESSES)
                             (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER)
                             (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-SIGNED-BYTE-P-SMALLER)
                             (:REWRITE MEMBER-P-OF-SUBSET-IS-MEMBER-P-OF-SUPERSET)
                             (:REWRITE ACL2::LOGTAIL-IDENTITY)
                             (:REWRITE MEMBER-P-CANONICAL-ADDRESS-LISTP)
                             (:TYPE-PRESCRIPTION BOOLEANP)
                             (:REWRITE SUBSET-P-CONS-MEMBER-P-LEMMA)
                             (:REWRITE DISJOINT-P-MEMBERS-OF-TRUE-LIST-LIST-DISJOINT-P)
                             (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P-AUX)
                             (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P)
                             (:TYPE-PRESCRIPTION MEMBER-P-PHYSICAL-ADDRESS-P-PHYSICAL-ADDRESS-LISTP)
                             (:TYPE-PRESCRIPTION CTRI-IS-N64P)
                             (:REWRITE RIGHT-SHIFT-TO-LOGTAIL)
                             (:REWRITE
                              DISJOINTNESS-OF-ALL-TRANSLATION-GOVERNING-ADDRESSES-FROM-ALL-TRANSLATION-GOVERNING-ADDRESSES-SUBSET-P)
                             (:DEFINITION STRIP-CDRS)
                             (:REWRITE CDR-ADDR-RANGE)
                             (:TYPE-PRESCRIPTION MEMBER-P-PHYSICAL-ADDRESS-P)
                             (:TYPE-PRESCRIPTION ZIP)
                             (:REWRITE NOT-MEMBER-P-ADDR-RANGE)
                             (:META ACL2::CANCEL_PLUS-LESSP-CORRECT)
                             (:REWRITE LA-TO-PAS-VALUES-AND-MV-NTH-1-WB)
                             (:REWRITE IA32E-LA-TO-PA-VALUES-AND-MV-NTH-1-WB)
                             (:TYPE-PRESCRIPTION IFIX)
                             (:REWRITE DEFAULT-<-1)
                             (:REWRITE DISJOINT-P-TWO-ADDR-RANGES-THM-0)
                             (:REWRITE NOT-DISJOINT-P-TWO-ADDR-RANGES-THM)
                             (:REWRITE ACL2::EQUAL-CONSTANT-+)
                             (:REWRITE DEFAULT-<-2)
                             (:REWRITE DISJOINT-P-TWO-ADDR-RANGES-THM-1)
                             (:LINEAR ADDING-7-TO-PAGE-DIR-PTR-TABLE-ENTRY-ADDR)
                             (:LINEAR *PHYSICAL-ADDRESS-SIZE*P-PAGE-DIR-PTR-TABLE-ENTRY-ADDR)
                             (:REWRITE CAR-ADDR-RANGE)
                             (:REWRITE BITOPS::SIGNED-BYTE-P-OF-LOGTAIL)
                             (:REWRITE MEMBER-P-ADDR-RANGE)
                             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)
                             (:TYPE-PRESCRIPTION NATP)
                             (:TYPE-PRESCRIPTION ACL2::LOGTAIL-TYPE)
                             (:REWRITE STRIP-CDRS-ADDR-BYTE-ALISTP-IS-BYTE-LISTP)
                             (:LINEAR ADDING-7-TO-PML4-TABLE-ENTRY-ADDR)
                             (:LINEAR *PHYSICAL-ADDRESS-SIZE*P-PML4-TABLE-ENTRY-ADDR)
                             (:REWRITE SUBSET-P-CDR-Y)
                             (:REWRITE ACL2::CONSP-OF-CAR-WHEN-ATOM-LISTP)
                             (:REWRITE SEG-VISIBLEI-IS-N16P)
                             (:REWRITE SUBSET-P-CDR-X)
                             (:TYPE-PRESCRIPTION ATOM-LISTP)
                             (:LINEAR MEMBER-P-POS-VALUE)
                             (:LINEAR MEMBER-P-POS-1-VALUE)
                             (:LINEAR ACL2::INDEX-OF-<-LEN)
                             (:REWRITE NOT-MEMBER-P-ADDR-RANGE-FROM-NOT-MEMBER-P-ADDR-RANGE)
                             (:REWRITE MEMBER-P-ADDR-RANGE-FROM-MEMBER-P-ADDR-RANGE)
                             (:REWRITE DISJOINT-P-TWO-ADDR-RANGES-THM-3)
                             (:REWRITE DISJOINT-P-TWO-ADDR-RANGES-THM-2))))))

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
    (equal page-dir-ptr-table-base-addr
           (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
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
     (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)))
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
       (page-dir-ptr-table-base-addr
        (page-dir-ptr-table-base-addr lin-addr x86))
       (page-dir-ptr-table-entry-addr
        (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
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
       (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)))
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
                             ;; las-to-pas-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr
                             member-p-strip-cars-of-remove-duplicate-keys
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl
                             bitops::logand-with-negated-bitmask
                             force (force)
                             not
                             (:REWRITE XR-IA32E-LA-TO-PA)
                             (:REWRITE XR-MV-NTH-2-IA32E-LA-TO-PA)
                             (:REWRITE IA32E-LA-TO-PA-LOWER-12-BITS-ERROR)
                             (:REWRITE MV-NTH-1-IA32E-LA-TO-PA-SYSTEM-LEVEL-NON-MARKING-MODE-WHEN-ERROR)
                             (:REWRITE X86P-MV-NTH-2-IA32E-LA-TO-PA)
                             (:REWRITE WB-REMOVE-DUPLICATE-WRITES-IN-SYSTEM-LEVEL-NON-MARKING-MODE)
                             (:REWRITE MV-NTH-1-LAS-TO-PAS-SYSTEM-LEVEL-NON-MARKING-MODE-WHEN-ERROR)
                             (:REWRITE IA32E-LA-TO-PA-LOWER-12-BITS-VALUE-OF-ADDRESS-WHEN-ERROR)
                             (:REWRITE ACL2::LOGHEAD-IDENTITY)
                             (:REWRITE WB-RETURNS-X86P)
                             (:DEFINITION DISJOINT-P)
                             (:DEFINITION ADDR-BYTE-ALISTP)
                             (:REWRITE LOGHEAD-OF-NON-INTEGERP)
                             (:REWRITE IA32E-LA-TO-PA-LOWER-12-BITS)
                             (:DEFINITION MEMBER-P)
                             (:REWRITE ACL2::CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP)
                             (:REWRITE ACL2::ASH-0)
                             (:TYPE-PRESCRIPTION NATP-COMBINE-BYTES)
                             (:TYPE-PRESCRIPTION N64P-RM-LOW-64)
                             (:REWRITE ACL2::ZIP-OPEN)
                             (:REWRITE BITOPS::UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-LESS)
                             (:DEFINITION CREATE-CANONICAL-ADDRESS-LIST)
                             (:REWRITE
                              MV-NTH-0-IA32E-LA-TO-PA-MEMBER-OF-MV-NTH-1-LAS-TO-PAS-IF-LIN-ADDR-MEMBER-P)
                             (:DEFINITION COMBINE-BYTES)
                             (:REWRITE LOGHEAD-UNEQUAL)
                             (:REWRITE DEFAULT-+-2)
                             (:REWRITE DEFAULT-+-1)
                             (:REWRITE LOGHEAD-NEGATIVE)
                             (:REWRITE CDR-CREATE-CANONICAL-ADDRESS-LIST)
                             (:REWRITE CONSP-OF-CREATE-CANONICAL-ADDRESS-LIST)
                             (:REWRITE CAR-CREATE-CANONICAL-ADDRESS-LIST)
                             (:TYPE-PRESCRIPTION N01P-PAGE-USER-SUPERVISOR)
                             (:TYPE-PRESCRIPTION N01P-PAGE-READ-WRITE)
                             (:TYPE-PRESCRIPTION N01P-PAGE-PRESENT)
                             (:TYPE-PRESCRIPTION N01P-PAGE-EXECUTE-DISABLE)
                             (:REWRITE ACL2::EQUAL-OF-BOOLEANS-REWRITE)
                             (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-3)
                             (:DEFINITION N08P$INLINE)
                             (:REWRITE ACL2::IFIX-WHEN-NOT-INTEGERP)
                             (:TYPE-PRESCRIPTION MEMBER-P)
                             (:TYPE-PRESCRIPTION N01P-PAGE-SIZE)
                             (:DEFINITION STRIP-CARS)
                             (:REWRITE BITOPS::BASIC-UNSIGNED-BYTE-P-OF-+)
                             (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-2)
                             (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-1)
                             (:DEFINITION BYTE-LISTP)
                             (:TYPE-PRESCRIPTION SIGNED-BYTE-P)
                             (:REWRITE R-W-X-IS-IRRELEVANT-FOR-MV-NTH-1-IA32E-LA-TO-PA-WHEN-NO-ERRORS)
                             (:TYPE-PRESCRIPTION N52P-MV-NTH-1-IA32E-LA-TO-PA)
                             (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL)
                             (:META ACL2::CANCEL_TIMES-EQUAL-CORRECT)
                             (:META ACL2::CANCEL_PLUS-EQUAL-CORRECT)
                             (:REWRITE MEMBER-P-OF-NOT-A-CONSP)
                             (:REWRITE MEMBER-P-CDR)
                             (:LINEAR UNSIGNED-BYTE-P-OF-COMBINE-BYTES)
                             (:LINEAR SIZE-OF-COMBINE-BYTES)
                             (:REWRITE CDR-STRIP-CARS-IS-STRIP-CARS-CDR)
                             (:REWRITE R-W-X-IS-IRRELEVANT-FOR-MV-NTH-1-LAS-TO-PAS-WHEN-NO-ERRORS)
                             (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP)
                             (:REWRITE LAS-TO-PAS-SUBSET-P-WITH-L-ADDRS-FROM-BIND-FREE)
                             (:REWRITE WB-NOT-CONSP-ADDR-LST)
                             (:TYPE-PRESCRIPTION ALL-TRANSLATION-GOVERNING-ADDRESSES)
                             (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER)
                             (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-SIGNED-BYTE-P-SMALLER)
                             (:REWRITE MEMBER-P-OF-SUBSET-IS-MEMBER-P-OF-SUPERSET)
                             (:REWRITE ACL2::LOGTAIL-IDENTITY)
                             (:REWRITE MEMBER-P-CANONICAL-ADDRESS-LISTP)
                             (:TYPE-PRESCRIPTION BOOLEANP)
                             (:REWRITE SUBSET-P-CONS-MEMBER-P-LEMMA)
                             (:REWRITE DISJOINT-P-MEMBERS-OF-TRUE-LIST-LIST-DISJOINT-P)
                             (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P-AUX)
                             (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P)
                             (:TYPE-PRESCRIPTION MEMBER-P-PHYSICAL-ADDRESS-P-PHYSICAL-ADDRESS-LISTP)
                             (:TYPE-PRESCRIPTION CTRI-IS-N64P)
                             (:REWRITE RIGHT-SHIFT-TO-LOGTAIL)
                             (:REWRITE
                              DISJOINTNESS-OF-ALL-TRANSLATION-GOVERNING-ADDRESSES-FROM-ALL-TRANSLATION-GOVERNING-ADDRESSES-SUBSET-P)
                             (:DEFINITION STRIP-CDRS)
                             (:REWRITE CDR-ADDR-RANGE)
                             (:TYPE-PRESCRIPTION MEMBER-P-PHYSICAL-ADDRESS-P)
                             (:TYPE-PRESCRIPTION ZIP)
                             (:REWRITE NOT-MEMBER-P-ADDR-RANGE)
                             (:META ACL2::CANCEL_PLUS-LESSP-CORRECT)
                             (:REWRITE LA-TO-PAS-VALUES-AND-MV-NTH-1-WB)
                             (:REWRITE IA32E-LA-TO-PA-VALUES-AND-MV-NTH-1-WB)
                             (:TYPE-PRESCRIPTION IFIX)
                             (:REWRITE DEFAULT-<-1)
                             (:REWRITE DISJOINT-P-TWO-ADDR-RANGES-THM-0)
                             (:REWRITE NOT-DISJOINT-P-TWO-ADDR-RANGES-THM)
                             (:REWRITE ACL2::EQUAL-CONSTANT-+)
                             (:REWRITE DEFAULT-<-2)
                             (:REWRITE DISJOINT-P-TWO-ADDR-RANGES-THM-1)
                             (:LINEAR ADDING-7-TO-PAGE-DIR-PTR-TABLE-ENTRY-ADDR)
                             (:LINEAR *PHYSICAL-ADDRESS-SIZE*P-PAGE-DIR-PTR-TABLE-ENTRY-ADDR)
                             (:REWRITE CAR-ADDR-RANGE)
                             (:REWRITE BITOPS::SIGNED-BYTE-P-OF-LOGTAIL)
                             (:REWRITE MEMBER-P-ADDR-RANGE)
                             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)
                             (:TYPE-PRESCRIPTION NATP)
                             (:TYPE-PRESCRIPTION ACL2::LOGTAIL-TYPE)
                             (:REWRITE STRIP-CDRS-ADDR-BYTE-ALISTP-IS-BYTE-LISTP)
                             (:LINEAR ADDING-7-TO-PML4-TABLE-ENTRY-ADDR)
                             (:LINEAR *PHYSICAL-ADDRESS-SIZE*P-PML4-TABLE-ENTRY-ADDR)
                             (:REWRITE SUBSET-P-CDR-Y)
                             (:REWRITE ACL2::CONSP-OF-CAR-WHEN-ATOM-LISTP)
                             (:REWRITE SEG-VISIBLEI-IS-N16P)
                             (:REWRITE SUBSET-P-CDR-X)
                             (:TYPE-PRESCRIPTION ATOM-LISTP)
                             (:LINEAR MEMBER-P-POS-VALUE)
                             (:LINEAR MEMBER-P-POS-1-VALUE)
                             (:LINEAR ACL2::INDEX-OF-<-LEN)
                             (:REWRITE NOT-MEMBER-P-ADDR-RANGE-FROM-NOT-MEMBER-P-ADDR-RANGE)
                             (:REWRITE MEMBER-P-ADDR-RANGE-FROM-MEMBER-P-ADDR-RANGE)
                             (:REWRITE DISJOINT-P-TWO-ADDR-RANGES-THM-3)
                             (:REWRITE DISJOINT-P-TWO-ADDR-RANGES-THM-2))))))

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
    (equal page-dir-ptr-table-base-addr
           (ash (loghead 40 (logtail 12 pml4-table-entry)) 12))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
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
     (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)))
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

;; TODO: Move to paging-defs.
(defthm read-from-physical-memory-and-mv-nth-1-wb-disjoint
  ;; Similar to rb-wb-disjoint-in-system-level-non-marking-mode
  (implies (and (disjoint-p
                 p-addrs
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                ;; I should try to eliminate the following hyp too...
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86))
                (x86p x86))
           (equal (read-from-physical-memory p-addrs (mv-nth 1 (wb addr-lst x86)))
                  (read-from-physical-memory p-addrs x86)))
  :hints (("Goal" :in-theory (e/d* (wb) ()))))

(defthm rb-of-1G-in-terms-of-read-from-physical-memory
  (implies (and (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86)))
           (equal
            (mv-nth 1 (rb (create-canonical-address-list
                           *2^30* (xr :rgf *rdi* x86)) :r x86))
            (read-from-physical-memory
             (mv-nth 1 (las-to-pas (create-canonical-address-list
                                    *2^30* (xr :rgf *rdi* x86)) :r (cpl x86) x86))
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
                             page-dir-ptr-table-base-addr
                             pml4-table-entry-addr
                             page-dir-ptr-table-entry-addr

                             pml4-table-entry-addr-to-c-program-optimized-form
                             pml4-table-entry-addr-to-c-program-optimized-form-gl
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl

                             member-p-strip-cars-of-remove-duplicate-keys
                             wb-remove-duplicate-writes-in-system-level-non-marking-mode
                             las-to-pas


                             not
                             bitops::logand-with-negated-bitmask
                             unsigned-byte-p
                             force (force))))))

(defthm rewire_dst_to_src-after-the-copy-source-p-addrs-open
  (implies (and
            (equal prog-len (len *rewire_dst_to_src*))
            (x86p x86)
            (not (programmer-level-mode x86))
            (not (page-structure-marking-mode x86))
            (not (alignment-checking-enabled-p x86))

            ;; CR3's reserved bits must be zero (MBZ).
            (equal (logtail 40 (ctri *cr3* x86)) 0)

            ;; Source address is canonical.
            (canonical-address-p (xr :rgf *rdi* x86))
            (canonical-address-p (+ -1 *2^30* (xr :rgf *rdi* x86)))
            ;; Source address is 1G-aligned.
            (equal (loghead 30 (xr :rgf *rdi* x86)) 0)
            ;; Destination address is canonical.
            (canonical-address-p (xr :rgf *rsi* x86))
            (canonical-address-p (+ -1 *2^30* (xr :rgf *rsi* x86)))
            ;; Destination address is 1G-aligned.
            (equal (loghead 30 (xr :rgf *rsi* x86)) 0)
            ;; Program addresses are canonical.
            (canonical-address-p (+ prog-len (xr :rip 0 x86)))
            ;; (canonical-address-p (xr :rip 0 x86))
            ;; Stack addresses are canonical.
            (canonical-address-p (+ -24 (xr :rgf *rsp* x86)))
            ;; (canonical-address-p (xr :rgf *rsp* x86))
            (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
            (equal (xr :ms 0 x86) nil)
            (equal (xr :fault 0 x86) nil)
            (equal (cpl x86) 0)
            (program-at (create-canonical-address-list prog-len (xr :rip 0 x86))
                        *rewire_dst_to_src* x86)

            ;; No errors encountered while translating the linear
            ;; addresses where the program is located.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list prog-len (xr :rip 0 x86))
                            :x (cpl x86) x86)))
            ;; Writing to stack: No errors encountered while
            ;; translating the linear addresses corresponding to the
            ;; program stack.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                            :w (cpl x86) x86)))
            ;; Reading from stack: No errors encountered while
            ;; translating the linear addresses corresponding to the
            ;; stack.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                            :r (cpl x86) x86)))
            ;; Reading from stack: The stack is located in a
            ;; contiguous region of memory --- no overlaps among
            ;; physical addresses of the stack. I need this hypothesis
            ;; so that rb-wb-equal-in-system-level-non-marking-mode
            ;; can fire.
            (no-duplicates-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                        :r (cpl x86) x86)))
            ;; The physical addresses corresponding to the program and
            ;; stack are disjoint.
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list prog-len (xr :rip 0 x86))
                        :x (cpl x86) x86))
             (mv-nth 1
                     (las-to-pas
                      (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                      :w (cpl x86) x86)))
            ;; Translation-governing addresses of the program are
            ;; disjoint from the physical addresses of the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list prog-len (xr :rip 0 x86))
              x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                        :w (cpl x86) x86)))
            ;; Translation-governing addresses of the stack are
            ;; disjoint from the physical addresses of the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
              x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                        :w (cpl x86) x86)))

            ;; ============================================================

            ;; Assumptions about the source PML4TE:

            ;; PML4TE linear addresses are canonical.
            ;; (canonical-address-p
            ;;  (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
            (canonical-address-p
             (+ 7 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))))

            ;; No errors encountered while translating the PML4TE linear addresses.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list
                             8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
                            :r (cpl x86) x86)))
            ;; The translation-governing addresses of PML4TE addresses
            ;; are disjoint from the physical addresses corresponding
            ;; to the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list
               8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
              x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
            ;; The PML4TE physical addresses are disjoint from the
            ;; stack physical addresses.
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
                        :r (cpl x86) x86))
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))

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
             1)

            ;; ------------------------------------------------------------

            ;; Assumptions about the source PDPTE:

            ;; PDPTE linear addresses are canonical.
            ;; (canonical-address-p
            ;;  (page-dir-ptr-table-entry-addr
            ;;   (xr :rgf *rdi* x86)
            ;;   (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
            (canonical-address-p
             (+ 7 (page-dir-ptr-table-entry-addr
                   (xr :rgf *rdi* x86)
                   (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86))))

            ;; No errors encountered while translating the PDPTE linear addresses.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list
                             8
                             (page-dir-ptr-table-entry-addr
                              (xr :rgf *rdi* x86)
                              (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                            :r (cpl x86) x86)))
            ;; The translation-governing addresses of PDPTE addresses
            ;; are disjoint from the physical addresses corresponding
            ;; to the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rdi* x86)
                (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
              x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
            ;; The PDPTE physical addresses are disjoint from the
            ;; stack physical addresses.
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (page-dir-ptr-table-entry-addr
                          (xr :rgf *rdi* x86)
                          (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                        :r (cpl x86) x86))
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))

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
                                (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
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
                                (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                              :r x86)))
                    :low 7 :width 1)
                   1)

            ;; ======================================================================

            ;; Direct map for paging structures, specifically
            ;; destination and source PML4E and PDPTE.
            (equal (mv-nth 1 (las-to-pas
                              (create-canonical-address-list
                               8
                               (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
                              :r (cpl x86) x86))
                   (addr-range
                    8
                    (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))))

            (equal (mv-nth 1 (las-to-pas
                              (create-canonical-address-list
                               8
                               (page-dir-ptr-table-entry-addr
                                (xr :rgf *rdi* x86)
                                (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                              :r 0 x86))
                   (addr-range
                    8
                    (page-dir-ptr-table-entry-addr
                     (xr :rgf *rdi* x86)
                     (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86))))


            ;; ======================================================================

            ;; No errors encountered while translating the source
            ;; linear addresses.
            (not
             (mv-nth 0
                     (las-to-pas (create-canonical-address-list
                                  *2^30* (xr :rgf *rdi* x86))
                                 :r (cpl x86) x86)))

            ;; -------
            (equal cpl (cpl x86)))

           (equal
            (mv-nth 1 (las-to-pas (create-canonical-address-list
                                   *2^30* (xr :rgf *rdi* x86)) :r cpl x86))
            (addr-range *2^30*
                        (ash (loghead 22
                                      (logtail 30
                                               (rm-low-64
                                                (page-dir-ptr-table-entry-addr
                                                 (xr :rgf *rdi* x86)
                                                 (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86))
                                                x86)))
                             30))))
  :hints (("Goal"
           :use ((:instance ;; las-to-pas-open-up-for-a-1G-page-setup
                  las-to-pas-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr-general
                  (lin-addr (xr :rgf *rdi* x86))
                  (r-w-x :r)
                  (cpl (cpl x86))))
           :do-not '(preprocess)
           :do-not-induct t
           :in-theory (e/d* (page-dir-ptr-table-base-addr
                             pml4-table-base-addr
                             pos member-p subset-p
                             page-size)

                            (rewire_dst_to_src-clk
                             (rewire_dst_to_src-clk)

                             ;; pml4-table-base-addr
                             ;; page-dir-ptr-table-base-addr
                             pml4-table-entry-addr
                             page-dir-ptr-table-entry-addr

                             pml4-table-entry-addr-to-c-program-optimized-form
                             pml4-table-entry-addr-to-c-program-optimized-form-gl
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl

                             member-p-strip-cars-of-remove-duplicate-keys
                             wb-remove-duplicate-writes-in-system-level-non-marking-mode
                             las-to-pas

                             (:REWRITE MV-NTH-1-IA32E-LA-TO-PA-SYSTEM-LEVEL-NON-MARKING-MODE-WHEN-ERROR)
                             (:REWRITE IA32E-LA-TO-PA-LOWER-12-BITS-ERROR)
                             (:REWRITE
                              DISJOINTNESS-OF-ALL-TRANSLATION-GOVERNING-ADDRESSES-FROM-ALL-TRANSLATION-GOVERNING-ADDRESSES-SUBSET-P)
                             (:TYPE-PRESCRIPTION NATP-PML4-TABLE-ENTRY-ADDR)
                             (:REWRITE ACL2::CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP)
                             (:REWRITE IA32E-LA-TO-PA-XW-STATE)
                             (:REWRITE R-W-X-IS-IRRELEVANT-FOR-MV-NTH-1-IA32E-LA-TO-PA-WHEN-NO-ERRORS)
                             (:LINEAR ADDING-7-TO-PML4-TABLE-ENTRY-ADDR)
                             (:LINEAR *PHYSICAL-ADDRESS-SIZE*P-PML4-TABLE-ENTRY-ADDR)
                             (:REWRITE LAS-TO-PAS-XW-STATE)
                             (:REWRITE ACL2::EQUAL-OF-BOOLEANS-REWRITE)
                             (:REWRITE LOGHEAD-UNEQUAL)
                             (:REWRITE NEGATIVE-LOGAND-TO-POSITIVE-LOGAND-WITH-INTEGERP-X)
                             (:DEFINITION COMBINE-BYTES)
                             (:REWRITE |(logand -4096 base-addr) = base-addr when low 12 bits are 0|)
                             (:REWRITE XR-IA32E-LA-TO-PA)
                             (:REWRITE ACL2::NFIX-WHEN-NOT-NATP)
                             (:REWRITE ACL2::NFIX-WHEN-NATP)
                             (:REWRITE CONSTANT-UPPER-BOUND-OF-LOGIOR-FOR-NATURALS)
                             (:LINEAR COMBINE-BYTES-SIZE-FOR-RM64-PROGRAMMER-LEVEL-MODE)
                             (:REWRITE ACL2::NATP-WHEN-INTEGERP)
                             (:REWRITE ACL2::NATP-WHEN-GTE-0)
                             (:REWRITE 4K-ALIGNED-PHYSICAL-ADDRESS-HELPER)
                             (:REWRITE BITOPS::SIGNED-BYTE-P-OF-LOGTAIL)
                             (:LINEAR ADDING-7-TO-PAGE-DIR-PTR-TABLE-ENTRY-ADDR)
                             (:LINEAR *PHYSICAL-ADDRESS-SIZE*P-PAGE-DIR-PTR-TABLE-ENTRY-ADDR)
                             (:TYPE-PRESCRIPTION ADDING-7-TO-PML4-TABLE-ENTRY-ADDR)
                             (:TYPE-PRESCRIPTION ADDING-7-TO-PAGE-DIR-PTR-TABLE-ENTRY-ADDR)
                             (:REWRITE ACL2::SIGNED-BYTE-P-LOGEXT)
                             (:TYPE-PRESCRIPTION BOOLEANP)
                             (:REWRITE LOGHEAD-64-N64-TO-I64-CANONICAL-ADDRESS)
                             (:TYPE-PRESCRIPTION PML4-TABLE-BASE-ADDR)
                             (:REWRITE GET-PREFIXES-OPENER-LEMMA-GROUP-4-PREFIX)
                             (:REWRITE GET-PREFIXES-OPENER-LEMMA-GROUP-3-PREFIX)
                             (:REWRITE GET-PREFIXES-OPENER-LEMMA-GROUP-2-PREFIX)
                             (:REWRITE GET-PREFIXES-OPENER-LEMMA-GROUP-1-PREFIX)
                             (:REWRITE MV-NTH-1-LAS-TO-PAS-SYSTEM-LEVEL-NON-MARKING-MODE-WHEN-ERROR)
                             (:REWRITE
                              COMBINE-BYTES-RB-IN-TERMS-OF-RB-SUBSET-P-IN-SYSTEM-LEVEL-NON-MARKING-MODE)
                             (:DEFINITION MEMBER-P)
                             (:LINEAR UNSIGNED-BYTE-P-OF-COMBINE-BYTES)
                             (:TYPE-PRESCRIPTION ACL2::|x < y  =>  0 < -x+y|)
                             (:REWRITE DEFAULT-+-2)
                             (:REWRITE ACL2::NATP-RW)
                             (:REWRITE IA32E-LA-TO-PA-LOWER-12-BITS)
                             (:REWRITE DEFAULT-+-1)
                             (:REWRITE ACL2::ASH-0)
                             (:REWRITE ACL2::ZIP-OPEN)
                             (:REWRITE LOGHEAD-OF-NON-INTEGERP)
                             (:TYPE-PRESCRIPTION ADDR-BYTE-ALISTP-CREATE-ADDR-BYTES-ALIST)
                             (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-3)
                             (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-2)
                             (:REWRITE ZF-SPEC-THM)
                             (:LINEAR ACL2::LOGHEAD-UPPER-BOUND)
                             (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2)
                             (:LINEAR SIZE-OF-COMBINE-BYTES)
                             (:REWRITE DISJOINT-P-SUBSET-P)
                             (:DEFINITION BINARY-APPEND)
                             (:DEFINITION CREATE-ADDR-BYTES-ALIST)
                             (:REWRITE MEMBER-P-OF-SUBSET-IS-MEMBER-P-OF-SUPERSET)
                             (:LINEAR RGFI-IS-I64P . 1)
                             (:REWRITE MEMBER-P-CDR)
                             (:REWRITE BITOPS::UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-LESS)
                             (:REWRITE ACL2::DIFFERENCE-UNSIGNED-BYTE-P)
                             (:LINEAR RGFI-IS-I64P . 2)
                             (:REWRITE ACL2::APPEND-WHEN-NOT-CONSP)
                             (:LINEAR RIP-IS-I48P . 2)
                             (:LINEAR RIP-IS-I48P . 1)
                             (:TYPE-PRESCRIPTION BYTE-IFY)
                             (:REWRITE ACL2::IFIX-WHEN-NOT-INTEGERP)
                             (:REWRITE BITOPS::BASIC-UNSIGNED-BYTE-P-OF-+)
                             (:REWRITE DISJOINT-P-APPEND-1)
                             (:REWRITE DEFAULT-<-1)
                             (:REWRITE DEFAULT-CAR)
                             (:REWRITE DEFAULT-CDR)
                             (:META ACL2::CANCEL_PLUS-LESSP-CORRECT)
                             (:REWRITE WB-NOT-CONSP-ADDR-LST)
                             (:DEFINITION NTHCDR)
                             (:REWRITE SUBSET-P-CDR-Y)
                             (:REWRITE IA32E-LA-TO-PA-LOWER-12-BITS-VALUE-OF-ADDRESS-WHEN-ERROR)
                             (:REWRITE DEFAULT-<-2)
                             (:TYPE-PRESCRIPTION N52P-MV-NTH-1-IA32E-LA-TO-PA)
                             (:META ACL2::CANCEL_PLUS-EQUAL-CORRECT)
                             (:DEFINITION NTH)
                             (:REWRITE CONSP-CREATE-ADDR-BYTES-ALIST)
                             (:REWRITE SUBSET-P-REFLEXIVE)
                             (:META ACL2::CANCEL_TIMES-EQUAL-CORRECT)
                             (:REWRITE SET::SETS-ARE-TRUE-LISTS)
                             (:LINEAR RFLAGS-IS-N32P)
                             (:REWRITE CONSP-BYTE-IFY)
                             (:DEFINITION TRUE-LISTP)
                             (:TYPE-PRESCRIPTION RFLAGS-IS-N32P)
                             (:REWRITE CDR-APPEND-IS-APPEND-CDR)
                             (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP)
                             (:REWRITE DISJOINT-P-MEMBERS-OF-TRUE-LIST-LIST-DISJOINT-P)
                             (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P-AUX)
                             (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P)
                             (:REWRITE SUBSET-P-CDR-X)
                             (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT)
                             (:REWRITE SET::NONEMPTY-MEANS-SET)
                             (:TYPE-PRESCRIPTION XW)
                             (:TYPE-PRESCRIPTION CONSP-CREATE-ADDR-BYTES-ALIST-IN-TERMS-OF-LEN)
                             (:TYPE-PRESCRIPTION CONSP-CREATE-ADDR-BYTES-ALIST)
                             (:TYPE-PRESCRIPTION NATP-COMBINE-BYTES)
                             (:TYPE-PRESCRIPTION TRUE-LISTP)
                             (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL)
                             (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP)
                             (:TYPE-PRESCRIPTION ALL-TRANSLATION-GOVERNING-ADDRESSES)
                             (:TYPE-PRESCRIPTION SET::SETP-TYPE)
                             (:TYPE-PRESCRIPTION SET::EMPTY-TYPE)
                             (:REWRITE ACL2::EQUAL-CONSTANT-+)
                             (:DEFINITION BYTE-LISTP)
                             (:REWRITE UNSIGNED-BYTE-P-OF-ASH)
                             (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL)
                             (:REWRITE BITOPS::LOGBITP-OF-NEGATIVE-CONST)
                             (:REWRITE BITOPS::LOGBITP-OF-MASK)
                             (:REWRITE BITOPS::LOGBITP-OF-CONST)
                             (:REWRITE GREATER-LOGBITP-OF-UNSIGNED-BYTE-P . 1)
                             (:META BITOPS::OPEN-LOGBITP-OF-CONST-LITE-META)
                             (:REWRITE RB-RETURNS-BYTE-LISTP)
                             (:REWRITE CAR-OF-APPEND)
                             (:TYPE-PRESCRIPTION RB-RETURNS-TRUE-LISTP)
                             (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER)
                             (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-SIGNED-BYTE-P-SMALLER)
                             (:TYPE-PRESCRIPTION CONSP-APPEND)
                             (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2)
                             (:DEFINITION ACONS)
                             (:REWRITE UNSIGNED-BYTE-P-OF-COMBINE-BYTES)
                             (:REWRITE UNSIGNED-BYTE-P-OF-LOGIOR)
                             (:TYPE-PRESCRIPTION NATP)
                             (:REWRITE SET::IN-SET)
                             (:TYPE-PRESCRIPTION ACL2::LOGTAIL-TYPE)
                             (:REWRITE ACL2::MEMBER-OF-CONS)
                             (:TYPE-PRESCRIPTION TRUE-LISTP-CREATE-ADDR-BYTES-ALIST)
                             (:TYPE-PRESCRIPTION RB-RETURNS-BYTE-LISTP)
                             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)
                             (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE)
                             (:TYPE-PRESCRIPTION COMBINE-BYTES)
                             (:DEFINITION N08P$INLINE)
                             (:DEFINITION LEN)
                             (:REWRITE XR-MV-NTH-2-IA32E-LA-TO-PA)
                             (:REWRITE BITOPS::LOGSQUASH-OF-LOGHEAD-ZERO)
                             (:REWRITE DEFAULT-UNARY-MINUS)
                             (:REWRITE LEN-OF-RB-IN-PROGRAMMER-LEVEL-MODE)
                             (:TYPE-PRESCRIPTION ACL2::BITP$INLINE)
                             (:TYPE-PRESCRIPTION ACL2::TRUE-LISTP-APPEND)
                             (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2)
                             (:REWRITE WEED-OUT-IRRELEVANT-LOGAND-WHEN-FIRST-OPERAND-CONSTANT)
                             (:REWRITE LOGAND-REDUNDANT)
                             (:LINEAR ASH-MONOTONE-2)
                             (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2)
                             (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 1)
                             (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1)
                             (:REWRITE
                              MV-NTH-1-IA32E-LA-TO-PA-MEMBER-OF-MV-NTH-1-LAS-TO-PAS-IF-LIN-ADDR-MEMBER-P)
                             (:LINEAR MV-NTH-1-IDIV-SPEC)
                             (:LINEAR MV-NTH-1-DIV-SPEC)
                             (:REWRITE UNSIGNED-BYTE-P-OF-LOGAND-2)
                             (:LINEAR ACL2::EXPT->-1)
                             (:REWRITE ACL2::UNSIGNED-BYTE-P-LOGHEAD)
                             (:TYPE-PRESCRIPTION ZIP)
                             (:LINEAR BITOPS::LOGAND-<-0-LINEAR)
                             (:REWRITE BITOPS::LOGIOR-FOLD-CONSTS)
                             (:LINEAR <=-LOGIOR)
                             (:LINEAR MEMBER-P-POS-VALUE)
                             (:LINEAR MEMBER-P-POS-1-VALUE)
                             (:LINEAR BITOPS::LOGIOR->=-0-LINEAR)
                             (:REWRITE NO-DUPLICATES-P-AND-APPEND)
                             (:REWRITE ACL2::SUBSETP-MEMBER . 2)
                             (:REWRITE ACL2::SUBSETP-MEMBER . 1)
                             (:TYPE-PRESCRIPTION WR32$INLINE)
                             (:REWRITE UNSIGNED-BYTE-P-OF-LOGAND-1)
                             (:REWRITE SUBSET-P-CONS-MEMBER-P-LEMMA)
                             (:REWRITE MEMBER-P-OF-NOT-A-CONSP)
                             (:REWRITE GET-PREFIXES-OPENER-LEMMA-ZERO-CNT)
                             (:REWRITE ACL2::EXPT-WITH-VIOLATED-GUARDS)
                             (:REWRITE BITOPS::BASIC-SIGNED-BYTE-P-OF-+)
                             (:TYPE-PRESCRIPTION ASH)
                             (:LINEAR ACL2::EXPT-IS-INCREASING-FOR-BASE>1)
                             (:DEFINITION MEMBER-EQUAL)
                             (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1)
                             (:LINEAR BITOPS::UPPER-BOUND-OF-LOGIOR-FOR-NATURALS)
                             (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP)

                             not
                             bitops::logand-with-negated-bitmask
                             unsigned-byte-p
                             force (force))))))

(defthm rewire_dst_to_src-after-the-copy-destination==source
  (implies (and
            (equal prog-len (len *rewire_dst_to_src*))
            (x86p x86)
            (not (programmer-level-mode x86))
            (not (page-structure-marking-mode x86))
            (not (alignment-checking-enabled-p x86))

            ;; CR3's reserved bits must be zero (MBZ).
            (equal (logtail 40 (ctri *cr3* x86)) 0)

            ;; Source address is canonical.
            (canonical-address-p (xr :rgf *rdi* x86))
            (canonical-address-p (+ -1 *2^30* (xr :rgf *rdi* x86)))
            ;; Source address is 1G-aligned.
            (equal (loghead 30 (xr :rgf *rdi* x86)) 0)
            ;; Destination address is canonical.
            (canonical-address-p (xr :rgf *rsi* x86))
            (canonical-address-p (+ -1 *2^30* (xr :rgf *rsi* x86)))
            ;; Destination address is 1G-aligned.
            (equal (loghead 30 (xr :rgf *rsi* x86)) 0)
            ;; Program addresses are canonical.
            (canonical-address-p (+ prog-len (xr :rip 0 x86)))
            ;; (canonical-address-p (xr :rip 0 x86))
            ;; Stack addresses are canonical.
            (canonical-address-p (+ -24 (xr :rgf *rsp* x86)))
            ;; (canonical-address-p (xr :rgf *rsp* x86))
            (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
            (equal (xr :ms 0 x86) nil)
            (equal (xr :fault 0 x86) nil)
            (equal (cpl x86) 0)
            (program-at (create-canonical-address-list prog-len (xr :rip 0 x86))
                        *rewire_dst_to_src* x86)

            ;; No errors encountered while translating the linear
            ;; addresses where the program is located.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list prog-len (xr :rip 0 x86))
                            :x (cpl x86) x86)))
            ;; Writing to stack: No errors encountered while
            ;; translating the linear addresses corresponding to the
            ;; program stack.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list
                             8
                             (+ -24 (xr :rgf *rsp* x86)))
                            :w (cpl x86) x86)))
            ;; Reading from stack: No errors encountered while
            ;; translating the linear addresses corresponding to the
            ;; stack.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list
                             8 (+ -24 (xr :rgf *rsp* x86)))
                            :r (cpl x86) x86)))
            ;; Reading from stack: The stack is located in a
            ;; contiguous region of memory --- no overlaps among
            ;; physical addresses of the stack. I need this hypothesis
            ;; so that rb-wb-equal-in-system-level-non-marking-mode
            ;; can fire.
            (no-duplicates-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8 (+ -24 (xr :rgf *rsp* x86)))
                        :r (cpl x86) x86)))
            ;; The physical addresses corresponding to the program and
            ;; stack are disjoint.
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list prog-len (xr :rip 0 x86))
                        :x (cpl x86) x86))
             (mv-nth 1
                     (las-to-pas
                      (create-canonical-address-list
                       8 (+ -24 (xr :rgf *rsp* x86)))
                      :w (cpl x86) x86)))
            ;; Translation-governing addresses of the program are
            ;; disjoint from the physical addresses of the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list prog-len (xr :rip 0 x86))
              x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8 (+ -24 (xr :rgf *rsp* x86)))
                        :w (cpl x86) x86)))
            ;; Translation-governing addresses of the stack are
            ;; disjoint from the physical addresses of the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list
               8 (+ -24 (xr :rgf *rsp* x86)))
              x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8 (+ -24 (xr :rgf *rsp* x86)))
                        :w (cpl x86) x86)))

            ;; ============================================================

            ;; Assumptions about the source PML4TE:

            ;; PML4TE linear addresses are canonical.
            ;; (canonical-address-p
            ;;  (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
            (canonical-address-p
             (+ 7 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))))

            ;; No errors encountered while translating the PML4TE linear addresses.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list
                             8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
                            :r (cpl x86) x86)))
            ;; The translation-governing addresses of PML4TE addresses
            ;; are disjoint from the physical addresses corresponding
            ;; to the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list
               8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
              x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
            ;; The PML4TE physical addresses are disjoint from the
            ;; stack physical addresses.
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
                        :r (cpl x86) x86))
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))

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
             1)

            ;; ------------------------------------------------------------

            ;; Assumptions about the source PDPTE:

            ;; PDPTE linear addresses are canonical.
            ;; (canonical-address-p
            ;;  (page-dir-ptr-table-entry-addr
            ;;   (xr :rgf *rdi* x86)
            ;;   (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
            (canonical-address-p
             (+ 7 (page-dir-ptr-table-entry-addr
                   (xr :rgf *rdi* x86)
                   (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86))))

            ;; No errors encountered while translating the PDPTE linear addresses.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list
                             8
                             (page-dir-ptr-table-entry-addr
                              (xr :rgf *rdi* x86)
                              (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                            :r (cpl x86) x86)))
            ;; The translation-governing addresses of PDPTE addresses
            ;; are disjoint from the physical addresses corresponding
            ;; to the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rdi* x86)
                (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
              x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
            ;; The PDPTE physical addresses are disjoint from the
            ;; stack physical addresses.
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (page-dir-ptr-table-entry-addr
                          (xr :rgf *rdi* x86)
                          (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                        :r (cpl x86) x86))
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))

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
                                (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
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
                                (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                              :r x86)))
                    :low 7 :width 1)
                   1)

            ;; ============================================================

            ;; Assumptions about the destination PML4TE:

            ;; PML4TE linear addresses are canonical.
            ;; (canonical-address-p
            ;;  (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
            (canonical-address-p
             (+ 7 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))))

            ;; No errors encountered while translating the PML4TE linear addresses.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list
                             8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
                            :r (cpl x86) x86)))
            ;; The translation-governing addresses of PML4TE addresses
            ;; are disjoint from the physical addresses corresponding
            ;; to the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list
               8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
              x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
            ;; The PML4TE physical addresses are disjoint from the
            ;; stack physical addresses.
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
                        :r (cpl x86) x86))
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))

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
             1)

            ;; ------------------------------------------------------------

            ;; Assumptions about the destination PDPTE:

            ;; PDPTE linear addresses are canonical.
            (canonical-address-p
             (page-dir-ptr-table-entry-addr
              (xr :rgf *rsi* x86)
              (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
            (canonical-address-p
             (+ 7 (page-dir-ptr-table-entry-addr
                   (xr :rgf *rsi* x86)
                   (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86))))

            ;; No errors encountered while translating the PDPTE
            ;; linear addresses on behalf of a read.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list
                             8
                             (page-dir-ptr-table-entry-addr
                              (xr :rgf *rsi* x86)
                              (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                            :r (cpl x86) x86)))
            ;; No errors encountered while translating the PDPTE
            ;; linear addresses on behalf of a write.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list
                             8
                             (page-dir-ptr-table-entry-addr
                              (xr :rgf *rsi* x86)
                              (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                            :w (cpl x86) x86)))
            ;; The translation-governing addresses of PDPTE addresses
            ;; are disjoint from the physical addresses corresponding
            ;; to the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
              x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
            ;; The PDPTE physical addresses are disjoint from the
            ;; stack physical addresses.
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (page-dir-ptr-table-entry-addr
                          (xr :rgf *rsi* x86)
                          (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                        :r (cpl x86) x86))
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))

            ;; The physical addresses corresponding to the program are
            ;; disjoint from those of the PDPTE (on behalf of a
            ;; write).
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list prog-len (xr :rip 0 x86))
                        :x (cpl x86) x86))
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (page-dir-ptr-table-entry-addr
                          (xr :rgf *rsi* x86)
                          (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                        :w (cpl x86) x86)))

            ;; Translation-governing addresses of the program are
            ;; disjoint from the PDPTE physical addresses (on behalf
            ;; of a write).
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list prog-len (xr :rip 0 x86))
              x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (page-dir-ptr-table-entry-addr
                          (xr :rgf *rsi* x86)
                          (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                        :w (cpl x86) x86)))
            ;; Translation-governing addresses of the stack are
            ;; disjoint from the physical addresses of the PDPTE (on
            ;; behalf of a write).
            ;; (disjoint-p
            ;;  (all-translation-governing-addresses
            ;;   (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
            ;;   x86)
            ;;  (mv-nth 1 (las-to-pas
            ;;             (create-canonical-address-list
            ;;              8
            ;;              (page-dir-ptr-table-entry-addr
            ;;               (xr :rgf *rsi* x86)
            ;;               (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
            ;;             :w (cpl x86) x86)))

            ;; Destination PDPTE does not have the P or PS bit cleared
            ;; (i.e., the entry is present and it points to a 1G
            ;; page).
            (equal (part-select
                    (combine-bytes
                     (mv-nth 1
                             (rb
                              (create-canonical-address-list
                               8
                               (page-dir-ptr-table-entry-addr
                                (xr :rgf *rsi* x86)
                                (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
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
                                (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                              :r x86)))
                    :low 7 :width 1)
                   1)

            ;; ======================================================================
            ;; For the final ret instruction:

            ;; Reading from stack for the final ret instruction
            ;; doesn't cause errors.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list
                             8 (xr :rgf *rsp* x86))
                            :r (cpl x86) x86)))

            ;; The program and the ret address on the stack are
            ;; disjoint.
            ;; (disjoint-p
            ;;  (mv-nth 1 (las-to-pas
            ;;             (create-canonical-address-list prog-len (xr :rip 0 x86))
            ;;             :x (cpl x86) x86))
            ;;  (mv-nth 1 (las-to-pas
            ;;             (create-canonical-address-list 8 (xr :rgf *rsp* x86))
            ;;             :r (cpl x86) x86)))

            ;; The translation-governing addresses of the ret address
            ;; are disjoint from the destination PDPTE.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list 8 (xr :rgf *rsp* x86)) x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (page-dir-ptr-table-entry-addr
                          (xr :rgf *rsi* x86)
                          (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                        :r (cpl x86) x86)))

            ;; The destination PDPTE is disjoint from the ret address
            ;; on the stack.
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (xr :rgf *rsp* x86))
                        :r (cpl x86) x86))
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (page-dir-ptr-table-entry-addr
                          (xr :rgf *rsi* x86)
                          (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                        :r (cpl x86) x86)))
            ;; The destination PDPTE is disjoint from the rest of the stack.
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8
                         (page-dir-ptr-table-entry-addr
                          (xr :rgf *rsi* x86)
                          (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                        :r (cpl x86) x86))
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))

            ;; The ret address on the stack is disjoint from the rest
            ;; of the stack.
            (disjoint-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (xr :rgf *rsp* x86))
                        :r (cpl x86) x86))
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))

            ;; The translation-governing addresses of the return
            ;; address on the stack are disjoint from the physical
            ;; addresses of the rest of the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list 8 (xr :rgf *rsp* x86)) x86)
             (mv-nth 1
                     (las-to-pas (create-canonical-address-list
                                  8 (+ -24 (xr :rgf *rsp* x86)))
                                 :w (cpl x86) x86)))

            ;; Return address on the stack is canonical.
            (canonical-address-p
             (logext 64
                     (combine-bytes
                      (mv-nth 1
                              (rb (create-canonical-address-list
                                   8 (xr :rgf *rsp* x86))
                                  :r x86)))))

            ;; ======================================================================

            ;; Direct map for paging structures, specifically
            ;; destination and source PML4E and PDPTE.
            (equal (mv-nth 1 (las-to-pas
                              (create-canonical-address-list
                               8
                               (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
                              :r (cpl x86) x86))
                   (addr-range
                    8
                    (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))))

            (equal (mv-nth 1 (las-to-pas
                              (create-canonical-address-list
                               8
                               (page-dir-ptr-table-entry-addr
                                (xr :rgf *rdi* x86)
                                (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
                              :r 0 x86))
                   (addr-range
                    8
                    (page-dir-ptr-table-entry-addr
                     (xr :rgf *rdi* x86)
                     (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86))))

            (equal (mv-nth 1 (las-to-pas
                              (create-canonical-address-list
                               8
                               (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
                              :r (cpl x86) x86))
                   (addr-range
                    8
                    (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))))

            (equal (mv-nth 1 (las-to-pas
                              (create-canonical-address-list
                               8
                               (page-dir-ptr-table-entry-addr
                                (xr :rgf *rsi* x86)
                                (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
                              :r 0 x86))
                   (addr-range
                    8
                    (page-dir-ptr-table-entry-addr
                     (xr :rgf *rsi* x86)
                     (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86))))


            ;; ======================================================================

            ;; TO-DO: Check these preconditions. Also, change
            ;; rm-low-64 to rb. We have a direct map after all.

            ;; The source physical addresses are disjoint from the the
            ;; physical addresses of the destination PDPTE.
            (disjoint-p
             (addr-range *2^30*
                         (ash (loghead 22 (logtail 30
                                                   (rm-low-64
                                                    (page-dir-ptr-table-entry-addr
                                                     (xr :rgf *rdi* x86)
                                                     (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86))
                                                    x86)))
                              30))
             (addr-range 8
                         (page-dir-ptr-table-entry-addr
                          (xr :rgf *rsi* x86)
                          (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86))))

            ;; The destination PML4E and PDPTE are disjoint.
            (disjoint-p
             (addr-range 8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
             (addr-range 8 (page-dir-ptr-table-entry-addr
                            (xr :rgf *rsi* x86)
                            (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86))))

            ;; The translation-governing addresses of the destination
            ;; are disjoint from the physical addresses corresponding
            ;; to the stack.
            (disjoint-p
             (all-translation-governing-addresses
              (create-canonical-address-list *2^30* (xr :rgf *rsi* x86)) x86)
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list
                         8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))


            ;; No errors encountered while translating the destination
            ;; linear addresses.
            (not
             (mv-nth 0
                     (las-to-pas (create-canonical-address-list
                                  *2^30* (xr :rgf *rsi* x86))
                                 :r (cpl x86) x86)))

            ;; The source addresses are disjoint from the physical
            ;; addresses corresponding to the stack.
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
                             (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86))
                            x86)))
               30))
             (mv-nth
              1
              (las-to-pas (create-canonical-address-list
                           8 (+ -24 (xr :rgf *rsp* x86)))
                          :w (cpl x86) x86)))

            ;; No errors encountered while translating the source
            ;; linear addresses.
            (not
             (mv-nth 0
                     (las-to-pas (create-canonical-address-list
                                  *2^30* (xr :rgf *rdi* x86))
                                 :r (cpl x86) x86))))

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
                             pos member-p subset-p
                             page-dir-ptr-table-base-addr
                             page-size)

                            (rewire_dst_to_src-clk
                             (rewire_dst_to_src-clk)

                             pml4-table-base-addr
                             ;; page-dir-ptr-table-base-addr
                             pml4-table-entry-addr
                             page-dir-ptr-table-entry-addr

                             pml4-table-entry-addr-to-c-program-optimized-form
                             pml4-table-entry-addr-to-c-program-optimized-form-gl
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                             page-dir-ptr-table-entry-addr-to-c-program-optimized-form-gl

                             member-p-strip-cars-of-remove-duplicate-keys
                             wb-remove-duplicate-writes-in-system-level-non-marking-mode
                             las-to-pas

                             (:REWRITE MV-NTH-1-IA32E-LA-TO-PA-SYSTEM-LEVEL-NON-MARKING-MODE-WHEN-ERROR)
                             (:REWRITE IA32E-LA-TO-PA-LOWER-12-BITS-ERROR)
                             (:REWRITE
                              DISJOINTNESS-OF-ALL-TRANSLATION-GOVERNING-ADDRESSES-FROM-ALL-TRANSLATION-GOVERNING-ADDRESSES-SUBSET-P)
                             (:TYPE-PRESCRIPTION NATP-PML4-TABLE-ENTRY-ADDR)
                             (:REWRITE ACL2::CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP)
                             (:REWRITE IA32E-LA-TO-PA-XW-STATE)
                             (:REWRITE R-W-X-IS-IRRELEVANT-FOR-MV-NTH-1-IA32E-LA-TO-PA-WHEN-NO-ERRORS)
                             (:LINEAR ADDING-7-TO-PML4-TABLE-ENTRY-ADDR)
                             (:LINEAR *PHYSICAL-ADDRESS-SIZE*P-PML4-TABLE-ENTRY-ADDR)
                             (:REWRITE LAS-TO-PAS-XW-STATE)
                             (:REWRITE ACL2::EQUAL-OF-BOOLEANS-REWRITE)
                             (:REWRITE LOGHEAD-UNEQUAL)
                             (:REWRITE NEGATIVE-LOGAND-TO-POSITIVE-LOGAND-WITH-INTEGERP-X)
                             (:DEFINITION COMBINE-BYTES)
                             (:REWRITE |(logand -4096 base-addr) = base-addr when low 12 bits are 0|)
                             (:REWRITE XR-IA32E-LA-TO-PA)
                             (:REWRITE ACL2::NFIX-WHEN-NOT-NATP)
                             (:REWRITE ACL2::NFIX-WHEN-NATP)
                             (:REWRITE CONSTANT-UPPER-BOUND-OF-LOGIOR-FOR-NATURALS)
                             (:LINEAR COMBINE-BYTES-SIZE-FOR-RM64-PROGRAMMER-LEVEL-MODE)
                             (:REWRITE ACL2::NATP-WHEN-INTEGERP)
                             (:REWRITE ACL2::NATP-WHEN-GTE-0)
                             (:REWRITE 4K-ALIGNED-PHYSICAL-ADDRESS-HELPER)
                             (:REWRITE BITOPS::SIGNED-BYTE-P-OF-LOGTAIL)
                             (:LINEAR ADDING-7-TO-PAGE-DIR-PTR-TABLE-ENTRY-ADDR)
                             (:LINEAR *PHYSICAL-ADDRESS-SIZE*P-PAGE-DIR-PTR-TABLE-ENTRY-ADDR)
                             (:TYPE-PRESCRIPTION ADDING-7-TO-PML4-TABLE-ENTRY-ADDR)
                             (:TYPE-PRESCRIPTION ADDING-7-TO-PAGE-DIR-PTR-TABLE-ENTRY-ADDR)
                             (:REWRITE ACL2::SIGNED-BYTE-P-LOGEXT)
                             (:TYPE-PRESCRIPTION BOOLEANP)
                             (:REWRITE LOGHEAD-64-N64-TO-I64-CANONICAL-ADDRESS)
                             (:TYPE-PRESCRIPTION PML4-TABLE-BASE-ADDR)
                             (:REWRITE GET-PREFIXES-OPENER-LEMMA-GROUP-4-PREFIX)
                             (:REWRITE GET-PREFIXES-OPENER-LEMMA-GROUP-3-PREFIX)
                             (:REWRITE GET-PREFIXES-OPENER-LEMMA-GROUP-2-PREFIX)
                             (:REWRITE GET-PREFIXES-OPENER-LEMMA-GROUP-1-PREFIX)
                             (:REWRITE MV-NTH-1-LAS-TO-PAS-SYSTEM-LEVEL-NON-MARKING-MODE-WHEN-ERROR)
                             (:REWRITE
                              COMBINE-BYTES-RB-IN-TERMS-OF-RB-SUBSET-P-IN-SYSTEM-LEVEL-NON-MARKING-MODE)
                             (:DEFINITION MEMBER-P)
                             (:LINEAR UNSIGNED-BYTE-P-OF-COMBINE-BYTES)
                             (:TYPE-PRESCRIPTION ACL2::|x < y  =>  0 < -x+y|)
                             (:REWRITE DEFAULT-+-2)
                             (:REWRITE ACL2::NATP-RW)
                             (:REWRITE IA32E-LA-TO-PA-LOWER-12-BITS)
                             (:REWRITE DEFAULT-+-1)
                             (:REWRITE ACL2::ASH-0)
                             (:REWRITE ACL2::ZIP-OPEN)
                             (:REWRITE LOGHEAD-OF-NON-INTEGERP)
                             (:TYPE-PRESCRIPTION ADDR-BYTE-ALISTP-CREATE-ADDR-BYTES-ALIST)
                             (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-3)
                             (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-2)
                             (:REWRITE ZF-SPEC-THM)
                             (:LINEAR ACL2::LOGHEAD-UPPER-BOUND)
                             (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2)
                             (:LINEAR SIZE-OF-COMBINE-BYTES)
                             (:REWRITE DISJOINT-P-SUBSET-P)
                             (:DEFINITION BINARY-APPEND)
                             (:DEFINITION CREATE-ADDR-BYTES-ALIST)
                             (:REWRITE MEMBER-P-OF-SUBSET-IS-MEMBER-P-OF-SUPERSET)
                             (:LINEAR RGFI-IS-I64P . 1)
                             (:REWRITE MEMBER-P-CDR)
                             (:REWRITE BITOPS::UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-LESS)
                             (:REWRITE ACL2::DIFFERENCE-UNSIGNED-BYTE-P)
                             (:LINEAR RGFI-IS-I64P . 2)
                             (:REWRITE ACL2::APPEND-WHEN-NOT-CONSP)
                             (:LINEAR RIP-IS-I48P . 2)
                             (:LINEAR RIP-IS-I48P . 1)
                             (:TYPE-PRESCRIPTION BYTE-IFY)
                             (:REWRITE ACL2::IFIX-WHEN-NOT-INTEGERP)
                             (:REWRITE BITOPS::BASIC-UNSIGNED-BYTE-P-OF-+)
                             (:REWRITE DISJOINT-P-APPEND-1)
                             (:REWRITE DEFAULT-<-1)
                             (:REWRITE DEFAULT-CAR)
                             (:REWRITE DEFAULT-CDR)
                             (:META ACL2::CANCEL_PLUS-LESSP-CORRECT)
                             (:REWRITE WB-NOT-CONSP-ADDR-LST)
                             (:DEFINITION NTHCDR)
                             (:REWRITE SUBSET-P-CDR-Y)
                             (:REWRITE IA32E-LA-TO-PA-LOWER-12-BITS-VALUE-OF-ADDRESS-WHEN-ERROR)
                             (:REWRITE DEFAULT-<-2)
                             (:TYPE-PRESCRIPTION N52P-MV-NTH-1-IA32E-LA-TO-PA)
                             (:META ACL2::CANCEL_PLUS-EQUAL-CORRECT)
                             (:DEFINITION NTH)
                             (:REWRITE CONSP-CREATE-ADDR-BYTES-ALIST)
                             (:REWRITE SUBSET-P-REFLEXIVE)
                             (:META ACL2::CANCEL_TIMES-EQUAL-CORRECT)
                             (:REWRITE SET::SETS-ARE-TRUE-LISTS)
                             (:LINEAR RFLAGS-IS-N32P)
                             (:REWRITE CONSP-BYTE-IFY)
                             (:DEFINITION TRUE-LISTP)
                             (:TYPE-PRESCRIPTION RFLAGS-IS-N32P)
                             (:REWRITE CDR-APPEND-IS-APPEND-CDR)
                             (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP)
                             (:REWRITE DISJOINT-P-MEMBERS-OF-TRUE-LIST-LIST-DISJOINT-P)
                             (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P-AUX)
                             (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P)
                             (:REWRITE SUBSET-P-CDR-X)
                             (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT)
                             (:REWRITE SET::NONEMPTY-MEANS-SET)
                             (:TYPE-PRESCRIPTION XW)
                             (:TYPE-PRESCRIPTION CONSP-CREATE-ADDR-BYTES-ALIST-IN-TERMS-OF-LEN)
                             (:TYPE-PRESCRIPTION CONSP-CREATE-ADDR-BYTES-ALIST)
                             (:TYPE-PRESCRIPTION NATP-COMBINE-BYTES)
                             (:TYPE-PRESCRIPTION TRUE-LISTP)
                             (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL)
                             (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP)
                             (:TYPE-PRESCRIPTION ALL-TRANSLATION-GOVERNING-ADDRESSES)
                             (:TYPE-PRESCRIPTION SET::SETP-TYPE)
                             (:TYPE-PRESCRIPTION SET::EMPTY-TYPE)
                             (:REWRITE ACL2::EQUAL-CONSTANT-+)
                             (:DEFINITION BYTE-LISTP)
                             (:REWRITE UNSIGNED-BYTE-P-OF-ASH)
                             (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL)
                             (:REWRITE BITOPS::LOGBITP-OF-NEGATIVE-CONST)
                             (:REWRITE BITOPS::LOGBITP-OF-MASK)
                             (:REWRITE BITOPS::LOGBITP-OF-CONST)
                             (:REWRITE GREATER-LOGBITP-OF-UNSIGNED-BYTE-P . 1)
                             (:META BITOPS::OPEN-LOGBITP-OF-CONST-LITE-META)
                             (:REWRITE RB-RETURNS-BYTE-LISTP)
                             (:REWRITE CAR-OF-APPEND)
                             (:TYPE-PRESCRIPTION RB-RETURNS-TRUE-LISTP)
                             (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER)
                             (:REWRITE BITOPS::SIGNED-BYTE-P-WHEN-SIGNED-BYTE-P-SMALLER)
                             (:TYPE-PRESCRIPTION CONSP-APPEND)
                             (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2)
                             (:DEFINITION ACONS)
                             (:REWRITE UNSIGNED-BYTE-P-OF-COMBINE-BYTES)
                             (:REWRITE UNSIGNED-BYTE-P-OF-LOGIOR)
                             (:TYPE-PRESCRIPTION NATP)
                             (:REWRITE SET::IN-SET)
                             (:TYPE-PRESCRIPTION ACL2::LOGTAIL-TYPE)
                             (:REWRITE ACL2::MEMBER-OF-CONS)
                             (:TYPE-PRESCRIPTION TRUE-LISTP-CREATE-ADDR-BYTES-ALIST)
                             (:TYPE-PRESCRIPTION RB-RETURNS-BYTE-LISTP)
                             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)
                             (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE)
                             (:TYPE-PRESCRIPTION COMBINE-BYTES)
                             (:DEFINITION N08P$INLINE)
                             (:DEFINITION LEN)
                             (:REWRITE XR-MV-NTH-2-IA32E-LA-TO-PA)
                             (:REWRITE BITOPS::LOGSQUASH-OF-LOGHEAD-ZERO)
                             (:REWRITE DEFAULT-UNARY-MINUS)
                             (:REWRITE LEN-OF-RB-IN-PROGRAMMER-LEVEL-MODE)
                             (:TYPE-PRESCRIPTION ACL2::BITP$INLINE)
                             (:TYPE-PRESCRIPTION ACL2::TRUE-LISTP-APPEND)
                             (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2)
                             (:REWRITE WEED-OUT-IRRELEVANT-LOGAND-WHEN-FIRST-OPERAND-CONSTANT)
                             (:REWRITE LOGAND-REDUNDANT)
                             (:LINEAR ASH-MONOTONE-2)
                             (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2)
                             (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 1)
                             (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1)
                             (:REWRITE
                              MV-NTH-1-IA32E-LA-TO-PA-MEMBER-OF-MV-NTH-1-LAS-TO-PAS-IF-LIN-ADDR-MEMBER-P)
                             (:LINEAR MV-NTH-1-IDIV-SPEC)
                             (:LINEAR MV-NTH-1-DIV-SPEC)
                             (:REWRITE UNSIGNED-BYTE-P-OF-LOGAND-2)
                             (:LINEAR ACL2::EXPT->-1)
                             (:REWRITE ACL2::UNSIGNED-BYTE-P-LOGHEAD)
                             (:TYPE-PRESCRIPTION ZIP)
                             (:LINEAR BITOPS::LOGAND-<-0-LINEAR)
                             (:REWRITE BITOPS::LOGIOR-FOLD-CONSTS)
                             (:LINEAR <=-LOGIOR)
                             (:LINEAR MEMBER-P-POS-VALUE)
                             (:LINEAR MEMBER-P-POS-1-VALUE)
                             (:LINEAR BITOPS::LOGIOR->=-0-LINEAR)
                             (:REWRITE NO-DUPLICATES-P-AND-APPEND)
                             (:REWRITE ACL2::SUBSETP-MEMBER . 2)
                             (:REWRITE ACL2::SUBSETP-MEMBER . 1)
                             (:TYPE-PRESCRIPTION WR32$INLINE)
                             (:REWRITE UNSIGNED-BYTE-P-OF-LOGAND-1)
                             (:REWRITE SUBSET-P-CONS-MEMBER-P-LEMMA)
                             (:REWRITE MEMBER-P-OF-NOT-A-CONSP)
                             (:REWRITE GET-PREFIXES-OPENER-LEMMA-ZERO-CNT)
                             (:REWRITE ACL2::EXPT-WITH-VIOLATED-GUARDS)
                             (:REWRITE BITOPS::BASIC-SIGNED-BYTE-P-OF-+)
                             (:TYPE-PRESCRIPTION ASH)
                             (:LINEAR ACL2::EXPT-IS-INCREASING-FOR-BASE>1)
                             (:DEFINITION MEMBER-EQUAL)
                             (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1)
                             (:LINEAR BITOPS::UPPER-BOUND-OF-LOGIOR-FOR-NATURALS)
                             (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP)

                             not
                             bitops::logand-with-negated-bitmask
                             unsigned-byte-p
                             force (force))))))

;; ======================================================================
