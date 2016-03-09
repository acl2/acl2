;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "../utilities/system-level-mode/paging-defs")

(include-book "centaur/bitops/ihs-extensions" :dir :system)
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

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

(acl2::add-untranslate-pattern-function
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
 *rewire_dst_to_src*)

;; ======================================================================

;; All the lemmas below need a home later...

(defthm canonical-address-p-and-logext-48
  (implies (canonical-address-p a)
           (equal (logext 48 a) a))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p) ()))))

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

(defthm xr-fault-wb-in-system-level-mode
  (implies (and (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (page-structure-marking-mode x86)))
           (equal (xr :fault 0 (mv-nth 1 (wb addr-lst x86)))
                  (xr :fault 0 x86)))
  :hints
  (("Goal" :in-theory (e/d* (wb)
                            (write-to-physical-memory force (force))))))

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

(defthm disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses
  (implies (and (bind-free
                 (find-l-addrs-from-fn 'all-translation-governing-addresses 'l-addrs mfc state)
                 (l-addrs))
                (syntaxp (not (eq l-addrs-subset l-addrs)))
                (disjoint-p (all-translation-governing-addresses l-addrs x86) other-p-addrs)
                (subset-p l-addrs-subset l-addrs))
           (disjoint-p (all-translation-governing-addresses l-addrs-subset x86) other-p-addrs))
  :hints (("Goal" :in-theory (e/d* (subset-p member-p) ()))))

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

(defthm wb-not-consp-addr-lst
  (implies (not (consp addr-lst))
           (equal (mv-nth 1 (wb addr-lst x86))
                  x86))
  :hints (("Goal" :in-theory (e/d* (wb) (force (force))))))

(defthm alignment-checking-enabled-p-and-mv-nth-1-wb
  (equal (alignment-checking-enabled-p (mv-nth 1 (wb addr-lst x86)))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (e/d* (alignment-checking-enabled-p
                                    wb
                                    write-to-physical-memory
                                    flgi)
                                   (member-p-strip-cars-of-remove-duplicate-keys)))))

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
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                (subset-p l-addrs-subset l-addrs)
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

;; ================================================================================

(i-am-here)

;; (acl2::why x86-run-opener-not-ms-not-zp-n)
;; (acl2::why x86-fetch-decode-execute-opener)
;; (acl2::why get-prefixes-opener-lemma-no-prefix-byte)
;; (acl2::why ia32e-la-to-pa-values-and-mv-nth-1-wb)
;; (acl2::why rb-in-terms-of-nth-and-pos-in-system-level-non-marking-mode)
;; (acl2::why combine-bytes-rb-in-terms-of-rb-subset-p-in-system-level-non-marking-mode)
;; (acl2::why program-at-wb-disjoint-in-system-level-non-marking-mode)
;; (acl2::why disjointness-of-translation-governing-addresses-from-all-translation-governing-addresses)
;; (acl2::why la-to-pas-values-and-mv-nth-1-wb)


;; Argh, ACL2's default ancestors-check is killing me --- it prevents
;; program-at-wb-disjoint-in-system-level-non-marking-mode from being
;; used. So, I'm going to use Sol's trivial ancestors-check version.
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))

(defthm rewire_dst_to_src-effects
  (implies (and
            (equal prog-len (len *rewire_dst_to_src*))
            (x86p x86)
            (not (programmer-level-mode x86))
            (not (page-structure-marking-mode x86))
            (not (alignment-checking-enabled-p x86))

            (canonical-address-p (+ prog-len (xr :rip 0 x86)))
            (canonical-address-p (xr :rip 0 x86))
            (canonical-address-p (+ -24 (xr :rgf *rsp* x86)))
            (canonical-address-p (xr :rgf *rsp* x86))
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
                            :w 0 x86)))
            ;; Reading from stack: No errors encountered while
            ;; translating the linear addresses corresponding to the
            ;; stack.
            (not (mv-nth 0 (las-to-pas
                            (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                            :r 0 x86)))
            ;; Reading from stack: The stack is located in a
            ;; contiguous region of memory --- no overlaps among
            ;; physical addresses of the stack. I need this hypothesis
            ;; so that rb-wb-equal-in-system-level-non-marking-mode
            ;; can fire.
            (no-duplicates-p
             (mv-nth 1 (las-to-pas
                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                        :r 0 x86)))
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

            ;; Other stuff from the 9th instruction:
            ;; (CANONICAL-ADDRESS-P
            ;;  (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
            ;;          (LOGAND 4088
            ;;                  (LOGHEAD 28
            ;;                           (LOGTAIL 36 (XR :RGF *RDI* X86))))))

            )

           (equal (x86-run 8 x86)
                  xxx))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (instruction-decoding-and-spec-rules
                             shr-spec
                             shr-spec-64
                             gpr-and-spec-4
                             gpr-and-spec-8
                             gpr-or-spec-8
                             top-level-opcode-execute
                             two-byte-opcode-decode-and-execute
                             x86-operand-from-modr/m-and-sib-bytes
                             x86-effective-addr
                             x86-effective-addr-from-sib
                             x86-operand-to-reg/mem
                             rr64 rr32 wr32 wr64
                             rim08 !flgi-undefined
                             write-user-rflags

                             rb-wb-equal-in-system-level-non-marking-mode

                             pos member-p subset-p)

                            (member-p-strip-cars-of-remove-duplicate-keys
                             wb-remove-duplicate-writes-in-system-level-non-marking-mode

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

;; One-to-one mapping

(defconst *2^64-2^47*      (- *2^64* *2^47*))

(equal (mv-nth 1 (las-to-pas (create-canonical-address-list *2^47* 0) :r (cpl x86) x86))
       (create-physical-address-list *2^47* 0))

(equal (mv-nth 1 (las-to-pas (create-canonical-address-list *2^47* *2^64-2^47*) :r (cpl x86) x86))
       (create-physical-address-list *2^47* *2^64-2^47*))

(local (defattach (ancestors-check nil)))

;; ======================================================================
