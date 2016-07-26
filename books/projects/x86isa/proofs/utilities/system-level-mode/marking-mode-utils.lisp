;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "common-system-level-utils")
(include-book "paging/top")
(include-book "gl-lemmas")
(include-book "clause-processors/find-subterms" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d* () (signed-byte-p unsigned-byte-p))))

;; ======================================================================

(local (xdoc::set-default-parents marking-mode-top))

;; ======================================================================

;; Combining nests of (mv-nth 2 (las-to-pas ...)) when linear
;; addresses are in sequence:

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
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x-2 cpl x86))))
           (equal (mv-nth 1 (las-to-pas l-addrs r-w-x-2 cpl x86))
                  (mv-nth 1 (las-to-pas l-addrs r-w-x-1 cpl x86))))
  :hints (("Goal" :in-theory (e/d* (r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-when-no-errors)
                                   ()))))

(defthm r/x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors
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
                (not (equal r-w-x-1 :w))
                (not (equal r-w-x-2 :w))
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x-1 cpl x86)))
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x-2 cpl x86))))
           (equal (mv-nth 2 (las-to-pas l-addrs r-w-x-2 cpl x86))
                  (mv-nth 2 (las-to-pas l-addrs r-w-x-1 cpl x86))))
  :hints (("Goal" :in-theory (e/d* (r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-when-no-errors)
                                   ()))))

(defthm combine-mv-nth-2-las-to-pas-same-r-w-x
  (implies (and (not (mv-nth 0 (las-to-pas l-addrs-1 r-w-x cpl (double-rewrite x86))))
                (canonical-address-listp l-addrs-1))
           (equal (mv-nth 2 (las-to-pas l-addrs-2 r-w-x cpl
                                        (mv-nth 2 (las-to-pas l-addrs-1 r-w-x cpl x86))))
                  (mv-nth 2 (las-to-pas (append l-addrs-1 l-addrs-2) r-w-x cpl x86))))
  :hints (("Goal" :in-theory (e/d* (las-to-pas) ()))))

(defun int-lists-in-seq-p (xs)
  ;; xs is an integer list such that the difference between
  ;; consecutive elements is 1, and these elements are arranged in
  ;; ascending order.
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

(local
 (defthm signed-byte-p-48-1+lin-addr
   (implies (and (bind-free '((cnt . cnt)))
                 (signed-byte-p 48 (+ cnt lin-addr))
                 (signed-byte-p 48 lin-addr)
                 (< 0 cnt))
            (signed-byte-p 48 (1+ lin-addr)))
   :hints (("Goal" :in-theory (e/d* (signed-byte-p) ())))))

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
                                    zp
                                    consp-create-canonical-address-list-implies-posp-cnt
                                    not-consp-create-canonical-address-list-implies-zp-cnt)
                                   ()))))

(defthmd car-create-canonical-address-list-alt
  (implies (consp (create-canonical-address-list cnt lin-addr))
           (equal (car (create-canonical-address-list cnt lin-addr))
                  lin-addr))
  :hints (("Goal" :in-theory (e/d* (create-canonical-address-list)
                                   ()))))

(defthm int-lists-in-seq-p-of-create-canonical-address-list
  (implies (and (canonical-address-p lin-addr)
                (canonical-address-p (+ -1 cnt lin-addr))
                (posp cnt))
           (int-lists-in-seq-p (create-canonical-address-list cnt lin-addr)))
  :hints (("Goal"
           :in-theory (e/d* (car-create-canonical-address-list
                             zp
                             car-create-canonical-address-list-alt
                             consp-create-canonical-address-list-implies-posp-cnt)
                            ()))))

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
                                    car-create-canonical-address-list-alt
                                    zp
                                    not-consp-create-canonical-address-list-implies-zp-cnt)
                                   ()))))

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
           (if
               ;; Apply to all subgoals under a top-level induction.
               (and (consp (car id))
                    (< 1 (len (car id))))
               '(:use ((:instance create-canonical-address-list-append-and-int-lists-in-seq-p-helper-1
                                  (car-x (car x))
                                  (cadr-x (cadr x)))))
             nil))))

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
          (if
              ;; Apply to all subgoals under a top-level induction.
              (and (consp (car id))
                   (< 1 (len (car id))))
              '(:use ((:instance create-canonical-address-list-append-and-int-lists-in-seq-p-helper-1
                                 (car-x (car x))
                                 (cadr-x (car y)))
                      (:instance create-canonical-address-list-append-and-int-lists-in-seq-p-helper-1
                                 (car-x (car x))
                                 (cadr-x (cadr x)))
                      (:instance create-canonical-address-list-append-and-int-lists-in-seq-p-helper-2
                                 (x y)))
                     :in-theory (e/d* (append create-canonical-address-list len)
                                      ()))
            nil)))

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

;; Disabling the more general rule that combines nests of (mv-nth 2
;; (las-to-pas ...)) indiscriminately...
(in-theory (e/d* () (combine-mv-nth-2-las-to-pas-same-r-w-x)))

;; ======================================================================

;; Lemmas to read a byte of an instruction when symbolically
;; simulating a program:

(local
 (defthmd rm08-in-terms-of-nth-pos-and-rb-helper
   (implies (and (disjoint-p (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86))
                             (all-translation-governing-addresses l-addrs x86))
                 (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                 (member-p addr l-addrs))
            (equal (member-p
                    (mv-nth 1 (ia32e-la-to-pa addr r-w-x cpl x86))
                    (translation-governing-addresses addr x86))
                   nil))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance not-member-p-when-disjoint-p
                             (e (mv-nth 1 (ia32e-la-to-pa addr r-w-x cpl x86)))
                             (x (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))
                             (y (translation-governing-addresses addr x86))))
            :in-theory (e/d* (all-translation-governing-addresses
                              member-p
                              disjoint-p
                              subset-p
                              disjoint-p-commutative)
                             (not-member-p-when-disjoint-p))))))

(defthm nth-of-read-from-physical-memory
  (implies (and (natp i)
                (< i (len p-addrs)))
           (equal (nth i (read-from-physical-memory p-addrs x86))
                  (xr :mem (nth i p-addrs) x86))))

(defthm nth-of-mv-nth-1-las-to-pas
  (implies (and (natp i)
                (< i (len l-addrs))
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86))))
           (equal (nth i (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))
                  (mv-nth 1 (ia32e-la-to-pa (nth i l-addrs) r-w-x cpl x86)))))

(defthm nth-pos-member-p
  (implies (member-p addr l-addrs)
           (equal (nth (pos addr l-addrs) l-addrs) addr))
  :hints (("Goal" :in-theory (e/d* (pos nth) ()))))

(defthmd rm08-in-terms-of-nth-pos-and-rb-in-system-level-mode
  (implies (and
            (disjoint-p (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86)))
                        (all-translation-governing-addresses l-addrs (double-rewrite x86)))
            (not (mv-nth 0 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86))))
            (member-p addr l-addrs)
            (canonical-address-listp l-addrs)
            (not (programmer-level-mode x86))
            (x86p x86))
           (equal (mv-nth 1 (rm08 addr r-w-x x86))
                  (nth (pos addr l-addrs) (mv-nth 1 (rb l-addrs r-w-x (double-rewrite x86))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance member-p-canonical-address-p
                            (e addr)
                            (x l-addrs)))
           :in-theory (e/d (rm08
                            member-p disjoint-p
                            rm08-in-terms-of-nth-pos-and-rb-helper)
                           (member-p-canonical-address-p
                            all-translation-governing-addresses
                            signed-byte-p
                            (:meta acl2::mv-nth-cons-meta))))))

(local
 (defthmd rb-in-terms-of-nth-and-pos-helper
   (implies
    (and (not (mv-nth 0 (rb (list lin-addr) :x x86)))
         (x86p x86))
    (equal (car (mv-nth 1 (rb (list lin-addr) :x x86)))
           (combine-bytes (mv-nth 1 (rb (list lin-addr) :x x86)))))
   :hints (("Goal" :in-theory (e/d* () ((:meta acl2::mv-nth-cons-meta)))))))

(defthm rb-in-terms-of-nth-and-pos-in-system-level-mode
  (implies (and (bind-free
                 (find-info-from-program-at-term 'rb-in-terms-of-nth-and-pos-in-system-level-mode mfc state)
                 (n prog-addr bytes))
                (program-at (create-canonical-address-list n prog-addr) bytes x86)
                (member-p lin-addr (create-canonical-address-list n prog-addr))
                (disjoint-p
                 (mv-nth 1 (las-to-pas
                            (create-canonical-address-list n prog-addr)
                            :x (cpl x86) (double-rewrite x86)))
                 (all-translation-governing-addresses
                  (create-canonical-address-list n prog-addr) (double-rewrite x86)))
                (syntaxp (quotep n))
                (not (programmer-level-mode x86))
                (x86p x86))
           (equal (car (mv-nth 1 (rb (list lin-addr) :x x86)))
                  (nth (pos lin-addr (create-canonical-address-list n prog-addr)) bytes)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (program-at
                            rb-in-terms-of-nth-and-pos-helper
                            rm08)
                           (acl2::mv-nth-cons-meta
                            member-p-canonical-address-p-canonical-address-listp))
           :use ((:instance member-p-canonical-address-p-canonical-address-listp
                            (e lin-addr))
                 (:instance rm08-in-terms-of-nth-pos-and-rb-in-system-level-mode
                            (addr lin-addr)
                            (r-w-x :x)
                            (l-addrs (create-canonical-address-list n prog-addr)))))))

(defthmd rb-unwinding-thm-in-system-level-mode
  (implies (and (consp l-addrs)
                (not (mv-nth 0 (rb l-addrs r-w-x x86)))
                (disjoint-p (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86)))
                            (all-translation-governing-addresses l-addrs (double-rewrite x86)))
                (canonical-address-listp l-addrs)
                (not (programmer-level-mode x86)))
           (equal (mv-nth 1 (rb l-addrs r-w-x x86))
                  (cons (car (mv-nth 1 (rb (list (car l-addrs)) r-w-x x86)))
                        (mv-nth 1 (rb (cdr l-addrs) r-w-x x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (rb append disjoint-p)
                           (acl2::mv-nth-cons-meta force (force))))))

(defthmd rb-unwinding-thm-in-system-level-mode-for-errors
  (implies (and (subset-p l-addrs-subset l-addrs)
                (not (mv-nth 0 (rb l-addrs r-w-x x86))))
           (equal (mv-nth 0 (rb l-addrs-subset r-w-x x86))
                  nil))
  :hints
  (("Goal" :in-theory (e/d (subset-p)
                           (acl2::mv-nth-cons-meta force (force))))))

(local
 (defthmd rb-in-terms-of-rb-subset-p-helper
   (implies (and (subset-p l-addrs-subset l-addrs)
                 (disjoint-p (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86))
                             (all-translation-governing-addresses l-addrs x86))
                 (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86))))
            (disjoint-p (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86))
                        (all-translation-governing-addresses l-addrs-subset x86)))))

(defthm rb-in-terms-of-rb-subset-p-in-system-level-mode
  (implies
   (and (bind-free
         (find-info-from-program-at-term
          'rb-in-terms-of-rb-subset-p-in-system-level-mode
          mfc state)
         (n prog-addr bytes))
        (program-at (create-canonical-address-list n prog-addr) bytes x86)
        (subset-p l-addrs (create-canonical-address-list n prog-addr))
        (disjoint-p (mv-nth 1 (las-to-pas
                               (create-canonical-address-list n prog-addr)
                               :x (cpl x86) (double-rewrite x86)))
                    (all-translation-governing-addresses
                     (create-canonical-address-list n prog-addr)
                     (double-rewrite x86)))
        (syntaxp (quotep n))
        (consp l-addrs)
        (not (mv-nth 0 (las-to-pas (create-canonical-address-list n prog-addr)
                                   :x (cpl x86) (double-rewrite x86))))
        (not (programmer-level-mode x86))
        (x86p x86))
   (equal (mv-nth 1 (rb l-addrs :x x86))
          (append (list (nth (pos
                              (car l-addrs)
                              (create-canonical-address-list n prog-addr))
                             bytes))
                  (mv-nth 1 (rb (cdr l-addrs) :x x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (subset-p
                            member-p
                            disjoint-p
                            disjoint-p-commutative
                            rb-in-terms-of-rb-subset-p-helper)
                           (rb
                            canonical-address-p
                            acl2::mv-nth-cons-meta
                            rb-in-terms-of-nth-and-pos-in-system-level-mode
                            all-translation-governing-addresses
                            las-to-pas))
           :use ((:instance rb-in-terms-of-nth-and-pos-in-system-level-mode
                            (lin-addr (car l-addrs)))
                 (:instance rb-unwinding-thm-in-system-level-mode
                            (r-w-x :x))
                 (:instance rb-unwinding-thm-in-system-level-mode-for-errors
                            (r-w-x :x)
                            (l-addrs-subset (list (car l-addrs))))))))

;; ======================================================================

;; Lemmas about interaction of memory writes and paging walkers:

(defthm xr-mem-wb-in-system-level-mode
  (implies (and (disjoint-p (list index)
                            (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86))))
                (disjoint-p (list index)
                            (all-translation-governing-addresses (strip-cars addr-lst) (double-rewrite x86)))
                (addr-byte-alistp addr-lst)
                (not (programmer-level-mode x86)))
           (equal (xr :mem index (mv-nth 1 (wb addr-lst x86)))
                  (xr :mem index x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (wb disjoint-p member-p)
                            (write-to-physical-memory
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm rm-low-32-wb-in-system-level-mode-disjoint
  (implies (and (disjoint-p (addr-range 4 index)
                            (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86))))
                (disjoint-p (addr-range 4 index)
                            (all-translation-governing-addresses (strip-cars addr-lst) (double-rewrite x86)))
                (addr-byte-alistp addr-lst))
           (equal (rm-low-32 index (mv-nth 1 (wb addr-lst x86)))
                  (rm-low-32 index x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (rm-low-32 disjoint-p member-p)
                            (wb
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm rm-low-64-wb-in-system-level-mode-disjoint
  (implies (and
            (disjoint-p (addr-range 8 index)
                        (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86))))
            (disjoint-p (addr-range 8 index)
                        (all-translation-governing-addresses (strip-cars addr-lst) (double-rewrite x86)))
            (addr-byte-alistp addr-lst)
            (integerp index))
           (equal (rm-low-64 index (mv-nth 1 (wb addr-lst x86)))
                  (rm-low-64 index x86)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rm-low-32-wb-in-system-level-mode-disjoint
                            (index index))
                 (:instance disjoint-p-and-addr-range-first-part
                            (n 8)
                            (m 4)
                            (index index)
                            (xs (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86))))
                 (:instance disjoint-p-and-addr-range-first-part
                            (n 8)
                            (m 4)
                            (index index)
                            (xs (all-translation-governing-addresses (strip-cars addr-lst) x86)))
                 (:instance disjoint-p-and-addr-range-second-part-n=8
                            (index index)
                            (xs (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86))))
                 (:instance disjoint-p-and-addr-range-second-part-n=8
                            (index index)
                            (xs (all-translation-governing-addresses (strip-cars addr-lst) x86)))
                 (:instance rm-low-32-wb-in-system-level-mode-disjoint
                            (index (+ 4 index))))
           :in-theory (e/d* (rm-low-64)
                            (rm-low-32-wb-in-system-level-mode-disjoint
                             wb (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm las-to-pas-values-and-write-to-physical-memory-disjoint
  ;; Generalization of
  ;; ia32e-la-to-pa-values-and-write-to-physical-memory-disjoint.
  (implies (and (disjoint-p p-addrs
                            (all-translation-governing-addresses l-addrs (double-rewrite x86)))
                (physical-address-listp p-addrs)
                (byte-listp bytes)
                (equal (len bytes) (len p-addrs))
                (canonical-address-listp l-addrs)
                (not (programmer-level-mode x86))
                (x86p x86))
           (and (equal (mv-nth 0 (las-to-pas l-addrs r-w-x cpl
                                             (write-to-physical-memory p-addrs bytes x86)))
                       (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                (equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl
                                             (write-to-physical-memory p-addrs bytes x86)))
                       (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))))
  :hints (("Goal" :induct (las-to-pas l-addrs r-w-x cpl x86)
           :in-theory (e/d* (disjoint-p disjoint-p-commutative)
                            (translation-governing-addresses)))))

(defthm ia32e-la-to-pa-page-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and (equal cpl (cpl x86))
                (disjoint-p
                 (mv-nth 1 (las-to-pas
                            (strip-cars addr-lst) :w cpl (double-rewrite x86)))
                 (translation-governing-addresses-for-page-table
                  lin-addr base-addr (double-rewrite x86)))
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
                             disjoint-p-commutative
                             member-p
                             ia32e-la-to-pa-page-table
                             translation-governing-addresses-for-page-table
                             wb)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm rm-low-64-page-directory-entry-addr-and-mv-nth-1-wb
  ;; Different from RM-LOW-64-WB-IN-SYSTEM-LEVEL-MODE-DISJOINT, which
  ;; hangs on equal instead of xlate-equiv-entries.
  (implies
   (and (equal cpl (cpl x86))
        (disjoint-p
         (mv-nth 1 (las-to-pas
                    (strip-cars addr-lst) :w cpl (double-rewrite x86)))
         (translation-governing-addresses-for-page-directory
          lin-addr base-addr (double-rewrite x86))))
   (xlate-equiv-entries
    (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
               (mv-nth 1 (wb addr-lst x86)))
    (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
               x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (translation-governing-addresses-for-page-directory
                             disjoint-p-commutative)
                            ()))))

(defthm ia32e-la-to-pa-page-directory-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and (equal cpl (cpl x86))
                (disjoint-p
                 (mv-nth 1 (las-to-pas
                            (strip-cars addr-lst) :w cpl (double-rewrite x86)))
                 (translation-governing-addresses-for-page-directory
                  lin-addr base-addr (double-rewrite x86)))
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
           :use ((:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb addr-lst x86)))))
                 (:instance xlate-equiv-entries-and-page-execute-disable
                            (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb addr-lst x86)))))
                 (:instance xlate-equiv-entries-and-logtail
                            (n 12)
                            (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb addr-lst x86)))))
                 (:instance xlate-equiv-entries-and-logtail
                            (n 21)
                            (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb addr-lst x86))))))
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             member-p
                             ia32e-la-to-pa-page-directory
                             translation-governing-addresses-for-page-directory)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm rm-low-64-page-dir-ptr-table-entry-addr-and-mv-nth-1-wb
  ;; Different from RM-LOW-64-WB-IN-SYSTEM-LEVEL-MODE-DISJOINT, which
  ;; hangs on equal instead of xlate-equiv-entries.
  (implies
   (and (equal cpl (cpl x86))
        (disjoint-p
         (mv-nth 1 (las-to-pas
                    (strip-cars addr-lst) :w cpl (double-rewrite x86)))
         (translation-governing-addresses-for-page-dir-ptr-table
          lin-addr base-addr (double-rewrite x86))))
   (xlate-equiv-entries
    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
               (mv-nth 1 (wb addr-lst x86)))
    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
               x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (translation-governing-addresses-for-page-dir-ptr-table
                             disjoint-p-commutative)
                            ()))))

(defthm ia32e-la-to-pa-page-dir-ptr-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and
            (equal cpl (cpl x86))
            (disjoint-p
             (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl (double-rewrite x86)))
             (translation-governing-addresses-for-page-dir-ptr-table
              lin-addr base-addr (double-rewrite x86)))
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
           :use ((:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb addr-lst x86)))))
                 (:instance xlate-equiv-entries-and-page-execute-disable
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb addr-lst x86)))))
                 (:instance xlate-equiv-entries-and-logtail
                            (n 12)
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb addr-lst x86)))))
                 (:instance xlate-equiv-entries-and-logtail
                            (n 30)
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb addr-lst x86))))))

           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             member-p
                             ia32e-la-to-pa-page-dir-ptr-table
                             translation-governing-addresses-for-page-dir-ptr-table)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm rm-low-64-pml4-table-entry-addr-and-mv-nth-1-wb
  ;; Different from RM-LOW-64-WB-IN-SYSTEM-LEVEL-MODE-DISJOINT, which
  ;; hangs on equal instead of xlate-equiv-entries.
  (implies
   (and (equal cpl (cpl x86))
        (disjoint-p
         (mv-nth 1 (las-to-pas
                    (strip-cars addr-lst) :w cpl (double-rewrite x86)))
         (translation-governing-addresses-for-pml4-table
          lin-addr base-addr (double-rewrite x86))))
   (xlate-equiv-entries
    (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
               (mv-nth 1 (wb addr-lst x86)))
    (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
               x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (translation-governing-addresses-for-pml4-table
                             disjoint-p-commutative)
                            (force (force))))))

(defthm ia32e-la-to-pa-pml4-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and
            (equal cpl (cpl x86))
            (disjoint-p
             (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl (double-rewrite x86)))
             (translation-governing-addresses-for-pml4-table
              lin-addr base-addr (double-rewrite x86)))
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
           :use ((:instance xlate-equiv-entries-and-page-execute-disable
                            (e-1 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb addr-lst x86)))))
                 (:instance xlate-equiv-entries-and-logtail
                            (n 12)
                            (e-1 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb addr-lst x86))))))
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             member-p
                             ia32e-la-to-pa-pml4-table
                             translation-governing-addresses-for-pml4-table)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and (equal cpl (cpl x86))
                (disjoint-p
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl (double-rewrite x86)))
                 (translation-governing-addresses lin-addr (double-rewrite x86)))
                (canonical-address-p lin-addr))
           (and
            (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
            (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             member-p
                             ia32e-la-to-pa
                             translation-governing-addresses)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and (equal cpl (cpl x86))
                (disjoint-p
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl (double-rewrite x86)))
                 (all-translation-governing-addresses l-addrs (double-rewrite x86)))
                (canonical-address-listp l-addrs))
           (and
            (equal (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86))))
            (equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86))))))
  :hints (("Goal"
           :induct (all-translation-governing-addresses l-addrs x86)
           :in-theory (e/d* ()
                            (disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
                             mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                             wb
                             translation-governing-addresses
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

;; ======================================================================

;; Lemmas about interaction of top-level memory reads and writes:

(defthm rb-wb-disjoint-in-system-level-mode
  (implies (and
            (disjoint-p
             ;; The physical addresses pertaining to the read
             ;; operation are disjoint from those pertaining to the
             ;; write operation.
             (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
             (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86))))
            (disjoint-p
             ;; The physical addresses corresponding to the read are
             ;; disjoint from the translation-governing-addresses
             ;; pertaining to the write.
             (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86)))
             (all-translation-governing-addresses (strip-cars addr-lst) (double-rewrite x86)))
            (disjoint-p
             ;; The physical addresses pertaining to the read are
             ;; disjoint from the translation-governing-addresses
             ;; pertaining to the read.
             (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86)))
             (all-translation-governing-addresses l-addrs (double-rewrite x86)))
            (disjoint-p
             ;; The physical addresses pertaining to the write are
             ;; disjoint from the translation-governing-addresses
             ;; pertaining to the read.
             (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
             (all-translation-governing-addresses l-addrs (double-rewrite x86)))
            (canonical-address-listp l-addrs)
            (addr-byte-alistp addr-lst)
            (not (programmer-level-mode x86))
            (x86p x86))
           (and
            (equal (mv-nth 0 (rb l-addrs r-w-x (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 0 (rb l-addrs r-w-x x86)))
            (equal (mv-nth 1 (rb l-addrs r-w-x (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 1 (rb l-addrs r-w-x x86)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance xlate-equiv-memory-and-las-to-pas
                            (cpl (cpl x86))
                            (x86-1 (mv-nth 2 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                            (x86-2 x86)))
           :in-theory (e/d* (disjoint-p-commutative)
                            (disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
                             mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)))))

(defthm read-from-physical-memory-and-mv-nth-1-wb-disjoint
  ;; Similar to rb-wb-disjoint-in-system-level-mode
  (implies (and (disjoint-p
                 p-addrs
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86))))
                (disjoint-p p-addrs
                            (all-translation-governing-addresses
                             (strip-cars addr-lst) (double-rewrite x86)))
                (addr-byte-alistp addr-lst)
                (not (programmer-level-mode x86))
                (x86p x86))
           (equal (read-from-physical-memory p-addrs (mv-nth 1 (wb addr-lst x86)))
                  (read-from-physical-memory p-addrs x86)))
  :hints (("Goal" :in-theory (e/d* (wb) ()))))

(defthmd rb-wb-equal-in-system-level-mode
  (implies (and (equal
                 ;; The physical addresses pertaining to the read
                 ;; operation are equal to those pertaining to the
                 ;; write operation.
                 (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86)))
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86))))
                (disjoint-p
                 ;; The physical addresses pertaining to the write are
                 ;; disjoint from the translation-governing-addresses
                 ;; pertaining to the read.
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
                 (all-translation-governing-addresses l-addrs (double-rewrite x86)))

                (no-duplicates-p
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x (cpl x86) x86)))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (canonical-address-listp l-addrs)
                (addr-byte-alistp addr-lst)
                (not (programmer-level-mode x86))
                (x86p x86))
           (equal (mv-nth 1 (rb l-addrs r-w-x (mv-nth 1 (wb addr-lst x86))))
                  (strip-cdrs addr-lst)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d* (disjoint-p-commutative) (force (force)))
           :use ((:instance xlate-equiv-memory-and-las-to-pas
                            (cpl (cpl x86))
                            (x86-1 (mv-nth 2 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                            (x86-2 x86))))))

;; ======================================================================

;; Lemmas about program-at:

(defthm program-at-wb-disjoint-in-system-level-mode
  (implies (and
            (disjoint-p
             ;; The physical addresses pertaining to the write
             ;; operation are disjoint from those pertaining to the
             ;; read operation.
             (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
             (mv-nth 1 (las-to-pas l-addrs :x (cpl x86) (double-rewrite x86))))
            (disjoint-p
             ;; The physical addresses corresponding to the read are
             ;; disjoint from the translation-governing-addresses
             ;; pertaining to the write.
             (mv-nth 1 (las-to-pas l-addrs :x (cpl x86) (double-rewrite x86)))
             (all-translation-governing-addresses (strip-cars addr-lst) (double-rewrite x86)))
            (disjoint-p
             ;; The physical addresses pertaining to the read are
             ;; disjoint from the translation-governing-addresses
             ;; pertaining to the read.
             (mv-nth 1 (las-to-pas l-addrs :x (cpl x86) (double-rewrite x86)))
             (all-translation-governing-addresses l-addrs (double-rewrite x86)))
            (disjoint-p
             ;; The physical addresses pertaining to the write are
             ;; disjoint from the translation-governing-addresses
             ;; pertaining to the read.
             (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
             (all-translation-governing-addresses l-addrs (double-rewrite x86)))
            (canonical-address-listp l-addrs)
            (addr-byte-alistp addr-lst)
            (not (programmer-level-mode x86))
            (x86p x86))
           (equal (program-at l-addrs bytes (mv-nth 1 (wb addr-lst x86)))
                  (program-at l-addrs bytes x86)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rb-wb-disjoint-in-system-level-mode
                            (r-w-x :x)))
           :in-theory (e/d (program-at)
                           (rb-wb-disjoint-in-system-level-mode
                            disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
                            mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                            rb wb)))))

;; ======================================================================

(globally-disable '(rb
                    wb
                    canonical-address-p
                    program-at
                    las-to-pas
                    all-translation-governing-addresses
                    unsigned-byte-p
                    signed-byte-p))

(in-theory (e/d*
            ;; We enable all these functions so that reasoning about
            ;; memory can be done in terms of rb and wb.
            (rim-size
             rm-size
             wim-size
             wm-size
             rm08 rim08 wm08 wim08
             rm16 rim16 wm16 wim16
             rm32 rim32 wm32 wim32
             rm64 rim64 wm64 wim64)
            ()))

;; ======================================================================

(defsection xlate-equiv-memory-and-rm08
  :parents (marking-mode-top)

  (defthmd xlate-equiv-memory-and-rvm08
    (implies (and (xr :programmer-level-mode 0 x86-1)
                  (xlate-equiv-memory x86-1 x86-2))
             (and (equal (mv-nth 0 (rvm08 lin-addr x86-1))
                         (mv-nth 0 (rvm08 lin-addr x86-2)))
                  (equal (mv-nth 1 (rvm08 lin-addr x86-1))
                         (mv-nth 1 (rvm08 lin-addr x86-2)))))
    :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory)
                                     (force (force))))))


  (defthm xlate-equiv-memory-and-mv-nth-0-rm08-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (equal (mv-nth 0 (rm08 lin-addr r-w-x x86-1))
                    (mv-nth 0 (rm08 lin-addr r-w-x x86-2))))
    :hints
    (("Goal" :cases ((xr :programmer-level-mode 0 x86-1))
      :in-theory (e/d* (rm08 disjoint-p member-p)
                       (force (force)))
      :use ((:instance xlate-equiv-memory-and-rvm08))))
    :rule-classes :congruence)

  (defthmd xlate-equiv-memory-and-xr-mem-from-rest-of-memory
    (implies
     (and (bind-free
           (find-an-xlate-equiv-x86
            'xlate-equiv-memory-and-xr-mem-from-rest-of-memory
            x86-1 'x86-2 mfc state)
           (x86-2))
          (syntaxp (not (equal x86-1 x86-2)))
          (xlate-equiv-memory (double-rewrite x86-1) x86-2)
          (disjoint-p (list j)
                      (open-qword-paddr-list
                       (gather-all-paging-structure-qword-addresses (double-rewrite x86-1))))
          (natp j)
          (< j *mem-size-in-bytes*))
     (equal (xr :mem j x86-1) (xr :mem j x86-2)))
    :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory disjoint-p)
                                     ()))))

  (defthm xlate-equiv-memory-and-mv-nth-1-rm08
    (implies (and (bind-free
                   (find-an-xlate-equiv-x86
                    'xlate-equiv-memory-and-mv-nth-1-rm08
                    x86-1 'x86-2 mfc state)
                   (x86-2))
                  (syntaxp (not (equal x86-1 x86-2)))
                  (xlate-equiv-memory (double-rewrite x86-1) x86-2)
                  (disjoint-p
                   (list (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x (cpl x86-1) x86-1)))
                   (open-qword-paddr-list
                    (gather-all-paging-structure-qword-addresses (double-rewrite x86-1)))))
             (equal (mv-nth 1 (rm08 lin-addr r-w-x x86-1))
                    (mv-nth 1 (rm08 lin-addr r-w-x x86-2))))
    :hints (("Goal"
             :cases ((xr :programmer-level-mode 0 x86-1))
             :in-theory (e/d* (rm08
                               rb
                               disjoint-p
                               member-p
                               las-to-pas)
                              (force (force)))
             :use ((:instance xlate-equiv-memory-and-xr-mem-from-rest-of-memory
                              (j (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x (cpl x86-1) x86-1)))
                              (x86-1 (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x (cpl x86-1) x86-1)))
                              (x86-2 (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x (cpl x86-2) x86-2))))
                   (:instance xlate-equiv-memory-and-rvm08)))))

  (defthm xlate-equiv-memory-and-two-mv-nth-2-rm08-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (xlate-equiv-memory (mv-nth 2 (rm08 lin-addr r-w-x x86-1))
                                 (mv-nth 2 (rm08 lin-addr r-w-x x86-2))))
    :hints (("Goal" :in-theory (e/d* (rm08 rb) (force (force)))))
    :rule-classes :congruence)

  (defthm xlate-equiv-memory-and-mv-nth-2-rm08
    (xlate-equiv-memory (mv-nth 2 (rm08 lin-addr r-w-x x86)) x86)
    :hints (("Goal" :in-theory (e/d* (rm08 rb) (force (force)))))))

;; ======================================================================

;; Get-prefixes in system-level marking mode:

(defsection get-prefixes-in-system-level-marking-mode
  :parents (marking-mode-top)

  (defthmd xr-not-mem-and-get-prefixes
    ;; I don't need this lemma in the programmer-level mode because
    ;; (mv-nth 2 (get-prefixes ... x86)) == x86 there.
    (implies (and (not (equal fld :mem))
                  (not (equal fld :fault)))
             (equal (xr fld index (mv-nth 2 (get-prefixes start-rip prefixes cnt x86)))
                    (xr fld index x86)))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :in-theory (e/d* (get-prefixes rm08 rb las-to-pas)
                              (negative-logand-to-positive-logand-with-integerp-x
                               unsigned-byte-p-of-logior
                               acl2::loghead-identity
                               not force (force))))))

  ;; The following make-events generate a bunch of rules that together
  ;; say the same thing as xr-not-mem-and-get-prefixes, but these
  ;; rules are more efficient than xr-not-mem-and-get-prefixes as they
  ;; match less frequently.
  (make-event
   (generate-xr-over-write-thms
    (remove-elements-from-list
     '(:mem :fault)
     *x86-field-names-as-keywords*)
    'get-prefixes
    (acl2::formals 'get-prefixes (w state))
    :output-index 2
    :prepwork '((local (in-theory (e/d (xr-not-mem-and-get-prefixes) ()))))))

  (defthm xr-fault-and-get-prefixes
    (implies (not (mv-nth 0 (las-to-pas
                             (create-canonical-address-list cnt start-rip)
                             :x (cpl x86) x86)))
             (equal (xr :fault index (mv-nth 2 (get-prefixes start-rip prefixes cnt x86)))
                    (xr :fault index x86)))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :in-theory (e/d* (get-prefixes
                               rb
                               las-to-pas)
                              (mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
                               negative-logand-to-positive-logand-with-integerp-x
                               unsigned-byte-p-of-logior
                               subset-p-two-create-canonical-address-lists-general
                               subset-p
                               not force (force))))))

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
             :in-theory (e/d* (get-prefixes
                               rb
                               las-to-pas)
                              (rm08
                               negative-logand-to-positive-logand-with-integerp-x
                               unsigned-byte-p-of-logior
                               acl2::ash-0
                               acl2::zip-open
                               acl2::ifix-when-not-integerp
                               acl2::loghead-identity
                               (:t bitops::logior-natp-type)
                               (:t natp-get-prefixes)
                               (:t n08p-mv-nth-1-rm08)
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
             :in-theory (e/d* (get-prefixes
                               las-to-pas
                               rb)
                              (rm08
                               negative-logand-to-positive-logand-with-integerp-x
                               unsigned-byte-p-of-logior
                               acl2::ash-0
                               acl2::zip-open
                               acl2::ifix-when-not-integerp
                               acl2::loghead-identity
                               (:t bitops::logior-natp-type)
                               (:t natp-get-prefixes)
                               (:t n08p-mv-nth-1-rm08)
                               force (force))))))

  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
     *x86-field-names-as-keywords*)
    'get-prefixes
    (acl2::formals 'get-prefixes (w state))
    :output-index 0
    :prepwork '((local (in-theory (e/d (get-prefixes-xw-values-in-system-level-mode
                                        get-prefixes-xw-state-in-system-level-mode)
                                       ()))))
    :hyps '(not (programmer-level-mode x86))))

  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
     *x86-field-names-as-keywords*)
    'get-prefixes
    (acl2::formals 'get-prefixes (w state))
    :output-index 1
    :prepwork '((local (in-theory (e/d (get-prefixes-xw-values-in-system-level-mode
                                        get-prefixes-xw-state-in-system-level-mode)
                                       ()))))
    :hyps '(not (programmer-level-mode x86))))

  (make-event
   (generate-write-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
     *x86-field-names-as-keywords*)
    'get-prefixes
    (acl2::formals 'get-prefixes (w state))
    :output-index 2
    :prepwork '((local (in-theory (e/d (get-prefixes-xw-values-in-system-level-mode
                                        get-prefixes-xw-state-in-system-level-mode)
                                       ()))))
    :hyps '(not (programmer-level-mode x86))))

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
                              (negative-logand-to-positive-logand-with-integerp-x
                               unsigned-byte-p-of-logior
                               acl2::ash-0
                               acl2::zip-open
                               acl2::ifix-when-not-integerp
                               acl2::loghead-identity
                               (:t bitops::logior-natp-type)
                               (:t natp-get-prefixes)
                               (:t n08p-mv-nth-1-rm08)
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
                              (force (force))))))

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
                              (rm08 force (force))))))

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
                              (rm08
                               get-prefixes-xw-rflags-not-ac-values-in-system-level-mode
                               force (force))))))

  ;; Opener lemmas:

  (defthm get-prefixes-opener-lemma-group-1-prefix-in-marking-mode
    (implies
     (and
      (canonical-address-p (1+ start-rip))
      (not (zp cnt))
      (equal (prefixes-slice :group-1-prefix prefixes) 0)
      (let*
          ((flg (mv-nth 0 (rm08 start-rip :x x86)))
           (prefix-byte-group-code
            (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))))
        (and (not flg)
             (equal prefix-byte-group-code 1))))
     (equal (get-prefixes start-rip prefixes cnt x86)
            (get-prefixes (+ 1 start-rip)
                          (!prefixes-slice :group-1-prefix
                                           (mv-nth 1 (rm08 start-rip :x x86))
                                           prefixes)
                          (+ -1 cnt)
                          (mv-nth 2 (rm08 start-rip :x x86)))))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :in-theory (e/d* (get-prefixes
                               las-to-pas)
                              (acl2::ash-0
                               acl2::zip-open
                               byte-listp
                               unsigned-byte-p-of-logior
                               negative-logand-to-positive-logand-with-integerp-x
                               force (force))))))

  (defthm get-prefixes-opener-lemma-group-2-prefix-in-marking-mode
    (implies (and
              (canonical-address-p (1+ start-rip))
              (not (zp cnt))
              (equal (prefixes-slice :group-2-prefix prefixes) 0)
              (let*
                  ((flg (mv-nth 0 (rm08 start-rip :x x86)))
                   (prefix-byte-group-code
                    (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))))
                (and (not flg)
                     (equal prefix-byte-group-code 2))))
             (equal (get-prefixes start-rip prefixes cnt x86)
                    (get-prefixes (1+ start-rip)
                                  (!prefixes-slice :group-2-prefix
                                                   (mv-nth 1 (rm08 start-rip :x x86))
                                                   prefixes)
                                  (1- cnt)
                                  (mv-nth 2 (rm08 start-rip :x x86)))))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :in-theory (e/d* (get-prefixes
                               las-to-pas)
                              (acl2::ash-0
                               acl2::zip-open
                               byte-listp
                               unsigned-byte-p-of-logior
                               negative-logand-to-positive-logand-with-integerp-x
                               force (force))))))

  (defthm get-prefixes-opener-lemma-group-3-prefix-in-marking-mode
    (implies (and
              (canonical-address-p (1+ start-rip))
              (not (zp cnt))
              (equal (prefixes-slice :group-3-prefix prefixes) 0)
              (let*
                  ((flg (mv-nth 0 (rm08 start-rip :x x86)))
                   (prefix-byte-group-code
                    (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))))
                (and (not flg)
                     (equal prefix-byte-group-code 3))))
             (equal (get-prefixes start-rip prefixes cnt x86)
                    (get-prefixes (1+ start-rip)
                                  (!prefixes-slice :group-3-prefix
                                                   (mv-nth 1 (rm08 start-rip :x x86))
                                                   prefixes)
                                  (1- cnt)
                                  (mv-nth 2 (rm08 start-rip :x x86)))))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :in-theory (e/d* (get-prefixes
                               las-to-pas)
                              (acl2::ash-0
                               acl2::zip-open
                               byte-listp
                               unsigned-byte-p-of-logior
                               negative-logand-to-positive-logand-with-integerp-x
                               force (force))))))

  (defthm get-prefixes-opener-lemma-group-4-prefix-in-marking-mode
    (implies (and
              (canonical-address-p (1+ start-rip))
              (not (zp cnt))
              (equal (prefixes-slice :group-4-prefix prefixes) 0)
              (let*
                  ((flg (mv-nth 0 (rm08 start-rip :x x86)))
                   (prefix-byte-group-code
                    (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))))
                (and (not flg)
                     (equal prefix-byte-group-code 4))))
             (equal (get-prefixes start-rip prefixes cnt x86)
                    (get-prefixes (1+ start-rip)
                                  (!prefixes-slice :group-4-prefix
                                                   (mv-nth 1 (rm08 start-rip :x x86))
                                                   prefixes)
                                  (1- cnt)
                                  (mv-nth 2 (rm08 start-rip :x x86)))))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :in-theory (e/d* (get-prefixes
                               las-to-pas)
                              (acl2::ash-0
                               acl2::zip-open
                               byte-listp
                               unsigned-byte-p-of-logior
                               negative-logand-to-positive-logand-with-integerp-x
                               force (force))))))

  ;; Get-prefixes and xlate-equiv-memory:

  (defun-nx get-prefixes-two-x86-induct-hint
    (start-rip prefixes cnt x86-1 x86-2)
    (declare (xargs :measure (nfix cnt)))
    (if (zp cnt)
        ;; Error, too many prefix bytes
        (mv nil prefixes x86-1 x86-2)

      (b* ((ctx 'get-prefixes-two-x86-induct-hint)
           ((mv flg-1 byte-1 x86-1)
            (rm08 start-rip :x x86-1))
           ((mv flg-2 byte-2 x86-2)
            (rm08 start-rip :x x86-2))
           ((when flg-1)
            (mv (cons ctx flg-1) byte-1 x86-1))
           ((when flg-2)
            (mv (cons ctx flg-2) byte-2 x86-2))
           ;; Quit if byte-1 and byte-2 aren't equal...
           ((when (not (equal byte-1 byte-2)))
            (mv nil prefixes x86-1 x86-2))
           (byte byte-1)

           (prefix-byte-group-code
            (get-one-byte-prefix-array-code byte)))

        (if (zp prefix-byte-group-code)
            (let ((prefixes
                   (!prefixes-slice :next-byte byte prefixes)))
              (mv nil (!prefixes-slice :num-prefixes (- 5 cnt) prefixes) x86-1 x86-2))

          (case prefix-byte-group-code
            (1 (let ((prefix-1?
                      (prefixes-slice :group-1-prefix prefixes)))
                 (if (or (eql 0 (the (unsigned-byte 8) prefix-1?))
                         ;; Redundant Prefix Okay
                         (eql byte prefix-1?))
                     (let ((next-rip (the (signed-byte
                                           #.*max-linear-address-size+1*)
                                       (1+ start-rip))))
                       (if (mbe :logic (canonical-address-p next-rip)
                                :exec
                                (< (the (signed-byte
                                         #.*max-linear-address-size+1*)
                                     next-rip)
                                   #.*2^47*))
                           ;; Storing the group 1 prefix and going on...
                           (get-prefixes-two-x86-induct-hint
                            next-rip
                            (the (unsigned-byte 43)
                              (!prefixes-slice :group-1-prefix
                                               byte
                                               prefixes))
                            (the (integer 0 5) (1- cnt))
                            x86-1
                            x86-2)
                         (mv (cons 'non-canonical-address next-rip) prefixes x86-1 x86-2)))
                   ;; We do not tolerate more than one prefix from a prefix group.
                   (mv t prefixes x86-1 x86-2))))

            (2 (let ((prefix-2?
                      (prefixes-slice :group-2-prefix prefixes)))
                 (if (or (eql 0 (the (unsigned-byte 8) prefix-2?))
                         ;; Redundant Prefixes Okay
                         (eql byte (the (unsigned-byte 8) prefix-2?)))
                     (let ((next-rip (the (signed-byte
                                           #.*max-linear-address-size+1*)
                                       (1+ start-rip))))
                       (if (mbe :logic (canonical-address-p next-rip)
                                :exec
                                (< (the (signed-byte
                                         #.*max-linear-address-size+1*)
                                     next-rip)
                                   #.*2^47*))
                           ;; Storing the group 2 prefix and going on...
                           (get-prefixes-two-x86-induct-hint
                            next-rip
                            (!prefixes-slice :group-2-prefix
                                             byte
                                             prefixes)
                            (the (integer 0 5) (1- cnt))
                            x86-1 x86-2)
                         (mv (cons 'non-canonical-address next-rip)
                             prefixes x86-1 x86-2)))
                   ;; We do not tolerate more than one prefix from a prefix group.
                   (mv t prefixes x86-1 x86-2))))

            (3 (let ((prefix-3?
                      (prefixes-slice :group-3-prefix prefixes)))
                 (if (or (eql 0 (the (unsigned-byte 8) prefix-3?))
                         ;; Redundant Prefix Okay
                         (eql byte (the (unsigned-byte 8) prefix-3?)))

                     (let ((next-rip (the (signed-byte
                                           #.*max-linear-address-size+1*)
                                       (1+ start-rip))))
                       (if (mbe :logic (canonical-address-p next-rip)
                                :exec
                                (< (the (signed-byte
                                         #.*max-linear-address-size+1*)
                                     next-rip)
                                   #.*2^47*))
                           ;; Storing the group 3 prefix and going on...
                           (get-prefixes-two-x86-induct-hint
                            next-rip
                            (!prefixes-slice :group-3-prefix
                                             byte
                                             prefixes)
                            (the (integer 0 5) (1- cnt)) x86-1 x86-2)
                         (mv (cons 'non-canonical-address next-rip)
                             prefixes x86-1 x86-2)))
                   ;; We do not tolerate more than one prefix from a prefix group.
                   (mv t prefixes x86-1 x86-2))))

            (4 (let ((prefix-4?
                      (prefixes-slice :group-4-prefix prefixes)))
                 (if (or (eql 0 (the (unsigned-byte 8) prefix-4?))
                         ;; Redundant Prefix Okay
                         (eql byte (the (unsigned-byte 8) prefix-4?)))
                     (let ((next-rip (the (signed-byte
                                           #.*max-linear-address-size+1*)
                                       (1+ start-rip))))
                       (if (mbe :logic (canonical-address-p next-rip)
                                :exec
                                (< (the (signed-byte
                                         #.*max-linear-address-size+1*)
                                     next-rip)
                                   #.*2^47*))
                           ;; Storing the group 4 prefix and going on...
                           (get-prefixes-two-x86-induct-hint
                            next-rip
                            (!prefixes-slice :group-4-prefix
                                             byte
                                             prefixes)
                            (the (integer 0 5) (1- cnt))
                            x86-1 x86-2)
                         (mv (cons 'non-canonical-address next-rip)
                             prefixes x86-1 x86-2)))
                   ;; We do not tolerate more than one prefix from a prefix group.
                   (mv t prefixes x86-1 x86-2))))

            (otherwise
             (mv t prefixes x86-1 x86-2)))))))

  (defthm xlate-equiv-memory-and-two-get-prefixes-values
    (implies
     (and
      (bind-free
       (find-an-xlate-equiv-x86
        'xlate-equiv-memory-and-two-get-prefixes-values
        x86-1 'x86-2 mfc state)
       (x86-2))
      (syntaxp (not (equal x86-1 x86-2)))
      (xlate-equiv-memory (double-rewrite x86-1) x86-2)
      (canonical-address-p start-rip)
      (not (mv-nth 0 (las-to-pas
                      (create-canonical-address-list cnt start-rip)
                      :x (cpl x86-1) x86-1)))
      (disjoint-p
       (mv-nth 1 (las-to-pas
                  (create-canonical-address-list cnt start-rip)
                  :x (cpl x86-1) x86-1))
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses (double-rewrite x86-1)))))
     (and (equal (mv-nth 0 (get-prefixes start-rip prefixes cnt x86-1))
                 (mv-nth 0 (get-prefixes start-rip prefixes cnt x86-2)))
          (equal (mv-nth 1 (get-prefixes start-rip prefixes cnt x86-1))
                 (mv-nth 1 (get-prefixes start-rip prefixes cnt x86-2)))))
    :hints (("Goal"
             :induct (get-prefixes-two-x86-induct-hint start-rip prefixes cnt x86-1 x86-2)
             :in-theory (e/d* (get-prefixes disjoint-p member-p las-to-pas  mv-nth-0-las-to-pas-subset-p)
                              ()))
            (if
                ;; Apply to all subgoals under a top-level induction.
                (and (consp (car id))
                     (< 1 (len (car id))))
                '(:expand ((get-prefixes start-rip prefixes cnt x86-1)
                           (get-prefixes start-rip prefixes cnt x86-2))
                          :use
                          ((:instance xlate-equiv-memory-and-mv-nth-0-rm08-cong
                                      (lin-addr start-rip)
                                      (r-w-x :x))
                           (:instance xlate-equiv-memory-and-mv-nth-1-rm08
                                      (lin-addr start-rip)
                                      (r-w-x :x)))
                          :in-theory
                          (e/d* (disjoint-p
                                 member-p
                                 get-prefixes
                                 las-to-pas
                                 mv-nth-0-las-to-pas-subset-p)
                                (rm08
                                 xlate-equiv-memory-and-mv-nth-0-rm08-cong
                                 xlate-equiv-memory-and-mv-nth-1-rm08
                                 mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                                 (:rewrite mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p)
                                 (:rewrite cdr-mv-nth-1-las-to-pas))))
              nil)))

  (defthm xlate-equiv-memory-and-mv-nth-2-get-prefixes
    (implies (and (not (programmer-level-mode (double-rewrite x86)))
                  (page-structure-marking-mode (double-rewrite x86))
                  (canonical-address-p start-rip)
                  (not (mv-nth 0 (las-to-pas (create-canonical-address-list cnt start-rip)
                                             :x (cpl x86) (double-rewrite x86)))))
             (xlate-equiv-memory (mv-nth 2 (get-prefixes start-rip prefixes cnt x86))
                                 (double-rewrite x86)))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :in-theory (e/d* (get-prefixes  mv-nth-0-las-to-pas-subset-p subset-p)
                              (rm08
                               acl2::ash-0
                               acl2::zip-open
                               cdr-create-canonical-address-list
                               force (force))))
            (if
                ;; Apply to all subgoals under a top-level induction.
                (and (consp (car id))
                     (< 1 (len (car id))))
                '(:in-theory (e/d* (subset-p get-prefixes  mv-nth-0-las-to-pas-subset-p)
                                   (rm08
                                    acl2::ash-0
                                    acl2::zip-open
                                    cdr-create-canonical-address-list
                                    force (force)))
                             :use ((:instance xlate-equiv-memory-and-las-to-pas
                                              (l-addrs (create-canonical-address-list (+ -1 cnt) (+ 1 start-rip)))
                                              (r-w-x :x)
                                              (cpl (cpl x86))
                                              (x86-1 (mv-nth 2 (las-to-pas (list start-rip) :x (cpl x86) x86)))
                                              (x86-2 x86))))
              nil)))

  (defthmd xlate-equiv-memory-and-two-mv-nth-2-get-prefixes
    (implies (and (xlate-equiv-memory x86-1 x86-2)
                  (not (programmer-level-mode x86-2))
                  (page-structure-marking-mode (double-rewrite x86-2))
                  (canonical-address-p start-rip)
                  (not (mv-nth 0
                               (las-to-pas (create-canonical-address-list cnt start-rip)
                                           :x (cpl x86-2) (double-rewrite x86-2)))))
             (xlate-equiv-memory (mv-nth 2 (get-prefixes start-rip prefixes cnt x86-1))
                                 (mv-nth 2 (get-prefixes start-rip prefixes cnt x86-2))))
    :hints (("Goal"
             :use ((:instance xlate-equiv-memory-and-mv-nth-2-get-prefixes (x86 x86-1))
                   (:instance xlate-equiv-memory-and-mv-nth-2-get-prefixes (x86 x86-2)))
             :in-theory (e/d* ()
                              (xlate-equiv-memory-and-mv-nth-2-get-prefixes
                               acl2::ash-0
                               acl2::zip-open
                               cdr-create-canonical-address-list))))))

;; ======================================================================

;; rb in system-level marking mode:

(defsection rb-in-system-level-marking-mode
  :parents (marking-mode-top)

  (defthm xr-fault-rb-state-in-system-level-mode
    (implies (not (mv-nth 0 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86))))
             (equal (xr :fault index (mv-nth 2 (rb l-addrs r-w-x x86)))
                    (xr :fault index x86)))
    :hints (("Goal" :in-theory (e/d* (las-to-pas rb) (force (force))))))

  (defthm rb-and-!flgi-state-in-system-level-mode
    (implies (and (not (equal index *ac*))
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
                              (force (force))))))

  (defthm mv-nth-0-rb-and-xlate-equiv-memory-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (equal (mv-nth 0 (rb l-addrs r-w-x x86-1))
                    (mv-nth 0 (rb l-addrs r-w-x x86-2))))
    :hints (("Goal" :in-theory (e/d* (rb) (force (force)))))
    :rule-classes :congruence)

  (local
   (defthmd read-from-physical-memory-and-xlate-equiv-memory-disjoint-from-paging-structures-helper
     (implies (and (bind-free
                    (find-an-xlate-equiv-x86
                     'read-from-physical-memory-and-xlate-equiv-memory
                     x86-1 'x86-2 mfc state)
                    (x86-2))
                   (syntaxp (and (not (eq x86-2 x86-1))
                                 ;; x86-2 must be smaller than x86-1.
                                 (term-order x86-2 x86-1)))
                   (xlate-equiv-memory (double-rewrite x86-1) x86-2)
                   (disjoint-p
                    (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86-1)))
                    (all-translation-governing-addresses l-addrs (double-rewrite x86-1)))
                   (disjoint-p
                    (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86-1)))
                    (open-qword-paddr-list
                     (gather-all-paging-structure-qword-addresses (double-rewrite x86-1))))
                   (canonical-address-listp l-addrs))
              (equal (read-from-physical-memory (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86-1)) x86-1)
                     (read-from-physical-memory (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86-1)) x86-2)))
     :hints (("Goal"
              :induct (las-to-pas l-addrs r-w-x cpl x86-1)
              :in-theory (e/d* (las-to-pas
                                disjoint-p
                                disjoint-p-commutative
                                xlate-equiv-memory)
                               (disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
                                mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs))))))

  (defthm read-from-physical-memory-and-xlate-equiv-memory-disjoint-from-paging-structures
    (implies (and (bind-free
                   (find-an-xlate-equiv-x86
                    'read-from-physical-memory-and-xlate-equiv-memory
                    x86-1 'x86-2 mfc state)
                   (x86-2))
                  (syntaxp (and (not (eq x86-2 x86-1))
                                ;; x86-2 must be smaller than x86-1.
                                (term-order x86-2 x86-1)))
                  (xlate-equiv-memory (double-rewrite x86-1) x86-2)
                  (disjoint-p (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86-1)))
                              (open-qword-paddr-list
                               (gather-all-paging-structure-qword-addresses (double-rewrite x86-1))))
                  (canonical-address-listp l-addrs))
             (equal (read-from-physical-memory (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86-1)) x86-1)
                    (read-from-physical-memory (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86-1)) x86-2)))
    :hints (("Goal"
             :use ((:instance read-from-physical-memory-and-xlate-equiv-memory-disjoint-from-paging-structures-helper))
             :in-theory (e/d* ()
                              (disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
                               mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)))))

  (defthm mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
    (implies (and (bind-free
                   (find-an-xlate-equiv-x86
                    'mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
                    x86-1 'x86-2 mfc state)
                   (x86-2))
                  (syntaxp (and
                            (not (eq x86-2 x86-1))
                            ;; x86-2 must be smaller than x86-1.
                            (term-order x86-2 x86-1)))
                  (xlate-equiv-memory (double-rewrite x86-1) x86-2)
                  (disjoint-p
                   (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86-1) (double-rewrite x86-1)))
                   (open-qword-paddr-list
                    (gather-all-paging-structure-qword-addresses (double-rewrite x86-1))))
                  (canonical-address-listp l-addrs))
             (equal (mv-nth 1 (rb l-addrs r-w-x x86-1))
                    (mv-nth 1 (rb l-addrs r-w-x x86-2))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance xlate-equiv-memory-in-programmer-level-mode-implies-equal-states)
                   (:instance read-from-physical-memory-and-xlate-equiv-memory-disjoint-from-paging-structures
                              (cpl (cpl x86-1))))
             :in-theory (e/d* (rb
                               disjoint-p-commutative)
                              (read-from-physical-memory-and-xlate-equiv-memory-disjoint-from-paging-structures
                               force (force))))))

  (defthm mv-nth-2-rb-and-xlate-equiv-memory
    (implies (and (page-structure-marking-mode (double-rewrite x86))
                  (not (mv-nth 0 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86))))
                  (not (programmer-level-mode (double-rewrite x86))))
             (xlate-equiv-memory (mv-nth 2 (rb l-addrs r-w-x x86))
                                 (double-rewrite x86)))
    :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthmd xlate-equiv-memory-and-two-mv-nth-2-rb
    (implies (and (xlate-equiv-memory x86-1 x86-2)
                  (page-structure-marking-mode x86-1)
                  (not (programmer-level-mode x86-1))
                  (not (mv-nth 0 (las-to-pas l-addrs r-w-x (cpl x86-1) (double-rewrite x86-1)))))
             (xlate-equiv-memory (mv-nth 2 (rb l-addrs r-w-x x86-1))
                                 (mv-nth 2 (rb l-addrs r-w-x x86-2))))
    :hints (("Goal" :in-theory (e/d* () (mv-nth-2-rb-and-xlate-equiv-memory))
             :use ((:instance mv-nth-2-rb-and-xlate-equiv-memory (x86 x86-1))
                   (:instance mv-nth-2-rb-and-xlate-equiv-memory (x86 x86-2))))))

  (defthm mv-nth-1-rb-after-mv-nth-2-rb
    ;; This rule will come in useful when rb isn't rewritten to
    ;; rb-alt, i.e., for reads from the paging structures.  Hence,
    ;; I'll use disjoint-p$ in the hyps here instead of disjoint-p.
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
             :in-theory (e/d* (rb disjoint-p$) (force (force))))))

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
             :in-theory (e/d* (rb) (force (force)))))))

;; ======================================================================
