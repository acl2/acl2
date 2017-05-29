;; AUTHOR:
;; Shilpi Goel <shilpi@centtech.com>

(in-package "X86ISA")

(include-book "x86-row-wow-thms" :ttags :all :dir :proof-utils)
(include-book "general-memory-utils" :ttags :all :dir :proof-utils)
(include-book "clause-processors/find-subterms" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
;; (local (include-book "std/lists/take" :dir :system))

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
;; (acl2::why one-read-with-rb-from-prog-at)
;; (acl2::why prog-at-wb-disjoint)

;; ======================================================================

(local (in-theory (enable rvm08 wvm08)))

;; Theorems about rvm08 and wvm08:

;; rvm08 and wmw08 RoW:

(defthm |(rvm08 addr2 (wvm08 addr1 val x86)) --- same addr|
  (implies (and (equal addr1 addr2)
                (n08p val)
                (canonical-address-p addr1))
           (equal (rvm08 addr2 (mv-nth 1 (wvm08 addr1 val x86)))
                  (mv nil val (mv-nth 1 (wvm08 addr1 val x86))))))

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

(defthm rb-!flgi-in-programmer-level-mode
  (implies (programmer-level-mode x86)
           (equal (mv-nth 1 (rb n addr r-x (!flgi flg val x86)))
                  (mv-nth 1 (rb n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d* (!flgi) (rb force (force))))))

(defthm !flgi-and-wb-in-programmer-level-mode
  (implies (programmer-level-mode x86)
           (equal (!flgi flg val (mv-nth 1 (wb n addr w val x86)))
                  (mv-nth 1 (wb n addr w val (!flgi flg val x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (!flgi) (force (force))))))

(defthm prog-at-!flgi
  (implies (programmer-level-mode x86)
           (equal (prog-at prog-addr bytes (!flgi flg val x86))
                  (prog-at prog-addr bytes x86)))
  :hints (("Goal" :in-theory (e/d (prog-at !flgi) (force (force) rb)))))

(defthm rb-!flgi-undefined-in-programmer-level-mode
  (implies (programmer-level-mode x86)
           (equal (mv-nth 1 (rb n addr r-x (!flgi-undefined flg x86)))
                  (mv-nth 1 (rb n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d* (!flgi-undefined) (rb force (force))))))

(defthm !flgi-undefined-and-wb-in-programmer-level-mode
  (implies (programmer-level-mode x86)
           (equal (!flgi-undefined flg (mv-nth 1 (wb n addr w val x86)))
                  (mv-nth 1 (wb n addr w val (!flgi-undefined flg x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (!flgi-undefined !flgi) (force (force))))))

(defthm prog-at-!flgi-undefined
  (implies (programmer-level-mode x86)
           (equal (prog-at prog-addr bytes (!flgi-undefined flg x86))
                  (prog-at prog-addr bytes x86)))
  :hints (("Goal" :in-theory (e/d (prog-at !flgi-undefined) (prog-at)))))

(defthm rb-write-user-rflags-in-programmer-level-mode
  (implies (programmer-level-mode x86)
           (equal (mv-nth 1 (rb n addr r-x (write-user-rflags flags mask x86)))
                  (mv-nth 1 (rb n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d* (write-user-rflags) (rb force (force))))))

(defthm write-user-rflags-and-wb-in-programmer-level-mode
  (implies (programmer-level-mode x86)
           (equal (write-user-rflags flags mask (mv-nth 1 (wb n addr w val x86)))
                  (mv-nth 1 (wb n addr w val (write-user-rflags flags mask x86)))))
  :hints (("Goal" :do-not '(preprocess) :do-not-induct t
           :in-theory (e/d* (write-user-rflags !flgi-undefined)
                            (acl2::loghead-identity
                             wb !flgi force (force))))))

(defthm flgi-wb-in-programmer-level-mode
  (implies (programmer-level-mode x86)
           (equal (flgi flg (mv-nth 1 (wb n addr w val x86)))
                  (flgi flg x86)))
  :hints (("Goal" :in-theory (e/d* (flgi) (wb)))))

(defthm alignment-checking-enabled-p-and-wb-in-programmer-level-mode
  (implies (programmer-level-mode x86)
           (equal (alignment-checking-enabled-p (mv-nth 1 (wb n addr w val x86)))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal" :in-theory (e/d* (alignment-checking-enabled-p)
                                   (wb force (force))))))

(defthm write-x86-file-contents-wb
  (implies (programmer-level-mode x86)
           (equal (write-x86-file-contents i v (mv-nth 1 (wb n addr w val x86)))
                  (mv-nth 1 (wb n addr w val (write-x86-file-contents i v x86)))))
  :hints (("Goal" :in-theory (e/d* (write-x86-file-contents
                                    write-x86-file-contents-logic)
                                   ()))))

(defthm delete-x86-file-contents-wb
  (implies (programmer-level-mode x86)
           (equal (delete-x86-file-contents i (mv-nth 1 (wb n addr w val x86)))
                  (mv-nth 1 (wb n addr w val (delete-x86-file-contents i x86)))))
  :hints (("Goal" :in-theory (e/d* (delete-x86-file-contents
                                    delete-x86-file-contents-logic)
                                   ()))))

(defthm pop-x86-oracle-wb
  (implies (programmer-level-mode x86)
           (equal (mv-nth 1 (pop-x86-oracle (mv-nth 1 (wb n addr w val x86))))
                  (mv-nth 1 (wb n addr w val (mv-nth 1 (pop-x86-oracle x86))))))
  :hints (("Goal" :in-theory (e/d* (pop-x86-oracle pop-x86-oracle-logic) (wb)))))

(defthm rb-and-write-x86-file-des
  (implies (programmer-level-mode x86)
           (equal (mv-nth 1 (rb n addr r-x (write-x86-file-des i val x86)))
                  (mv-nth 1 (rb n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d* (write-x86-file-des write-x86-file-des-logic)
                                   (rb)))))

(defthm rb-and-write-x86-file-contents
  (implies (programmer-level-mode x86)
           (equal (mv-nth 1 (rb n addr r-x (write-x86-file-contents i val x86)))
                  (mv-nth 1 (rb n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d* (write-x86-file-contents
                                    write-x86-file-contents-logic)
                                   (rb)))))

(defthm rb-and-pop-x86-oracle
  (implies (programmer-level-mode x86)
           (equal (mv-nth 1 (rb n addr r-x (mv-nth 1 (pop-x86-oracle x86))))
                  (mv-nth 1 (rb n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d* (pop-x86-oracle pop-x86-oracle-logic) (rb)))))

(defthm delete-x86-file-des-wb
  (implies (programmer-level-mode x86)
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
            (equal (mv-nth 1 (rb-1 n-1 addr-1 r-x
                                   (mv-nth 1 (wb-1 n-2 addr-2 w val x86))))
                   (mv-nth 1 (rb-1 n-1 addr-1 r-x x86))))
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (e/d* (push-ash-inside-logior)
                             (rvm08 wvm08))))))

(defthm rb-wb-disjoint
  (implies (and (or (<= (+ n-2 addr-2) addr-1)
                    (<= (+ n-1 addr-1) addr-2))
                (programmer-level-mode x86))
           (equal (mv-nth 1 (rb n-1 addr-1 r-x (mv-nth 1 (wb n-2 addr-2 w val x86))))
                  (mv-nth 1 (rb n-1 addr-1 r-x x86))))
  :hints (("Goal"
           :use ((:instance rb-1-wb-1-disjoint))
           :in-theory (e/d* (rb wb) (rb-1-wb-1-disjoint wb-1 rb-1)))))

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
                (programmer-level-mode x86))
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
   (and (programmer-level-mode x86)
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

(defthmd rb-rb-subset
  ;; [Shilpi]: Expensive rule. Keep this disabled.
  (implies (and (equal (mv-nth 1 (rb i addr r-x-i x86)) val)
                (canonical-address-p (+ -1 i addr))
                (posp j)
                (< j i)
                (programmer-level-mode x86)
                (x86p x86))
           (equal (mv-nth 1 (rb j addr r-x-j x86))
                  (loghead (ash j 3) val)))
  :hints (("Goal"
           :in-theory (e/d* (rb-1-rb-1-subset-helper-1
                             rb-1-rb-1-subset-helper-2)
                            (unsigned-byte-p)))))

;; ----------------------------------------------------------------------

;; Lemmas about prog-at:

(defthm prog-at-wb-disjoint
  (implies (and (or (<= (+ (len bytes) prog-addr) addr)
                    (<= (+ n addr) prog-addr))
                (programmer-level-mode x86))
           (equal (prog-at prog-addr bytes (mv-nth 1 (wb n addr w val x86)))
                  (prog-at prog-addr bytes x86)))
  :hints (("Goal" :in-theory (e/d (prog-at) (rb wb)))))

(defthm prog-at-write-x86-file-des
  (implies (programmer-level-mode x86)
           (equal (prog-at addr bytes (write-x86-file-des i v x86))
                  (prog-at addr bytes x86)))
  :hints (("Goal" :in-theory (e/d (prog-at
                                   write-x86-file-des
                                   write-x86-file-des-logic)
                                  (rb)))))

(defthm prog-at-delete-x86-file-des
  (implies (programmer-level-mode x86)
           (equal (prog-at addr bytes (delete-x86-file-des i x86))
                  (prog-at addr bytes x86)))
  :hints (("Goal" :in-theory (e/d (prog-at
                                   delete-x86-file-des
                                   delete-x86-file-des-logic)
                                  (rb)))))

(defthm prog-at-write-x86-file-contents
  (implies (programmer-level-mode x86)
           (equal (prog-at addr bytes (write-x86-file-contents i v x86))
                  (prog-at addr bytes x86)))
  :hints (("Goal" :in-theory (e/d (prog-at
                                   write-x86-file-contents
                                   write-x86-file-contents-logic)
                                  (rb)))))

(defthm prog-at-delete-x86-file-contents
  (implies (programmer-level-mode x86)
           (equal (prog-at addr bytes (delete-x86-file-contents i x86))
                  (prog-at addr bytes x86)))
  :hints (("Goal" :in-theory (e/d (prog-at
                                   delete-x86-file-contents
                                   delete-x86-file-contents-logic)
                                  (rb)))))

(defthm prog-at-pop-x86-oracle
  (implies (programmer-level-mode x86)
           (equal (prog-at addr bytes (mv-nth 1 (pop-x86-oracle x86)))
                  (prog-at addr bytes x86)))
  :hints (("Goal" :in-theory (e/d (prog-at pop-x86-oracle pop-x86-oracle-logic)
                                  (rb)))))

(defthm prog-at-write-user-rflags
  (implies (programmer-level-mode x86)
           (equal (prog-at addr bytes (write-user-rflags flags mask x86))
                  (prog-at addr bytes x86)))
  :hints (("Goal" :in-theory (e/d (write-user-rflags !flgi-undefined)
                                  (force (force))))))

;; ======================================================================

;; Lemmas about rb and prog-at:

;; The following theorems help in relieving the hypotheses of
;; get-prefixes opener lemmas.
(local
 (defthm rb-1-from-prog-at-helper
   (implies (and (signed-byte-p 48 prog-addr)
                 (equal (car bytes) (ifix (mv-nth 1 (rvm08 prog-addr x86))))
                 (equal (mv-nth 1 (rb-1 1 addr :x x86))
                        (nth (+ -1 addr (- prog-addr)) (cdr bytes)))
                 (prog-at (+ 1 prog-addr) (cdr bytes) x86)
                 (signed-byte-p 48 addr)
                 (<= prog-addr addr)
                 (xr :programmer-level-mode 0 x86))
            (equal (mv-nth 1 (rb-1 1 addr :x x86))
                   (nth (+ addr (- prog-addr)) bytes)))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d* () (signed-byte-p))
            :expand ((nth (+ addr (- prog-addr)) bytes))))))

(local
 (defthm rb-1-from-prog-at
   (implies (and (prog-at prog-addr bytes x86)
                 (<= prog-addr addr)
                 (< addr (+ (len bytes) prog-addr))
                 (canonical-address-p addr)
                 (programmer-level-mode x86))
            (equal (mv-nth 1 (rb-1 1 addr :x x86))
                   (nth (nfix (- addr prog-addr)) bytes)))
   :hints (("Goal"
            :induct (prog-at prog-addr bytes x86)
            :in-theory (e/d (prog-at)
                            (nth signed-byte-p))))))

(defun find-info-from-prog-at-term-in-programmer-mode (ctx mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable ctx state))
  (b* ((call (acl2::find-call-lst 'prog-at (acl2::mfc-clause mfc)))
       ((when (not call))
        ;; (cw "~%~p0: prog-at term not encountered.~%" ctx)
        nil)
       (prog-addr (cadr call))
       (bytes (caddr call)))
    `((prog-addr . ,prog-addr)
      (bytes . ,bytes))))

(defthm one-read-with-rb-from-prog-at
  (implies (and
            (bind-free (find-info-from-prog-at-term-in-programmer-mode
                        'one-read-with-rb-from-prog-at
                        mfc state)
                       (prog-addr bytes))
            (prog-at prog-addr bytes x86)
            (<= prog-addr addr)
            (< addr (+ (len bytes) prog-addr))
            (canonical-address-p addr)
            (programmer-level-mode x86))
           (equal (mv-nth 1 (rb 1 addr :x x86))
                  (nth (nfix (- addr prog-addr)) bytes)))
  :hints (("Goal" :in-theory (e/d () (rb-1 nth signed-byte-p)))))

(local
 (defthm many-reads-with-rb-1-from-prog-at
   (implies
    (and (prog-at prog-addr bytes x86)
         (<= prog-addr addr)
         (< (+ n addr) (+ (len bytes) prog-addr))
         (canonical-address-p addr)
         (canonical-address-p (+ -1 n addr))
         (posp n)
         (programmer-level-mode x86))
    (equal (mv-nth 1 (rb-1 n addr :x x86))
           (logior (nth (nfix (- addr prog-addr)) bytes)
                   (ash (mv-nth 1 (rb-1 (1- n) (1+ addr) :x x86)) 8))))
   :hints (("Goal"
            :induct (prog-at prog-addr bytes x86)
            :in-theory (e/d* (prog-at)
                             (signed-byte-p))))))

(defthm many-reads-with-rb-from-prog-at
  (implies
   (and (bind-free (find-info-from-prog-at-term-in-programmer-mode
                    'many-reads-with-rb-from-prog-at
                    mfc state)
                   (prog-addr bytes))
        (prog-at prog-addr bytes x86)
        (<= prog-addr addr)
        (< (+ n addr) (+ (len bytes) prog-addr))
        (canonical-address-p addr)
        (canonical-address-p (+ -1 n addr))
        (posp n)
        (programmer-level-mode x86))
   (equal (mv-nth 1 (rb n addr :x x86))
          (logior (nth (nfix (- addr prog-addr)) bytes)
                  (ash (mv-nth 1 (rb (1- n) (1+ addr) :x x86)) 8))))
  :hints (("Goal" :in-theory (e/d* () (rb-1 signed-byte-p)))))

;; ======================================================================

(globally-disable '(rb wb canonical-address-p prog-at unsigned-byte-p signed-byte-p))

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
            ;; We disable some expensive and irrelevant lemmas in
            ;; the programmer-level mode.
            (mv-nth-1-wb-and-!flgi-commute
             ia32e-la-to-pa-values-and-!flgi
             las-to-pas
             las-to-pas-values-and-!flgi
             mv-nth-2-las-to-pas-and-!flgi-not-ac-commute
             xr-fault-wb-in-system-level-marking-mode
             xr-fault-wb-in-system-level-mode)))

;; ======================================================================
