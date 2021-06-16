; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")
;(include-book "lists")
(include-book "u32-listp")
(include-book "std/basic/defs" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/stobjs/absstobjs" :dir :system)
(include-book "arithmetic/nat-listp" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "misc/definline" :dir :system)
(include-book "std/stobjs/updater-independence" :dir :system)
(include-book "std/stobjs/clone" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(in-theory (enable* arith-equiv-forwarding))

(local (in-theory (disable nth update-nth nth-when-zp resize-list-when-atom take
                           update-nth-when-zp
                           update-nth-when-atom)))
(local (std::add-default-post-define-hook :fix))
;; this is a dumb "memory manager" which can allocate new blocks at will, but
;; only frees any blocks if it frees all blocks.

(defstobj smme
  (smme-nblocks :type (integer 0 *) :initially 0)
  ;; one larger than smme-blocksizes
  (smme-blockstarts :type (array (integer 0 *) (1))
                    :initially 0
                    :resizable t)
  ;; (smme-blocksizes :type (array (integer 0 *) (0))
  ;;                  :initially 0
  ;;                  :resizable t)
  ;; 32-bit unsigneds for now, why not
  (smme-mem :type (array (unsigned-byte 32) (0))
             :initially 0
             :resizable t)
  :inline t
  :renaming ((smme-memi __smme-memi)
             (update-smme-memi __update-smme-memi)
             (smme-nblocks __smme-nblocks)
             (update-smme-nblocks __update-smme-nblocks)))



(defthm smme-blockstarts-p-nat-listp
  (equal (smme-blockstartsp x)
         (nat-listp x)))

;; (defthm smme-blocksizes-p-nat-listp
;;   (equal (smme-blocksizesp x)
;;          (nat-listp x)))

(local (defthm nth-in-nat-listp
         (implies (and (nat-listp x)
                       (< (nfix n) (len x)))
                  (and (integerp (nth n x))
                       (<= 0 (nth n x))))
         :hints(("Goal" :in-theory (enable nth)))
         :rule-classes (:rewrite
                        (:rewrite :corollary
                         (implies (and (nat-listp x)
                                       (< (nfix n) (len x)))
                                  (natp (nth n x))))
                        ;; :type-prescription
                        (:linear :corollary
                         (implies (and (nat-listp x)
                                       (< (nfix n) (len x)))
                                  (<= 0 (nth n x)))))))

(local (defthm rationalp-+-of-integers
         (implies (and (integerp x) (integerp y))
                  (rationalp (+ x y)))))

(defsection smme-blockstarts-accessors

  (def-updater-independence-thm smme-blockstarts-length-updater-independence
    (implies (equal (len (nth *smme-blockstartsi* new))
                    (len (nth *smme-blockstartsi* old)))
             (equal (smme-blockstarts-length new)
                    (smme-blockstarts-length old))))


  (define smme-block-start ((n natp) smme)
    :inline t
    :guard (< n (smme-blockstarts-length smme))
    (lnfix (smme-blockstartsi n smme))
    ///

    (def-updater-independence-thm smme-block-start-updater-independence
      (implies (nat-equiv (nth n (nth *smme-blockstartsi* new))
                          (nth n (nth *smme-blockstartsi* old)))
               (equal (smme-block-start n new)
                      (smme-block-start n old)))))

  (define update-smme-block-start ((n natp) (val natp) smme)
    :inline t
    :guard (< n (smme-blockstarts-length smme))
    (update-smme-blockstartsi (lnfix n) (lnfix val) smme)
    ///

    (defthm update-smme-block-start-preserves-smme-blockstarts
      (implies (not (equal (nfix k) (nfix n)))
               (equal (nth k (nth *smme-blockstartsi* (update-smme-block-start n val smme)))
                      (nth k (nth *smme-blockstartsi* smme)))))

    (defthm update-smme-block-start-preserves-smme-blockstarts-len
      (implies (< (nfix n) (smme-blockstarts-length smme))
               (equal (smme-blockstarts-length (update-smme-block-start n val smme))
                      (smme-blockstarts-length smme))))

    (defthm update-smme-block-start-preserves-other
      (implies (not (equal (nfix k) *smme-blockstartsi*))
               (equal (nth k (update-smme-block-start n val smme))
                      (nth k smme))))

    (defthm smme-blockstarts-length-of-update-smme-block-start-nondecr
      (<= (smme-blockstarts-length smme)
          (smme-blockstarts-length (update-smme-block-start n val smme)))
      :rule-classes :linear)

    (defthm smme-block-start-of-update-smme-block-start
      (equal (smme-block-start n (update-smme-block-start n val smme))
             (nfix val))
      :hints(("Goal" :in-theory (enable smme-block-start)))))

  (defthm smme-blockstarts-length-of-resize-smme-blockstarts
    (equal (smme-blockstarts-length (resize-smme-blockstarts n smme))
           (nfix n)))

  (defthm resize-smme-blockstarts-preserves-smme-blockstarts
    (implies (< (nfix k) (nfix n))
             (nat-equiv (nth k (nth *smme-blockstartsi* (resize-smme-blockstarts n smme)))
                        (nth k (nth *smme-blockstartsi* smme))))
    :hints(("Goal" :in-theory (disable resize-list)
            :cases ((< (nfix k) (Len (nth *smme-blockstartsi* smme)))))))

  (defthm resize-smme-blockstarts-preserves-others
    (implies (not (equal (nfix k) *smme-blockstartsi*))
             (equal (nth k (resize-smme-blockstarts n smme))
                    (nth k smme))))

  (in-theory (disable smme-blockstarts-length
                      resize-smme-blockstarts)))

;; (defsection smme-blocksizes-accessors

;;   (def-updater-independence-thm smme-blocksizes-length-updater-independence
;;     (implies (equal (len (nth *smme-blocksizesi* new))
;;                     (len (nth *smme-blocksizesi* old)))
;;              (equal (smme-blocksizes-length new)
;;                     (smme-blocksizes-length old))))


;;   (define smme-block-size ((n natp) smme)
;;     :inline t
;;     :guard (< n (smme-blocksizes-length smme))
;;     (lnfix (smme-blocksizesi n smme))
;;     ///

;;     (def-updater-independence-thm smme-block-size-updater-independence
;;       (implies (nat-equiv (nth n (nth *smme-blocksizesi* new))
;;                           (nth n (nth *smme-blocksizesi* old)))
;;                (equal (smme-block-size n new)
;;                       (smme-block-size n old)))))

;;   (define update-smme-block-size ((n natp) (val natp) smme)
;;     :inline t
;;     :guard (< n (smme-blocksizes-length smme))
;;     (update-smme-blocksizesi (lnfix n) (lnfix val) smme)
;;     ///

;;     (defthm update-smme-block-size-preserves-smme-blocksizes
;;       (implies (not (equal (nfix k) (nfix n)))
;;                (equal (nth k (nth *smme-blocksizesi* (update-smme-block-size n val smme)))
;;                       (nth k (nth *smme-blocksizesi* smme)))))

;;     (defthm update-smme-block-size-preserves-smme-blocksizes-len
;;       (implies (< (nfix n) (smme-blocksizes-length smme))
;;                (equal (smme-blocksizes-length (update-smme-block-size n val smme))
;;                       (smme-blocksizes-length smme))))

;;     (defthm update-smme-block-size-preserves-other
;;       (implies (not (equal (nfix k) *smme-blocksizesi*))
;;                (equal (nth k (update-smme-block-size n val smme))
;;                       (nth k smme))))

;;     (defthm smme-blocksizes-length-of-update-smme-block-size-nondecr
;;       (<= (smme-blocksizes-length smme)
;;           (smme-blocksizes-length (update-smme-block-size n val smme)))
;;       :rule-classes :linear)

;;     (defthm smme-block-size-of-update-smme-block-size
;;       (equal (smme-block-size n (update-smme-block-size n val smme))
;;              (nfix val))
;;       :hints(("Goal" :in-theory (enable smme-block-size)))))

;;   (defthm smme-blocksizes-length-of-resize-smme-blocksizes
;;     (equal (smme-blocksizes-length (resize-smme-blocksizes n smme))
;;            (nfix n)))

;;   (defthm resize-smme-blocksizes-preserves-smme-blocksizes
;;     (implies (< (nfix k) (nfix n))
;;              (nat-equiv (nth k (nth *smme-blocksizesi* (resize-smme-blocksizes n smme)))
;;                         (nth k (nth *smme-blocksizesi* smme))))
;;     :hints(("Goal" :in-theory (disable resize-list)
;;             :cases ((< (nfix k) (Len (nth *smme-blocksizesi* smme)))))))

;;   (defthm resize-smme-blocksizes-preserves-others
;;     (implies (not (equal (nfix k) *smme-blocksizesi*))
;;              (equal (nth k (resize-smme-blocksizes n smme))
;;                     (nth k smme))))

;;   (in-theory (disable smme-blocksizes-length
;;                       resize-smme-blocksizes)))



(defsection smme-mem-accessors


  (defthm smme-memp-is-u32-listp
    (equal (smme-memp x)
           (u32-listp x)))

  (local (in-theory (enable nth-in-u32-listp-natp)))

  (defconst *smme-memi* *__smme-memi*)

  (def-updater-independence-thm smme-mem-length-updater-independence
    (implies (equal (len (nth *smme-memi* new))
                    (len (nth *smme-memi* old)))
             (equal (smme-mem-length new)
                    (smme-mem-length old))))


  (define smme-memi ((n natp) smme)
    :inline t
    :guard (< n (smme-mem-length smme))
    (lnfix (__smme-memi n smme))
    ///

    (def-updater-independence-thm smme-memi-updater-independence
      (implies (nat-equiv (nth n (nth *smme-memi* new))
                          (nth n (nth *smme-memi* old)))
               (equal (smme-memi n new)
                      (smme-memi n old)))))

  (define update-smme-memi ((n natp) (val :type (unsigned-byte 32)) smme)
    :inline t
    :guard (and (< n (smme-mem-length smme))
                (unsigned-byte-p 32 val))
    :split-types t
    (__update-smme-memi (lnfix n) (lnfix val) smme)
    ///
    (fty::deffixequiv update-smme-memi :args ((n natp) (val natp)))

    (defthm update-smme-memi-preserves-smme-mem
      (implies (not (equal (nfix k) (nfix n)))
               (equal (nth k (nth *smme-memi* (update-smme-memi n val smme)))
                      (nth k (nth *smme-memi* smme)))))

    ;; (defthm update-smme-memi-preserves-smme-mem-len
    ;;   (implies (< (nfix n) (smme-mem-length smme))
    ;;            (equal (smme-mem-length (update-smme-memi n val smme))
    ;;                   (smme-mem-length smme))))

    (defthm update-smme-memi-preserves-other
      (implies (not (equal (nfix k) *smme-memi*))
               (equal (nth k (update-smme-memi n val smme))
                      (nth k smme))))

    (defthm smme-mem-length-of-update-smme-memi-nondecr
      (<= (smme-mem-length smme)
          (smme-mem-length (update-smme-memi n val smme)))
      :rule-classes :linear)

    (defthm smme-memi-of-update-smme-memi
      (equal (smme-memi n (update-smme-memi n val smme))
             (nfix val))
      :hints(("Goal" :in-theory (enable smme-memi)))))

  (defthm smme-mem-length-of-resize-smme-mem
    (equal (smme-mem-length (resize-smme-mem n smme))
           (nfix n)))

  (defthm resize-smme-mem-preserves-smme-mem
    (implies (< (nfix k) (nfix n))
             (nat-equiv (nth k (nth *smme-memi* (resize-smme-mem n smme)))
                        (nth k (nth *smme-memi* smme))))
    :hints(("Goal" :in-theory (disable resize-list)
            :cases ((< (nfix k) (Len (nth *smme-memi* smme)))))))

  (defthm resize-smme-mem-preserves-others
    (implies (not (equal (nfix k) *smme-memi*))
             (equal (nth k (resize-smme-mem n smme))
                    (nth k smme))))

  (in-theory (disable smme-mem-length
                      resize-smme-mem)))


(defsection smme-nblocks-accessors

  (defconst *smme-nblocks* *__smme-nblocks*)

  (define smme-nblocks (smme)
    :inline t
    (lnfix (__smme-nblocks smme))
    ///
    (def-updater-independence-thm smme-nblocks-updater-independence
      (implies (nat-equiv (nth *smme-nblocks* new)
                          (nth *smme-nblocks* old))
               (equal (smme-nblocks new)
                      (smme-nblocks old)))))

  (define update-smme-nblocks ((nblocks natp) smme)
    :inline t
    (__update-smme-nblocks (lnfix nblocks) smme)
    ///
    (defthm update-smme-nblocks-preserves-nth
      (implies (not (equal (nfix n) *smme-nblocks*))
               (equal (nth n (update-smme-nblocks nblocks smme))
                      (nth n smme))))

    (defthm smme-nblocks-of-update-smme-nblocks
      (equal (smme-nblocks (update-smme-nblocks nblocks smme))
             (nfix nblocks))
      :hints(("Goal" :in-theory (enable smme-nblocks))))))




;; (define smme-sizes-okp (smme)
;;   (and (< (smme-nblocks smme)
;;           (smme-blockstarts-length smme))
;;        (<= (smme-nblocks smme)
;;            (smme-blocksizes-length smme))))













(define smme-blocks-wfp ((n natp) smme)
  :guard (< n (smme-blockstarts-length smme))
  ;; :guard-hints (("goal" :in-theory (enable smme-sizes-okp)))
  (or (zp n)
      (and (>= (smme-block-start n smme)
               (smme-block-start (1- n) smme))
           (smme-blocks-wfp (1- n) smme)))
  ///
  (def-updater-independence-thm smme-blocks-wfp-updater-independence
    (implies (and (smme-blocks-wfp n old)
                  (stobjs::range-nat-equiv 0 (+ 1 (nfix n))
                                           (nth *smme-blockstartsi* new)
                                           (nth *smme-blockstartsi* old))
                  ;; (stobjs::range-nat-equiv 0 n
                  ;;                          (nth *smme-blocksizesi* new)
                  ;;                          (nth *smme-blocksizesi* old))
                  )
             (smme-blocks-wfp n new))
    :hints(("Goal" :in-theory (enable stobjs::nth-when-range-nat-equiv)))))



(define smme-wfp (smme)
  ;; :guard-hints (("goal" :in-theory (enable smme-sizes-okp)))
  (and (< (smme-nblocks smme)
          (smme-blockstarts-length smme)) ;; (smme-sizes-okp smme)
       (int= 0 (smme-block-start 0 smme))
       (<= (smme-block-start (smme-nblocks smme) smme)
           (smme-mem-length smme))
       (smme-blocks-wfp (smme-nblocks smme) smme))
  ///
  (def-updater-independence-thm smme-wfp-updater-independence
    (implies (and (smme-wfp old)
                  (nat-equiv (nth *smme-nblocks* new)
                             (nth *smme-nblocks* old))
                  (stobjs::range-nat-equiv 0 (+ 1 (smme-nblocks old))
                                           (nth *smme-blockstartsi* new)
                                           (nth *smme-blockstartsi* old))
                  ;; (stobjs::range-nat-equiv 0 (smme-nblocks old)
                  ;;                          (nth *smme-blocksizesi* new)
                  ;;                          (nth *smme-blocksizesi* old))
                  (<= (smme-blockstarts-length old) (smme-blockstarts-length new))
                  ;; (<= (smme-blocksizes-length old) (smme-blocksizes-length new))
                  (<= (smme-mem-length old) (smme-mem-length new)))
             (smme-wfp new))
    :hints(("Goal" :in-theory (enable ;; smme-sizes-okp
                                      stobjs::nth-when-range-nat-equiv))))

  ;; (defthm smme-wfp-of-update-smme-memi
  ;;   (implies (smme-wfp smme)
  ;;            (smme-wfp (update-smme-memi i v smme))))

  ;; (local (in-theory (disable smme-wfp-updater-independence)))

  (defthm smme-wfp-implies-blockstarts-length
    (implies (smme-wfp smme)
             (< (smme-nblocks smme)
                (smme-blockstarts-length smme)))
    ;; :hints(("Goal" :in-theory (enable smme-sizes-okp)))
    :rule-classes :linear)

  ;; (defthm smme-wfp-implies-blocksizes-length
  ;;   (implies (smme-wfp smme)
  ;;            (<= (smme-nblocks smme)
  ;;                (smme-blocksizes-length smme)))
  ;;   :hints(("Goal" :in-theory (enable smme-sizes-okp)))
  ;;   :rule-classes :linear)

  (local
   (defthm smme-blocks-wfp-implies-blockstarts-monotonic-1
    (implies (and (smme-blocks-wfp k smme)
                  (<= (nfix n) (nfix k)))
             (<= (smme-block-start n smme) (smme-block-start k smme)))
    :hints(("Goal" :in-theory (enable smme-blocks-wfp)))))

  (local
   (defthm smme-blocks-wfp-implies-blockstarts-monotonic
    (implies (and (smme-blocks-wfp k smme)
                  (<= (nfix n) (nfix m))
                  (<= (nfix m) (nfix k)))
             (<= (smme-block-start n smme) (smme-block-start m smme)))
    :hints(("Goal" :in-theory (enable smme-blocks-wfp)))))

  (defthm smme-wfp-implies-blockstarts-monotonic
    (implies (and (smme-wfp smme)
                  (<= (nfix n) (nfix m))
                  (<= (nfix m) (smme-nblocks smme)))
             (<= (smme-block-start n smme) (smme-block-start m smme))))

  (defthm smme-wfp-implies-block-start-lte-last
    (implies (and (smme-wfp smme)
                  (<= (nfix n) (smme-nblocks smme)))
             (<= (smme-block-start n smme) (smme-block-start (smme-nblocks smme) smme)))
    :rule-classes :linear)

  ;; (local
  ;;  (defthm smme-blocks-wfp-implies-block-start-plus-size-lte-last
  ;;   (implies (and (smme-blocks-wfp k smme)
  ;;                 (< (nfix n) (nfix k)))
  ;;            (<= (+ (smme-block-size n smme)
  ;;                   (smme-block-start n smme))
  ;;                (smme-block-start k smme)))
  ;;   :hints(("Goal" :in-theory (enable smme-blocks-wfp)))))

  ;; (local
  ;;  (defthm smme-blocks-wfp-implies-block-start-plus-size-lte-last
  ;;   (implies (and (smme-blocks-wfp k smme)
  ;;                 (< (nfix n) (nfix k)))
  ;;            (<= (+ (smme-block-size n smme)
  ;;                   (smme-block-start n smme))
  ;;                (smme-block-start k smme)))
  ;;   :hints(("Goal" :in-theory (enable smme-blocks-wfp)))))

  ;; (local
  ;;  (defthm smme-blocks-wfp-implies-block-start-plus-size-lte-greater
  ;;   (implies (and (smme-blocks-wfp k smme)
  ;;                 (< (nfix n) (nfix m))
  ;;                 (<= (nfix m) (nfix k)))
  ;;            (<= (+ (smme-block-size n smme)
  ;;                   (smme-block-start n smme))
  ;;                (smme-block-start m smme)))
  ;;   :hints(("Goal" :in-theory (enable smme-blocks-wfp)))))

  ;; (defthm smme-wfp-implies-block-start-plus-size-lte-greater
  ;;   (implies (and (smme-wfp smme)
  ;;                 (< (nfix n) (nfix m))
  ;;                 (<= (nfix m) (smme-nblocks smme)))
  ;;            (<= (+ (smme-block-start n smme)
  ;;                   (smme-block-size n smme))
  ;;                (smme-block-start m smme))))

  ;; (defthm smme-wfp-implies-block-start-plus-size-lte-last
  ;;   (implies (and (smme-wfp smme)
  ;;                 (< (nfix n) (smme-nblocks smme)))
  ;;            (<= (+ (smme-block-start n smme)
  ;;                   (smme-block-size n smme))
  ;;                (smme-block-start (smme-nblocks smme) smme)))
  ;;   :rule-classes :linear)

  (defthm smme-wfp-implies-block-bound-lte-mem-length
    (implies (and (equal (smme-nblocks smme1) (smme-nblocks smme))
                  (smme-wfp smme))
             (<= (smme-block-start (smme-nblocks smme1) smme)
                 (smme-mem-length smme)))
    :rule-classes :linear)

  (defthm smme-block-start-0-when-smme-wfp
    (implies (smme-wfp smme)
             (equal (smme-block-start 0 smme) 0))))


(define smme-block-size ((n natp) smme)
  :guard (and (smme-wfp smme)
              (< n (smme-nblocks smme)))
  :inline t
  (lnfix (- (smme-block-start (+ 1 (lnfix n)) smme)
            (smme-block-start n smme)))
  ///
  (def-updater-independence-thm smme-block-size-updater-independence
    (implies (and (nat-equiv (nth n (nth *smme-blockstartsi* new))
                             (nth n (nth *smme-blockstartsi* old)))
                  (nat-equiv (nth (+ 1 (nfix n)) (nth *smme-blockstartsi* new))
                             (nth (+ 1 (nfix n)) (nth *smme-blockstartsi* old))))
             (equal (smme-block-size n new)
                    (smme-block-size n old))))

  (defthm smme-block-size-linear
    (implies (and (smme-wfp smme)
                  (< (nfix n) (smme-nblocks smme)))
             (= (+ (smme-block-start n smme)
                   (smme-block-size n smme))
                (smme-block-start (+ 1 (nfix n)) smme)))
    :rule-classes ((:linear :trigger-terms ((smme-block-size n smme))))))


(define smme-addr ((n natp) (i natp) smme)
  :guard (and (smme-wfp smme)
              (< n (smme-nblocks smme))
              (< i (smme-block-size n smme)))
  (+ (lnfix i)
     (smme-block-start n smme))
  ///

  ;; (local (defthm smme-blocks-wfp-implies-block-ref-in-bounds
  ;;          (implies (and (smme-blocks-wfp m smme)
  ;;                        (< (nfix n) (nfix m))
  ;;                        (< (nfix i) (smme-block-size n smme)))
  ;;                   (< (smme-addr n i smme) (smme-block-start m smme)))
  ;;          :hints(("Goal" :in-theory (enable smme-blocks-wfp)))
  ;;          :rule-classes :linear))

  (defthm smme-wfp-implies-block-ref-in-bounds
    (implies (and (smme-wfp smme)
                  (< (nfix n) (nfix m))
                  (<= (nfix m) (smme-nblocks smme))
                  (< (nfix i) (smme-block-size n smme)))
             (< (smme-addr n i smme)
                (smme-block-start m smme)))
    :hints (("goal" :use ((:instance smme-wfp-implies-blockstarts-monotonic
                           (n (+ 1 (nfix n)))))
             :in-theory (disable smme-wfp-implies-blockstarts-monotonic)))
    ;; :hints (("goal" :use ((:instance smme-wfp-implies-block-start-plus-size-lte-greater))
    ;;          :in-theory (disable smme-wfp-implies-block-start-plus-size-lte-greater)))
    )

  (defthm smme-wfp-implies-block-ref-in-bounds-linear
    (implies (and (smme-wfp smme)
                  (< (nfix n) (smme-nblocks smme))
                  (< (nfix i) (smme-block-size n smme)))
             (< (smme-addr n i smme)
                (smme-block-start (smme-nblocks smme) smme)))
    :hints(("Goal" :in-theory (enable smme-wfp)))
    :rule-classes ((:linear :trigger-terms ((smme-addr n i smme)))))

  (defthm smme-wfp-implies-different-block-refs-ordered
    (implies (and (smme-wfp smme)
                  (< (nfix n) (nfix m))
                  (<= (nfix m) (smme-nblocks smme))
                  (< (nfix i) (smme-block-size n smme)))
             (< (smme-addr n i smme)
                (smme-addr m j smme)))
    :hints (("goal" :use ((:instance smme-wfp-implies-blockstarts-monotonic
                           (n (+ 1 (nfix n)))))
             :in-theory (disable smme-wfp-implies-blockstarts-monotonic)))
    ;; :hints (("goal" :use ((:instance smme-wfp-implies-block-start-plus-size-lte-greater))
    ;;          :in-theory (disable smme-wfp-implies-block-start-plus-size-lte-greater)))
    )

  (defthm smme-wfp-implies-different-block-refs-differ
    (implies (and (smme-wfp smme)
                  (not (equal (nfix n) (nfix m)))
                  (<= (nfix m) (smme-nblocks smme))
                  (<= (nfix n) (smme-nblocks smme))
                  (< (nfix i) (smme-block-size n smme))
                  (< (nfix j) (smme-block-size m smme)))
             (not (equal (smme-addr n i smme)
                         (smme-addr m j smme))))
    :hints (("goal" :use ((:instance smme-wfp-implies-blockstarts-monotonic
                           (n (+ 1 (nfix n))))
                          (:instance smme-wfp-implies-blockstarts-monotonic
                           (n (+ 1 (nfix m))) (m n)))
             :in-theory (disable smme-wfp-implies-blockstarts-monotonic)
             :cases ((< (nfix m) (nfix n))
                     (< (nfix n) (nfix m))))))

  (defthm smme-addrs-with-different-i
    (implies (not (equal (nfix i1) (nfix i2)))
             (not (equal (smme-addr n i1 smme)
                         (smme-addr n i2 smme)))))

  (def-updater-independence-thm smme-addr-updater-independence
    (implies (nat-equiv (nth n (nth *smme-blockstartsi* new))
                        (nth n (nth *smme-blockstartsi* old)))
             (equal (smme-addr n i new)
                    (smme-addr n i old)))))

;; (defthm smme-blocks-wfp-for-smaller-n
;;   (implies (and (smme-blocks-wfp m smme)
;;                 (<= (nfix n) (nfix m)))
;;            (smme-blocks-wfp n smme)))


;; (defthm smme-wfp-implies-block-refs-differ-1
;;   (implies (and (smme-wfp smme)
;;                 (< (nfix n1) (nfix n2))
;;                 (< (nfix n2) (nfix (smme-nblocks smme)))
;;                 (< (nfix i1) (smme-block-size n1 smme)))
;;            (< (smme-addr n1 i1 smme)
;;               (smme-addr n2 i2 smme)))
;;   :hints(("Goal" :in-theory (disable smme-addr)))
;;   :rule-classes (:rewrite :linear))

;; (defthm smme-wfp-implies-block-refs-differ
;;   (implies (and (smme-wfp smme)
;;                 (< (nfix n1) (nfix (smme-nblocks smme)))
;;                 (< (nfix n2) (nfix (smme-nblocks smme)))
;;                 (not (equal (nfix n1) (nfix n2)))
;;                 (< (nfix i1) (smme-block-size n1 smme))
;;                 (< (nfix i2) (smme-block-size n2 smme)))
;;            (not (equal (smme-addr n1 i1 smme)
;;                        (smme-addr n2 i2 smme))))
;;   :hints (("goal" :use ((:instance smme-wfp-implies-block-refs-differ-1)
;;                         (:instance smme-wfp-implies-block-refs-differ-1
;;                          (n1 n2) (n2 n1) (i1 i2) (i2 i1))))))



;; (defthm smme-wfp-implies-block-refs-differ-in-n-or-i
;;   (implies (and (smme-wfp smme)
;;                 (< (nfix n1) (nfix (smme-nblocks smme)))
;;                 (< (nfix n2) (nfix (smme-nblocks smme)))
;;                 (< (nfix i1) (smme-block-size n1 smme))
;;                 (< (nfix i2) (smme-block-size n2 smme))
;;                 (or (not (equal (nfix n1) (nfix n2)))
;;                     (not (equal (nfix i1) (nfix i2)))))
;;            (not (equal (smme-addr n1 i1 smme)
;;                        (smme-addr n2 i2 smme))))
;;   :hints (("Goal" :cases ((equal (nfix n1) (nfix n2)))
;;            :in-theory (disable smme-addr))))

(define smme-read ((n natp) (i natp) smme)
  :guard (and (smme-wfp smme)
              (< n (smme-nblocks smme))
              (< i (smme-block-size n smme)))
  :inline t
  (smme-memi (smme-addr n i smme) smme)
  ///
  (def-updater-independence-thm smme-read-updater-independence
    (implies (and (nat-equiv (nth n (nth *smme-blockstartsi* new))
                             (nth n (nth *smme-blockstartsi* old)))
                  (equal addr (smme-addr n i old))
                  (nat-equiv (nth addr (nth *smme-memi* new))
                             (nth addr (nth *smme-memi* old))))
             (equal (smme-read n i new)
                    (smme-read n i old)))))

(define smme-write ((n natp)
                    (i natp)
                    (v :type (unsigned-byte 32))
                    smme)
  :guard (and (smme-wfp smme)
              (< n (smme-nblocks smme))
              (< i (smme-block-size n smme))
              (unsigned-byte-p 32 v))
  :split-types t
  :inline t
  (update-smme-memi (smme-addr n i smme) v smme)
  ///
  (fty::deffixequiv smme-write :args ((n natp) (i natp) (v natp)))

  (defthm smme-memi-of-smme-write
    (implies (not (equal (nfix k) (smme-addr n i smme)))
             (equal (nth k (nth *smme-memi* (smme-write n i v smme)))
                    (nth k (nth *smme-memi* smme)))))

  (defthm smme-write-preserves-other-fields
    (implies (not (equal (nfix k) *smme-memi*))
             (equal (nth k (smme-write n i v smme))
                    (nth k smme))))

  (defthm smme-read-of-smme-write
    (equal (smme-read n i (smme-write n i v smme))
           (nfix v))
    :hints(("Goal" :in-theory (enable smme-read))))

  (defthm smme-mem-length-of-smme-write-nondecr
    (<= (smme-mem-length smme) (smme-mem-length (smme-write n i v smme)))
    :rule-classes :linear)

  ;; got it by updater independence...
  ;; (defthm smme-wfp-of-smme-write
  ;;   (implies (smme-wfp smme)
  ;;            (smme-wfp (smme-write n i v smme)))
  ;;   :hints(("Goal" :in-theory (disable smme-write))))
  )

;; (defthm smme-addr-of-update-mem
;;   (equal (smme-addr n i (update-nth *smme-memi* v smme))
;;          (smme-addr n i smme))
;;   :hints(("Goal" :in-theory (enable smme-addr))))


;; (defthmd smme-read-of-smme-write-split
;;   (implies (and (smme-wfp smme)
;;                 (< (nfix nr) (nfix (smme-nblocks smme)))
;;                 (< (nfix ir) (smme-block-size nr smme))
;;                 (< (nfix nw) (nfix (smme-nblocks smme)))
;;                 (< (nfix iw) (smme-block-size nw smme)))
;;            (equal (smme-read nr ir (smme-write nw iw v smme))
;;                   (if (and (equal (nfix nr) (nfix nw))
;;                            (equal (nfix ir) (nfix iw)))
;;                       v
;;                     (smme-read nr ir smme))))
;;   :hints(("Goal" :in-theory (disable smme-wfp)
;;           :cases ((equal (nfix nr) (nfix nw))))))

;; (defthm smme-write-of-smme-write-same
;;   (implies (and (and (equal (nfix n1) (nfix n2))
;;                      (equal (nfix i1) (nfix i2)))
;;                 (< (nfix n1) (nfix (smme-nblocks smme)))
;;                 (< (nfix i1) (smme-block-size n1 smme)))
;;            (equal (smme-write n1 i1 v1 (smme-write n2 i2 v2 smme))
;;                   (smme-write n1 i1 v1 smme))))


;; (defthm smme-write-of-smme-write-diff
;;   (implies (and (smme-wfp smme)
;;                 (< (nfix n1) (nfix (smme-nblocks smme)))
;;                 (< (nfix i1) (smme-block-size n1 smme))
;;                 (< (nfix n2) (nfix (smme-nblocks smme)))
;;                 (< (nfix i2) (smme-block-size n2 smme))
;;                 (or (not (equal (nfix n1) (nfix n2)))
;;                     (not (equal (nfix i1) (nfix i2)))))
;;            (equal (smme-write n1 i1 v1 (smme-write n2 i2 v2 smme))
;;                   (smme-write n2 i2 v2 (smme-write n1 i1 v1 smme))))
;;   :hints (("goal" :cases ((< (smme-addr n1 i1 smme)
;;                              (smme-addr n2 i2 smme))
;;                           (< (smme-addr n2 i2 smme)
;;                              (smme-addr n1 i1 smme)))
;;            :in-theory (disable smme-wfp))
;;           '(:cases ((equal (nfix n1) (nfix n2))))))

;; (defthm smme-read-of-smme-write-same
;;   (implies (and (and (equal (nfix n1) (nfix n2))
;;                      (equal (nfix i1) (nfix i2)))
;;                 (< (nfix n1) (nfix (smme-nblocks smme)))
;;                 (< (nfix i1) (smme-block-size n1 smme)))
;;            (equal (smme-read n1 i1 (smme-write n2 i2 v2 smme))
;;                   v2)))


;; (defthm smme-read-of-smme-write-diff
;;   (implies (and (smme-wfp smme)
;;                 (< (nfix n1) (nfix (smme-nblocks smme)))
;;                 (< (nfix i1) (smme-block-size n1 smme))
;;                 (< (nfix n2) (nfix (smme-nblocks smme)))
;;                 (< (nfix i2) (smme-block-size n2 smme))
;;                 (or (not (equal (nfix n1) (nfix n2)))
;;                     (not (equal (nfix i1) (nfix i2)))))
;;            (equal (smme-read n1 i1 (smme-write n2 i2 v2 smme))
;;                   (smme-read n1 i1 smme)))
;;   :hints (("goal" :cases ((equal (nfix n1) (nfix n2)))
;;            :in-theory (disable smme-wfp))))


;; (defthm smme-blocks-wfp-of-update-memi
;;   (equal (smme-blocks-wfp n (update-nth *smme-memi* v smme))
;;          (smme-blocks-wfp n smme)))

;; (defthm smme-wfp-of-smme-write
;;   (implies (smme-wfp smme)
;;            (smme-wfp (smme-write n i v smme))))


;; (defthm smme-block-size-of-smme-write
;;   (equal (smme-block-size n1 (smme-write n i v smme))
;;          (smme-block-size n1 smme)))

;; (defthm smme-nblocks-of-smme-write
;;   (equal (smme-nblocks (smme-write n i v smme))
;;          (smme-nblocks smme)))


(local (defthm max-linear-1
         (<= a (max a b))
         :rule-classes :linear))

(local (defthm max-linear-2
         (<= b (max a b))
         :rule-classes :linear))


(local (defthm *-2-nfix-linear
         (<= (nfix n) (* 2 (nfix n)))
         :rule-classes :linear))

(defthm nat-listp-resize-list
  (implies (and (nat-listp lst)
                (natp default))
           (nat-listp (resize-list lst n default))))


(defthm u32-listp-resize-list
  (implies (and (u32-listp lst)
                (unsigned-byte-p 32 default))
           (u32-listp (resize-list lst n default))))

;; (define smme-maybe-grow-sizes ((n natp) smme)
;;   :inline t
;;   (if (< (lnfix n) (smme-blocksizes-length smme))
;;       smme
;;     (resize-smme-blocksizes (max 16 (* 2 (lnfix n))) smme))
;;   ///
;;   (defthm blocksize-of-smme-maybe-grow-sizes
;;     (implies (or (< (nfix k) (nfix n))
;;                  (< (nfix k) (smme-blocksizes-length smme)))
;;              (nat-equiv (nth k (nth *smme-blocksizesi* (smme-maybe-grow-sizes n smme)))
;;                         (nth k (nth *smme-blocksizesi* smme)))))

;;   (defthm smme-blocksizes-length-of-smme-maybe-grow-sizes
;;     (< (nfix n) (smme-blocksizes-length (smme-maybe-grow-sizes n smme)))
;;     :rule-classes :linear)

;;   (defthm smme-blocksizes-length-nondecr-of-smme-maybe-grow-sizes
;;     (<= (smme-blocksizes-length smme) (smme-blocksizes-length (smme-maybe-grow-sizes n smme)))
;;     :rule-classes :linear)

;;   (defthm nth-of-smme-maybe-grow-sizes
;;     (implies (not (equal (nfix k) *smme-blocksizesi*))
;;              (equal (nth k (smme-maybe-grow-sizes n smme))
;;                     (nth k smme))))

;;   ;; (defthm smme-wfp-of-smme-maybe-grow-sizes
;;   ;;   (implies (smme-wfp smme)
;;   ;;            (smme-wfp (smme-maybe-grow-sizes n smme)))
;;   ;;   :hints(("Goal" :in-theory (disable smme-maybe-grow-sizes))))
;;   )


(define smme-maybe-grow-starts ((n natp) smme)
  :inline t
  (if (< (lnfix n) (smme-blockstarts-length smme))
      smme
    (resize-smme-blockstarts (max 16 (* 2 (lnfix n))) smme))
  ///
  (defthm blockstart-of-smme-maybe-grow-starts
    (implies (or (< (nfix k) (nfix n))
                 (< (nfix k) (smme-blockstarts-length smme)))
             (nat-equiv (nth k (nth *smme-blockstartsi* (smme-maybe-grow-starts n smme)))
                        (nth k (nth *smme-blockstartsi* smme)))))

  (defthm smme-blockstarts-length-of-smme-maybe-grow-starts
    (< (nfix n) (smme-blockstarts-length (smme-maybe-grow-starts n smme)))
    :rule-classes :linear)

  (defthm smme-blockstarts-length-nondecr-of-smme-maybe-grow-starts
    (<= (smme-blockstarts-length smme) (smme-blockstarts-length (smme-maybe-grow-starts n smme)))
    :rule-classes :linear)

  (defthm nth-of-smme-maybe-grow-starts
    (implies (not (equal (nfix k) *smme-blockstartsi*))
             (equal (nth k (smme-maybe-grow-starts n smme))
                    (nth k smme))))

  ;; (defthm smme-wfp-of-smme-maybe-grow-starts
  ;;   (implies (smme-wfp smme)
  ;;            (smme-wfp (smme-maybe-grow-starts n smme)))
  ;;   :hints(("Goal" :in-theory (disable smme-maybe-grow-starts))))

  )

(define smme-maybe-grow-mem ((n natp) smme)
  :inline t
  (if (< (lnfix n) (smme-mem-length smme))
      smme
    (resize-smme-mem (max 16 (* 2 (lnfix n))) smme))
  ///
  (defthm blockstart-of-smme-maybe-grow-mem
    (implies (or (< (nfix k) (nfix n))
                 (< (nfix k) (smme-mem-length smme)))
             (nat-equiv (nth k (nth *smme-memi* (smme-maybe-grow-mem n smme)))
                        (nth k (nth *smme-memi* smme)))))

  (defthm smme-mem-length-of-smme-maybe-grow-mem
    (< (nfix n) (smme-mem-length (smme-maybe-grow-mem n smme)))
    :rule-classes :linear)

  (defthm smme-mem-length-nondecr-of-smme-maybe-grow-mem
    (<= (smme-mem-length smme) (smme-mem-length (smme-maybe-grow-mem n smme)))
    :rule-classes :linear)

  (defthm nth-of-smme-maybe-grow-mem
    (implies (not (equal (nfix k) *smme-memi*))
             (equal (nth k (smme-maybe-grow-mem n smme))
                    (nth k smme))))

  ;; (defthm smme-wfp-of-smme-maybe-grow-mem
  ;;   (implies (smme-wfp smme)
  ;;            (smme-wfp (smme-maybe-grow-mem n smme)))
  ;;   :hints(("Goal" :in-theory (disable smme-maybe-grow-mem))))
  )



;; (defthm blocksize-of-smme-maybe-grow-sizes
;;   (equal (nfix (nth m (nth *smme-blocksizesi* (smme-maybe-grow-sizes n smme))))
;;          (nfix (nth m (nth *smme-blocksizesi* smme))))
;;   :hints(("Goal" :in-theory (enable nth-of-resize-list-split))))

;; (defthm len-sizes-of-smme-maybe-grow-sizes
;;   (< (nfix n)
;;      (len (nth *smme-blocksizesi* (smme-maybe-grow-sizes n smme))))
;;   :rule-classes :linear)

;; (defthm nth-of-smme-maybe-grow-sizes
;;   (implies (not (equal i *smme-blocksizesi*))
;;            (equal (nth i (smme-maybe-grow-sizes n smme))
;;                   (nth i smme))))

;; (defthm smme-blocks-wfp-of-smme-maybe-grow-sizes
;;   (equal (smme-blocks-wfp m (smme-maybe-grow-sizes n smme))
;;          (smme-blocks-wfp m smme))
;;   :hints (("goal" :induct (smme-blocks-wfp m smme)
;;            :in-theory (disable smme-maybe-grow-sizes))))

;; (defthm true-listp-smme-maybe-grow-sizes
;;   (implies (true-listp smme)
;;            (true-listp (smme-maybe-grow-sizes n smme)))
;;   :hints(("Goal" :in-theory (enable smme-maybe-grow-sizes))))

;; (defthm len-of-smme-maybe-grow-sizes
;;   (implies (equal (len smme) 4)
;;            (equal (len (smme-maybe-grow-sizes sz smme)) 4))
;;   :hints(("Goal" :in-theory (enable smme-maybe-grow-sizes))))

;; (defthm len-sizes-of-smme-maybe-grow-sizes-linear1
;;   (< (nfix n)
;;      (len (nth *smme-blocksizesi*
;;                (smme-maybe-grow-sizes n smme))))
;;   :hints(("Goal" :in-theory (enable smme-maybe-grow-sizes)))
;;   :rule-classes :linear)

;; (defthm len-sizes-of-smme-maybe-grow-sizes-linear2
;;   (<= (len (nth *smme-blocksizesi* smme))
;;       (len (nth *smme-blocksizesi*
;;                 (smme-maybe-grow-sizes n smme))))
;;   :hints(("Goal" :in-theory (enable smme-maybe-grow-sizes)))
;;   :rule-classes :linear)

;; (defthm nat-listp-sizes-of-smme-maybe-grow-sizes
;;   (implies (nat-listp (nth *smme-blocksizesi* smme))
;;            (nat-listp (nth *smme-blocksizesi*
;;                            (smme-maybe-grow-sizes n smme))))
;;   :hints(("Goal" :in-theory (enable smme-maybe-grow-sizes))))

;; (definline smme-maybe-grow-starts (n smme)
;;   (declare (xargs :stobjs smme
;;                   :guard (natp n)))
;;   (if (< (lnfix n) (smme-blockstarts-length smme))
;;       smme
;;     (resize-smme-blockstarts (max 16 (* 2 (lnfix n))) smme)))

;; (defthm blockstart-of-smme-maybe-grow-starts
;;   (equal (nfix (nth m (nth *smme-blockstartsi* (smme-maybe-grow-starts n smme))))
;;          (nfix (nth m (nth *smme-blockstartsi* smme))))
;;   :hints(("Goal" :in-theory (enable nth-of-resize-list-split))))

;; (defthm len-starts-of-smme-maybe-grow-starts
;;   (< (nfix n)
;;      (len (nth *smme-blockstartsi* (smme-maybe-grow-starts n smme))))
;;   :rule-classes :linear)

;; (defthm nth-of-smme-maybe-grow-starts
;;   (implies (not (equal i *smme-blockstartsi*))
;;            (equal (nth i (smme-maybe-grow-starts n smme))
;;                   (nth i smme))))

;; (defthm smme-blocks-wfp-of-smme-maybe-grow-starts
;;   (equal (smme-blocks-wfp m (smme-maybe-grow-starts n smme))
;;          (smme-blocks-wfp m smme))
;;   :hints (("goal" :induct (smme-blocks-wfp m smme)
;;            :in-theory (disable smme-maybe-grow-starts))))

;; (defthm true-listp-smme-maybe-grow-starts
;;   (implies (true-listp smme)
;;            (true-listp (smme-maybe-grow-starts n smme)))
;;   :hints(("Goal" :in-theory (enable smme-maybe-grow-starts))))

;; (defthm len-of-smme-maybe-grow-starts
;;   (implies (equal (len smme) 4)
;;            (equal (len (smme-maybe-grow-starts sz smme)) 4))
;;   :hints(("Goal" :in-theory (enable smme-maybe-grow-starts))))

;; (defthm len-starts-of-smme-maybe-grow-starts-linear1
;;   (< (nfix n)
;;      (len (nth *smme-blockstartsi*
;;                (smme-maybe-grow-starts n smme))))
;;   :hints(("Goal" :in-theory (enable smme-maybe-grow-starts)))
;;   :rule-classes :linear)

;; (defthm len-starts-of-smme-maybe-grow-starts-linear2
;;   (<= (len (nth *smme-blockstartsi* smme))
;;       (len (nth *smme-blockstartsi*
;;                 (smme-maybe-grow-starts n smme))))
;;   :hints(("Goal" :in-theory (enable smme-maybe-grow-starts)))
;;   :rule-classes :linear)

;; (defthm nat-listp-starts-of-smme-maybe-grow-starts
;;   (implies (nat-listp (nth *smme-blockstartsi* smme))
;;            (nat-listp (nth *smme-blockstartsi*
;;                            (smme-maybe-grow-starts n smme))))
;;   :hints(("Goal" :in-theory (enable smme-maybe-grow-starts))))


;; (definline smme-maybe-grow-mem (n smme)
;;   (declare (xargs :stobjs smme
;;                   :guard (natp n)))
;;   (if (< (lnfix n) (smme-mem-length smme))
;;       smme
;;     (resize-smme-mem (max 16 (* 2 (lnfix n))) smme)))


;; (defthm memi-of-smme-maybe-grow-mem
;;   (implies (< (nfix m) (len (nth *smme-memi* smme)))
;;            (equal (nth m (nth *smme-memi* (smme-maybe-grow-mem n smme)))
;;                   (nth m (nth *smme-memi* smme)))))

;; (defthm len-mem-of-smme-maybe-grow-mem
;;   (< (nfix n)
;;      (len (nth *smme-memi* (smme-maybe-grow-mem n smme))))
;;   :rule-classes :linear)

;; (defthm nth-of-smme-maybe-grow-mem
;;   (implies (not (equal i *smme-memi*))
;;            (equal (nth i (smme-maybe-grow-mem n smme))
;;                   (nth i smme))))

;; (defthm smme-blocks-wfp-of-smme-maybe-grow-mem
;;   (equal (smme-blocks-wfp m (smme-maybe-grow-mem n smme))
;;          (smme-blocks-wfp m smme))
;;   :hints (("goal" :induct (smme-blocks-wfp m smme)
;;            :in-theory (disable smme-maybe-grow-mem))))

;; (defthm true-listp-smme-maybe-grow-mem
;;   (implies (true-listp smme)
;;            (true-listp (smme-maybe-grow-mem n smme)))
;;   :hints(("Goal" :in-theory (enable smme-maybe-grow-mem))))

;; (defthm len-of-smme-maybe-grow-mem
;;   (implies (equal (len smme) 4)
;;            (equal (len (smme-maybe-grow-mem sz smme)) 4))
;;   :hints(("Goal" :in-theory (enable smme-maybe-grow-mem))))

;; (defthm len-mem-of-smme-maybe-grow-mem-linear1
;;   (< (nfix n)
;;      (len (nth *smme-memi*
;;                (smme-maybe-grow-mem n smme))))
;;   :hints(("Goal" :in-theory (enable smme-maybe-grow-mem)))
;;   :rule-classes :linear)

;; (defthm len-mem-of-smme-maybe-grow-mem-linear2
;;   (<= (len (nth *smme-memi* smme))
;;       (len (nth *smme-memi*
;;                 (smme-maybe-grow-mem n smme))))
;;   :hints(("Goal" :in-theory (enable smme-maybe-grow-mem)))
;;   :rule-classes :linear)

;; (defthm u32-listp-mem-of-smme-maybe-grow-mem
;;   (implies (u32-listp (nth *smme-memi* smme))
;;            (u32-listp (nth *smme-memi*
;;                           (smme-maybe-grow-mem n smme))))
;;   :hints(("Goal" :in-theory (enable smme-maybe-grow-mem))))



;; (in-theory (disable smme-maybe-grow-sizes
;;                     smme-maybe-grow-starts
;;                     smme-maybe-grow-mem))

(define smme-mem-clear ((n natp) (max natp) (val :type (unsigned-byte 32)) smme)
  :guard (and (<= n max)
              (<= max (smme-mem-length smme))
              (unsigned-byte-p 32 val))
  :split-types t
  :measure (nfix (- (nfix max) (nfix n)))
  (if (mbe :logic (zp (- (nfix max) (nfix n)))
           :exec (int= max n))
      smme
    (let ((smme (update-smme-memi n val smme)))
      (smme-mem-clear (+ 1 (lnfix n)) max val smme)))
  ///

  (defthm nth-of-smme-mem-clear
    (implies (not (equal m *smme-memi*))
             (equal (nth m (smme-mem-clear n max val smme))
                    (nth m smme))))

  (defthm memi-preserved-of-smme-mem-clear
    (implies (not (and (<= (nfix n) (nfix m))
                       (< (nfix m) (nfix max))))
             (equal (nth m (nth *smme-memi* (smme-mem-clear n max val smme)))
                    (nth m (nth *smme-memi* smme)))))

  (defthm smme-memi-of-smme-mem-clear
    (equal (smme-memi m (smme-mem-clear n max val smme))
           (if (and (<= (nfix n) (nfix m))
                    (< (nfix m) (nfix max)))
               (nfix val)
             (smme-memi m smme))))

  (defthm smme-mem-length-of-smme-mem-clear
    (<= (smme-mem-length smme) (smme-mem-length (smme-mem-clear n max val smme)))
    :rule-classes :linear)

  ;; (defthm smme-wfp-of-smme-mem-clear
  ;;   (implies (smme-wfp smme)
  ;;            (smme-wfp (smme-mem-clear n max val smme)))
  ;;   :hints(("Goal" :in-theory (disable smme-mem-clear))))
  )

;; (defthm smme-blocks-wfp-of-smme-mem-clear
;;   (equal (smme-blocks-wfp m (smme-mem-clear n max val smme))
;;          (smme-blocks-wfp m smme)))

;; (defthm mem-length-of-smme-mem-clear
;;   (implies (<= (nfix max) (len (nth *smme-memi* smme)))
;;            (equal (len (nth *smme-memi* (smme-mem-clear n max val smme)))
;;                   (len (nth *smme-memi* smme)))))

;; (defthm true-listp-smme-mem-clear
;;   (implies (true-listp smme)
;;            (true-listp (smme-mem-clear n max val smme))))

;; (defthm len-of-smme-mem-clear
;;   (implies (equal (len smme) 4)
;;            (equal (len (smme-mem-clear n max val smme)) 4)))

(local (defthm u32-listp-update-nth
         (implies (and (unsigned-byte-p 32 v)
                       (< (nfix n) (len x))
                       (u32-listp x))
                  (u32-listp (update-nth n v x)))
         :hints(("Goal" :in-theory (enable update-nth)))))

;; (defthm u32-listp-of-smme-mem-clear
;;   (implies (and (u32-listp (nth *smme-memi* smme))
;;                 (<= (nfix max) (len (nth *smme-memi* smme)))
;;                 (unsigned-byte-p 32 val))
;;            (u32-listp (nth *smme-memi* (smme-mem-clear n max val smme)))))

;; (defthm smme-wfp-implies-smme-sizes-okp
;;   (implies (smme-wfp smme)
;;            (smme-sizes-okp smme)))

(define smme-addblock ((sz natp) smme)
  :guard (smme-wfp smme)
  :returns (new-smme)
  (b* ((n (smme-nblocks smme))
       (nstart (smme-block-start n smme))
       ;; (smme (smme-maybe-grow-sizes n smme))
       (smme (smme-maybe-grow-starts (+ 1 n) smme))
       (sz   (lnfix sz))
       (nextfree (+ sz nstart))
       (smme (smme-maybe-grow-mem nextfree smme))
       (smme (update-smme-nblocks (+ 1 n) smme))
       (smme (update-smme-block-start (+ 1 n) nextfree smme))
       ;; (smme (update-smme-block-size n sz smme))
       (smme (smme-mem-clear nstart nextfree 0 smme)))
    smme)
  ///
  (defret smme-wfp-of-smme-addblock
    (implies (smme-wfp smme)
             (smme-wfp new-smme))
    :hints(("Goal" :in-theory (e/d (smme-wfp)
                                   (smme-wfp-updater-independence))
            :expand ((:free (smme2) (smme-blocks-wfp (+ 1 (smme-nblocks smme)) smme2))))))

  (defret nth-block-start-preserved-of-smme-addblock
    (implies (<= (nfix n) (smme-nblocks smme))
             (nat-equiv (nth n (nth *smme-blockstartsi* new-smme))
                        (nth n (nth *smme-blockstartsi* smme)))))

  ;; (defret nth-block-size-preserved-of-smme-addblock
  ;;   (implies (< (nfix n) (smme-nblocks smme))
  ;;            (nat-equiv (nth n (nth *smme-blocksizesi* new-smme))
  ;;                       (nth n (nth *smme-blocksizesi* smme)))))

  (defret nth-mem-preserved-of-smme-addblock
    (implies (< (nfix n) (smme-block-start (smme-nblocks smme) smme))
             (nat-equiv (nth n (nth *smme-memi* new-smme))
                        (nth n (nth *smme-memi* smme)))))

  (defret new-block-start-of-smme-addblock
    (implies (equal (smme-nblocks smme1) (smme-nblocks smme))
             (equal (smme-block-start (+ 1 (smme-nblocks smme1)) new-smme)
                    (+ (nfix sz) (smme-block-start (smme-nblocks smme) smme)))))

  (defret new-block-size-of-smme-addblock
    (implies (equal (smme-nblocks smme1) (smme-nblocks smme))
             (equal (smme-block-size (smme-nblocks smme1) new-smme)
                    (nfix sz)))
    :hints(("Goal" :in-theory (enable smme-block-size))))

  (defret new-mem-of-smme-addblock
    (implies (and (<= (smme-block-start (smme-nblocks smme) smme) (nfix n))
                  (< (nfix n) (+ (nfix sz) (smme-block-start (smme-nblocks smme) smme))))
             (equal (smme-memi n new-smme) 0)))

  (defret smme-nblocks-of-smme-addblock
    (equal (smme-nblocks new-smme) (+ 1 (smme-nblocks smme))))

  (defret new-addr-of-smme-addblock
    (implies (equal (smme-nblocks smme1) (smme-nblocks smme))
             (equal (smme-addr (smme-nblocks smme1) i new-smme)
                    (+ (nfix i) (smme-block-start (smme-nblocks smme) smme))))
    :hints(("Goal" :in-theory (enable smme-addr))))

;; (defthm smme-addr-of-smme-addblock
;;   (implies (and (smme-wfp smme)
;;                 (< (nfix n) (nfix (smme-nblocks smme))))
;;            (equal (smme-addr n i (smme-addblock sz smme))
;;                   (smme-addr n i smme)))
;;   :hints(("Goal" :in-theory (enable smme-addr))))

;; (defthm memi-of-smme-addblock
;;   (implies (and (< (nfix n) (smme-block-start (smme-nblocks smme) smme))
;;                 (<= (smme-block-start (smme-nblocks smme) smme)
;;                     (len (nth *smme-memi* smme))))
;;            (equal (nth n (nth *smme-memi* (smme-addblock sz smme)))
;;                   (nth n (nth *smme-memi* smme)))))

;; (defthm smme-read-of-smme-addblock
;;   (implies (and (smme-wfp smme)
;;                 (< (nfix n) (nfix (smme-nblocks smme)))
;;                 (< (nfix i) (smme-block-size n smme)))
;;            (equal (smme-read n i (smme-addblock sz smme))
;;                   (smme-read n i smme)))
;;   :hints(("Goal" :in-theory (disable smme-addr smme-addblock))))


  (defret smme-read-new-of-smme-addblock
    (implies (and (equal (smme-nblocks smme1) (smme-nblocks smme))
                  ;; (smme-wfp smme)
                  (< (nfix i) (nfix sz)))
             (equal (smme-read (smme-nblocks smme1) i new-smme)
                    0))
    :hints(("Goal" :in-theory (enable smme-read smme-addr)))))

;; (defthm smme-nblocks-of-smme-addblock
;;   (equal (smme-nblocks (smme-addblock sz smme))
;;          (+ 1 (nfix (smme-nblocks smme)))))

;; (defthm smme-block-size-of-smme-addblock-preserved
;;   (implies (< (nfix n) (nfix (smme-nblocks smme)))
;;            (equal (smme-block-size n (smme-addblock sz smme))
;;                   (smme-block-size n smme))))

;; (defthm smme-block-size-of-smme-addblock-new
;;   (equal (smme-block-size (nth *smme-nblocks* smme) (smme-addblock sz smme))
;;          (nfix sz)))

;; (defthm true-listp-smme-addblock
;;   (implies (true-listp smme)
;;            (true-listp (smme-addblock sz smme))))

;; (defthm len-smme-addblock
;;   (implies (equal (len smme) 4)
;;            (equal (len (smme-addblock sz smme)) 4)))


;; (local (defthm nat-listp-update-nth
;;          (implies (and (natp v)
;;                        (< (nfix n) (len x))
;;                        (nat-listp x))
;;                   (nat-listp (update-nth n v x)))
;;          :hints(("Goal" :in-theory (enable update-nth)))))




(define smme-rewind ((n natp) smme)
  :guard (<= n (smme-nblocks smme))
  :returns (new-smme)
  :inline t
  (update-smme-nblocks (lnfix n) smme)
  ///
  (local (defthm smme-blocks-wfp-of-reduce-nblocks
           (implies (and ;; (smme-blocks-wfp n smme1)
                         (smme-blocks-wfp n smme)
                         (<= (nfix m) (nfix n)))
                    (smme-blocks-wfp m smme))
           :hints(("Goal" :in-theory (enable smme-blocks-wfp)))))

  (defret smme-wfp-of-smme-rewind
    (implies (and (smme-wfp smme)
                  (<= (nfix n) (smme-nblocks smme)))
             (smme-wfp new-smme))
    :hints(("Goal" :in-theory (enable smme-wfp))))

  (defret nth-of-smme-rewind
    (implies (not (equal (nfix k) *smme-nblocks*))
             (equal (nth k new-smme)
                    (nth k smme))))

  (defret smme-nblocks-of-smme-rewind
    (equal (smme-nblocks new-smme) (nfix n))))


(define smme-resize-last ((sz natp) smme)
  :guard (and (< 0 (smme-nblocks smme))
              (smme-wfp smme))
  :returns (new-smme)
  (b* ((nblocks (smme-nblocks smme))
       (last (1- nblocks))
       (start (smme-block-start last smme))
       (old-end (smme-block-start nblocks smme))
       (sz (lnfix sz))
       (new-end (+ start sz))
       ;; (smme (update-smme-block-size n sz smme))
       (smme (update-smme-block-start (smme-nblocks smme) new-end smme))
       ((when (<= new-end old-end))
        smme)
       (smme (smme-maybe-grow-mem new-end smme)))
    (smme-mem-clear old-end new-end 0 smme))
  ///
  (defret smme-wfp-of-smme-resize-last
    (implies (and (smme-wfp smme)
                  (< 0 (smme-nblocks smme)))
             (smme-wfp new-smme))
    :hints(("Goal" :in-theory (enable smme-wfp ;; smme-sizes-okp
                                      )
            :expand ((:free (smme1) (smme-blocks-wfp (smme-nblocks smme) smme1))))))

  (defret nblocks-preserved-of-smme-resize-last
    (equal (nth *smme-nblocks* new-smme)
           (nth *smme-nblocks* smme)))


  (defret nth-block-start-preserved-of-smme-resize-last
    (implies (< (nfix n) (smme-nblocks smme))
             (nat-equiv (nth n (nth *smme-blockstartsi* new-smme))
                        (nth n (nth *smme-blockstartsi* smme)))))

  (defret nth-mem-preserved-of-smme-resize-last
    (implies (and (< (nfix n) (smme-block-start (smme-nblocks smme) smme))
                  (< 0 (smme-nblocks smme)))
             (nat-equiv (nth n (nth *smme-memi* new-smme))
                        (nth n (nth *smme-memi* smme)))))

  (defret new-block-start-of-smme-resize-last
    (implies (equal (smme-nblocks smme1) (smme-nblocks smme))
             (equal (smme-block-start (smme-nblocks smme1) new-smme)
                    (+ (nfix sz) (smme-block-start (+ -1 (smme-nblocks smme)) smme)))))

  (defret new-block-size-of-smme-resize-last
    (implies (and (equal (smme-nblocks smme1) (smme-nblocks smme))
                  (< 0 (smme-nblocks smme)))
             (equal (smme-block-size (+ -1 (smme-nblocks smme1)) new-smme)
                    (nfix sz)))
    :hints(("Goal" :in-theory (enable smme-block-size))))

  (defret new-mem-of-smme-resize-last
    (implies (and (<= (smme-block-start (smme-nblocks smme) smme) (nfix n))
                  (< (nfix n) (+ (nfix sz) (smme-block-start (+ -1 (smme-nblocks smme)) smme)))
                  (< 0 (smme-nblocks smme)))
             (equal (smme-memi n new-smme) 0)))

  )


(define smme-clear (smme)
  :inline t
  (b* ((smme (update-smme-nblocks 0 smme))
       (smme (smme-maybe-grow-starts 1 smme)))
    (update-smme-block-start 0 0 smme))
  ///

  (defthm smme-wfp-of-smme-clear
    (smme-wfp (smme-clear smme))
    :hints(("Goal" :in-theory (enable smme-wfp smme-blocks-wfp))))

  (defthm nblocks-of-smme-clear
    (equal (smme-nblocks (smme-clear smme)) 0)))

(define smme-max-index (smme)
  :guard (smme-wfp smme)
  :enabled t
  :inline t
  (smme-block-start (smme-nblocks smme) smme))



(defmacro def-unguarded (name formals &rest decl-body)
  (let ((name-nx (intern-in-package-of-symbol
                  (concatenate 'string (symbol-name name) "-NX")
                  name))
        (decls (butlast decl-body 1))
        (body (car (last decl-body))))
    `(progn (defun ,name-nx ,formals
              (declare (xargs :verify-guards nil))
              . ,decl-body)
            (defun ,name ,formals
              (declare (xargs :guard t))
              ,@decls
              (mbe :logic ,body
                   :exec (ec-call (,name-nx . ,formals)))))))

(def-unguarded smml-nblocks (smm)
  (len smm))

(def-unguarded smml-block-size (n smm)
  (declare (xargs :guard (and (natp n)
                              (< n (smml-nblocks smm)))))
  (len (nth n smm)))

(def-unguarded smml-read (n i smm)
  (declare (xargs :guard (and (natp n)
                              (natp i)
                              (< n (smml-nblocks smm))
                              (< i (smml-block-size n smm)))))
  (nfix (nth i (nth n smm))))

(def-unguarded smml-write (n i v smm)
  (declare (xargs :guard (and (natp n)
                              (natp i)
                              (< n (smml-nblocks smm))
                              (< i (smml-block-size n smm))
                              (unsigned-byte-p 32 v))))
  (update-nth n (update-nth i (nfix v) (nth n smm)) smm))

(def-unguarded smml-addblock (sz smm)
  (declare (xargs :guard (natp sz)))
  (append smm (list (make-list sz :initial-element 0))))

(def-unguarded smml-rewind (n smm)
  (declare (xargs :guard (and (natp n)
                              (<= n (smml-nblocks smm)))))
  (take n smm))

(def-unguarded smml-resize-last (sz smm)
  (declare (xargs :guard (and (natp sz)
                              (< 0 (smml-nblocks smm)))))
  (b* ((n (1- (len smm))))
    (update-nth n
                (resize-list (nth n smm) sz 0)
                smm)))

(def-unguarded smml-clear (smm)
  (declare (ignorable smm))
  nil)

(defmacro def-unguarded-rec (name formals &rest decl-body)
  (let ((name-nx (intern-in-package-of-symbol
                  (concatenate 'string (symbol-name name) "-NX")
                  name))
        (decls (butlast decl-body 1))
        (body (car (last decl-body))))
    `(progn (defun ,name-nx ,formals
              (declare (xargs :verify-guards nil))
              ,@decls
              ,(subst name-nx name body))
            (defun ,name ,formals
              (declare (xargs :guard t
                              :verify-guards nil))
              ,@decls
              (mbe :logic ,body
                   :exec (ec-call (,name-nx . ,formals))))
            (encapsulate nil
              (local (defthm def-unguarded-identity
                       (equal (,name-nx . ,formals)
                              (,name . ,formals))
                       :hints (("goal" :in-theory
                                '((:induction ,name-nx)
                                  ,name ,name-nx)))))
              (verify-guards ,name)))))

(def-unguarded-rec smml-block-start (n smm)
  (declare (xargs :guard (and (natp n)
                              (<= n (smml-nblocks smm)))))
  (if (or (atom smm)
          (zp n))
      0
    (+ (len (car smm))
       (smml-block-start (1- n) (cdr smm)))))


(def-unguarded smml-max-index (smm)
  (smml-block-start (smml-nblocks smm) smm))

(def-unguarded-rec smml-fast-read (a smm)
  (declare (xargs :measure (len smm)
                  :guard (and (natp a)
                              (< a (smml-max-index smm)))))
  (if (atom smm)
      0
    (if (< (nfix a) (len (car smm)))
        (nfix (nth a (car smm)))
      (smml-fast-read (- (nfix a) (len (car smm)))
                     (cdr smm)))))


(defcong nat-equiv equal (smml-fast-read a smm) 1)

(defthm smml-read-in-terms-of-fast-read
  (implies (< (nfix i) (len (nth n smm)))
           (equal (smml-read n i smm)
                  (smml-fast-read (+ (smml-block-start n smm) (nfix i)) smm)))
    :hints(("Goal" :induct t
            :in-theory (enable nth))))


(def-unguarded-rec smml-fast-write (a v smm)
  (declare (xargs :measure (len smm)
                  :guard (and (natp a)
                              (< a (smml-max-index smm))
                              (unsigned-byte-p 32 v))))
  (if (atom smm)
      nil
    (if (< (nfix a) (len (car smm)))
        (cons (update-nth a (nfix v) (car smm)) (cdr smm))
      (cons (car smm)
            (smml-fast-write (- (nfix a) (len (car smm))) v
                            (cdr smm))))))

(defcong nat-equiv equal (smml-fast-write a v smm) 1)

(defthm smml-write-in-terms-of-fast-write
  (implies (< (nfix i) (len (nth n smm)))
           (equal (smml-write n i v smm)
                  (smml-fast-write (+ (smml-block-start n smm) (nfix i)) v smm)))
  :hints(("Goal" :in-theory (enable nth update-nth)
          :induct t)))

(defun u32-list-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (u32-listp (car x))
         (u32-list-listp (cdr x)))))

(defthm u32-listp-nth-of-u32-list-listp
  (implies (u32-list-listp x)
           (u32-listp (nth n x)))
  :hints(("Goal" :in-theory (enable nth))))

(defun smmlp (smm)
  (declare (xargs :guard t))
  (u32-list-listp smm))

(defun smml-create ()
  (declare (xargs :guard t))
  nil)

(defthm u32-list-listp-update-nth
  (implies (and (u32-listp v)
                (u32-list-listp x))
           (u32-list-listp (update-nth n v x)))
  :hints(("Goal" :in-theory (enable update-nth))))

(defthm u32-list-listp-append
  (implies (and (u32-list-listp x)
                (u32-list-listp y))
           (u32-list-listp (append x y))))

(defthm true-list-listp-update-nth
  (implies (and (true-listp v)
                (true-list-listp x))
           (true-list-listp (update-nth n v x)))
  :hints(("Goal" :in-theory (enable update-nth))))

(defthm true-listp-nth-when-true-list-listp
  (implies (true-list-listp x)
           (true-listp (nth n x)))
  :hints(("Goal" :in-theory (enable nth))))




(defthm true-list-listp-append
  (implies (and (true-list-listp x)
                (true-list-listp y))
           (true-list-listp (append x y))))



;; (defun-sk smml-smme-blocksizes-ok (smm smme)
;;   (forall n
;;           (implies (< (nfix n) (len smm))
;;                    (equal (nfix (nth n (nth *smme-blocksizesi* smme)))
;;                           (len (nth n smm)))))
;;   :rewrite :direct)

;; (defthm smml-smme-blocksizes-ok-necc2
;;   (implies (and (smml-smme-blocksizes-ok smm smme)
;;                 (< (nfix n) (len smm))
;;                 (natp (nth n (nth *smme-blocksizesi* smme))))
;;            (equal (nth n (nth *smme-blocksizesi* smme))
;;                   (len (nth n smm))))
;;   :hints (("goal" :use smml-smme-blocksizes-ok-necc
;;            :in-theory (disable smml-smme-blocksizes-ok-necc
;;                                smml-smme-blocksizes-ok))))

(defun-sk smml-smme-blocksizes-ok (smm smme)
  (forall n
          (implies (< (nfix n) (len smm))
                   (equal (len (nth n smm))
                          (smme-block-size n smme))))
  :rewrite :direct)

(in-theory (disable smml-smme-blocksizes-ok))

(defun-sk smml-smme-reads-ok (smm smme)
  (forall (a)
          (implies (< (nfix a) (smml-block-start (len smm) smm))
                   (equal (smml-fast-read a smm)
                          (smme-memi a smme))))
  :rewrite :direct)

(defcong nat-equiv equal (smml-block-start n smm) 1)

(local (defthm smml-block-start-of-list-fix
         (equal (smml-block-start n (list-fix smm))
                (smml-block-start n smm))
         :hints(("Goal" :in-theory (enable smml-block-start list-fix)))))

(defcong list-equiv equal (smml-block-start n smm) 2
  :hints (("goal" :use ((:instance smml-block-start-of-list-fix)
                        (:instance smml-block-start-of-list-fix (smm smm-equiv)))
           :in-theory (e/d (list-equiv)
                           (smml-block-start-of-list-fix)))))

;; (defthm smme-blocks-wfp-block-start-bound
;;   (implies (and (smme-blocks-wfp n smme)
;;                 (< (nfix m) (nfix n)))
;;            (equal (+ (nfix (nth m (nth *smme-blockstartsi* smme)))
;;                      (nfix (nth m (nth *smme-blocksizesi* smme))))
;;                   (nfix (nth (+ 1 (nfix m)) (nth *smme-blockstartsi* smme)))))
;;   :hints (("goal" :induct (smme-blocks-wfp n smme))))



(defthm smml-block-start-lemma
  (implies (and (natp n) (natp m))
           (equal (smml-block-start (+ n m) smm)
                  (+ (smml-block-start n smm)
                     (smml-block-start m (nthcdr n smm)))))
  :hints (("goal" :induct (smml-block-start n smm))))

(defun smml-block-start-alt-ind (n smm)
  (if (zp n)
      smm
    (smml-block-start-alt-ind (1- n) smm)))

(local (defthm nthcdr-of-nil
         (equal (nthcdr n nil) nil)
         :hints(("Goal" :in-theory (enable nthcdr)))))
(local (defthm consp-nthcdr
         (iff (consp (nthcdr n x))
              (< (nfix n) (len x)))
         :hints(("Goal" :in-theory (enable nthcdr)))))
(local (defthm car-nthcdr
         (equal (car (nthcdr n x))
                (nth n x))
         :hints(("Goal" :in-theory (enable nthcdr nth)))))

(defthm smml-block-start-alt
  (equal (smml-block-start n smm)
         (if (zp n)
             0
           (+ (smml-block-size (1- n) smm)
              (smml-block-start (1- n) smm))))
  :hints (("goal" :use ((:instance smml-block-start-lemma
                         (n (1- n)) (m 1)))
           :in-theory (e/d ()
                           (smml-block-start-lemma))
           :expand ((:free (smm) (smml-block-start 1 smm)))
           :do-not-induct t))
  :rule-classes
  ((:definition :controller-alist ((smml-block-start t nil)))))



;; (defthm smml-block-start-when-smme-wfp
;;   (implies (and (smme-wfp smme)
;;                 ;; (equal (smme-block-start 0 smme) 0)
;;                 (equal (len smm) (smme-nblocks smme))
;;                 (smml-smme-blocksizes-ok smm smme)
;;                 (<= (nfix m) (smme-nblocks smme)))
;;            (equal (smml-block-start m smm)
;;                   (smme-block-start m smme)))
;;   :hints (("goal" :induct (smml-block-start-alt-ind m smm)
;;            :in-theory (e/d () ;; smml-smme-blocksizes-ok
;;                            (smml-block-start)
;;                            ;; smme-blocks-wfp-block-start-bound
;;                            )
;;            ;; '(:use ((:instance smme-blocks-wfp-block-start-bound
;;            ;;          (m (+ -1 m)))))
;;            )))

(local (defthm smml-block-start-when-smme-wfp
         (implies (and (smml-smme-blocksizes-ok smm smme)
                       (smme-wfp smme)
                       (equal (len smm) (smme-nblocks smme))
                       (<= (nfix m) (nfix (smme-nblocks smme))))
                  (equal (smml-block-start m smm)
                         (smme-block-start m smme)))
         :hints (("goal" :induct (smml-block-start-alt-ind m smm)
                  :in-theory (disable smml-block-start)))))


(defthm smml-fast-read-when-smme-wfp
  (implies (and (smml-smme-blocksizes-ok smm smme)
                (smml-smme-reads-ok smm smme)
                (smme-wfp smme)
                (equal (len smm) (smme-nblocks smme))
                (< (nfix a) (smme-block-start (smme-nblocks smme) smme)))
           (equal (smml-fast-read a smm)
                  (smme-memi a smme)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d ()
                           (smml-smme-blocksizes-ok
                            smml-smme-blocksizes-ok-necc
                            smml-smme-reads-ok
                            smme-blocks-wfp
                            smml-block-start
                            smml-block-start-alt)))))

(encapsulate nil
  (local (defun ind (a1 a2 smm)
           (if (atom smm)
               (list a1 a2)
             (ind (- (nfix a1) (len (car smm)))
                  (- (nfix a2) (len (car smm)))
                  (cdr smm)))))

  (defthm smml-fast-read-of-smml-fast-write-split
    (equal (smml-fast-read a1 (smml-fast-write a2 v smm))
           (if (and (equal (nfix a1) (nfix a2))
                    (< (nfix a2) (smml-block-start (len smm) smm)))
               (nfix v)
             (smml-fast-read a1 smm)))
    :hints (("goal" :induct (ind a1 a2 smm)
             :in-theory (disable smml-block-start-alt)))))


(defthm true-list-listp-smml-fast-write
  (implies (true-list-listp smm)
           (true-list-listp (smml-fast-write a v smm))))

(defthm u32-list-listp-smml-fast-write
  (implies (and (u32-list-listp smm)
                (unsigned-byte-p 32 v))
           (u32-list-listp (smml-fast-write a v smm))))

(defthm len-smml-fast-write
  (equal (len (smml-fast-write a v smm))
         (len smm)))

(defthm len-nth-smml-fast-write
  (equal (len (nth n (smml-fast-write a v smm)))
         (len (nth n smm)))
  :hints(("Goal" :in-theory (enable nth))))

(defthm smml-smme-blocksizes-ok-of-smml-fast-write-alt
  (implies (smml-smme-blocksizes-ok smm smme)
           (smml-smme-blocksizes-ok (smml-fast-write a v smm) smme))
  :hints (("goal" :in-theory (disable smml-smme-blocksizes-ok)
           :expand ((smml-smme-blocksizes-ok (smml-fast-write a v smm) smme))
           :do-not-induct t)))


(defthm smml-read-is-smme-read
  (implies (and (smml-smme-blocksizes-ok smm smme)
                (smml-smme-reads-ok smm smme)
                (equal (len smm) (smme-nblocks smme))
                (smme-wfp smme)
                (< (nfix n) (len smm))
                (< (nfix i) (len (nth n smm))))
           (equal (smml-read n i smm)
                  (smme-read n i smme)))
  :hints(("Goal" :in-theory (e/d (smme-addr smme-read)
                                 (smml-smme-blocksizes-ok
                                  smme-wfp-implies-block-ref-in-bounds
                                  smml-smme-reads-ok
                                  smml-smme-reads-ok-necc
                                  smml-read
                                  smme-wfp))
          :use smme-wfp-implies-block-ref-in-bounds
          :do-not-induct t)))

(defthm smml-addr-in-terms-of-smme-addr
  (implies (and (smml-smme-blocksizes-ok smm smme)
                (smml-smme-reads-ok smm smme)
                (equal (len smm) (nfix (smme-nblocks smme)))
                (smme-wfp smme)
                (natp i)
                (< (nfix n) (len smm))
                (< i (len (nth n smm))))
           (equal (+ i (smml-block-start n smm))
                  (smme-addr n i smme)))
  :hints(("Goal" :in-theory (e/d (smme-addr)
                                 (smml-smme-blocksizes-ok
                                  smme-wfp-implies-block-ref-in-bounds
                                  smml-smme-reads-ok
                                  smml-smme-reads-ok-necc
                                  smml-read
                                  smme-wfp))
          :do-not-induct t)))



(defthm smml-block-start-of-smml-fast-write
  (equal (smml-block-start n (smml-fast-write a v smm))
         (smml-block-start n smm))
  :hints(("Goal" :in-theory (e/d (smml-block-start)
                                 (smml-block-start-alt)))))


(defthm smml-smme-reads-ok-of-smml-fast-write-alt
  (implies (smml-smme-reads-ok smm smme)
           (smml-smme-reads-ok (smml-fast-write a v smm)
                               (update-smme-memi a v smme)))
  :hints(("Goal" :in-theory (disable smml-smme-reads-ok)
          :expand ((:free (smme) (smml-smme-reads-ok (smml-fast-write a v smm)
                                                  smme)))
          :do-not-induct t)))





(defthm smme-addr-in-memi-bounds
  (implies (and (smme-wfp smme)
                (< (nfix n) (smme-nblocks smme))
                (< (nfix i) (smme-block-size n smme)))
           (< (smme-addr n i smme) (smme-mem-length smme)))
  :rule-classes :linear)

(local (defthm len-of-append
         (Equal (len (append a b))
                (+ (len a) (len b)))))

(local (defthm my-nth-of-append
         (equal (nth n (append x y))
                (if (< (nfix n) (len x))
                    (nth n x)
                  (nth (- (nfix n) (len x)) y)))
         :hints (("goal" :use nth-of-append
                  :in-theory (e/d (nfix) (nth-of-append))))))

(local (in-theory (disable nth-of-append)))

(defthm smml-smme-blocksizes-ok-of-addblock
  (implies (and (smml-smme-blocksizes-ok smm smme)
                (smml-smme-reads-ok smm smme)
                (smme-wfp smme)
                (equal (len smm) (nfix (smme-nblocks smme))))
           (smml-smme-blocksizes-ok (append smm (list (repeat sz 0)))
                                  (smme-addblock sz smme)))
  :hints(("Goal" :in-theory (disable smme-wfp
                                     smml-smme-reads-ok
                                     smml-smme-blocksizes-ok
                                     smme-addblock)
          :expand ((smml-smme-blocksizes-ok (append smm (list (repeat sz 0)))
                                          (smme-addblock sz smme)))
          :do-not-induct t)
         (and stable-under-simplificationp
              '(:in-theory (disable smme-wfp ;; enable smme-addblock
                                     smml-smme-reads-ok
                                     smml-smme-blocksizes-ok)))))


(defthm smml-block-start-of-addblock
  (equal (smml-block-start (+ 1 (len smm))
                          (append smm (list (repeat sz 0))))
         (+ (nfix sz)
            (smml-block-start (len smm) smm)))
  :hints(("Goal" :in-theory (e/d (smml-block-start)
                                 (smml-block-start-alt
                                  (smml-block-start)))
          :induct (smml-block-start (len smm) smm))))

(encapsulate nil
  (local (defthm smml-fast-read-of-append-split
           (equal (smml-fast-read i (append smm smm2))
                  (if (< (nfix i)
                         (smml-block-start (len smm) smm))
                      (smml-fast-read i smm)
                    (smml-fast-read (- (nfix i)
                                      (smml-block-start (len smm) smm))
                                   smm2)))
           :hints(("Goal" :in-theory (e/d (smml-block-start)
                                          (smml-block-start-alt))))))


  (defthm smml-smme-read-of-addblock
    (implies (and (smml-smme-blocksizes-ok smm smme)
                  (smml-smme-reads-ok smm smme)
                  (smme-wfp smme)
                  (equal (len smm) (smme-nblocks smme))
                  (< (nfix i) (smml-block-start
                               (+ 1 (len smm))
                               (append smm (list (repeat sz 0))))))
             (equal (smml-fast-read i (append smm (list (repeat sz 0))))
                    (smme-memi i (smme-addblock sz smme))))
    :hints (("goal" :do-not-induct t
             :in-theory (disable smml-smme-blocksizes-ok
                                 smml-smme-reads-ok)))))


(defthm smml-smme-reads-ok-of-addblock
  (implies (and (smml-smme-blocksizes-ok smm smme)
                (smml-smme-reads-ok smm smme)
                (smme-wfp smme)
                (equal (len smm) (smme-nblocks smme)))
           (smml-smme-reads-ok (append smm (list (repeat sz 0)))
                             (smme-addblock sz smme)))
  :hints(("Goal" :in-theory (disable smme-wfp
                                     smml-smme-reads-ok
                                     smml-smme-blocksizes-ok
                                     smme-addblock
                                     smml-smme-blocksizes-ok-of-addblock)
          :expand ((smml-smme-reads-ok (append smm (list (repeat sz 0)))
                                     (smme-addblock sz smme)))
          :use smml-smme-blocksizes-ok-of-addblock
          :do-not-induct t)))


(defthm nfix-of-decr-less-than
  (implies (natp x)
           (equal (< (nfix (+ -1 x)) x)
                  (not (equal x 0)))))

(defthm smml-block-start-lte-len-memi
  (implies (and (smml-smme-blocksizes-ok smm smme)
                (smme-wfp smme)
                (equal (len smm)
                       (smme-nblocks smme)))
           (<= (smml-block-start (len smm) smm)
               (smme-mem-length smme)))
  :hints(("Goal" :in-theory (e/d (smme-addr)
                                 (smml-smme-blocksizes-ok))
          :do-not-induct t
          :use ((:instance smme-addr-in-memi-bounds
                 (n (1- (nfix (smme-nblocks smme))))
                 (i (1- (smme-block-size (1- (nfix (smme-nblocks smme))) smme)))))))
  :rule-classes :linear)

(defthm smml-block-start-of-take-same
  (implies (<= (nfix n) (len x))
           (equal (smml-block-start n (take n x))
                  (smml-block-start n x)))
  :hints (("goal" :induct t
           :in-theory (e/d (take) (smml-block-start-alt))
           :expand ((:free (x) (smml-block-start n x))))))

(defthm smml-fast-read-of-take
  (implies (And (< (nfix k) (smml-block-start n smm))
                (<= (nfix n) (len smm)))
           (equal (smml-fast-read k (take n smm))
                  (smml-fast-read k smm)))
  :hints(("Goal" :in-theory (e/d () (smml-block-start-alt)))))

;; (defthm smml-fast-read-of-take
;;   (implies (< (nfix n) (smml-block-start


(defthm u32-listp-of-repeat
  (implies (unsigned-byte-p 32 default)
           (u32-listp (repeat sz default)))
  :hints(("Goal" :in-theory (enable repeat))))

(defthm u32-list-listp-take
  (implies (u32-list-listp x)
           (u32-list-listp (take n x)))
  :hints(("Goal" :in-theory (e/d (take) (take-of-too-many take-when-atom)))))

(local (defthm len-equal-0
         (equal (equal (len x) 0) (atom x))))

(local (defthm len-greater-0
         (equal (< 0 (len x)) (consp x))))

(defthm smml-block-start-of-update-last
  (implies (consp smm)
           (equal (smml-block-start n (update-nth (+ -1 (len smm)) new-last smm))
                  (if (< (nfix n) (len smm))
                      (smml-block-start n smm)
                    (+ (smml-block-start (+ -1 (len smm)) smm) (len new-last)))))
  :hints (("goal" :induct (smml-block-start n smm)
           :in-theory (disable smml-block-start-alt))))

(defthm smml-fast-read-of-update-last
  (equal (smml-fast-read n (update-nth (+ -1 (len smm)) new-last smm))
         (if (< (nfix n) (smml-block-start (+ -1 (len smm)) smm))
             (smml-fast-read n smm)
           (if (< (nfix n) (+ (smml-block-start (+ -1 (len smm)) smm) (len new-last)))
               (nfix (nth (- (nfix n) (smml-block-start (+ -1 (len smm)) smm)) new-last))
             0)))
  :hints(("Goal" :in-theory (e/d (update-nth) (smml-block-start-alt))
          :expand ((:free (smm) (smml-fast-read n smm))
                   (:with smml-block-start (smml-block-start (+ -1 (len smm)) smm)))
          :induct (smml-fast-read n smm))))

(local (defun special-nth-is-smml-fast-read-ind (idx block blockstart smm)
         (declare (xargs :measure (nfix block)))
         (if (zp block)
             (list idx block blockstart smm)
           (if (< (nfix idx) (len (car smm)))
               (list idx block blockstart)
             (special-nth-is-smml-fast-read-ind
              (- (nfix idx) (len (car smm)))
              (- block 1) (smml-block-start (- block 1) (cdr smm))
              (cdr smm))))))

(local (defthm special-nth-is-smml-fast-read
         (implies (and (natp idx)
                       (equal blockstart (smml-block-start block smm))
                       (<= blockstart idx)
                       (< idx (+ blockstart
                                 (len (nth block smm)))))
                  (nat-equiv (nth (+ (- blockstart) idx)
                                  (nth block smm))
                             (smml-fast-read idx smm)))
         :hints(("Goal" :induct (special-nth-is-smml-fast-read-ind idx block blockstart smm)
                 :in-theory (disable smml-block-start-alt)
                 :expand ((nth block smm)
                          (smml-fast-read idx smm)
                          (:with smml-block-start (smml-block-start block smm)))))))

(encapsulate nil
  (local
   (progn


     (defun-nx smme-corr (smme smm)
       (and ;; (true-list-listp smm)
            (smme-wfp smme)
            ;; (smmep smme)
            (equal (len smm) (smme-nblocks smme))
            (smml-smme-blocksizes-ok smm smme)
            (smml-smme-reads-ok smm smme)))))

  (local (in-theory (disable (smme-corr)
                             (force)
                             smmep
                             smme-wfp
                             smme-clear
                             smml-read (smml-read)
                             smme-write (smme-write)
                             smme-read (smme-read)
                             smml-smme-blocksizes-ok
                             smml-smme-reads-ok
                             smme-addblock
                             smml-read-in-terms-of-fast-read
                             smml-block-start-when-smme-wfp
                             smmep
                             ; smme-addr-in-terms-of-smml-block-start
                             ;; smml-block-start-when-smme-blocks-wfp
                             )))

  (local (set-default-hints '('(:do-not-induct t)
                              (and stable-under-simplificationp
                                   '(:in-theory (enable smmep)))
                              (and stable-under-simplificationp
                                   (let ((lit (car (last clause))))
                                     (and (member (car lit) '(smml-smme-reads-ok
                                                              smml-smme-blocksizes-ok))
                                          `(:expand (,lit)))))
                              (and stable-under-simplificationp
                                   '(:in-theory (enable smme-read
                                                        ; smme-addr-in-terms-of-smml-block-start
                                                        smme-write)))
                              (and stable-under-simplificationp
                                   '(:in-theory (enable smme-addblock
                                                        smml-block-start-when-smme-wfp)))
                              )))


  (defabsstobj-events smm
    :foundation smme
    :recognizer (smmp :logic smmlp :exec smmep)
    :creator (smm-create :logic smml-create :exec create-smme)
    :corr-fn smme-corr
    :exports ((smm-nblocks :logic smml-nblocks :exec smme-nblocks$inline)
              (smm-block-size :logic smml-block-size :exec smme-block-size$inline)
              (smm-read :logic smml-read :exec smme-read$inline)
              (smm-write :logic smml-write :exec smme-write$inline)
              (smm-addblock :logic smml-addblock :exec smme-addblock
                            :protect t)
              (smm-clear :logic smml-clear :exec smme-clear$inline
                         :protect t)
              (smm-block-start :logic smml-block-start :exec smme-block-start$inline)
              (smm-max-index :logic smml-max-index :exec smme-max-index$inline)
              (smm-fast-read :logic smml-fast-read :exec smme-memi$inline)
              (smm-fast-write :logic smml-fast-write :exec update-smme-memi$inline)
              (smm-rewind :logic smml-rewind :exec smme-rewind$inline)
              (smm-resize-last :logic smml-resize-last :exec smme-resize-last
                               :protect t)))

  (defstobj-clone smm2 smm :suffix "2")
  (defstobj-clone smm3 smm :suffix "3"))
