; TRUTH - integer truth table representation
; Copyright (C) 2017 Centaur Technology
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


(in-package "TRUTH")

(include-book "sizes")
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/bitstruct" :dir :system)

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (in-theory (disable unsigned-byte-p signed-byte-p)))

(local (std::add-default-post-define-hook :fix))

(define perm4p (x)
  (and (unsigned-byte-p 6 x)
       (<= 1 (nth-slice2 1 x))
       (<= 2 (nth-slice2 2 x)))
  ///
  (defthm perm4p-implies-unsigned-byte-p
    (implies (perm4p x)
             (unsigned-byte-p 6 x)))

  (defthm perm4p-implies-natp
    (implies (perm4p x)
             (natp x))
    :rule-classes :compound-recognizer))

(define perm4-fix ((x perm4p))
  :split-types t
  (declare (type (unsigned-byte 6) x))
  :returns (xx perm4p :rule-classes (:rewrite (:type-prescription :typed-term xx)))
  :inline t
  (mbe :logic (if (perm4p x) x #x24) ;; 0,1,2
       :exec x)
  ///
  (defret perm4-fix-when-perm4p
    (implies (perm4p x)
             (equal (perm4-fix x) x)))

  (fty::deffixtype perm4 :pred perm4p :fix perm4-fix :equiv perm4-equiv :define t :forward t))

(define perm4-idx0 ((x perm4p))
  :split-types t
  (declare (type (unsigned-byte 6) x))
  :returns (idx0 natp :rule-classes :type-prescription)
  :inline t
  (logand 3 (the (unsigned-byte 6) (perm4-fix x)))
  ///
  (defret perm4-idx0-upper-bound
    (< idx0 4)
    :rule-classes :linear))

(define perm4-idx1 ((x perm4p))
  :split-types t
  (declare (type (unsigned-byte 6) x))
  :returns (idx1 natp :rule-classes :type-prescription)
  :inline t
  (logand 3 (the (unsigned-byte 4) (ash (the (unsigned-byte 6) (perm4-fix x)) -2)))
  ///
  (defret perm4-idx1-upper-bound
    (< idx1 4)
    :rule-classes :linear)

  (defret perm4-idx1-lower-bound
    (<= 1 idx1)
    :hints(("Goal" :in-theory (enable perm4-fix perm4p nth-slice2)))
    :rule-classes :linear))

(define perm4-idx2 ((x perm4p))
  :split-types t
  (declare (type (unsigned-byte 6) x))
  :returns (idx2 natp :rule-classes :type-prescription)
  :inline t
  (logand 3 (the (unsigned-byte 2) (ash (the (unsigned-byte 6) (perm4-fix x)) -4)))
  ///
  (defret perm4-idx2-upper-bound
    (< idx2 4)
    :hints(("Goal" :in-theory (disable unsigned-byte-p-of-logtail)))
    :rule-classes :linear)

  (defret perm4-idx2-lower-bound
    (<= 2 idx2)
    :hints(("Goal" :in-theory (enable perm4-fix perm4p nth-slice2)))
    :rule-classes :linear))

(define perm4-index-list ((x perm4p))
  :returns (indices (index-listp indices 4)
                    :rule-classes (:rewrite (:type-prescription :typed-term indices
                                             :corollary (true-listp indices)))
                    :hints(("Goal" :in-theory (enable index-listp))))
  (list (perm4-idx0 x)
        (perm4-idx1 x)
        (perm4-idx2 x)
        3))

(define truth-permute4 ((perm perm4p)
                        (truth (unsigned-byte-p 16 truth)))
  :split-types t
  (declare (type (unsigned-byte 6) perm)
           (type (unsigned-byte 16) truth))
  :enabled t
  :guard-hints (("goal" :in-theory (enable perm4-index-list)
                 :expand ((:free (a b c) (truth-perm a b c 4)))))
  (mbe :logic (truth-perm 0 (perm4-index-list perm) truth 4)
       :exec
       (b* ((truth (swap-vars-ordered4 (perm4-idx0 perm) 0 truth))
            (truth (swap-vars-ordered4 (perm4-idx1 perm) 1 truth)))
         (swap-vars-ordered4 (perm4-idx2 perm) 2 truth))))

(define truth-permute4-rev ((perm perm4p)
                            (truth (unsigned-byte-p 16 truth)))
  :split-types t
  (declare (type (unsigned-byte 6) perm)
           (type (unsigned-byte 16) truth))
  :enabled t
  :guard-hints (("goal" :in-theory (enable perm4-index-list)
                 :expand ((:free (a b c) (truth-perm-rev a b c 4)))))
  (mbe :logic (truth-perm-rev 0 (perm4-index-list perm) truth 4)
       :exec
       (b* ((truth (swap-vars-ordered4 (perm4-idx2 perm) 2 truth))
            (truth (swap-vars-ordered4 (perm4-idx1 perm) 1 truth)))
         (swap-vars-ordered4 (perm4-idx0 perm) 0 truth))))

(local
(progn
  (define perms-insert-in-list ((n natp) (pos natp) (lst nat-listp))
    :hooks nil
    :returns (perms nat-listp)
    (if (atom lst)
        nil
      (cons (bitops::update-nth-slice 2 pos n (lnfix (car lst)))
            (perms-insert-in-list n pos (cdr lst)))))

  (define append-perms4 ((n natp) (pos natp) (lst nat-listp))
    :guard (<= n 4)
    :measure (nfix (- 4 (nfix n)))
    :hooks nil
    ;; :guard-debug t
    :returns (perms nat-listp)
    (if (mbe :logic (zp (- 4 (nfix n)))
             :exec (eql n 4))
        nil
      (append (perms-insert-in-list n pos lst)
              (append-perms4 (+ 1 (lnfix n)) pos lst))))

    ;; :guard (<= n 4)
    ;; :measure (nfix (- 4 (nfix n)))
    ;; (if (mbe :logic (zp (- 4 (nfix n)))
    ;;          :exec (eql n 4))
    ;;     nil
    ;;   (cons ( (lnfix n) tail)
    ;;         (all-perms4-aux (1+ (lnfix n)) tail))))
  (define all-perms4 ((n natp) (head natp))
    :guard (<= n 3)
    :measure (nfix (- 3 (nfix n)))
    :returns (perms nat-listp)
    :verify-guards nil
    :hooks nil
    (if (mbe :logic (zp (- 3 (nfix n)))
             :exec (eql n 3))
        (list (lnfix head))
      (append-perms4 n n (all-perms4 (+ 1 (lnfix n)) head)))
    ///
    (verify-guards all-perms4)))
)


(fty::deflist perm4-list :elt-type perm4)

(make-event
 `(defconst *all-perms4* ',(all-perms4 0 0)))



(fty::defbitstruct polarity4 4)
(fty::defbitstruct truth4 16)

(fty::fixtype-to-bitstruct perm4 :width 6)

(fty::defbitstruct npn4
  ((truth truth4 "normal-form truth table")
   (negate bitp)
   (polarity polarity4)
   (perm perm4 :default #x24)))

(defthm truth-norm-when-truth4-p
  (implies (truth4-p x)
           (equal (truth-norm x 4) x))
  :hints(("Goal" :in-theory (enable truth-norm))))

(local (defthm truth4-p-by-bounds
         (implies (and (natp n)
                       (< n 65536))
                  (truth4-p n))
         :hints(("Goal" :in-theory (enable truth4-p unsigned-byte-p)))))



(include-book "std/stobjs/1d-arr" :dir :system)

(define maybe-npn4-p (x)
  (or (npn4-p x) (eql x 0))
  ///
  (defthm maybe-npn4-p-compound-recognizer
    (implies (maybe-npn4-p x) (natp x))
    :rule-classes :compound-recognizer)

  (defthm maybe-npn4-p-implies-size
    (implies (maybe-npn4-p x)
             (unsigned-byte-p 27 x)))

  (defthm npn4-p-when-maybe-npn4-p
    (implies (and (maybe-npn4-p x)
                  (not (equal x 0)))
             (npn4-p x)))

  (defthm maybe-npn4-p-when-npn4-p
    (implies (npn4-p x)
             (maybe-npn4-p x))))

(define maybe-npn4-fix ((x maybe-npn4-p))
  :returns (xx maybe-npn4-p :rule-classes (:rewrite (:type-prescription :typed-term xx)))
  (mbe :logic (if (maybe-npn4-p x) x 0)
       :exec x)
  ///
  (defthm maybe-npn4-fix-when-maybe-npn4-p
    (implies (maybe-npn4-p x)
             (equal (maybe-npn4-fix x) x))))

(fty::deffixtype maybe-npn4 :pred maybe-npn4-p :fix maybe-npn4-fix :equiv maybe-npn4-equiv
  :define t :forward t)

(stobjs::def-1d-arr npn4arr
  :slotname npn4
  :pred maybe-npn4-p
  :type-decl (unsigned-byte 27)
  :fix maybe-npn4-fix
  :default-val 0)



(define npn4-truth-value ((npn npn4-p))
  :returns (val truth4-p)
  (b* (((npn4 npn))
       (neg-truth (truth-norm4 (logxor npn.truth (- (lbfix npn.negate)))))
       (flip-truth (permute-polarity4 npn.polarity neg-truth)))
    (truth-permute4 npn.perm flip-truth))
  ///
  (defret npn4-truth-value-upper-bound
    (< val 65536)
    :hints (("goal" :use truth4-p-of-npn4-truth-value
             :in-theory (e/d (truth4-p unsigned-byte-p)
                             (truth4-p-of-npn4-truth-value))))
    :rule-classes (:rewrite :linear))

  (defret npn4-truth-value-of-identity
    (b* (((npn4 npn)))
      (implies (and (equal npn.negate 0)
                    (equal npn.polarity 0)
                    (equal npn.perm #x24))
               (equal val
                      npn.truth)))
    :hints (("goal" :expand ((:free (n truth) (truth-perm n '(0 1 2 3) truth 4)))))))
  

(defun-sk npn4arr-partly-correct (npn4arr)
  (forall idx
          (b* ((val (maybe-npn4-fix (nth idx npn4arr))))
            (implies (not (equal 0 val))
                     (equal (npn4-truth-value val) (nfix idx)))))
  :rewrite :direct)

(in-theory (disable npn4arr-partly-correct))


(define record-npn4 ((npn npn4-p)
                     npn4arr)
  :guard (<= (ash 1 16) (npn4s-length npn4arr))
  :returns (new-npn4arr)
  (b* (((npn4 npn) (npn4-fix npn))
       (perm-truth (npn4-truth-value npn))
       (look (get-npn4 perm-truth npn4arr))
       ((unless (eql look 0))
        (b* (((npn4 look)))
          (and (not (eql look.truth npn.truth))
               (progn$ (cw "Error: ~x0 has two different canonical forms? ~x1, ~x2~%"
                           perm-truth npn.truth look.truth)
                       (break$))))
        npn4arr))
    (set-npn4 perm-truth npn npn4arr))
  ///
  (defret length-of-record-npn4
    (implies (<= (ash 1 16) (len npn4arr))
             (equal (len new-npn4arr) (len npn4arr))))

  (defret record-npn4-preserves-partly-correct
    (implies (npn4arr-partly-correct npn4arr)
             (npn4arr-partly-correct new-npn4arr))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret index-bound-of-record-npn4
    (not (equal (maybe-npn4-fix (nth (npn4-truth-value npn) new-npn4arr)) 0)))

  (defret index-bound-preserved-of-record-npn4
    (implies (not (equal 0 (maybe-npn4-fix (nth n npn4arr))))
             (equal (nth n new-npn4arr)
                    (nth n npn4arr)))))


(define record-npn4-negs ((npn npn4-p)
                          npn4arr)
  :guard (<= (ash 1 16) (npn4s-length npn4arr))
  :returns (new-npn4arr)
  (b* ((npn4arr (record-npn4 (!npn4->negate 0 npn) npn4arr)))
    (record-npn4 (!npn4->negate 1 npn) npn4arr))
  ///
  (defret length-of-record-npn4-negs
    (implies (<= (ash 1 16) (len npn4arr))
             (equal (len new-npn4arr) (len npn4arr))))

  (defret record-npn4-negs-preserves-partly-correct
    (implies (npn4arr-partly-correct npn4arr)
             (npn4arr-partly-correct new-npn4arr)))

  (defret index-bound-preserved-of-record-npn4-negs
    (implies (not (equal 0 (maybe-npn4-fix (nth n npn4arr))))
             (equal (nth n new-npn4arr)
                    (nth n npn4arr))))

  (defret index-bound-of-record-npn4-negs
    (not (equal 0 (maybe-npn4-fix (nth (npn4-truth-value (!npn4->negate 0 npn)) new-npn4arr))))))

(define record-npn4-polarities ((polarity natp)
                                (npn npn4-p)
                                npn4arr)
  :guard (and (<= (ash 1 16) (npn4s-length npn4arr))
              (<= polarity 16))
  :returns (new-npn4arr)
  :guard-hints (("goal" :in-theory (enable unsigned-byte-p)))
  (b* (((when (zp polarity)) npn4arr)
       (polarity (1- polarity))
       (npn4arr (record-npn4-negs (!npn4->polarity polarity npn) npn4arr)))
    (record-npn4-polarities polarity npn npn4arr))
  ///
  (defret length-of-record-npn4-polarities
    (implies (<= (ash 1 16) (len npn4arr))
             (equal (len new-npn4arr) (len npn4arr))))

  (defret record-npn4-polarities-preserves-partly-correct
    (implies (npn4arr-partly-correct npn4arr)
             (npn4arr-partly-correct new-npn4arr)))

  (defret index-bound-preserved-of-record-npn4-polarities
    (implies (not (equal 0 (maybe-npn4-fix (nth n npn4arr))))
             (equal (nth n new-npn4arr)
                    (nth n npn4arr))))

  (defret index-bound-of-record-npn4-polarities
    (implies (posp polarity)
             (not (equal 0 (maybe-npn4-fix (nth (npn4-truth-value
                                                 (!npn4->negate 0 (!npn4->polarity 0 npn)))
                                                new-npn4arr)))))))


(define record-npn4-perms ((perms perm4-list-p)
                           (npn npn4-p)
                           npn4arr)
  :guard (<= (ash 1 16) (npn4s-length npn4arr))
  :returns (new-npn4arr)
  (b* (((when (atom perms)) npn4arr)
       (npn4arr (record-npn4-polarities 16 (!npn4->perm (car perms) npn) npn4arr)))
    (record-npn4-perms (cdr perms) npn npn4arr))
  ///
  (defret length-of-record-npn4-perms
    (implies (<= (ash 1 16) (len npn4arr))
             (equal (len new-npn4arr) (len npn4arr))))

  (defret record-npn4-perms-preserves-partly-correct
    (implies (npn4arr-partly-correct npn4arr)
             (npn4arr-partly-correct new-npn4arr)))

  (defret index-bound-preserved-of-record-npn4-perms
    (implies (not (equal 0 (maybe-npn4-fix (nth n npn4arr))))
             (equal (nth n new-npn4arr)
                    (nth n npn4arr))))

  (local
   (defret index-bound-of-record-npn4-perms-lemma
     (implies (member-equal #x24 perms)
              (not (equal 0 (maybe-npn4-fix (nth (npn4-truth-value
                                                  (!npn4->negate 0 (!npn4->polarity 0 (!npn4->perm #x24 npn))))
                                                 new-npn4arr)))))
     :hints (("goal" :induct t
              :in-theory (disable npn4-truth-value-of-identity)))
     :rule-classes nil))

  (defret index-bound-of-record-npn4-perms
    (implies (and (member-equal #x24 perms)
                  (equal (nfix n) (npn4->truth npn)))
             (not (equal 0 (maybe-npn4-fix (nth n new-npn4arr)))))
    :hints (("goal" :use index-bound-of-record-npn4-perms-lemma))))

(defun-sk npn4arr-correct (npn4arr)
  (forall idx
          (implies (< (nfix idx) 65536)
                   (b* ((val (maybe-npn4-fix (nth idx npn4arr))))
                     (and (not (equal 0 val))
                          (equal (npn4-truth-value val) (nfix idx))))))
  :rewrite :direct)

(in-theory (disable npn4arr-correct))

(define record-all-npn4-perms ((n natp)
                               npn4arr)
  :guard (and (<= n (ash 1 16))
              (<= (ash 1 16) (npn4s-length npn4arr)))
  :measure (nfix (- (ash 1 16) (nfix n)))
  :returns (new-npn4arr)
  :guard-hints (("goal" :in-theory (enable unsigned-byte-p)))
  (b* (((when (mbe :logic (zp (- (ash 1 16) (nfix n)))
                   :exec (eql n (ash 1 16))))
        npn4arr)
       ((unless (eql 0 (get-npn4 n npn4arr)))
        (record-all-npn4-perms (1+ (lnfix n)) npn4arr))
       (npn4arr (record-npn4-perms *all-perms4* (make-npn4 :truth (lnfix n)) npn4arr)))
    (record-all-npn4-perms (1+ (lnfix n)) npn4arr))
  ///
  (defret length-of-record-all-npn4-perms
    (implies (<= (ash 1 16) (len npn4arr))
             (equal (len new-npn4arr) (len npn4arr))))

  (defret record-all-npn4-perms-preserves-partly-correct
    (implies (npn4arr-partly-correct npn4arr)
             (npn4arr-partly-correct new-npn4arr)))

  
  (defret index-bound-preserved-of-record-all-npn4-perms
    (implies (not (equal 0 (maybe-npn4-fix (nth k npn4arr))))
             (equal (nth k new-npn4arr)
                    (nth k npn4arr))))

  (defret indices-bound-of-record-all-npn4-perms
    (implies (and (<= (nfix n) (nfix i))
                  (< (nfix i) 65536))
             (not (equal (maybe-npn4-fix (nth i new-npn4arr)) 0)))
    :hints (("goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defret npn4arr-correct-of-record-all-npn4-perms
    (implies (and (equal n 0)
                  (npn4arr-partly-correct npn4arr))
             (npn4arr-correct new-npn4arr))
    :hints(("Goal" :in-theory (disable record-all-npn4-perms))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause))))))))



(define record-all-npn4-perms-top (npn4arr)
  :returns (new-npn4arr)
  (b* ((npn4arr (resize-npn4s 0 npn4arr))
       (npn4arr (resize-npn4s (ash 1 16) npn4arr)))
    (record-all-npn4-perms 0 npn4arr))
  ///
  (local (include-book "std/lists/resize-list" :dir :system))

  (local (in-theory (disable (record-all-npn4-perms)
                             resize-list
                             (resize-npn4s$a)
                             (resize-npn4s)
                             (resize-list)
                             acl2::resize-list-when-atom)))

  (defret length-of-record-all-npn4-perms-top
    (equal (len new-npn4arr) 65536))

  (local (defthm npn4arr-partly-correct-of-resize-empty
           (npn4arr-partly-correct (resize-list nil n 0))
           :hints (("goal" :expand ((npn4arr-partly-correct (resize-list nil n 0)))))))

  (defret npn4arr-correct-of-record-all-npn4-perms-top
    (npn4arr-correct new-npn4arr)))


(define collect-norm-truths ((n natp)
                                   npn4arr)
  :guard (<= n (npn4s-length npn4arr))
  (b* (((when (zp n)) nil)
       (n (1- n))
       (rest (collect-norm-truths n npn4arr))
       (look (get-npn4 n npn4arr))
       ((when (eql look 0))
        (raise "error -- uninitialized entry"))
       ((npn4 look))
       (look (hons-get look.truth rest))
       ((when look) rest))
    (hons-acons look.truth t rest)))

