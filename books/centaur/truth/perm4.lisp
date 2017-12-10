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
        3)
  ///
  (defret len-of-perm4-index-list
    (equal (len indices) 4))

  (defret nat-listp-of-perm4-index-list
    (nat-listp indices)))

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

;; BOZO this doesn't need to be 16 bits wide -- could be just 8, which would
;; cover the 222 NPN normal forms.  But the total width of an npn4 bitstruct is
;; still less than 32 so it doesn't matter much.
(fty::defbitstruct truth-idx 16)

(fty::fixtype-to-bitstruct perm4 :width 6)

(fty::defbitstruct npn4
  ((truth-idx truth-idx "normal-form truth table")
   (negate bitp)
   (polarity polarity4)
   (perm perm4 :default #x24)))

(defthm npn4-p-compound-recognizer-stronger
  (implies (npn4-p x)
           (and (integerp x)
                (< 1 x)))
  :hints (("goal" :cases ((equal x 0)
                          (equal x 1))))
  :rule-classes :compound-recognizer)

(defthm npn4-fix-type
  (npn4-p (npn4-fix x))
  :rule-classes ((:type-prescription :typed-term (npn4-fix x))))

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
             (equal (maybe-npn4-fix x) x)))

  (defthm maybe-npn4-fix-when-not-zero
    (implies (not (equal 0 (maybe-npn4-fix x)))
             (equal (maybe-npn4-fix x) (npn4-fix x)))))

(fty::deffixtype maybe-npn4 :pred maybe-npn4-p :fix maybe-npn4-fix :equiv maybe-npn4-equiv
  :define t :forward t)

(stobjs::def-1d-arr npn4arr
  :slotname npn4
  :pred maybe-npn4-p
  :type-decl (unsigned-byte 27)
  :fix maybe-npn4-fix
  :default-val 0)

(stobjs::def-1d-arr truth4arr
  :slotname truth4
  :pred truth4-p
  :type-decl (unsigned-byte 16)
  :fix truth4-fix
  :default-val 0)



(define npn4-truth-value ((npn npn4-p)
                          (truth truth4-p))
  :returns (val truth4-p)
  (b* (((npn4 npn))
       (neg-truth (truth-norm4 (logxor (truth4-fix truth) (- (lbfix npn.negate)))))
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
                      (truth-norm truth 4))))
    :hints (("goal" :expand ((:free (n truth) (truth-perm n '(0 1 2 3) truth 4))))))
  
  (defret eval-of-npn4-truth-value
    (equal (truth-eval val env 4)
           (b* (((npn4 npn))
                (env (env-perm-rev 0 (perm4-index-list npn.perm) env 4))
                (env (env-permute-polarity 0 npn.polarity env 4)))
             (xor (acl2::bit->bool npn.negate)
                  (truth-eval truth env 4)))))

  (defret eval-of-npn4-truth-value-with-permuted-env
    (b* (((npn4 npn))
         (env (env-permute-polarity 0 npn.polarity orig-env 4))
         (env (env-perm 0 (perm4-index-list npn.perm) env 4)))
      (equal (truth-eval val env 4)
             (xor (acl2::bit->bool npn.negate)
                  (truth-eval truth orig-env 4))))))

(define maybe-grow-truth4arr ((size natp)
                              (truth4arr))
  :returns new-truth4arr
  (if (<= (lnfix size) (truth4s-length truth4arr))
      truth4arr
    (resize-truth4s (max 222 (* 2 (lnfix size))) truth4arr))
  ///
  (local (include-book "std/lists/resize-list" :dir :system))
  (local (include-book "std/lists/nth" :dir :system))

  (defret length-of-maybe-grow-truth4arr-at-least-size
    (<= (nfix size) (len new-truth4arr))
    :rule-classes :linear)

  (defret length-of-maybe-grow-truth4arr-at-least-previous
    (<= (len truth4arr) (len new-truth4arr))
    :rule-classes :linear)

  (defret nth-of-maybe-grow-truth4arr
    (truth4-equiv (nth n new-truth4arr)
                  (nth n truth4arr))))  

(defsection npn4arr-partly-correct

  (defun-sk npn4arr-partly-correct (npn4arr truth4arr)
    (forall idx
            (b* ((val (nth idx npn4arr)))
              (implies (not (equal 0 (maybe-npn4-fix val)))
                       (b* (((npn4 val)))
                         (equal (npn4-truth-value val (nth val.truth-idx truth4arr))
                                (nfix idx))))))
    :rewrite :direct)

  (defun-sk npn4arr-indices-bounded (bound npn4arr)
    (forall idx
            (b* ((val (nth idx npn4arr)))
              (implies (not (equal 0 (maybe-npn4-fix val)))
                       (< (npn4->truth-idx val) (nfix bound)))))
    :rewrite :direct)

  (in-theory (disable npn4arr-partly-correct
                      npn4arr-indices-bounded))

  (defthm npn4arr-indices-bounded-linear
    (implies (npn4arr-indices-bounded bound npn4arr)
             (b* ((val (nth idx npn4arr)))
               (implies (not (equal 0 (maybe-npn4-fix val)))
                        (< (npn4->truth-idx val) (nfix bound)))))
    :rule-classes :linear)

  (defthm npn4arr-partly-correct-preserved-by-update-truth4arr
    (implies (and (npn4arr-indices-bounded n npn4arr)
                  (npn4arr-partly-correct npn4arr truth4arr))
             (npn4arr-partly-correct npn4arr (update-nth n val truth4arr)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm npn4arr-partly-correct-preserved-by-maybe-grow-truth4arr
    (implies (npn4arr-partly-correct npn4arr truth4arr)
             (npn4arr-partly-correct npn4arr (maybe-grow-truth4arr size truth4arr)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm npn4arr-indices-bounded-monotonic
    (implies (and (npn4arr-indices-bounded bound npn4arr)
                  (<= (nfix bound) (nfix new-bound)))
             (npn4arr-indices-bounded new-bound npn4arr))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))


(define record-npn4 ((npn npn4-p)
                     (truth truth4-p)
                     npn4arr)
  :guard (<= (ash 1 16) (npn4s-length npn4arr))
  :returns (new-npn4arr)
  (b* (((npn4 npn) (npn4-fix npn))
       (perm-truth (npn4-truth-value npn truth))
       (look (get-npn4 perm-truth npn4arr))
       ((unless (eql look 0))
        (b* (((npn4 look))
             ((when (eql look.truth-idx npn.truth-idx)) nil))
          (cw "Error: ~x0 has two different canonical forms? Indices ~x1, ~x2~%"
              perm-truth
               npn.truth-idx
               look.truth-idx)
          (break$))
        npn4arr))
    (set-npn4 perm-truth npn npn4arr))
  ///
  (defret length-of-record-npn4
    (implies (<= (ash 1 16) (len npn4arr))
             (equal (len new-npn4arr) (len npn4arr))))

  (defret record-npn4-preserves-partly-correct
    (implies (and (npn4arr-partly-correct npn4arr truth4arr)
                  (truth4-equiv truth (nth (npn4->truth-idx npn) truth4arr)))
             (npn4arr-partly-correct new-npn4arr truth4arr))
    :hints (("goal" :in-theory (disable truth4-equiv))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret index-bound-of-record-npn4
    (not (equal (maybe-npn4-fix (nth (npn4-truth-value npn truth) new-npn4arr)) 0)))

  (defret index-bound-preserved-of-record-npn4
    (implies (not (equal 0 (maybe-npn4-fix (nth n npn4arr))))
             (equal (nth n new-npn4arr)
                    (nth n npn4arr))))

  (defret npn4arr-indices-bounded-of-record-npn4
    (implies (and (npn4arr-indices-bounded bound npn4arr)
                  (< (npn4->truth-idx npn) (nfix bound)))
             (npn4arr-indices-bounded bound new-npn4arr))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))


(define record-npn4-negs ((npn npn4-p)
                          (truth truth4-p)
                          npn4arr)
  :guard (and (<= (ash 1 16) (npn4s-length npn4arr)))
  :returns (new-npn4arr)
  (b* ((npn4arr (record-npn4 (!npn4->negate 0 npn) truth npn4arr)))
    (record-npn4 (!npn4->negate 1 npn) truth npn4arr))
  ///
  (defret length-of-record-npn4-negs
    (implies (<= (ash 1 16) (len npn4arr))
             (equal (len new-npn4arr) (len npn4arr))))

  (defret record-npn4-negs-preserves-partly-correct
    (implies (and (npn4arr-partly-correct npn4arr truth4arr)
                  (truth4-equiv truth (nth (npn4->truth-idx npn) truth4arr)))
             (npn4arr-partly-correct new-npn4arr truth4arr)))

  (defret index-bound-preserved-of-record-npn4-negs
    (implies (not (equal 0 (maybe-npn4-fix (nth n npn4arr))))
             (equal (nth n new-npn4arr)
                    (nth n npn4arr))))

  (defret index-bound-of-record-npn4-negs
    (not (equal 0 (maybe-npn4-fix (nth (npn4-truth-value (!npn4->negate 0 npn) truth) new-npn4arr)))))

  (defret npn4arr-indices-bounded-of-record-npn4-negs
    (implies (and (npn4arr-indices-bounded bound npn4arr)
                  (< (npn4->truth-idx npn) (nfix bound)))
             (npn4arr-indices-bounded bound new-npn4arr))))

(define record-npn4-polarities ((polarity natp)
                                (npn npn4-p)
                                (truth truth4-p)
                                npn4arr)
  :guard (and (<= (ash 1 16) (npn4s-length npn4arr))
              (<= polarity 16))
  :returns (new-npn4arr)
  :guard-hints (("goal" :in-theory (enable unsigned-byte-p)))
  (b* (((when (zp polarity)) npn4arr)
       (polarity (1- polarity))
       (npn4arr (record-npn4-negs (!npn4->polarity polarity npn) truth npn4arr)))
    (record-npn4-polarities polarity npn truth npn4arr))
  ///
  (defret length-of-record-npn4-polarities
    (implies (<= (ash 1 16) (len npn4arr))
             (equal (len new-npn4arr) (len npn4arr))))

  (defret record-npn4-polarities-preserves-partly-correct
    (implies (and (npn4arr-partly-correct npn4arr truth4arr)
                  (truth4-equiv truth (nth (npn4->truth-idx npn) truth4arr)))
             (npn4arr-partly-correct new-npn4arr truth4arr)))

  (defret index-bound-preserved-of-record-npn4-polarities
    (implies (not (equal 0 (maybe-npn4-fix (nth n npn4arr))))
             (equal (nth n new-npn4arr)
                    (nth n npn4arr))))

  (defret index-bound-of-record-npn4-polarities
    (implies (posp polarity)
             (not (equal 0 (maybe-npn4-fix (nth (npn4-truth-value
                                                 (!npn4->negate 0 (!npn4->polarity 0 npn))
                                                 truth)
                                                new-npn4arr))))))

  (defret npn4arr-indices-bounded-of-record-npn4-polarities
    (implies (and (npn4arr-indices-bounded bound npn4arr)
                  (< (npn4->truth-idx npn) (nfix bound)))
             (npn4arr-indices-bounded bound new-npn4arr))))


(define record-npn4-perms ((perms perm4-list-p)
                           (npn npn4-p)
                           (truth truth4-p)
                           npn4arr)
  :guard (and (<= (ash 1 16) (npn4s-length npn4arr)))
  :returns (new-npn4arr)
  (b* (((when (atom perms)) npn4arr)
       (npn4arr (record-npn4-polarities 16 (!npn4->perm (car perms) npn) truth npn4arr)))
    (record-npn4-perms (cdr perms) npn truth npn4arr))
  ///
  (defret length-of-record-npn4-perms
    (implies (<= (ash 1 16) (len npn4arr))
             (equal (len new-npn4arr) (len npn4arr))))

  (defret record-npn4-perms-preserves-partly-correct
    (implies (and (npn4arr-partly-correct npn4arr truth4arr)
                  (truth4-equiv truth (nth (npn4->truth-idx npn) truth4arr)))
             (npn4arr-partly-correct new-npn4arr truth4arr)))

  (defret index-bound-preserved-of-record-npn4-perms
    (implies (not (equal 0 (maybe-npn4-fix (nth n npn4arr))))
             (equal (nth n new-npn4arr)
                    (nth n npn4arr))))

  (local
   (defret index-bound-of-record-npn4-perms-lemma
     (implies (member-equal #x24 perms)
              (not (equal 0 (maybe-npn4-fix (nth (npn4-truth-value
                                                  (!npn4->negate 0 (!npn4->polarity 0 (!npn4->perm #x24 npn)))
                                                  truth)
                                                 new-npn4arr)))))
     :hints (("goal" :induct t
              :in-theory (disable npn4-truth-value-of-identity)))
     :rule-classes nil))

  (defret index-bound-of-record-npn4-perms
    (implies (and (member-equal #x24 perms)
                  (equal (nfix truth1) (truth4-fix truth)))
             (not (equal 0 (maybe-npn4-fix (nth truth1 new-npn4arr)))))
    :hints (("goal" :use index-bound-of-record-npn4-perms-lemma)))

  (defret npn4arr-indices-bounded-of-record-npn4-perms
    (implies (and (npn4arr-indices-bounded bound npn4arr)
                  (< (npn4->truth-idx npn) (nfix bound)))
             (npn4arr-indices-bounded bound new-npn4arr))))

(defun-sk npn4arr-correct (npn4arr truth4arr)
  (forall idx
          (implies (< (nfix idx) 65536)
                   (b* ((val (nth idx npn4arr)))
                     (and (not (equal 0 (maybe-npn4-fix val)))
                          (b* (((npn4 val)))
                            (equal (npn4-truth-value val (nth val.truth-idx truth4arr)) (nfix idx)))))))
  :rewrite :direct)

(in-theory (disable npn4arr-correct))



    
    

(define record-all-npn4-perms ((n natp)
                               (canonical-count natp)
                               npn4arr
                               truth4arr)
  :guard (and (<= n (ash 1 16))
              (<= canonical-count n)
              (<= (ash 1 16) (npn4s-length npn4arr)))
  :measure (nfix (- (ash 1 16) (nfix n)))
  :returns (mv (final-count natp :rule-classes :type-prescription)
               new-npn4arr new-truth4arr)
  :guard-hints (("goal" :in-theory (enable unsigned-byte-p)))
  (b* (((when (mbe :logic (zp (- (ash 1 16) (nfix n)))
                   :exec (eql n (ash 1 16))))
        (b* ((truth4arr (maybe-grow-truth4arr canonical-count truth4arr)))
          (mv (lnfix canonical-count)
              npn4arr
              truth4arr)))
       ((unless (eql 0 (get-npn4 n npn4arr)))
        (record-all-npn4-perms (1+ (lnfix n)) canonical-count npn4arr truth4arr))
       (truth4arr (maybe-grow-truth4arr (1+ (lnfix canonical-count)) truth4arr))
       (truth4arr (set-truth4 canonical-count (lnfix n) truth4arr))
       (npn4arr (record-npn4-perms *all-perms4* (make-npn4 :truth-idx (lnfix canonical-count))
                                   (lnfix n) npn4arr)))
    (record-all-npn4-perms (1+ (lnfix n)) (1+ (lnfix canonical-count)) npn4arr truth4arr))
  ///
  (defret length-of-record-all-npn4-perms
    (implies (<= (ash 1 16) (len npn4arr))
             (equal (len new-npn4arr) (len npn4arr))))


  (local (defthm truth-idx-fix-when-less-than-65536
           (implies (and (< x 65536)
                         (natp x))
                    (equal (truth-idx-fix x)
                           x))
           :hints(("Goal" :in-theory (enable truth-idx-fix
                                             unsigned-byte-p)))))

  (defret record-all-npn4-perms-preserves-partly-correct
    (implies (and (npn4arr-partly-correct npn4arr truth4arr)
                  (npn4arr-indices-bounded canonical-count npn4arr)
                  (<= (nfix canonical-count) (nfix n)))
             (npn4arr-partly-correct new-npn4arr new-truth4arr)))

  (defret record-all-npn4-perms-truth4arr-len-increasing
    (<= (len truth4arr) (len new-truth4arr))
    :rule-classes :linear)

  (local (defret len-update-nth-increasing
           (<= (len x) (len (update-nth n val x)))
           :rule-classes :linear))

  (local (in-theory (disable len-update-nth)))

  (defret record-all-npn4-perms-final-count-lower-bound
    (<= (nfix canonical-count) final-count)
    :rule-classes :linear)

  (defret record-all-npn4-perms-indices-bounded
    (implies (and (npn4arr-indices-bounded bound npn4arr)
                  (<= (nfix canonical-count) (nfix n))
                  (<= final-count (nfix bound)))
             (npn4arr-indices-bounded bound new-npn4arr)))


  (defret index-bound-preserved-of-record-all-npn4-perms
    (implies (not (equal 0 (maybe-npn4-fix (nth k npn4arr))))
             (equal (nth k new-npn4arr)
                    (nth k npn4arr))))

  (defret truth4arr-length-sufficient-of-record-all-npn4-perms
    (<= final-count (len new-truth4arr))
    :rule-classes :linear)

  (defret indices-bound-of-record-all-npn4-perms
    (implies (and (<= (nfix n) (nfix i))
                  (< (nfix i) 65536))
             (not (equal (maybe-npn4-fix (nth i new-npn4arr)) 0)))
    :hints (("goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defret npn4arr-correct-of-record-all-npn4-perms
    (implies (and (equal n 0) (equal canonical-count 0)
                  (npn4arr-partly-correct npn4arr truth4arr)
                  (npn4arr-indices-bounded 0 npn4arr))
             (npn4arr-correct new-npn4arr new-truth4arr))
    :hints(("Goal" :in-theory (disable record-all-npn4-perms))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause))))))))

(defun-sk npn4arr-indices-all-bound (npn4arr)
  (forall n
          (implies (< (nfix n) #x10000)
                   (not (equal (maybe-npn4-fix (nth n npn4arr)) 0))))
  :rewrite :direct)

(in-theory (disable npn4arr-indices-all-bound))

(define record-all-npn4-perms-top (npn4arr truth4arr)
  :returns (mv canonical-count
               new-npn4arr new-truth4arr)
  (b* ((npn4arr (resize-npn4s 0 npn4arr))
       (npn4arr (resize-npn4s (ash 1 16) npn4arr))
       (truth4arr (resize-truth4s 0 truth4arr))
       (truth4arr (resize-truth4s 222 truth4arr)))
    (record-all-npn4-perms 0 0 npn4arr truth4arr))
  ///
  (local (include-book "std/lists/resize-list" :dir :system))

  (local (in-theory (disable (record-all-npn4-perms)
                             resize-list
                             (resize-npn4s$a)
                             (resize-npn4s)
                             (resize-truth4s$a)
                             (resize-truth4s)
                             (resize-list)
                             acl2::resize-list-when-atom)))

  (defret natp-canonical-count-of-record-all-npn4-perms-top
    (natp canonical-count)
    :rule-classes :type-prescription)

  (defret truth4arr-length-of-record-all-npn4-perms-top
    (<= canonical-count (len new-truth4arr))
    :rule-classes :linear)

  (defret length-of-record-all-npn4-perms-top
    (equal (len new-npn4arr) 65536))

  (local (defthm npn4arr-partly-correct-of-resize-empty
           (npn4arr-partly-correct (resize-list nil n 0) truth4arr)
           :hints (("goal" :expand ((npn4arr-partly-correct (resize-list nil n 0) truth4arr))))))

  (local (defthm npn4arr-indices-bounded-of-resize-empty
           (npn4arr-indices-bounded bound (resize-list nil n 0))
           :hints (("goal" :expand ((npn4arr-indices-bounded bound (resize-list nil n 0)))))))

  (defret npn4arr-indices-bounded-of-record-all-npn4-perms-top
    (npn4arr-indices-bounded canonical-count new-npn4arr))

  (defret npn4arr-correct-of-record-all-npn4-perms-top
    (npn4arr-correct new-npn4arr new-truth4arr))

  (defret indices-bound-of-record-all-npn4-perms-top
    (implies (and (< (nfix i) 65536))
             (not (equal (maybe-npn4-fix (nth i new-npn4arr)) 0)))
    :hints (("goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defret npn4arr-indices-all-bound-of-record-all-npn4-perms-top
    (npn4arr-indices-all-bound new-npn4arr)
    :hints (("goal" :in-theory (enable npn4arr-indices-all-bound)))))


;; (define collect-norm-truths ((n natp)
;;                                    npn4arr)
;;   :guard (<= n (npn4s-length npn4arr))
;;   (b* (((when (zp n)) nil)
;;        (n (1- n))
;;        (rest (collect-norm-truths n npn4arr))
;;        (look (get-npn4 n npn4arr))
;;        ((when (eql look 0))
;;         (raise "error -- uninitialized entry"))
;;        ((npn4 look))
;;        (look (hons-get look.truth rest))
;;        ((when look) rest))
;;     (hons-acons look.truth t rest)))



(defsection perm4-rev-indices
  (local (set-default-hints
          '('(:in-theory (enable index-swap perm4-index-list)
              :expand ((:free (n perm x) (index-perm-rev n perm x 4))
                       (:free (n perm x) (index-perm n perm x 4)))))))

  (define perm4-rev-index0 ((x perm4p))
    :enabled t
    :inline t
    (mbe :logic (index-perm-rev 0 (perm4-index-list x) 0 4)
         :exec (perm4-idx0 x)))
  
  (define perm4-rev-index1 ((x perm4p))
    :enabled t
    :inline t
    (mbe :logic (index-perm-rev 0 (perm4-index-list x) 1 4)
       :exec (b* (((the (unsigned-byte 2) idx1) (perm4-idx1 x)))
               (if (eql idx1 (the (unsigned-byte 2) (perm4-idx0 x))) 0 idx1))))

  (define perm4-rev-index2 ((x perm4p))
    :enabled t
    :inline t
    (mbe :logic (index-perm-rev 0 (perm4-index-list x) 2 4)
       :exec (b* (((the (unsigned-byte 2) idx2) (perm4-idx2 x))
                  ((the (unsigned-byte 2) idx0) (perm4-idx0 x)))
               (if (eql idx2 (the (unsigned-byte 2) (perm4-idx1 x)))
                   (if (eql idx0 1) 0 1)
                 (if (eql idx0 idx2) 0 idx2)))))

  (define perm4-rev-index3 ((x perm4p))
    :enabled t
    :inline t
    (mbe :logic (index-perm-rev 0 (perm4-index-list x) 3 4)
         :exec (b* (((the (unsigned-byte 2) idx1) (perm4-idx1 x))
                    ((the (unsigned-byte 2) idx0) (perm4-idx0 x)))
                 (if (eql (the (unsigned-byte 2) (perm4-idx2 x)) 3)
                     (if (eql idx1 2)
                         (if (eql idx0 1) 0 1)
                       (if (eql idx0 2) 0 2))
                   (if (eql idx1 3)
                       (if (eql idx0 1) 0 1)
                     (if (eql idx0 3) 0 3))))))

  (define perm4-rev-index ((n natp) (x perm4p))
    :enabled t
    :inline t
    :guard (< n 4)
    (mbe :logic (index-perm-rev 0 (perm4-index-list x) n 4)
         :exec (case n
                 (0 (perm4-rev-index0 x))
                 (1 (perm4-rev-index1 x))
                 (2 (perm4-rev-index2 x))
                 (t (perm4-rev-index3 x)))))


  
  (define perm4-perm-index0 ((x perm4p))
    :enabled t
    :inline t
    (mbe :logic (index-perm 0 (perm4-index-list x) 0 4)
         :exec ;; (b* ((k (perm4-idx0 x))
               ;;      (k (if (eql k 1)
               ;;             (perm4-idx1 x)
               ;;           (if (eql k (perm4-idx1 x))
               ;;               1
               ;;             k))))
               ;;   (if (eql k 2)
               ;;       (perm4-idx2 x)
               ;;     (if (eql k (perm4-idx2 x))
               ;;         2
               ;;       k)))
         (b* (((the (unsigned-byte 2) idx0) (perm4-idx0 x))
              ((the (unsigned-byte 2) idx1) (perm4-idx1 x)))
           (cond ((eql idx0 0) 0)
                 ((eql idx1 idx0) 1)
                 (t (b* ((k (if (eql idx0 1)
                                idx1
                              idx0)))
                      (if (eql k (the (unsigned-byte 2) (perm4-idx2 x)))
                          2
                        3)))))))
  
  (define perm4-perm-index1 ((x perm4p))
    :enabled t
    :inline t
    (mbe :logic (index-perm 0 (perm4-index-list x) 1 4)
         :exec ;; (b* ((k (if (eql (perm4-idx0 x) 1) 0 1))
         ;;      (k (if (eql k 1)
         ;;               (perm4-idx1 x)
         ;;           (if (eql k (perm4-idx1 x))
         ;;               1
         ;;             k))))
         ;;   (if (eql k 2)
         ;;         (perm4-idx2 x)
         ;;       (if (eql k (perm4-idx2 x))
         ;;           2
         ;;         k)))
         (b* (((the (unsigned-byte 2) idx1) (perm4-idx1 x)))
           (cond ((eql (the (unsigned-byte 2) (perm4-idx0 x)) 1) 0)
                 ((eql idx1 1) 1)
                 ;; (t 
                 ;; x is idx1 going in,
                 ;; both idx1 and idx2 must be 2 or 3
                 ;;   idx2 \ idx1   2   3
                 ;;    2            2   3
                 ;;    3            3   2
                 ((eql idx1
                       (the (unsigned-byte 2) (perm4-idx2 x))) 2)
                 (t 3)
                 ;; ((eql (perm4-idx1 x) 2) (perm4-idx2 x))
                 ;; (t (perm4-idx1 x))
                 ))
         ))

  (define perm4-perm-index2 ((x perm4p))
    :enabled t
    :inline t
    (mbe :logic (index-perm 0 (perm4-index-list x) 2 4)
       :exec ;; (b* ((k (if (eql (perm4-idx0 x) 2) 0 2))
             ;;      (k (if (eql k (perm4-idx1 x))
             ;;             1
             ;;           k)))
             ;;   (if (eql k 2)
             ;;       (perm4-idx2 x)
             ;;     (if (eql k (perm4-idx2 x))
             ;;         2
             ;;       k)))
       (cond ((eql (the (unsigned-byte 2) (perm4-idx0 x)) 2) 0)
             ((eql (the (unsigned-byte 2) (perm4-idx1 x)) 2) 1)
             (t (the (unsigned-byte 2) (perm4-idx2 x))))
       ))

  (define perm4-perm-index3 ((x perm4p))
    :enabled t
    :inline t
    (mbe :logic (index-perm 0 (perm4-index-list x) 3 4)
         :exec ;; (b* ((k (if (eql (perm4-idx0 x) 3) 0 3))
               ;;      (k (if (eql k (perm4-idx1 x))
               ;;             1
               ;;           k)))
               ;;   (if (eql k (perm4-idx2 x))
               ;;       2
               ;;     k))
         (cond ((eql (the (unsigned-byte 2) (perm4-idx0 x)) 3) 0)
               ((eql (the (unsigned-byte 2) (perm4-idx1 x)) 3) 1)
               ((eql (the (unsigned-byte 2) (perm4-idx2 x)) 3) 2)
               (t 3))))

  (define perm4-index ((n natp) (x perm4p))
    :enabled t
    :inline t
    :guard (< n 4)
    (mbe :logic (index-perm 0 (perm4-index-list x) n 4)
         :exec (case n
                 (0 (perm4-perm-index0 x))
                 (1 (perm4-perm-index1 x))
                 (2 (perm4-perm-index2 x))
                 (t (perm4-perm-index3 x)))))

)
