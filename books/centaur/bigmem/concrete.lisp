; Big Memory Model
; Copyright (C) 2021 Centaur Technology
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

;   Original Author(s): Shilpi Goel <shilpi@centtech.com>

(in-package "BIGMEM")
(include-book "centaur/bitops/part-select" :dir :system)
(include-book "std/util/def-bound-theorems" :dir :system)
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ----------------------------------------------------------------------

(defconst *page-offset-width*
  ;; LSB *page-offset-width* bits of the address are used to index
  ;; into a selected page.
  20)

(defconst *num-page-entries*
  (expt 2 *page-offset-width*))

(defconst *page-entry-width*
  ;; A page mimics a 2^*num-page-entries* chunk of
  ;; *page-entry-width*-addressable memory.
  8)

(defconst *level-offset-width*
  ;; *level-offset-width* bits of the address are used to index into a
  ;; selected level.
  22)

(defconst *num-level-entries*
  (expt 2 *level-offset-width*))

(define get-i1 ((addr :type (unsigned-byte 64)))
  :inline t
  :returns (i1 (unsigned-byte-p *level-offset-width* i1))
  (mbe :logic (loghead 22 (part-select addr :low 42 :width 22))
       :exec (part-select addr :low 42 :width 22))
  ///
  (std::defthm-unsigned-byte-p get-i1-unsigned-byte-lemma
                               :bound *level-offset-width*
                               :concl (get-i1 addr)
                               :gen-type t
                               :gen-linear t))

(define get-i2 ((addr :type (unsigned-byte 64)))
  :inline t
  :returns (i2 (unsigned-byte-p *level-offset-width* i2))
  (mbe :logic (loghead 22 (part-select addr :low 20 :width 22))
       :exec (part-select addr :low 20 :width 22))
  ///
  (std::defthm-unsigned-byte-p get-i2-unsigned-byte-lemma
                               :bound *level-offset-width*
                               :concl (get-i2 addr)
                               :gen-type t
                               :gen-linear t))

(define get-offset ((addr :type (unsigned-byte 64)))
  :inline t
  :returns (offset (unsigned-byte-p *page-offset-width* offset))
  (mbe :logic (loghead 20 (part-select addr :low 0 :width 20))
       :exec (part-select addr :low 0 :width 20))
  ///
  (std::defthm-unsigned-byte-p get-offset-unsigned-byte-lemma
                               :bound *page-offset-width*
                               :concl (get-offset addr)
                               :gen-type t
                               :gen-linear t))

;; ----------------------------------------------------------------------

(local
 (defthm update-nth-thm-1
   (equal (update-nth i v2 (update-nth i v1 x))
          (update-nth i v2 x))))

(local
 (defthm update-nth-thm-2
   (implies (and (integerp i1)
                 (<= 0 i1)
                 (integerp i2)
                 (<= 0 i2)
                 (not (equal i1 i2)))
            (equal (update-nth i2 v2 (update-nth i1 v1 x))
                   (update-nth i1 v1 (update-nth i2 v2 x))))))

(local
 (defthm update-nth-thm-3
   (implies (and (integerp n)
                 (<= 0 n)
                 (< n (len x))
                 (integerp i)
                 (<= 0 i)
                 (< i (len (nth n x))))
            (equal (update-nth n
                               (update-nth i (nth i (nth n x))
                                           (nth n x))
                               x)
                   x))))

(local
 (defthm update-nth-thm-4
   (implies (and (integerp i)
                 (<= 0 i)
                 (< i (len x)))
            (equal (update-nth i (nth i x) x)
                   x))))

(local
 (defthm update-nth-thm-5
   (implies (and (equal (nth n x) e)
                 (natp n)
                 (< n (len x)))
            (equal (update-nth n e x) x))))

(local
 (defthm len-of-resize-list
   (equal (len (resize-list lst n default-value))
          (nfix n))))

(local
 (defun nth-resize-list-induction (i lst n default-value)
   (declare (ignorable i lst n default-value))
   (if (posp n)
       (nth-resize-list-induction (1- i)
                                  (if (atom lst) lst (cdr lst))
                                  (1- n)
                                  default-value)
     nil)))

(local
 (defthm nth-resize-list
   (implies (and (< i n) (natp i) (natp n))
            (equal (nth i (resize-list lst n default))
                   (if (< i (len lst))
                       (nth i lst)
                     default)))
   :hints (("Goal" :in-theory (e/d (resize-list nth) ())
            :induct (nth-resize-list-induction i lst n default-value)))))

(local (in-theory (e/d () (unsigned-byte-p nth (nth) (tau-system)))))

;; ----------------------------------------------------------------------

(make-event
 `(defstobj page
    (pg :type (array (unsigned-byte ,*page-entry-width*) (0))
        :initially 0
        :resizable t)
    (pg_vld :type bit :initially 0)
    :inline t
    :non-executable t
    :non-memoizable t))

(defstobj l1
  (pages :type (array page (0)) :resizable t)
  (pages_vld :type bit :initially 0)
  :inline t
  :non-executable t
  :non-memoizable t)

(make-event
 `(defstobj mem$c
    (level1 :type (array l1 (,*num-level-entries*))
            :resizable nil)
    :inline t
    :non-memoizable t))

;; ----------------------------------------------------------------------

(define good-pagep (page)
  :enabled t
  (and (pagep page)
       (if (equal (pg_vld page) 0)
           (equal (pg-length page) 0)
         (equal (pg-length page) *num-page-entries*)))
  ///
  (defthm good-pagep-and-offset
    (implies (and (unsigned-byte-p *page-offset-width* offset)
                  (good-pagep page))
             (iff (< offset (pg-length page))
                  (equal (pg_vld page) 1)))))

(define write-to-page ((offset   :type (unsigned-byte 20))
                       (val      :type (unsigned-byte 8))
                       (page      good-pagep))
  :inline nil
  :returns (new-page)
  (b* ((offset (mbe :logic (loghead 20 offset) :exec (the (unsigned-byte 20) offset)))
       (val    (mbe :logic (loghead 8 val)     :exec (the (unsigned-byte 8) val)))
       (page   (if (mbe :logic (< offset (pg-length page))
                        :exec (equal (the (unsigned-byte 1) (pg_vld page)) 1))
                   page
                 (b* ((page (update-pg_vld 1 page))
                      (page (resize-pg *num-page-entries* page)))
                   page)))
       (page (update-pgi offset val page)))
    page)
  ///

  (defthm pgp-update-nth
    (implies (and (< offset (len pg))
                  (unsigned-byte-p 8 val)
                  (pgp pg))
             (pgp (update-nth offset val pg)))
    :hints (("Goal" :induct (update-nth offset val pg)
             :in-theory (e/d (update-nth) ()))))

  (defthm pgp-resize-list
    (implies (and (unsigned-byte-p 8 default-val)
                  (pgp pg))
             (pgp (resize-list pg n default-val))))

  (defret pagep-of-<fn>
    (implies (pagep page)
             (pagep new-page)))

  (defret good-pagep-of-<fn>
    (implies (good-pagep page)
             (good-pagep new-page))))

(defthm write-to-page-shadow-writes
  (equal (write-to-page offset val2 (write-to-page offset val1 page))
         (write-to-page offset val2 page))
  :hints (("Goal" :in-theory (e/d (write-to-page) ()))))

(define read-from-page ((offset :type (unsigned-byte 20))
                        (page   good-pagep))
  :inline nil
  :prepwork
  ((defthm nth-pgp
     (implies (and (< offset (len pg))
                   (natp offset)
                   (pgp pg))
              (unsigned-byte-p 8 (nth offset pg)))
     :hints (("Goal" :induct (nth offset pg)
              :in-theory (e/d (nth) ())))))

  :returns (val)
  (b* ((offset (mbe :logic (loghead 20 offset) :exec (the (unsigned-byte 20) offset))))
    (if (mbe :logic (< offset (pg-length page))
             :exec (equal (the (unsigned-byte 1) (pg_vld page)) 1))
        (the (unsigned-byte 8) (pgi offset page))
      ;; Default memory value.
      0))
  ///

  (defret unsigned-byte-p-of-<fn>
    (implies (pagep page)
             (unsigned-byte-p 8 val))))

(defthm read-write-page
  (equal (read-from-page offset1 (write-to-page offset2 val page))
         (if (equal (loghead 20 offset1) (loghead 20 offset2))
             (loghead 8 val)
           (read-from-page offset1 page)))
  :hints (("Goal" :in-theory (e/d (read-from-page
                                   write-to-page)
                                  (pagep)))))

(local (in-theory (e/d () (good-pagep))))

;; ----------------------------------------------------------------------

(define good-pagesp ((i natp)
                     l1)
  :guard (<= i (pages-length l1))
  :enabled t
  (if (zp i)
      t
    (b* ((new-i (1- i))
         (okp (stobj-let
               ((page (pagesi new-i l1)))
               (okp)
               (good-pagep page)
               okp)))
      (and okp (good-pagesp new-i l1))))
  ///
  (defthm good-pagep-nth-of-good-pagesp
    (implies (and (< page-num i)
                  (good-pagesp i l1)
                  (natp page-num) (natp i))
             (good-pagep (nth page-num (nth *pagesi* l1))))))

(define simp-good-pagesp ((i natp) (pages pagesp))
  :verify-guards nil
  :non-executable t
  :enabled t
  (if (zp i)
      t
    (b* ((new-i (1- i)))
      (and (good-pagep (nth new-i pages))
           (simp-good-pagesp new-i pages))))
  ///
  (defthmd simp-good-pagesp-and-good-pagesp
    (equal (good-pagesp i l1)
           (simp-good-pagesp i (nth *pagesi* l1)))))

(define good-l1p (l1)
  :enabled t
  (and (l1p l1)
       (if (equal (pages_vld l1) 0)
           (equal (pages-length l1) 0)
         (equal (pages-length l1) *num-level-entries*))
       (good-pagesp (pages-length l1) l1))
  ///
  (defthm good-l1p-and-page-num
    (implies (and (unsigned-byte-p *level-offset-width* page-num)
                  (good-l1p l1))
             (iff (< page-num (pages-length l1))
                  (equal (pages_vld l1) 1)))))

(define write-to-l1 ((i2       :type (unsigned-byte 22))
                     (offset   :type (unsigned-byte 20))
                     (val      :type (unsigned-byte 8))
                     (l1       good-l1p))
  :inline nil
  :returns (new-l1)
  (b* ((i2 (mbe :logic (loghead 22 i2) :exec (the (unsigned-byte 22) i2)))
       (offset   (mbe :logic (loghead 20 offset)   :exec (the (unsigned-byte 20) offset)))
       (val      (mbe :logic (loghead 8 val)       :exec (the (unsigned-byte 8) val)))
       (l1       (if (mbe :logic (< i2 (pages-length l1))
                          :exec (equal (the (unsigned-byte 1) (pages_vld l1)) 1))
                     l1
                   (b* ((l1 (update-pages_vld 1 l1))
                        (l1 (resize-pages *num-level-entries* l1)))
                     l1))))
    (stobj-let
     ((page (pagesi i2 l1)))
     (page)
     (write-to-page offset val page)
     l1))

  ///

  (defthm pagep-of-nth-pagesp
    (implies (and (< i (len pages))
                  (natp i)
                  (pagesp pages))
             (pagep (nth i pages)))
    :hints (("Goal" :in-theory (e/d (nth (nth)) ())
             :induct (pagesp (nth i pages)))))

  (defthm pagesp-resize-list
    (implies (and (pagep default-val)
                  (pagesp pages))
             (pagesp (resize-list pages n default-val))))

  (defthm pagesp-update-nth
    (implies (and (< i2 (len pages))
                  (pagep page)
                  (pagesp pages))
             (pagesp (update-nth i2 page pages)))
    :hints (("Goal" :induct (update-nth i2 page pages)
             :in-theory (e/d (update-nth) ()))))

  (defret l1p-of-<fn>
    (implies (l1p l1)
             (l1p new-l1)))

  (defthm simp-good-pagesp-update-nth
    (implies (and (good-pagep page)
                  (simp-good-pagesp n pages))
             (simp-good-pagesp n (update-nth i2 page pages)))
    :hints (("goal" :in-theory (e/d (update-nth) ()))))

  (defthm simp-good-pagesp-resize-list
    (implies (and (equal (len pages) 0)
                  (good-pagep default-val))
             (simp-good-pagesp n (resize-list pages n default-val)))
    :hints (("Goal"
             :induct (nth-resize-list-induction n pages n default-value)
             :in-theory (e/d (nth resize-list) ()))))

  (local (in-theory (e/d (simp-good-pagesp-and-good-pagesp) ())))

  (defret good-l1p-of-<fn>
    (implies (good-l1p l1)
             (good-l1p new-l1))))

(defthm write-to-l1-shadow-writes
  (equal (write-to-l1 i2 offset val1 (write-to-l1 i2 offset val2 l1))
         (write-to-l1 i2 offset val1 l1))
  :hints (("Goal" :in-theory (e/d (write-to-l1) ()))))

(define read-from-l1 ((i2       :type (unsigned-byte 22))
                      (offset   :type (unsigned-byte 20))
                      (l1 good-l1p))
  :guard-hints (("Goal" :do-not-induct t))
  :inline nil
  :returns (val (unsigned-byte-p 8 val) :hyp (l1p l1))
  (b* ((i2 (mbe :logic (loghead 22 i2) :exec (the (unsigned-byte 22) i2)))
       (offset   (mbe :logic (loghead 20 offset)   :exec (the (unsigned-byte 20) offset)))
       ((unless (mbe :logic (< i2 (pages-length l1))
                     :exec (equal (the (unsigned-byte 1) (pages_vld l1)) 1)))
        ;; Default memory value.
        0))
    (stobj-let
     ((page (pagesi i2 l1)))
     (val)
     (read-from-page offset page)
     val)))

(local
 (defthm read-from-page-create-page
   (equal (read-from-page offset (create-page)) 0)
   :hints (("Goal" :in-theory (e/d (read-from-page) ())))))

(defthm read-write-l1
  (equal (read-from-l1 page-num1 offset1 (write-to-l1 page-num2 offset2 val l1))
         (if (and (equal (loghead 22 page-num1) (loghead 22 page-num2))
                  (equal (loghead 20 offset1)   (loghead 20 offset2)))
             (loghead 8 val)
           (read-from-l1 page-num1 offset1 l1)))
  :hints (("Goal" :in-theory (e/d (read-from-l1
                                   write-to-l1)
                                  (create-page
                                   pagesp)))))

(in-theory (e/d () (good-pagesp good-l1p)))

;; ----------------------------------------------------------------------

(define good-level1p ((i natp)
                      mem$c)
  :guard (<= i (level1-length mem$c))
  :enabled t
  (if (zp i)
      t
    (b* ((new-i (1- i))
         (okp (stobj-let
               ((l1 (level1i new-i mem$c)))
               (okp)
               (good-l1p l1)
               okp)))
      (and okp (good-level1p new-i mem$c))))
  ///
  (defthm good-l1p-nth-of-good-level1p
    (implies (and (good-level1p i l1)
                  (< i1 i) (natp i1) (natp i))
             (good-l1p (nth i1 (nth *level1i* l1))))))

(define simp-good-level1p ((i natp) (level1 level1p))
  :verify-guards nil
  :non-executable t
  :enabled t
  (if (zp i)
      t
    (b* ((new-i (1- i)))
      (and (good-l1p (nth new-i level1))
           (simp-good-level1p new-i level1))))
  ///
  (defthmd simp-good-level1p-and-good-level1p
    (equal (good-level1p i mem$c)
           (simp-good-level1p i (nth *level1i* mem$c)))))

(define good-mem$cp (mem$c)
  :enabled t
  (and (mem$cp mem$c)
       (good-level1p (level1-length mem$c) mem$c))
  ///
  (defthm good-mem$cp-and-i1
    (implies (and (unsigned-byte-p *level-offset-width* i1)
                  (good-mem$cp mem$c))
             (< i1 (level1-length mem$c)))
    :rule-classes :linear))

(define write-mem$c ((addr :type (unsigned-byte 64))
                     (val  :type (unsigned-byte 8))
                     (mem$c  good-mem$cp))
  :returns (new-mem$c)
  (b* ((i1       (the (unsigned-byte 22) (get-i1 addr)))
       (i2       (the (unsigned-byte 22) (get-i2 addr)))
       (offset   (the (unsigned-byte 20) (get-offset addr))))
    (stobj-let
     ;; Index into the i1-th l1 in level1.
     ((l1 (level1i i1 mem$c)))
     (l1)
     (write-to-l1 i2 offset (the (unsigned-byte 8) val) l1)
     mem$c))

  ///

  (defthm l1p-of-nth-level1p
    (implies (and (< i (len level1))
                  (natp i)
                  (level1p level1))
             (l1p (nth i level1)))
    :hints (("Goal" :in-theory (e/d (nth (nth)) ())
             :induct (l1p (nth i level1)))))

  (defthm level1p-resize-list
    (implies (and (l1p default-val)
                  (level1p level1))
             (level1p (resize-list level1 n default-val))))

  (defthm level1p-update-nth
    (implies (and (< i1 (len level1))
                  (level1p level1)
                  (l1p l1))
             (level1p (update-nth i1 l1 level1)))
    :hints (("Goal" :induct (update-nth i1 l1 level1)
             :in-theory (e/d (update-nth) ()))))

  (defret mem$cp-of-<fn>
    (implies (mem$cp mem$c)
             (mem$cp new-mem$c)))

  (defthm simp-good-level1p-update-nth
    (implies (and (good-l1p l1)
                  (simp-good-level1p n level1))
             (simp-good-level1p n (update-nth i1 l1 level1)))
    :hints (("goal" :in-theory (e/d (update-nth) ()))))

  (local (in-theory (e/d (simp-good-level1p-and-good-level1p) ())))

  (local
   (defthm good-l1p-nth-of-good-level1p-alt
     (implies (and (good-level1p *num-level-entries* l1)
                   (unsigned-byte-p *level-offset-width* i1))
              (good-l1p (nth i1 (nth *level1i* l1))))
     :hints (("Goal" :in-theory (e/d () (good-l1p-nth-of-good-level1p))
              :use ((:instance good-l1p-nth-of-good-level1p
                               (i1 i1) (i *num-level-entries*)))))))

  (defret good-mem$cp-of-<fn>
    (implies (good-mem$cp mem$c)
             (good-mem$cp new-mem$c))))

(defthm write-mem$c-shadow-writes
  (equal (write-mem$c addr val2 (write-mem$c addr val1 mem$c))
         (write-mem$c addr val2 mem$c))
  :hints (("Goal" :in-theory (e/d (write-mem$c) (l1p)))))

(define read-mem$c ((addr :type (unsigned-byte 64))
                    (mem$c  good-mem$cp))
  :returns (val (unsigned-byte-p 8 val) :hyp (mem$cp mem$c))
  (b* ((i1       (the (unsigned-byte 22) (get-i1 addr)))
       (i2       (the (unsigned-byte 22) (get-i2 addr)))
       (offset   (the (unsigned-byte 20) (get-offset addr))))
    (stobj-let
     ;; Index into the i1-th l1 in level1.
     ((l1 (level1i i1 mem$c)))
     (val)
     (read-from-l1 i2 offset l1)
     val)))

(local
 (encapsulate
   ()

   (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

   (defthm addr-parts-equal
     (iff (equal (loghead 64 addr1) (loghead 64 addr2))
          (and (equal (get-i1 addr1) (get-i1 addr2))
               (equal (get-i2 addr1) (get-i2 addr2))
               (equal (get-offset addr1) (get-offset addr2))))
     :hints (("Goal" :in-theory (e/d* (get-i1
                                       get-i2
                                       get-offset
                                       loghead logtail mod ifix)
                                      ()))))))

(defthm read-write-mem$c
  (equal (read-mem$c addr1 (write-mem$c addr2 val mem$c))
         (if (equal (loghead 64 addr1) (loghead 64 addr2))
             (loghead 8 val)
           (read-mem$c addr1 mem$c)))
  :hints (("Goal" :in-theory (e/d (read-mem$c write-mem$c)
                                  (l1p)))))

(in-theory (e/d () (good-level1p good-mem$cp mem$cp)))

;; ----------------------------------------------------------------------

;; (write-mem #ux0f0e0d0c_01020304 #xaa mem)
;; (read-mem #ux0f0e0d0c_01020304 mem)
;; (read-mem 0 mem)
;; (write-mem 0 #xFF mem)

;; ----------------------------------------------------------------------

#||

(local
 (define init-mem$c-region ((n :type (unsigned-byte 50))
                            (val :type (unsigned-byte 8))
                            (mem$c good-mem$cp))
   :prepwork ((local (in-theory (e/d (unsigned-byte-p) ()))))
   (if (zp n)
       mem$c
     (b* ((val (the (unsigned-byte 8) (if (< val #xFE) (1+ val) 0)))
          (mem$c (write-mem$c n val mem$c)))
       (init-mem$c-region (the (unsigned-byte 50) (1- n)) val mem$c)))))

;; (profile 'write-mem)
;; (profile 'write-to-l1)
;; (profile 'write-to-page)

;; (clear-memoize-statistics)

(time$ (init-mem-region (1- (expt 2 20)) 0 mem))
; (ACL2::EV-REC ACL2::*RETURN-LAST-ARG3* ...) took
; 0.86 seconds realtime, 0.86 seconds runtime
; (235,929,792 bytes allocated).
<mem>

(time$ (write-mem 0 #xFF mem))
; (ACL2::EV-REC ACL2::*RETURN-LAST-ARG3* ...) took
; 1.05 seconds realtime, 1.06 seconds runtime
; (235,929,760 bytes allocated).
<mem>

(time$ (init-mem$c-region (1- (expt 2 27)) 0 mem$c))
; (ACL2::EV-REC ACL2::*RETURN-LAST-ARG3* ...) took
; 5.37 seconds realtime, 5.37 seconds runtime
; (369,103,008 bytes allocated).
<mem>

(GOOD-MEM$CP
 Calls                                                                        1
 Time of all outermost calls                                               0.26
 Time per call                                                             0.26
 To GOOD-LEVEL1P                             1.00E+0 calls took 2.62E-1; 100.0%
 To self/unprofiled functions                                   1.15E-5; <0.01%
 From other functions                        1.00E+0 calls took 2.62E-1; 100.0%)
(GOOD-LEVEL1P
 Calls                                                                        1
 Time of all outermost calls                                               0.26
 Time per call                                                             0.26
 To GOOD-L1P                                  4.19E+6 calls took 1.40E-1; 53.5%
 To self/unprofiled functions                                    1.22E-1; 46.5%
 From GOOD-MEM$CP                            1.00E+0 calls took 2.62E-1; 100.0%)
(GOOD-L1P
 Calls                                                                  4.19E+6
 Time of all outermost calls                                               0.14
 Time per call                                                          3.35E-8
 From GOOD-LEVEL1P                           4.19E+6 calls took 1.40E-1; 100.0%)


(time$ (init-mem-region (1- (expt 2 27)) 0 mem))
; (ACL2::EV-REC ACL2::*RETURN-LAST-ARG3* ...) took
; 4.07 seconds realtime, 4.07 seconds runtime
; (128 bytes allocated).
<mem>


;; (memsum)

||#

;; ----------------------------------------------------------------------

(defxdoc bigmem-concrete-stobj
  :pkg "BIGMEM"
  :parents (bigmem)
  :short "Concrete stobj set-up corresponding to @('bigmem')'s @('mem') stobj"
  :long
  "<p>The @('mem$c') stobj provides a fast, array-like,
  allocate-on-demand implementation of a @('2^64') byte
  array.</p>

  <p> Here are the definitions of the stobjs involved: </p>

  @(def mem$c)
  @(def l1)
  @(def page)

  <p>Here's how a memory access works. A 64-bit address is split into
  three parts: MSB @('22') bits called @('i1'), then @('22') bits
  called @('i2'), and finally, LSB @('20') bits called
  @('offset').</p>

  <ul>

   <li><p>@('i1') is used to index into @('level1'); i.e., it gets the
   @('i1')-th @('l1') in @('level1').</p></li>

   <li><p>@('i2') is used to index into the @('pages') field of
   @('l1') obtained above; i.e., it gets the @('i2')-th @('page') from
   @('pages').</p>

  <p>Note that @('pages') is a resizable array; if @('i2') is not less
   than the length of @('pages'), we first resize @('pages') to
   @('2^22') (@('i2') is @('22') bits wide) and then get the newly
   created @('i2')-th @('page').</p>

   <p>The check @(' (< i2 (pages-length l1)) ') has pretty bad
   execution performance, so we optimize this by checking the value of
   @('pages_vld') (a simple scalar field of type @('bit')) instead.
   The default value of @('pages_vld') is @('0'), which corresponds to
   @(' (pages-length l1) == 0 '). Whenever we resize @('pages'), we
   always resize it to @('2^22') elements and then set @('pages_vld')
   to @('1'). In other words, we maintain the invariant that if
   @('pages_vld') is @('0'), then @(' (pages-length l1) ') is @('0'),
   and otherwise it is @('2^22').  Since @('i2') is @('22') bits wide,
   we know that if @('pages_vld') is @('1'), we don't have to resize
   @('pages').</p>

   </li>

   <li><p>@('offset') is used to index into the @('pg') field of
  @('page') obtained above; i.e., it accesses the @('offset')-th byte
  in @('pg').  Note that like @('pages') above, @('pg') is also a
  resizable array and we do the same kind of resizing here that we do
  for @('pages').</p></li>

  </ul>

  <p>A benefit of this set-up is that it does not occupy too much
  memory. At the very beginning, when no memory accesses have
  occurred, @('level1') of @('mem$c') may have @('2^22') elements of
  type @('l1'), but each of those @('l1')s has an array field
  @('pages') of length zero and one scalar bit field. When a memory
  access does happen, we resize @('pages') to @('2^22') @('page')
  elements, each of which has an array field @('pg') of length zero
  and one scalar bit field.  We only allocate @('2^20') bytes for the
  @('pg') in the @('page') selected by @('i2'). Of course, if we read
  from a memory location for which @('pages_vld') or @('pg_vld') is
  @('0'), then we simply return the default value, @('0'), without
  resizing any array fields. Also, if there's spatial locality (i.e.,
  if the memory accesses pertain to addresses which share @('i1')
  and/or @('i2') --- a common enough scenario), this set-up is pretty
  fast because we don't have to resize arrays as often.</p>"

  )

;; ----------------------------------------------------------------------
