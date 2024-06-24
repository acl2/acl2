; Big Memory, Model 2
; Copyright (C) 2024, Intel Corporation

; For development:
; (ld "concrete-21.lisp" :ld-pre-eval-print t)

; Should be removed
; (include-book "misc/disassemble" :dir :system :ttags (:disassemble$))

; Contact
;   Intel Corporation, ACL2 Formal Verification Group
;   1300 South MoPac Expy,  Austin, TX  78746, USA
;   https://www.intel.com/

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

;   Original Author(s): Warren A. Hunt, Jr <warren.hunt@intel.com>

; (in-package "ACL2")
(in-package "BIGMEM")

(include-book "std/util/define"  :dir :system)
(include-book "xdoc/top"         :dir :system)


(defxdoc bigmem-concrete-asymmetric
  :pkg "BIGMEM"
  :parents (acl2::projects)
  :short "A byte memory model that is logically a record but provides
  array-like performance for a (low-address) region of memory and association
  list lookup and update for memory modeled above a certain address limit."

  :long "<p>The @('concrete-asymmetric') library takes its inspriation from the
  @('bigmem') library, but provides a simpler implementation that operates
  faster than @('bigmem') when memory addresses are below some limit and
  operates more slowly when equal to or above this same address limit.  When
  accessing/updating a   An
  intended use of this memory model is to provide a physical-memory model for
  the ACL2 x86-ISA model.</p>

  <p>An obvious application of @('concrete-asymmetric') is to model a byte-wide
  memory; @('bm') can be used as a child STOBJ to define a field representing a
  byte memory in a parent STOBJ that models some machine's state.  See
  @('projects/x86isa/machine/state.lisp') for one such@('bigmem') example.</p>")

(include-book "ordered-alist")
; (local (include-book "ordered-alist"))


; We use !NTH as an alternative name for UPDATE-NTH.

(defmacro !nth (key val l)
 `(update-nth ,key ,val ,l))

(add-macro-fn !nth update-nth)  ;; UPDATE-NTH shown as !NTH


; Four rules relating NTH and !NTH

#|
(defthm nth-!nth
  ;; Read-over-Write; redundant with built-in lemma NTH-UPDATE-NTH
  (equal (nth a1 (!nth a2 v l))
         (if (equal (nfix a1) (nfix a2))
             v
           (nth a1 l))))
|#

(defthm !nth-nth
  ;; Write-over-Read
  ;; A read "off the end" is NIL, but a write extends L
  (implies (and (equal a1 a2)
                (< (nfix a1) (len l)))
           (equal (!nth a1 (nth a2 l) l)
                  l)))

(defthm !nth-!nth-same-address
  ;; Write-over-write; memory reflects last value written to address
  (implies (equal a1 a2)
           (equal (!nth a1 v (!nth a2 w st))
                  (!nth a1 v st))))

(defthm !nth-!nth-different-addresses
  ;; Order of writes to different memory locations makes no difference
  (implies (not (equal (nfix a1) (nfix a2)))
           (equal (!nth a1 v1 (!nth a2 v2 st))
                  (!nth a2 v2 (!nth a1 v1 st)))))

(defthm nth-from-atom
  (implies (atom l)
           (not (nth i l))))

(defthm nth-short-list
  (implies (and (natp i)
                (< (len m) i))
           (equal (nth i m) nil)))



; Define

; (defconst *mem-size* 10)

(defconst *mem-size* (* 6 (expt 2 30))) ; For MEM just below

(defstobj bm
  ;; An array of bytes (8-bit natural numbers)
  (a :type (array (unsigned-byte 8)
                  (*mem-size*)) ; with this length
     :initially 0
     :resizable nil)

  ;; Key-ordered alist of address-byte pairs
  (oal :type (satisfies nat-bytep)
      :initially nil)

  :inline t
  :non-memoizable t
  :renaming
  ((update-ai !ai)
   (a-length al)
   (update-oal !oal)
   ))

(defun bmp-extended (bm)
  "An extension of BMP that relates the two BM fields."
  (declare (xargs :guard t ; (bmp bm)
                  :stobjs bm))
  (and (bmp bm)
       (all-keys-as-big (al bm) (oal bm))))

(defthm ap-forward-to-true-listp
  (implies (ap m)
           (true-listp m))
  :rule-classes :forward-chaining)

(defthm bmp-extended-forward
  (implies (bmp-extended bm)
           (bmp bm))
  :rule-classes :forward-chaining)

(defthm bmp-forward
  (implies (bmp bm)
           (and (true-listp bm)
                (ap (nth 0 bm))
                (equal (len (nth 0 bm)) *mem-size*)
                (oalp (nth 1 bm)))))

(defthm ap-resize-list
  (implies (and (ap m)
                (unsigned-byte-p 8 v))
           (ap (resize-list m i v)))
  :hints
  (("Goal" :in-theory (e/d (resize-list) () ))))

(defthm ap-!nth
  (implies (and (ap m)
                (unsigned-byte-p 8 v)
                (<= i (len m)))
           (ap (!nth i v m)))
  :hints
  (("Goal" :in-theory (e/d (!nth) nil))))

(encapsulate
  ()

  ;; AI Read lemmas

  (local
   (defthm natp-nth-of-ap-type-prescription ; Needed when TAU system engaged?
     (implies (and (ap l)
                   ;; Want (NATP a) because type reasoning only
                   (natp a)
                   ;; Want (FORCE (< a (len x))) because type reasoning only
                   (force (< a (len l))))
              (natp (nth a l)))
     :hints
     (("Goal" ; :induct (nth a l)
              :in-theory (e/d (nth) ())))
     :rule-classes
     ((:type-prescription :typed-term (nth a l)))))

  (defthm ai-type-type-prescription-natp
    ;; For this to "fire", AL and BMP must be disabled.
    (implies (and (bmp bm)
                  (natp a)
                  (< a (al bm)))
             (natp (ai a bm)))
    :rule-classes :type-prescription)

  (defthm ai-type-type-prescription-integerp
    ;; For this to "fire", AL and BMP must be disabled.
    (implies (and (bmp bm)
                  (natp a)
                  (< a (al bm)))
             (integerp (ai a bm)))
    :rule-classes :type-prescription)

  (defthm ai-rewrite
    (implies (and (bmp bm)
                  (natp a)
                  (< a (al bm)))
             (integerp (ai a bm))))

  (local
   (defthm in-range-nth-of-ap
     (implies (and (ap l)
                   (natp a)
                   (< a (len l)))
              (and (<= 0 (nth a l))
                   (< (nth a l) 256)))
     :hints
     (("Goal" :induct (nth a l)
              :in-theory (e/d (nth) ())))))

  (defthm ai-of-bm-is-n08p
    (implies (and (bmp bm)
                  (natp a)
                  (< a (al bm)))
             (and (<= 0 (ai a bm))
                  (< (ai a bm) 256)))
    :hints (("Goal" :cases ((< (nfix a) (al bm)))))
    :rule-classes (:linear :rewrite)))


(encapsulate
  ()

  ;; AI Write lemmas

  (defthm bmp-!ai
    (implies (and (bmp bm)
                  (natp a)
                  (< a (al bm))
                  (unsigned-byte-p 8 v))
             (bmp (!ai a v bm))))

  (defthm al-!ai
    (implies (bmp bm)
             (equal (al (!ai a v bm))
                    (al bm)))))


(encapsulate
  ()

  (defthm ai-!ai
    ;; Read-over-Write
    (equal (ai a1 (!ai a2 v bm))
           (if (equal (nfix (double-rewrite a1))
                      (nfix (double-rewrite a2)))
               v
             (ai a1 bm))))

  (defthm !ai-ai
    ;; Write-over-Read
    (implies (and (bmp bm)
                  (equal a1 a2)
                  (< a1 (al bm)))
             (equal (!ai a1 (ai a2 bm) bm)
                    bm))
    :hints
    (("Goal" :do-not-induct t
             :in-theory (e/d (!nth) (!nth-nth))
             :use ((:instance !nth-nth
                              (a1 a1)
                              (a2 a2)
                              (l (nth *ai* bm)))))))

  (defthm !ai-!ai-same-address
    ;; !ai-over-!ai; memory reflects last value written to address
    (implies (equal (double-rewrite a1)
                    (double-rewrite a2))
             (equal (!ai a1 v (!ai a2 w bm))
                    (!ai a1 v bm))))

  (defthm !ai-!ai-different-addresses
    ;; Update ordering of different memory locations makes no difference
    ;; !!! Warning.  See: LOOP-STOPPER
    (implies (not (equal (nfix (double-rewrite a1))
                         (nfix (double-rewrite a2))))
             (equal (!ai a1 v1 (!ai a2 v2 bm))
                    (!ai a2 v2 (!ai a1 v1 bm))))
    :hints
    (("Goal" :do-not-induct t
             :in-theory (e/d (!nth) (!nth-!nth-different-addresses))
             :use ((:instance !nth-!nth-different-addresses
                              (a1 a1)
                              (v1 v1)
                              (a2 a2)
                              (v2 v2)
                              (st (car bm))))))))


;; OAL Read lemma

(defthm nat-bytep-oal
    (implies (bmp bm)
             (nat-bytep (oal bm))))

;; OAL Write lemmas

(defthm bmp-!oal
  (implies (and (nat-bytep oal)
                (bmp bm))
           (bmp (!oal oal bm))))

(defthm bmp-extended-!oal
  (implies (and (nat-bytep oal)
                (bmp bm)
                (all-keys-as-big (al bm) oal))
           (bmp-extended (!oal oal bm))))


;; Mixed AI-OAL lemmas

(encapsulate
  ()

  (defthm al-!oal
    (equal (al (!oal al bm))
           (al bm)))

  (defthm ai-!oal
    (equal (ai a (!oal oal bm))
           (ai a bm)))

  (defthm oal-!ai
    (equal (oal (!ai a v bm))
           (oal bm)))

  (defthm oal-!oal
    (equal (oal (!oal oal bm))
           oal))

  (defthm !ai-!oal
    ;; !!! Warning.  See: LOOP-STOPPER
    (equal (!ai a v (!oal oal bm))
           (!oal oal (!ai a v bm))))

  (defthm !oal-oal
    (implies (bmp bm)
             (equal (!oal (oal bm) bm)
                    bm)))

  (defthm !oal-!oal
    (equal (!oal oal (!oal oal2 bm))
           (!oal oal bm))))


(in-theory (disable ai !ai al))

(in-theory (disable oal !oal))

(in-theory (disable bmp bmp-extended))




; Concrete memory read

(define read-mem$c (i bm)
  :guard (and (natp i)
              (bmp bm))
  :stobjs bm
  :inline t
  (mbe :logic
       (let ((i (nfix i)))
         (if (< i (al bm))
             (ai i bm)
           (mbr-kv i (oal bm))))
       :exec
       (if (< i (al bm))
           (ai i bm)
         (mbr-kv i (oal bm))))
  ///
  (defthm natp-read-mem$c
    (implies (bmp bm)
             (natp (read-mem$c i bm)))
    :rule-classes :type-prescription)

  (defthm integerp-read-mem$c
    (implies (bmp bm)
             (integerp (read-mem$c i bm))))

  (defthm in-range-read-mem$c
    (implies (bmp bm)
             (and (<= 0 (read-mem$c a bm))
                  (< (read-mem$c a bm) 256)))
    :rule-classes :linear))




; Concrete memory write

(define write-mem$c (i v bm)
  :guard (and (natp i)
              (unsigned-byte-p 8 v)
              (bmp bm))
  :guard-hints
  (("Goal"
    :in-theory (e/d (nat-bytep-insrt-kv)
                    ())))
  :stobjs bm
  :inline t
  (mbe :logic
       (let ((i (nfix i)))
         (if (< i (al bm))
             (!ai i v bm)
           (!oal (insrt-kv i v (oal bm)) bm)))
       :exec
       (if (< i (al bm))
           (!ai i v bm)
         (!oal (insrt-kv i v (oal bm)) bm)))
  ///
  (defthm bmp-write-mem$c
    (implies (and (natp i)
                  (unsigned-byte-p 8 v)
                  (bmp bm))
             (bmp (write-mem$c i v bm)))
    :hints (("Goal" :in-theory (e/d (nat-bytep-insrt-kv)))))

  (defthm bmp-extended-write-mem$c
    (implies (and (natp i)
                  (unsigned-byte-p 8 v)
                  (bmp-extended bm))
             (bmp-extended (write-mem$c i v bm)))
    :hints
    (("Goal" :in-theory (e/d (all-keys-as-big-del-kv
                              all-keys-as-big-insrt-kv
                              nat-bytep-insrt-kv
                              bmp-extended) ()))))

  (defthm al-write-mem$c
    (implies (bmp bm)
             (equal (al (write-mem$c i v bm))
                    (al bm)))
    :hints
    (("Goal" :in-theory (e/d () (!oal))))))


; Main four lemmas

(encapsulate
  ()

  (defthm read-mem$c-write-mem$c
    ;; g-same-s
    ;; g-diff-s
    (implies (bmp bm)
             (equal (read-mem$c a1 (write-mem$c a2 v bm))
                    (if (equal (nfix a1) (nfix a2))
                        v
                      (read-mem$c a1 bm))))
    :hints
    (("Goal" :in-theory (e/d (read-mem$c write-mem$c) ()))))

  (defthm write-mem$c-read-mem$c
    ;; Write-over-Read; A read "off the end" is 0, but a non-zero write extends X
    ;; s-same-g
    (implies (and (bmp bm)
                  (equal a1 a2))
             (equal (write-mem$c a1 (read-mem$c a2 bm) bm)
                    bm))
    :hints
    (("Goal" :in-theory (e/d (read-mem$c write-mem$c) ())
             :do-not-induct t)))

  (defthm write-mem$c-write-mem$c-same-address
    ;; Write-over-write; memory at specific address reflects last value written
    ;; s-same-s
    (implies (and (bmp bm)
                  (equal a1 a2))
             (equal (write-mem$c a1 v (write-mem$c a2 w bm))
                    (write-mem$c a1 v bm)))
    :hints
    (("Goal" :in-theory (e/d (read-mem$c write-mem$c) ())
             :do-not-induct t)))

  (defthm write-mem$c-write-mem$c-different-address
    ;; Order of writes to different memory locations is irrelavant
    ;; s-diff-s
    (implies (and (bmp bm)
                  (not (equal (nfix a1) (nfix a2))))
             ;; !!! Warning.  See: LOOP-STOPPER
             (equal (write-mem$c a1 v1 (write-mem$c a2 v2 bm))
                    (write-mem$c a2 v2 (write-mem$c a1 v1 bm))))
    :hints
    (("Goal" :in-theory (e/d (read-mem$c write-mem$c) ())
             :do-not-induct t))))


; Some functions to clear the memory

(defun init-ai-zero-small (i bm)
  "Initialize array A to hold zero values with fixnum indicies."
  (declare (xargs :guard (and (natp i)
                              (<= i (al bm))
                              (< (al bm) (expt 2 60)))
                  :stobjs bm
                  :measure (nfix (- (al bm) i))
                  :hints
                  (("Goal" :in-theory (e/d (al))))))
  (let ((i (the (unsigned-byte 60) i)))
    (if (mbe :logic (zp (- (al bm) i))
             :exec  (= i (the (unsigned-byte 60) (al bm))))
        bm
      (let ((bm (write-mem$c i 0 bm)))
        (init-ai-zero-small (the (unsigned-byte 60) (1+ i)) bm)))))

(defun init-ai-zero-large (i bm)
  "Initialize array A to hold zero values with non-fixnum indicies."
  (declare (xargs :guard (and (natp i)
                              (<= i (al bm)))
                  :stobjs bm
                  :measure (nfix (- (al bm) i))
                  :hints
                  (("Goal" :in-theory (e/d (al))))))
  (if (mbe :logic (zp (- (al bm) i))
           :exec  (= i (al bm)))
        bm
      (let ((bm (write-mem$c i 0 bm)))
        (init-ai-zero-large (1+ i) bm))))


(defun init-ai (bm)
  "Initialize array A to hold zero values."
  (declare (xargs :guard t
                  :stobjs bm))
  (if (< (al bm) (expt 2 60))
      (init-ai-zero-small 0 bm)
    (init-ai-zero-large 0 bm)))

(defun init-bm (bm)
  "Initialize BM to hold zero values."
  (declare (xargs :guard t
                  :stobjs bm))
  (let* ((bm (init-ai bm))
         (bm (!oal NIL bm)))
    bm))


; Provide only the (read-mem$c and write-mem$c) memory lemmas.

(in-theory
 (disable

  ;; From "ordered-alistp.lisp"
  natp-mbr-kv
  in-range-mbr-kv

  ;; nth-!nth
  !nth-nth
  !nth-!nth-same-address
  !nth-!nth-different-addresses
  nth-from-atom
  nth-short-list

  ap-forward-to-true-listp
  bmp-extended-forward
  bmp-forward
  ap-resize-list
  ap-!nth
  ;; natp-nth-of-ap-type-prescription ; Needed when TAU system engaged?
  ai-type-type-prescription-natp
  ai-type-type-prescription-integerp
  ai-rewrite
  ;; in-range-nth-of-ap (local event)
  ai-of-bm-is-n08p
  bmp-!ai
  al-!ai
  ai-!ai
  !ai-ai
  !ai-!ai-same-address
  !ai-!ai-different-addresses
  nat-bytep-oal
  bmp-!oal
  bmp-extended-!oal
  al-!oal
  ai-!oal
  oal-!ai
  oal-!oal
  !ai-!oal
  !oal-oal
  !oal-!oal

  ;; The significant lemmas remain enabled
  ;; natp-read-mem$c
  ;; integerp-read-mem$c
  ;; in-range-read-mem$c

  ;; bmp-write-mem$c
  ;; bmp-extended-write-mem$c
  ;; al-write-mem$c

  ;; read-mem$c-write-mem$c
  ;; write-mem$c-read-mem$c
  ;; write-mem$c-write-mem$c-same-address
  ;; write-mem$c-write-mem$c-different-address

  ))
