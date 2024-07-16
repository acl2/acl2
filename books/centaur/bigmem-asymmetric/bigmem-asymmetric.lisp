; Big Memory Model
; Copyright (C) 2021 Centaur Technology
;
; For development:
; (ld "bigmem-asymmetric.lisp" :ld-pre-eval-print t)

; Should be removed
; (include-book "misc/disassemble" :dir :system :ttags (:disassemble$))

; Contact
;   Intel Corporation, ACL2 Formal Verification Group
;   1300 South MoPac Expy,  Austin, TX  78746, USA
;   https://www.intel.com/
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
;   Modified extensively by: Warren A. Hunt, Jr <warren.hunt@intel.com>
;     This memory model provides faster read/update operations for some
;     fixed (at build time) size of memory and slower access to the rest
;     of the memory; this helps when emulating memory when running Linux.

(in-package "BIGMEM-ASYMMETRIC")

(include-book "concrete-asymmetric")  ;; Contents replaced with what is below...

(include-book "centaur/defrstobj2/def-multityped-record" :dir :system)

; (include-book "std/lists/repeat" :dir :system)  ;; Redundant with above

(include-book "std/stobjs/absstobjs" :dir :system)

; Removed the ``local'' designation to process this file with ``cert.pl''.
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

(include-book "ihs/basic-definitions" :dir :system)

(local (xdoc::set-default-parents bigmem))

;; ----------------------------------------------------------------------

(defn ubp8-fix (x)
  (acl2::loghead 8 (ifix x)))

#!RSTOBJ2
(def-multityped-record ubp8
  :elem-p       (unsigned-byte-p 8 x)
  :elem-default 0
  :elem-fix     (bigmem-asymmetric::ubp8-fix x)
  :in-package-of bigmem-asymmetric::bigmem-pkg)

(defn mem$ap (mem$a)
  (declare (ignore mem$a))
  t)

(defn create-mem$a ()
  nil)

(define read-mem$a ((addr :type (unsigned-byte 64))
                    (mem$a mem$ap))
  (ubp8-get addr mem$a))

(define write-mem$a ((addr :type (unsigned-byte 64))
                     (val  :type (unsigned-byte 8))
                     (mem$a mem$ap))
  (ubp8-set addr val mem$a))


; Different from the original "bigmem.lisp" (a 2^64-byte memory model), we
; define the correspondence theorem in a somewhat different manner; in the
; "bigmen.lisp" file, a DEFUN-SK event was used to define the correspondence
; function, CORR.

(defthm read-mem$a-create-mem$a-is-0
  (equal (read-mem$a i (create-mem$a))
         0)
  :hints
  (("Goal" :in-theory (e/d (read-mem$a ubp8-get ubp8-get1)))))

(defthm read-mem$a-write-mem$a
  (equal (read-mem$a a1 (write-mem$a a2 v mem))
         (if (equal a1 a2)
             (ubp8-fix v)
           (read-mem$a a1 mem)))
  :hints
  (("Goal" :in-theory (e/d (read-mem$a write-mem$a)))))

#|
(defthm write-mem$a-read-mem$a
  (implies (and (natp i)
                (unsigned-byte-p 8 v)
                (ubp8-p mem))
           (equal (write-mem$a i v (read-mem$a i mem))
                  mem))
  :hints
  (("Goal" :in-theory (e/d (ubp8-p read-mem$a write-mem$a)))))
|#


; Now the lemmas about the initial concrete memory...

(encapsulate
  ()

  (local
   (defun sub-1-sub-1-template (i n)
     (if (zp i)
         (list i n)
       (sub-1-sub-1-template (1- i) (1- n)))))

  (local
   (defthm car-repeat
     (implies (posp n)
              (equal (car (acl2::repeat n x)) x))
     :hints
     (("Goal" :in-theory (e/d (acl2::repeat))))))

  (local
   (defthm nth-repeat
     (implies (and (natp i)
                   (natp n)
                   (< i n))
              (equal (nth i (acl2::repeat n v)) v))
     :hints
     (("Goal" :induct (sub-1-sub-1-template i n)
              :in-theory (e/d (acl2::repeat))))))

  (local
   (defthm read-mem$c-less-than-al
     (implies (and (natp i)
                   (< i (al (create-bm))))
              (equal (read-mem$c i (create-bm))
                     0))
     :hints
     (("Goal" :do-not-induct t
              :in-theory (e/d (read-mem$c create-bm ai al)
                              (make-list-ac (make-list-ac)
                                            acl2::repeat (acl2::repeat)))))))

  (local
   (defthm read-mem$c-greater-than-or-equal-to-al
     (implies (and (natp i)
                   (<= (al (create-bm)) i))
              (equal (read-mem$c i (create-bm))
                     0))
     :hints
     (("Goal" :do-not-induct t
              :in-theory (e/d (read-mem$c create-bm al oal)
                              (make-list-ac (make-list-ac)
                                            acl2::repeat (acl2::repeat)))))))

  (defthm read-mem$c-bm-create
    ;; Corresponds to lemma READ-MEM$C-FROM-CREATE-MEM$C in "bigmem.lisp".
    (implies (natp i)
             (equal (read-mem$c i (create-bm))
                    0))
    :hints
    (("Goal" :do-not-induct t
             :in-theory (e/d (al)
                             (create-bm make-list-ac (make-list-ac)
                                        acl2::repeat (acl2::repeat))  )
             :cases ((< i (al bm)))))
    :otf-flg t))


; Now the lemmas about the initial concrete memory...

(defun mem-corr-item (i bm m)
  (declare (xargs :guard (and (natp i)
                              (< i (expt 2 64)))
                  :stobjs bm))
  (equal (read-mem$a i m)
         (read-mem$c i bm)))

(defthm mem-corr-item-create
  (implies (natp i)
           (mem-corr-item i (create-bm) (create-mem$a)))
  :hints
  (("Goal" :do-not-induct t
           :in-theory (e/d (al)
                           (create-bm create-mem$a (create-mem$a)
                                      make-list-ac (make-list-ac)
                                      acl2::repeat (acl2::repeat))  ))))
(in-theory (disable mem-corr-item))

(defun mem-corr-items (i bm m)
  (declare (xargs :guard (and (natp i) (< i (expt 2 64)))
                  :stobjs bm))
  (if (zp i)
      (mem-corr-item 0 bm m)
    (let ((i-1 (1- i)))
      (and (mem-corr-item i bm m)
           (mem-corr-items i-1 bm m)))))

(defthm mem-corr-items-create
  (implies (natp i)
           (mem-corr-items i (create-bm) (create-mem$a)))
  :hints
  (("Goal" :in-theory (e/d (al)
                           (create-bm create-mem$a (create-mem$a)
                                      make-list-ac (make-list-ac)
                                      acl2::repeat (acl2::repeat))  ))))
(in-theory (disable mem-corr-items))

(defun mem-corr (bm m)
  ;; Could be a DEFUN-NX event...
  (declare (xargs :guard t
                  :stobjs bm
                  :guard-hints
                  (("Goal" :in-theory (enable nth oal bmp)))))
  (and (bmp-extended bm)
       (mem-corr-items (1- (expt 2 64)) bm m)))

(in-theory (disable mem-corr))

(encapsulate
  ()

  (local
   (defthm ap-repeat
     (implies (and (natp n)
                   (unsigned-byte-p 8 v))
              (ap (acl2::repeat n v)))
     :hints
     (("Goal" :in-theory (e/d (acl2::repeat))))))

  (local
   (defthm bmp-create-bm
     (bmp (create-bm))
     :hints
     (("Goal"; :do-not-induct t
              :in-theory (e/d (bmp create-bm)
                              (make-list-ac (make-list-ac)
                               acl2::repeat (acl2::repeat)))))))

  (local
   (defthm all-key-as-big-ok
     (all-keys-as-big (al (create-bm))
                      (oal (create-bm)))
     :hints
     (("Goal" ; :do-not-induct t
              :in-theory (e/d (bmp create-bm al oal all-keys-as-big)
                              (make-list-ac (make-list-ac)
                               acl2::repeat (acl2::repeat)))))))


  (local
   (defthm create-mem{correspondence}-help
     (mem-corr-items 18446744073709551615
                     (create-bm)
                     (create-mem$a))
     :hints
     (("Goal" :in-theory (e/d (ubp8-p ubp8-p1)
                              (create-bm create-mem$a (create-mem$a)
                                      make-list-ac (make-list-ac)
                                      acl2::repeat (acl2::repeat)))))))

  (DEFTHM CREATE-MEM{CORRESPONDENCE}
      (MEM-CORR (CREATE-BM) (CREATE-MEM$A))
    :hints
    (("Goal" :in-theory (e/d (bmp-extended mem-corr)
                             (mem-corr-items-create
                              create-bm create-mem$a (create-mem$a)
                              make-list-ac (make-list-ac)
                              acl2::repeat (acl2::repeat)))))
    :otf-flg t
    :RULE-CLASSES NIL))

(DEFTHM CREATE-MEM{PRESERVED}
  (MEM$AP (CREATE-MEM$A))
  :RULE-CLASSES NIL)

(DEFTHM READ-MEM{GUARD-THM}
  (IMPLIES (AND (MEM-CORR BM MEM)
                (UNSIGNED-BYTE-P 64 I)
                (MEM$AP MEM))
           (NATP I))
  :RULE-CLASSES NIL)

(DEFTHM WRITE-MEM{GUARD-THM}
  (IMPLIES (AND (MEM-CORR BM MEM)
                (UNSIGNED-BYTE-P 64 I)
                (UNSIGNED-BYTE-P 8 V)
                (MEM$AP MEM))
           (AND (NATP I) (UNSIGNED-BYTE-P 8 V)))
  :RULE-CLASSES NIL)

(DEFTHM WRITE-MEM{GUARD-THM}
  (IMPLIES (AND (MEM-CORR BM MEM)
                (UNSIGNED-BYTE-P 64 I)
                (UNSIGNED-BYTE-P 8 V)
                (MEM$AP MEM))
           (AND (NATP I) (UNSIGNED-BYTE-P 8 V)))
  :RULE-CLASSES NIL)

(DEFTHM WRITE-MEM{PRESERVED}
  (IMPLIES (AND (UNSIGNED-BYTE-P 64 I)
                (UNSIGNED-BYTE-P 8 V)
                (MEM$AP MEM))
           (MEM$AP (WRITE-MEM$A I V MEM)))
  :RULE-CLASSES NIL)


(defthm mem-corr-items-implies-read-mem$c-equal-read-mem$a
    (implies (and (bmp bm)
                  (natp i)
                  (natp j)
                  (<= i j)
                  (mem-corr-items j bm mem))
             (equal (read-mem$c i bm)
                    (read-mem$a i mem)))
    :hints
    (("Goal" :induct (mem-corr-items j bm mem)
             :in-theory (e/d (mem-corr-items mem-corr-item)))))

(DEFTHM READ-MEM{CORRESPONDENCE}
  (IMPLIES (AND (MEM-CORR BM MEM)
                (UNSIGNED-BYTE-P 64 I)
                (MEM$AP MEM))
           (EQUAL (READ-MEM$C I BM)
                  (READ-MEM$A I MEM)))
  :hints
  (("Goal" :do-not-induct t
           :in-theory (e/d (bmp-extended mem-corr)
                           (mem-corr-items-implies-read-mem$c-equal-read-mem$a))
           :use ((:instance mem-corr-items-implies-read-mem$c-equal-read-mem$a
                            (i i)
                            (j (1- (expt 2 64)))))))
  :RULE-CLASSES NIL)

(defthm mem-corr-items-implies-write-mem$c-equal-write-mem$a
  (implies (and (bmp bm)
                (natp i)
                (natp j)
                (<= i j)
                (unsigned-byte-p 8 v)
                (mem-corr-items j bm mem))
           (mem-corr-items j
                           (write-mem$c i v bm)
                           (write-mem$a i v mem)))
  :hints
  (("Goal" :induct (mem-corr-items j bm mem)
           :in-theory (e/d (mem-corr-items mem-corr-item))))
  :otf-flg t)

(DEFTHM WRITE-MEM{CORRESPONDENCE}
  (IMPLIES (AND (MEM-CORR BM MEM)
                (UNSIGNED-BYTE-P 64 I)
                (UNSIGNED-BYTE-P 8 V)
                (MEM$AP MEM))
           (MEM-CORR (WRITE-MEM$C I V BM)
                     (WRITE-MEM$A I V MEM)))
  :hints
  (("Goal" :do-not-induct t
           :in-theory (e/d (bmp-extended mem-corr)
                           (mem-corr-items-implies-write-mem$c-equal-write-mem$a))
           :use ((:instance mem-corr-items-implies-write-mem$c-equal-write-mem$a
                            (i i)
                            (j (1- (expt 2 64)))))))
  :RULE-CLASSES NIL)



;; For an attempt to automatically generate and prove all required lemmas, the
;; acl2::defabsstobj-events form can be used.  Our approaoch is more pedantic.

(acl2::defabsstobj mem

  ;; Much of what follows was copied verbatim from the ACL2 Documentation topic
  ;; ABSTRACT-STOBJ.

  ;; Foundation is the name of an existing STOBJ, which may have been
  ;; introduced either with [defstobj] or with defabsstobj.

  :foundation bm

  ;; Recognizer is a function spec (for the recognizer function).  The valid
  ;; keywords are :LOGIC and :EXEC.  The default for recognizer is obtained by
  ;; adding the suffix "P" to name.  The default value for :LOGIC is formed by
  ;; adding the suffix "$AP" to recognizer; for :EXEC, by adding the suffix
  ;; "$CP".  The :EXEC function must be the recognizer for the foundational
  ;; STOBJ (which can be specified using the :FOUNDATION keyword).

  ;; Here we are explict with the abstract STOBJ recognizer as well as the
  ;; recognizers for the :logic and :exec functions.  With explict recognizer
  ;; functions, the MEMP (recognizer) function is not used (as described just
  ;; above).

  :recognizer (memp              ;; The recognizer name seed
               :logic mem$ap     ;; The :logic recognizer (which, in this case,
                                 ;; is the same as would be generated)
               :exec bmp         ;; The :exec recognizer
               )

  ;; Creator is a function spec (for the creator function).  The valid keywords
  ;; are :LOGIC and :EXEC.  The default for creator is obtained by adding the
  ;; prefix "CREATE-" to name.  The default value for :LOGIC is formed by
  ;; adding the suffix "$A" to creator; for :EXEC, by adding the suffix "$C".
  ;; The :EXEC function must be the creator for the foundational stobj (which
  ;; can be specified using the :FOUNDATION keyword).

  ;; Like with the recognizer, we are providing explict names for the various
  ;; arguments.  Also required are the :CORRESPONDENCE and :PRESERVED lemmas,
  ;; which are given explict names.

  :creator (create-mem           ;; Name seed for creation function
            :logic create-mem$a  ;; Explict abstract creation function name
            :exec  create-bm     ;; Explict concrete creation function name


            :correspondence create-mem{correspondence}
            :preserved      create-mem{preserved})

  ;; Corr-fn is a known function symbol that takes two arguments (for the
  ;; correspondence theorems).  The default for corr-fn is obtained by adding
  ;; the suffix "$CORR" to name.

  ;; The abstract and concrete states are related by the :CORR-FN
  ;; (correspondence function).

  :corr-fn mem-corr

  ;; The value of :EXPORTS is a non-empty true list.  Each ei is a function
  ;; spec (for an exported function).  The valid keywords are :LOGIC, :EXEC,
  ;; :CORRESPONDENCE, and :GUARD-THM, :PROTECT, :UPDATER, and also :PRESERVED
  ;; if and only if the specified :EXEC function returns the foundational
  ;; stobj.  The default values for all of these keywords except :UPDATER and
  ;; :PROTECT are obtained by respectively adding the suffix "$A" "$C",
  ;; "{CORRESPONDENCE}", "{GUARD-THM}", or "{PRESERVED}".  For :PROTECT, the
  ;; default is nil unless the defabsstobj event specifies :PROTECT-DEFAULT t.
  ;; If :UPDATER upd is supplied and upd is not nil, then function exported by
  ;; the function spec is a child stobj accessor whose corresponding updater is
  ;; upd; see the discussion of :UPDATER in [nested-stobjs].

  ;; Once again, we are explict with our naming of functions and events.

  :exports ((read-mem
             :logic read-mem$a
             :exec  read-mem$c$inline
             :correspondence read-mem{correspondence}
             :guard-thm read-mem{guard-thm})

            (write-mem
             :logic write-mem$a
             :exec  write-mem$c$inline
             :correspondence write-mem{correspondence}
             :guard-thm write-mem{guard-thm}
             )))

#|
(defthm integerp-read-mem
  (implies (natp i)
           (integerp (read-mem i mem)))
  :hints
  (("Goal" :in-theory (e/d (read-mem$a
                            ubp8-get
                            ubp8-get1
                            ubp8-to-mtr
                            )))))
|#

(defthm integerp-ubp8-get1
  (implies (ubp8-p1 mem)
           (integerp (ubp8-get1 i mem)))
  :hints
  (("Goal" :in-theory (e/d (ubp8-get1 ubp8-p1) ))))

(defthm zero-<=-ubp8-get1
  (implies (ubp8-p1 mem)
           (and (<= 0 (ubp8-get1 i mem))
                (< (ubp8-get1 i mem) 256)))
  :hints
  (("Goal" :in-theory (e/d (ubp8-get1 ubp8-p1) )))
  :rule-classes (:rewrite :linear))

(defthm natp-read-mem
  (implies (and (natp i)
                (ubp8-p mem))
           (natp (read-mem i mem)))
  :hints
  (("Goal" :in-theory (e/d (read-mem$a ubp8-get ; ubp8-get1
                                       ubp8-p ubp8-to-mtr
                                       natp
                                       unsigned-byte-p)) )))

(defthm read-mem-over-write-mem
  (equal (read-mem addr-1 (write-mem addr-2 val mem))
         (if (equal addr-1 addr-2)
             (loghead 8 (ifix val))
           (read-mem addr-1 mem))))

(defthm write-mem-shadow-writes
  (equal (write-mem addr val-2 (write-mem addr val-1 mem))
         (write-mem addr val-2 mem))
  :hints (("Goal" :in-theory (e/d (write-mem$a) ()))))

(defthm write-mem-commute-safely
  (implies (not (equal addr-2 addr-1))
           (equal (write-mem addr-2 val-2 (write-mem addr-1 val-1 mem))
                  (write-mem addr-1 val-1 (write-mem addr-2 val-2 mem))))
  :hints (("Goal" :in-theory (e/d (write-mem$a) ()))))

(defthm write-the-read
  (equal (write-mem addr (read-mem addr mem) mem)
         mem)
  :hints (("Goal" :in-theory (e/d (write-mem
                                   write-mem$a
                                   read-mem
                                   read-mem$a)
                                  ()))))

(defthm read-mem-from-nil
  (equal (read-mem i nil) 0)
  :hints (("Goal" :in-theory (e/d (read-mem read-mem$a) ()))))

(defthmd loghead-identity-alt
  (implies (unsigned-byte-p n val)
           (equal (acl2::loghead n (ifix val))
                  val)))

(in-theory (e/d () (read-mem write-mem create-mem)))

;; ----------------------------------------------------------------------

;; Get the contents of the entire memory as a linear list --- suitable
;; for use by tools that are used to defstobj's logic representation
;; of an array.

(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)

(defthm unsigned-byte-p-8-read-mem
  (unsigned-byte-p 8 (read-mem addr mem))
  :hints (("Goal" :in-theory (e/d (read-mem read-mem$a) ()))))

(define get-mem-aux  ((i :type (unsigned-byte 64))
                      (mem  memp))
  :non-executable t
  :returns (memlist (acl2::unsigned-byte-listp 8 memlist)
                    :hyp (memp mem))
  :enabled t
  (if (zp i)
      (list (read-mem i mem))
    (cons (read-mem i mem)
          (get-mem-aux (1- i) mem)))
  ///
  (defthm len-of-get-mem-aux
    (implies (and (memp mem)
                  (natp i))
             (equal (len (get-mem-aux i mem))
                    (+ 1 i))))

  (local (include-book "std/lists/nth" :dir :system))

  (defthm read-mem-and-get-mem-aux
    (implies (and (memp mem)
                  (<= i j)
                  (natp i)
                  (natp j))
             (equal (nth i (acl2::rev (get-mem-aux j mem)))
                    (read-mem i mem))))

  (defthm get-mem-aux-beyond-write-mem
    (implies (< j i)
             (equal (get-mem-aux j (write-mem i v mem))
                    (get-mem-aux j mem)))
    :hints (("goal" :in-theory (e/d (get-mem-aux) nil))))

  (defthm get-mem-aux-after-write-mem
    (implies (and (<= i j)
                  (natp i)
                  (natp j))
             (equal (get-mem-aux j (write-mem i v mem))
                    (update-nth (- j i) (loghead 8 v) (get-mem-aux j mem))))
    :hints (("Goal" :in-theory (e/d (get-mem-aux) ())))))

(define get-mem ((mem  memp))
  :short "Get the entire contents of the memory in the form of a linear list"
  :non-executable t
  :returns (memlist (acl2::unsigned-byte-listp 8 memlist)
                    :hyp (memp mem))
  (acl2::rev (get-mem-aux (1- (expt 2 64)) mem))

  ///

  (defthmd rewrite-read-mem-to-nth-of-get-mem
    (implies (and (unsigned-byte-p 64 i)
                  (memp mem))
             (equal (read-mem i mem)
                    (nth i (get-mem mem)))))

  (local (include-book "std/lists/nth" :dir :system))
  (local (include-book "std/lists/update-nth" :dir :system))

  (local
   (defthm rev-and-update-nth
     (implies (and (equal j (len xs))
                   (< i j)
                   (natp i))
              (equal (update-nth i v (acl2::rev xs))
                     (acl2::rev (update-nth (- (- j 1) i) v xs))))
     :hints (("Goal" :in-theory (e/d (acl2::rev) ())))))

  (defthm get-mem-after-write-mem
    (implies (unsigned-byte-p 64 i)
             (equal (get-mem (write-mem i v mem))
                    (update-nth i (loghead 8 v) (get-mem mem))))
    :hints (("Goal" :do-not-induct t))))


;; ----------------------------------------------------------------------

(local
 (define init-mem-region ((n :type (unsigned-byte 60))
                          (val :type (unsigned-byte 8))
                          (mem memp))
   :prepwork ((local (in-theory (e/d (unsigned-byte-p) ()))))
   (if (zp n)
       mem
     (b* ((val (the (unsigned-byte 8) (if (< val #xFE) (1+ val) 0)))
          (mem (write-mem n val mem)))
       (init-mem-region (the (unsigned-byte 60) (1- n)) val mem)))))

;; (profile 'good-mem$cp)
;; (profile 'good-level1p)
;; (profile 'good-l1p)
;; (profile 'good-pagesp)
;; (profile 'write-mem$c)

;; (time$ (init-mem-region (1- (expt 2 20)) 0 mem))

;; (memsum)

; :i-am-here

(encapsulate
  ()

 ;; Some arithmetic facts...

  (local
   (include-book "arithmetic-5/top" :dir :system))

  (local
   (defun ind-hint-2 (x y)
     (if (or (zp x) (zp y))
         42
       (ind-hint-2 (floor x 2) (floor y 2)))))

  (local
   (defthm logxor-greater-or-equal-to-zero
     (implies (and (natp x) (natp y))
              (natp (logxor x y)))
     :hints (("Goal" :induct (ind-hint-2 x y)))
     :rule-classes :type-prescription))

  (local
   (defun ind-hint-3 (x y n)
     (if (or (zp x) (zp y) (zp n))
         42
       (ind-hint-3 (floor x 2) (floor y 2) (+ -1 n)))))

  (local
   (defthm break-logxor-apart
     (implies (and (natp x)
                   (natp y))
              (equal (logxor x y)
                     (+ (* 2 (logxor (floor x 2)
                                     (floor y 2)))
                        (logxor (mod x 2)
                                (mod y 2)))))
     :rule-classes nil))

 ;; This next rule would be a weird rewrite rule because of the (EXPT
 ;; 2 N) in the conclusion.  As a linear rule, then entire conclusion
 ;; doesn't need to match.

  (local
   (defthm logxor-<=-expt-2-to-n
     (implies (and (natp x) (natp y)
                   (< x (expt 2 n))
                   (< y (expt 2 n)))
              (< (logxor x y) (expt 2 n)))

     :hints (("Goal" :induct (ind-hint-3 x y n))
             ("Subgoal *1/2.6'4'" :use ((:instance break-logxor-apart)))
             ("Subgoal *1/2.10'4'" :use ((:instance break-logxor-apart))))
     :rule-classes :linear))

 ;; Yahya notes that the "ihs-extensions.lisp" book provides a better (or, at
 ;; least, supported) method for doing the kind of thing this code does
 ;; crudely.

  (local
   (defthm logxor-two-bytes
     (implies (and (natp x)
                   (< x 256)
                   (natp y)
                   (< y 256))
              (and (<= 0 (logxor x y))
                   (< (logxor x y) 256)))
     :hints
     (("Goal"
       :use ((:instance logxor-<=-expt-2-to-n
                        (x x) (y y) (n 8)))))
     :rule-classes :linear))

  (local
   (defthm integerp-read-mem
     (integerp (read-mem addr mem))
     :hints (("Goal"
              :in-theory (e/d () (unsigned-byte-p-8-read-mem))
              :use ((:instance unsigned-byte-p-8-read-mem
                               (addr addr)
                               (mem mem)))))))


  (define xor-mem-region ((n   :type (unsigned-byte 60))
                          (sum :type (unsigned-byte 8))
                          (mem memp))
    :prepwork ((local (in-theory (e/d (unsigned-byte-p) (logxor)))))
    (let ((n   (the (unsigned-byte 60) n))
          (sum (the (unsigned-byte 8) sum)))
      (if (mbe :logic (zp n) :exec (= n 0))
          (mv sum mem)
        (b* ((val (the (unsigned-byte 8)
                       (read-mem n mem)))
             (xor-sum (logxor val sum)))
          (xor-mem-region (the (unsigned-byte 60) (1- n))
                          (the (unsigned-byte 8) xor-sum)
                          mem))))
    ///

    (defthm natp-car-xor-mem-region
     (implies (and (natp n)
                   (unsigned-byte-p 8 sum)
                   (memp mem))
              (natp (car (xor-mem-region n sum mem))))
      :hints
      (("Goal" :in-theory (e/d (xor-mem-region unsigned-byte-p natp)
                               (logxor-two-bytes))))
      :rule-classes :type-prescription)

    (defthm bytep-car-xor-mem-region
     (implies (and (natp n)
                   (unsigned-byte-p 8 sum)
                   (memp mem))
              (and (<= 0 (car (xor-mem-region n sum mem)))
                   (< (car (xor-mem-region n sum mem)) 256)))
      :hints
      (("Goal" :in-theory (e/d (xor-mem-region)
                               (logxor-two-bytes))
               :use ((:instance logxor-two-bytes
                                (x sum)
                                (y (read-mem n mem))))))
      :rule-classes :linear)

    (defthm memp-cadr-xor-mem-region
     (implies (and (natp n)
                   (natp sum)
                   (memp mem))
              (memp (cadr (xor-mem-region n sum mem)))))
    ))


; (include-book "misc/disassemble" :dir :system :ttags (:disassemble$))
; (time$ (xor-mem-region (1- (expt 2 30)) 0 mem))


;; ----------------------------------------------------------------------

(defxdoc bigmem-asymmetric
  :pkg "BIGMEM-ASYMMETRIC"
  :parents (acl2::projects)
  :short "A @('2^64')-byte memory model that is logically a record but
  provides array-like performance for a fixed amount of emulated memory
  and slow(er) performance for the remaining (higher) memory locations."

  :long "<p>The @('bigmem') library implements the idea in the
  following paper using nested and abstract STOBJs, which leads to a simpler
  implementation of a large memory.  This @('bigmem-asymmetric') library
  provides faster access/update performance for some amount of low-address
  memory, and slow (alist-style) performance for high-address memory
  locations. For spiritual discussion of this kind of memory modeling, please
  see the reference below. </p>

  <blockquote>Warren A. Hunt, Jr. and Matt Kaufmann. A Formal Model of a Large
  Memory that Supports Efficient Execution. In Proceedings of the 12th
  International Conference on Formal Methods in Computer-Aided Design (FMCAD
  2012, Cambrige, UK, October 22-25), 2012</blockquote>

  <p>These books define an abstract STOBJ called @('mem') that exports an
  accessor function @('read-mem') and an updater function @('write-mem').
  @('mem') is logically a typed record that models @('2^64') bytes.  The
  corresponding concrete STOBJ for @('mem') is @('bm'), which is a STOBJ
  containing STOBJs that provides an array for the first part (0...) of
  the natural-number-addressed memory and for essentially allocates chunks of
  bytes on demand; see @(see bigmem-concrete-stobj) for implementation
  details.</p>

  <p>An obvious application of @('bigmem-asymmetric') is to model memory;
  @('mem') can be used as a child STOBJ to define a field representing the
  memory (up to @('2^64') bytes) in a parent STOBJ that models some machine's
  state. See @('projects/x86isa/machine/state.lisp') for one such example.</p>")

;; ----------------------------------------------------------------------
